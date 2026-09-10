import Std.Time.Date.PlainDate

/-! The emitted identity profile of the pinned eFMI Beta 1 schemas:
brace-delimited hexadecimal UUIDs and UTC timestamps at whole seconds.
Calendar validity reuses `Std.Time`, including Gregorian leap years.
The producer profile uses years 0001–9999 and hours 00–23; it does not accept
every alternate lexical representation of `xs:dateTime`. These predicates do
not establish global UUID freshness or the accuracy of a supplied wall clock. -/
namespace Rumoca.EFMI.Manifest

structure Identity where
  container : String
  algorithm : String
  production : String
  generated : String
  deriving Repr, BEq, DecidableEq

namespace Identity

inductive Slot where
  | literal (value : Char)
  | decimal
  | hex
  deriving Repr, DecidableEq

def Slot.Accepts : Slot → Char → Prop
  | .literal value, c => c = value
  | .decimal, c => '0' ≤ c ∧ c ≤ '9'
  | .hex, c => ('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f') ∨ ('A' ≤ c ∧ c ≤ 'F')

instance (slot : Slot) (c : Char) : Decidable (slot.Accepts c) := by
  cases slot <;> unfold Slot.Accepts <;> infer_instance

/-- Whole-string membership: both the layout and the input must be exhausted. -/
def Matches : List Slot → List Char → Prop
  | [], [] => True
  | slot :: slots, c :: cs => slot.Accepts c ∧ Matches slots cs
  | _, _ => False

instance matchesDecidable (slots : List Slot) (cs : List Char) : Decidable (Matches slots cs) :=
  match slots, cs with
  | [], [] => isTrue trivial
  | slot :: slots, c :: cs =>
    letI := matchesDecidable slots cs
    inferInstanceAs (Decidable (slot.Accepts c ∧ Matches slots cs))
  | [], _ :: _ | _ :: _, [] => isFalse id

def uuidLayout : List Slot :=
  [.literal '{'] ++ List.replicate 8 .hex ++ [.literal '-'] ++
    List.replicate 4 .hex ++ [.literal '-'] ++ List.replicate 4 .hex ++
    [.literal '-'] ++ List.replicate 4 .hex ++ [.literal '-'] ++
    List.replicate 12 .hex ++ [.literal '}']

def UUID (text : String) : Prop := Matches uuidLayout text.toList

instance (text : String) : Decidable (UUID text) := inferInstanceAs (Decidable (Matches _ _))

def utcLayout : List Slot :=
  List.replicate 4 .decimal ++ [.literal '-'] ++ List.replicate 2 .decimal ++
    [.literal '-'] ++ List.replicate 2 .decimal ++ [.literal 'T'] ++
    List.replicate 2 .decimal ++ [.literal ':'] ++ List.replicate 2 .decimal ++
    [.literal ':'] ++ List.replicate 2 .decimal ++ [.literal 'Z']

/-- Positional base-ten value; `Matches utcLayout` separately requires ASCII digits. -/
def digits (cs : List Char) (offset width : Nat) : Nat :=
  ((cs.drop offset).take width).foldl (fun n c => 10 * n + (c.toNat - '0'.toNat)) 0

/-- Use the standard library's dependent month/day bounds and date validity,
without clipping or normalizing a malformed date. -/
def Calendar (year month day : Nat) : Prop :=
  if h : (1 ≤ month ∧ month ≤ 12) ∧ (1 ≤ day ∧ day ≤ 31) then
    (Std.Time.Year.Offset.ofNat year).Valid
      (Std.Time.Month.Ordinal.ofNat month h.1) (Std.Time.Day.Ordinal.ofNat day h.2)
  else False

instance (year month day : Nat) : Decidable (Calendar year month day) := by
  unfold Calendar
  split <;> infer_instance

def UTC (text : String) : Prop :=
  let cs := text.toList
  Matches utcLayout cs ∧
    (1 ≤ digits cs 0 4 ∧ digits cs 0 4 ≤ 9999) ∧
    Calendar (digits cs 0 4) (digits cs 5 2) (digits cs 8 2) ∧
    digits cs 11 2 < 24 ∧ digits cs 14 2 < 60 ∧ digits cs 17 2 < 60

instance (text : String) : Decidable (UTC text) := by unfold UTC; infer_instance

/-- Compare UUIDs after ASCII case normalization: different hex letter case
must not give two manifests permission to identify the same UUID. -/
def Distinct (identity : Identity) : Prop :=
  identity.container.toLower ≠ identity.algorithm.toLower ∧
    identity.container.toLower ≠ identity.production.toLower ∧
    identity.algorithm.toLower ≠ identity.production.toLower

instance (identity : Identity) : Decidable (Distinct identity) := by
  unfold Distinct; infer_instance

def Valid (identity : Identity) : Prop :=
  UUID identity.container ∧ UUID identity.algorithm ∧ UUID identity.production ∧
    UTC identity.generated ∧ Distinct identity

instance (identity : Identity) : Decidable (Valid identity) := by unfold Valid; infer_instance

def valid (identity : Identity) : Bool := decide identity.Valid

end Identity
end Rumoca.EFMI.Manifest
