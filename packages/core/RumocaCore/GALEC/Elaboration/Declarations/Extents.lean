import Parser.DecimalNat
import Parser.Token

/-! Positive static declaration extents. This classifier traverses only written
axis tokens, retaining their order and rank; it never enumerates tensor cells.
The caller supplies a mathematical Nat ceiling, not an implicit machine width.
Empty extents represent scalar rank here, not a production admission decision. -/
namespace Rumoca.GALEC.Elaboration.Declarations.Extents
open _root_.Parser

/-- Independent meaning of one literal extent, using mathematical decimal
denotation rather than the executable decimal parser. Other Token categories
cannot witness this judgment, even when their text consists of digits. -/
inductive AxisDenotes (ceiling : Nat) : Token → Nat → Prop where
  | literal (decimal : DecimalNat.Denotes spelling extent)
      (positive : 0 < extent) (bounded : extent ≤ ceiling) :
      AxisDenotes ceiling (.literal spelling) extent

/-- Independent ordered list meaning, including the rank-zero case. -/
inductive Denotes (ceiling : Nat) : List Token → List Nat → Prop where
  | nil : Denotes ceiling [] []
  | cons : AxisDenotes ceiling token extent → Denotes ceiling tokens dims →
      Denotes ceiling (token :: tokens) (extent :: dims)

def readAxis (ceiling : Nat) : Token → Option Nat
  | .literal spelling => (DecimalNat.parse spelling).bind fun extent =>
      if 0 < extent ∧ extent ≤ ceiling then some extent else none
  | _ => none

def read (ceiling : Nat) : List Token → Option (List Nat)
  | [] => some []
  | token :: tokens => (readAxis ceiling token).bind fun extent =>
      (read ceiling tokens).map (extent :: ·)

theorem readAxis_iff (ceiling : Nat) (token : Token) (extent : Nat) :
    readAxis ceiling token = some extent ↔ AxisDenotes ceiling token extent := by
  cases token with
  | literal spelling =>
    constructor
    · intro found
      obtain ⟨candidate, parsed, fitted⟩ := Option.bind_eq_some_iff.mp found
      split at fitted
      · rename_i bounds
        cases Option.some.inj fitted
        exact .literal ((DecimalNat.parse_iff _ _).mp parsed) bounds.1 bounds.2
      · contradiction
    · intro denoted
      cases denoted with
      | literal decimal positive bounded =>
        simp only [readAxis, (DecimalNat.parse_iff _ _).mpr decimal, Option.bind_some,
          if_pos (And.intro positive bounded)]
  | ident spelling | number spelling =>
    constructor
    · intro impossible; cases impossible
    · intro impossible; cases impossible

theorem read_iff (ceiling : Nat) (tokens : List Token) (dims : List Nat) :
    read ceiling tokens = some dims ↔ Denotes ceiling tokens dims := by
  induction tokens generalizing dims with
  | nil =>
    constructor
    · intro found
      cases Option.some.inj found
      exact .nil
    · intro denoted
      cases denoted
      rfl
  | cons token tokens ih =>
    constructor
    · intro found
      obtain ⟨extent, head, tail⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨rest, lowered, same⟩ := Option.map_eq_some_iff.mp tail
      cases same
      exact .cons ((readAxis_iff _ _ _).mp head) ((ih _).mp lowered)
    · intro denoted
      cases denoted with
      | cons head tail =>
        simp only [read, (readAxis_iff _ _ _).mpr head, Option.bind_some,
          (ih _).mpr tail, Option.map_some]

theorem rank_preserved (denoted : Denotes ceiling tokens dims) :
    dims.length = tokens.length := by
  induction denoted with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem axis_bounds (denoted : AxisDenotes ceiling token extent) :
    0 < extent ∧ extent ≤ ceiling := by
  cases denoted with
  | literal _ positive bounded => exact ⟨positive, bounded⟩

theorem bounds (denoted : Denotes ceiling tokens dims) :
    ∀ extent ∈ dims, 0 < extent ∧ extent ≤ ceiling := by
  induction denoted with
  | nil => simp
  | cons head _ ih =>
    intro extent member
    cases List.mem_cons.mp member with
    | inl same => subst extent; exact axis_bounds head
    | inr tail => exact ih extent tail

end Rumoca.GALEC.Elaboration.Declarations.Extents
