import Std

namespace Parser.Source

/-- An immutable input snapshot. A compilation assigns identities by checked
indices in its input array; names and contents need not be unique. -/
structure Input where
  name : String
  source : String

/-- A selected file in a compilation-owned immutable input table. The checked
index distinguishes duplicate names/contents and needs no global counter. -/
structure InputRef where
  inputs : Array Input
  file : Fin inputs.size

def InputRef.input (ref : InputRef) : Input := ref.inputs[ref.file]
def InputRef.source (ref : InputRef) : String := ref.input.source
def InputRef.name (ref : InputRef) : String := ref.input.name

/-- Standalone compilation uses the same scoped identity as a file in a batch.
The caller supplies the actual display name and immutable source snapshot. -/
def InputRef.single (name source : String) : InputRef :=
  ⟨#[⟨name, source⟩], ⟨0, by simp⟩⟩

/-- A half-open UTF-8 range in one immutable source snapshot. Valid boundaries
come from Lean's String.Pos and are indexed by source contents. File identity
and version belong to the enclosing document, including equal-content files. -/
structure Span (source : String) where
  start : source.Pos
  stop : source.Pos
  ordered : start ≤ stop
  deriving DecidableEq

namespace Span

def point (p : source.Pos) : Span source := ⟨p, p, Nat.le_refl _⟩

def text (s : Span source) : String := String.extract s.start s.stop

def cover (a b : Span source) : Span source where
  start := if a.start ≤ b.start then a.start else b.start
  stop := if a.stop ≤ b.stop then b.stop else a.stop
  ordered := by
    have ha := a.ordered
    have hb := b.ordered
    simp only [String.Pos.le_iff, String.Pos.Raw.le_iff] at *
    split <;> split <;> omega

def Contains (outer inner : Span source) : Prop :=
  outer.start ≤ inner.start ∧ inner.stop ≤ outer.stop

theorem cover_left (a b : Span source) : (cover a b).Contains a := by
  simp only [Contains, cover, String.Pos.le_iff, String.Pos.Raw.le_iff]
  split <;> split <;> omega

theorem cover_right (a b : Span source) : (cover a b).Contains b := by
  simp only [Contains, cover, String.Pos.le_iff, String.Pos.Raw.le_iff]
  split <;> split <;> omega

theorem bounded (s : Span source) :
    s.start.offset.byteIdx ≤ s.stop.offset.byteIdx ∧
    s.stop.offset.byteIdx ≤ source.utf8ByteSize :=
  ⟨s.ordered, s.stop.isValid.le_utf8ByteSize⟩

end Span

structure Located (source : String) (α : Type) where
  value : α
  span : Span source
  deriving DecidableEq

/-- Checked construction for lexer byte cursors. Invalid UTF-8 boundaries and
reversed or out-of-bounds ranges are rejected, never clamped. -/
def span? (source : String) (start stop : Nat) : Option (Span source) := do
  let a : String.Pos.Raw := ⟨start⟩
  let b : String.Pos.Raw := ⟨stop⟩
  if ha : a.IsValid source then
    if hb : b.IsValid source then
      if hab : a ≤ b then
        some ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩
      else none
    else none
  else none

end Parser.Source
