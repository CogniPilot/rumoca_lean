import Parser.LALR.FirstProofs

/-! Structural lookahead traversal for membership-based checks. Ordering and
multiplicity are intentionally unconstrained; existing sorted metadata remains
owned by Parser.LALR.lookaheads. No grammar validity premise is required. -/
namespace Parser.LALR

def lookaheadCandidates (facts : Array First) : List Atom → Nat → List Nat
  | [], following => [following]
  | .terminal token :: _, _ => [token]
  | .nonterminal n :: rest, following =>
      let f := facts[n]?.getD {}
      f.terminals ++ if f.nullable then lookaheadCandidates facts rest following else []

/-- Independent FIRST/nullable characterization, including missing fact entries
with the existing default and arbitrary repeated/unsorted terminal lists. -/
theorem mem_lookaheadCandidates_spec (facts : Array First) (symbols : List Atom)
    (following token : Nat) :
    token ∈ lookaheadCandidates facts symbols following ↔
      FirstProofs.Begins facts token symbols ∨
        FirstProofs.Nullable facts symbols ∧ token = following := by
  induction symbols with
  | nil => simp [lookaheadCandidates, FirstProofs.Begins, FirstProofs.Nullable]
  | cons symbol rest ih =>
    cases symbol with
    | terminal t => simp [lookaheadCandidates, FirstProofs.Begins, FirstProofs.Nullable]
    | nonterminal n =>
      cases h : (facts[n]?.getD {}).nullable <;>
        simp [lookaheadCandidates, FirstProofs.Begins, FirstProofs.Nullable, h, ih, or_assoc]

/-- Equal membership, not list equality or a promise of canonical ordering. -/
theorem mem_lookaheadCandidates_iff (facts : Array First) (symbols : List Atom)
    (following token : Nat) :
    token ∈ lookaheadCandidates facts symbols following ↔
      token ∈ Parser.LALR.lookaheads facts symbols following :=
  (mem_lookaheadCandidates_spec facts symbols following token).trans
    FirstProofs.mem_lookaheads.symm

/-- Suitable for decidable_of_iff: candidates on the left, the existing sorted
lookahead obligation on the right. P need not be decidable for this theorem. -/
theorem forall_lookaheadCandidates_iff (facts : Array First) (symbols : List Atom)
    (following : Nat) (P : Nat → Prop) :
    (∀ token ∈ lookaheadCandidates facts symbols following, P token) ↔
      (∀ token ∈ Parser.LALR.lookaheads facts symbols following, P token) := by
  simp only [mem_lookaheadCandidates_iff]

end Parser.LALR

