import Mathlib.Computability.RegularExpressions

/-! Reuse mathlib's regular-language semantics, derivatives, alphabet mapping,
and recognition theorem. Only the executable smart constructors are local. -/
deriving instance Repr, BEq, DecidableEq for RegularExpression

namespace Parser
abbrev RE := RegularExpression
end Parser

namespace RegularExpression

def Accepts (r : RegularExpression α) (xs : List α) : Prop := xs ∈ r.matches'
abbrev nullable := @matchEpsilon
abbrev recognize := @rmatch

theorem nullable_correct [DecidableEq α] (r : RegularExpression α) :
    r.nullable = true ↔ r.Accepts [] := rmatch_iff_matches' r []

def smartAlt : RegularExpression α → RegularExpression α → RegularExpression α
  | .zero, b => b
  | a, .zero => a
  | a, b => .plus a b

def smartSeq : RegularExpression α → RegularExpression α → RegularExpression α
  | .zero, _ | _, .zero => .zero
  | .epsilon, b => b
  | a, .epsilon => a
  | a, b => .comp a b

theorem smartAlt_matches (a b : RegularExpression α) :
    (smartAlt a b).matches' = (a + b).matches' := by
  cases a <;> cases b <;> simp [smartAlt]

theorem smartSeq_matches (a b : RegularExpression α) :
    (smartSeq a b).matches' = (a * b).matches' := by
  cases a <;> cases b <;> simp [smartSeq]

def simplify : RegularExpression α → RegularExpression α
  | .plus a b => smartAlt (simplify a) (simplify b)
  | .comp a b => smartSeq (simplify a) (simplify b)
  | .star a => .star (simplify a)
  | r => r

theorem simplify_matches (r : RegularExpression α) : r.simplify.matches' = r.matches' := by
  induction r with
  | plus a b ia ib => simp only [simplify, smartAlt_matches, matches', ia, ib]
  | comp a b ia ib => simp only [simplify, smartSeq_matches, matches', ia, ib]
  | star a ia => simp only [simplify, matches'_star, ia]
  | _ => rfl

theorem simplify_correct (r : RegularExpression α) (xs : List α) :
    r.simplify.Accepts xs ↔ r.Accepts xs := by rw [Accepts, simplify_matches]; rfl

def step [DecidableEq α] (r : RegularExpression α) (c : α) : RegularExpression α :=
  (r.deriv c).simplify

theorem step_correct [DecidableEq α] (r : RegularExpression α) (c : α) (xs : List α) :
    (r.step c).Accepts xs ↔ r.Accepts (c :: xs) := by
  simp only [step, Accepts, simplify_matches, ← rmatch_iff_matches']
  rfl

def word : List α → RegularExpression α
  | [] => .epsilon
  | a :: as => .comp (.char a) (word as)

theorem word_correct (xs ys : List α) : (word xs).Accepts ys ↔ ys = xs := by
  induction xs generalizing ys with
  | nil => simp [word, Accepts]
  | cons x xs ih =>
    simp only [word, Accepts, matches', Language.mem_mul]
    constructor
    · rintro ⟨as, rfl, bs, hb, rfl⟩
      rw [(ih _).mp hb]; rfl
    · rintro rfl; exact ⟨[x], rfl, xs, (ih _).mpr rfl, rfl⟩

end RegularExpression
