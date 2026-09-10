import Mathlib.Order.RelSeries

/-! Deterministic transition systems with explicit termination, divergence and
stuck behavior. There are no external events in the admitted compiler profile. -/
namespace Rumoca.Transition

variable {S R : Type}

inductive Reaches (step : S → S → Prop) : S → S → Prop where
  | refl (s) : Reaches step s s
  | next : step s t → Reaches step t u → Reaches step s u

namespace Reaches

variable {step : S → S → Prop} {s t u : S}

theorem trans (h₁ : Reaches step s t) (h₂ : Reaches step t u) : Reaches step s u := by
  induction h₁ with
  | refl => exact h₂
  | next h _ ih => exact .next h (ih h₂)

theorem accessible (det : ∀ {s a b}, step s a → step s b → a = b)
    (h : Reaches step s t) (terminal : ∀ u, ¬ step t u) : Acc (fun t s => step s t) s := by
  induction h with
  | refl => exact ⟨_, fun u hu => False.elim (terminal u hu)⟩
  | next h _ ih =>
    constructor
    intro u hu
    cases det h hu
    exact ih terminal

/-- Every execution prefix of a deterministic terminating run can complete. -/
theorem completes (det : ∀ {s a b}, step s a → step s b → a = b)
    (h : Reaches step s t) (terminal : ∀ u, ¬ step t u)
    (prefixRun : Reaches step s u) : Reaches step u t := by
  induction prefixRun with
  | refl => exact h
  | next hs _ ih =>
    cases h with
    | refl => exact False.elim (terminal _ hs)
    | next ht rest =>
      cases det hs ht
      exact ih rest

end Reaches

inductive Observation (R : Type) where
  | terminates (result : R)
  | diverges
  | wrong
  deriving DecidableEq

structure Machine (S R : Type) where
  step : S → S → Prop
  final : S → Option R
  deterministic : ∀ {s a b}, step s a → step s b → a = b
  final_stuck : ∀ {s r}, final s = some r → ∀ t, ¬ step s t

namespace Machine
inductive Behaves (m : Machine S R) (s : S) : Observation R → Prop where
  | terminates : Reaches m.step s t → m.final t = some r → Behaves m s (.terminates r)
  | wrong : Reaches m.step s t → m.final t = none →
      (∀ u, ¬ m.step t u) → Behaves m s .wrong
  | diverges : (trace : Nat → S) → trace 0 = s →
      (∀ n, m.step (trace n) (trace (n + 1))) → Behaves m s .diverges

variable {s t : S} {r : R} {b : Observation R}

theorem no_infinite {m : Machine S R} (h : Acc (fun t s => m.step s t) s) :
    ¬ ∃ trace : Nat → S, trace 0 = s ∧ ∀ n, m.step (trace n) (trace (n + 1)) := by
  induction h with
  | intro s hs ih =>
    rintro ⟨trace, he, ht⟩
    apply ih (trace 1) (he ▸ ht 0)
    exact ⟨fun n => trace (n + 1), rfl, fun n => ht (n + 1)⟩

theorem behavior_iff (m : Machine S R) (h : Reaches m.step s t)
    (hf : m.final t = some r) : m.Behaves s b ↔ b = .terminates r := by
  have terminal := m.final_stuck hf
  have completion {u} (hp : Reaches m.step s u) : Reaches m.step u t :=
    Reaches.completes (fun ha hb => m.deterministic ha hb) h terminal hp
  constructor
  · intro hb
    cases hb with
    | terminates hp hg =>
      have hc := completion hp
      cases hc with
      | refl => rw [hf] at hg; cases Option.some.inj hg; rfl
      | next hs _ => exact False.elim (m.final_stuck hg _ hs)
    | wrong hp hg stuck =>
      have hc := completion hp
      cases hc with
      | refl => rw [hf] at hg; contradiction
      | next hs _ => exact False.elim (stuck _ hs)
    | diverges trace he ht =>
      exact False.elim (no_infinite (h.accessible (fun ha hb => m.deterministic ha hb) terminal) ⟨trace, he, ht⟩)
  · rintro rfl
    exact .terminates h hf
end Machine
end Rumoca.Transition
