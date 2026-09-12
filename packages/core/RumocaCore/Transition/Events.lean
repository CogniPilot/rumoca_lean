import RumocaCore.Transition.Events.History

/-! Labeled, potentially nondeterministic execution. Silent embedding preserves
all observations of the internal machine; local forced runs characterize every
behavior without assuming unrelated external calls terminate. -/
namespace Rumoca.Transition.Events
variable {S T E R : Type}

inductive Reaches (step : S → List E → S → Prop) : S → List E → S → Prop where
  | refl (s) : Reaches step s [] s
  | next : step s first t → Reaches step t rest u → Reaches step s (first ++ rest) u

namespace Reaches
variable {step : S → List E → S → Prop}

theorem trans (first : Reaches step s es t) (second : Reaches step t fs u) :
    Reaches step s (es ++ fs) u := by
  induction first with
  | refl => exact second
  | next head tail ih => simpa only [List.append_assoc] using Reaches.next head (ih second)

theorem invariant {P : S → Prop} (preserves : ∀ {s es t}, P s → step s es t → P t)
    (run : Reaches step s es t) (initial : P s) : P t := by
  induction run with
  | refl => exact initial
  | next head tail ih => exact ih (preserves initial head)

theorem erases (run : Reaches step s es t) :
    Transition.Reaches (fun s t => ∃ es, step s es t) s t := by
  induction run with
  | refl => exact .refl _
  | next head tail ih => exact .next ⟨_, head⟩ ih
end Reaches

inductive Observation (E R : Type) where
  | terminates (events : List E) (result : R)
  | wrong (events : List E)
  | diverges (history : History E)

structure Machine (S E R : Type) where
  step : S → List E → S → Prop
  final : S → Option R
  final_stuck : ∀ {s r}, final s = some r → ∀ events t, ¬ step s events t

inductive Machine.Behaves (m : Machine S E R) (s : S) : Observation E R → Prop where
  | terminates : Reaches m.step s events t → m.final t = some r → Behaves m s (.terminates events r)
  | wrong : Reaches m.step s events t → m.final t = none →
      (∀ events u, ¬ m.step t events u) → Behaves m s (.wrong events)
  | diverges : (states : Nat → S) → (chunks : Nat → List E) → states 0 = s →
      (∀ n, m.step (states n) (chunks n) (states (n + 1))) →
      Records chunks history → Behaves m s (.diverges history)

/-- Existing deterministic internal machines make only empty event steps. -/
def quiet (m : Transition.Machine S R) : Machine S E R where
  step s events t := events = [] ∧ m.step s t
  final := m.final
  final_stuck := fun done _ t step => m.final_stuck done t step.2

def observeQuiet : Transition.Observation R → Observation E R
  | .terminates result => .terminates [] result
  | .wrong => .wrong []
  | .diverges => .diverges (.finite [])

theorem quiet_reaches (m : Transition.Machine S R) (run : Transition.Reaches m.step s t) :
    Reaches (quiet m : Machine S E R).step s [] t := by
  induction run with
  | refl => exact .refl _
  | next head tail ih => exact .next ⟨rfl, head⟩ ih

theorem quiet_reflects (m : Transition.Machine S R)
    (run : Reaches (quiet m : Machine S E R).step s events t) :
    events = [] ∧ Transition.Reaches m.step s t := by
  induction run with
  | refl => exact ⟨rfl, .refl _⟩
  | next head tail ih =>
      exact ⟨by simp only [head.1, ih.1, List.nil_append], .next head.2 ih.2⟩

theorem accumulate_silent (silent : ∀ n, chunks n = ([] : List E)) :
    accumulate chunks n = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [accumulate, ih, silent, List.nil_append]

theorem records_silent (silent : ∀ n, chunks n = ([] : List E)) :
    Records chunks (.finite []) := by
  intro segment
  simp only [History.HasPrefix, accumulate_silent silent]
  simp

/-- The extension preserves and reflects all old observations, including
nontermination and stuck execution. No assumption about termination is added. -/
theorem quiet_behaviors (m : Transition.Machine S R) (s : S) (behavior : Transition.Observation R) :
    (quiet m : Machine S E R).Behaves s (observeQuiet behavior) ↔ m.Behaves s behavior := by
  constructor
  · intro run
    cases behavior with
    | terminates result =>
        cases run with
        | terminates path done => exact .terminates (quiet_reflects m path).2 done
    | wrong =>
        cases run with
        | wrong path done stuck =>
            exact .wrong (quiet_reflects m path).2 done (fun t step => stuck [] t ⟨rfl, step⟩)
    | diverges =>
        cases run with
        | diverges states chunks initial steps history =>
            exact .diverges states initial (fun n => (steps n).2)
  · intro run
    cases run with
    | terminates path done => exact .terminates (quiet_reaches m path) done
    | wrong path done stuck =>
        exact .wrong (quiet_reaches m path) done (fun es t step => stuck t step.2)
    | diverges states initial steps =>
        exact .diverges states (fun _ => []) initial (fun n => ⟨rfl, steps n⟩)
          (records_silent (fun _ => rfl))

/-- No additional nonempty-event behavior appears in the silent embedding. -/
theorem quiet_all (m : Transition.Machine S R)
    (run : (quiet m : Machine S E R).Behaves s observation) :
    ∃ behavior, observation = observeQuiet behavior ∧ m.Behaves s behavior := by
  cases run with
  | terminates path done =>
      obtain ⟨rfl, path'⟩ := quiet_reflects m path
      exact ⟨.terminates _, rfl, .terminates path' done⟩
  | wrong path done stuck =>
      obtain ⟨rfl, path'⟩ := quiet_reflects m path
      exact ⟨.wrong, rfl, .wrong path' done (fun t step => stuck [] t ⟨rfl, step⟩)⟩
  | diverges states chunks initial steps history =>
      have silent := records_silent (fun n => (steps n).1)
      have same := records_unique history silent
      exact ⟨.diverges, congrArg Observation.diverges same,
        .diverges states initial (fun n => (steps n).2)⟩

/-- Only the visited states must force a unique next transition. An unrelated
external call elsewhere in the machine may remain nondeterministic. -/
inductive Forced (m : Machine S E R) : S → List E → R → Prop where
  | final : m.final s = some r → Forced m s [] r
  | next : m.step s first t →
      (∀ events u, m.step s events u → events = first ∧ u = t) →
      Forced m t rest r → Forced m s (first ++ rest) r

namespace Forced
variable {m : Machine S E R}

theorem reaches (forced : Forced m s events r) :
    ∃ t, Reaches m.step s events t ∧ m.final t = some r := by
  induction forced with
  | final done => exact ⟨_, .refl _, done⟩
  | next head unique rest ih =>
      obtain ⟨last, path, done⟩ := ih
      exact ⟨last, .next head path, done⟩

theorem accessible (forced : Forced m s events r) :
    Acc (fun t s => ∃ events, m.step s events t) s := by
  induction forced with
  | final done =>
      constructor
      rintro t ⟨events, step⟩
      exact False.elim (m.final_stuck done events t step)
  | next head unique rest ih =>
      constructor
      rintro t ⟨events, step⟩
      obtain ⟨_, rfl⟩ := unique events t step
      exact ih

theorem terminal_matches (forced : Forced m s events r)
    (path : Reaches m.step s actual t) (stuck : ∀ es u, ¬ m.step t es u) :
    actual = events ∧ m.final t = some r := by
  induction forced generalizing actual t with
  | final done =>
      cases path with
      | refl => exact ⟨rfl, done⟩
      | next head tail => exact False.elim (m.final_stuck done _ _ head)
  | next head unique rest ih =>
      cases path with
      | refl => exact False.elim (stuck _ _ head)
      | next head' tail =>
          obtain ⟨rfl, rfl⟩ := unique _ _ head'
          obtain ⟨same, done⟩ := ih tail stuck
          exact ⟨congrArg (_ ++ ·) same, done⟩

private theorem no_infinite {step : S → S → Prop} (accessible : Acc (fun t s => step s t) s) :
    ¬ ∃ states : Nat → S, states 0 = s ∧ ∀ n, step (states n) (states (n + 1)) := by
  induction accessible with
  | intro s hs ih =>
      rintro ⟨states, initial, steps⟩
      apply ih (states 1) (initial ▸ steps 0)
      exact ⟨fun n => states (n + 1), rfl, fun n => steps (n + 1)⟩

/-- Local determinacy suffices for a complete all-behavior theorem, with the
exact event trace. This does not assume an arbitrary foreign callback returns. -/
theorem behaviors (forced : Forced m s events r) (observation : Observation E R) :
    m.Behaves s observation ↔ observation = .terminates events r := by
  constructor
  · intro behavior
    cases behavior with
    | terminates path done =>
        obtain ⟨rfl, done'⟩ := forced.terminal_matches path (m.final_stuck done)
        cases Option.some.inj (done.symm.trans done')
        rfl
    | wrong path failed stuck =>
        have done := (forced.terminal_matches path stuck).2
        rw [failed] at done
        contradiction
    | diverges states chunks initial steps history =>
        exact False.elim (no_infinite forced.accessible
          ⟨states, initial, fun n => ⟨chunks n, steps n⟩⟩)
  · rintro rfl
    obtain ⟨t, path, done⟩ := forced.reaches
    exact .terminates path done
end Forced

end Rumoca.Transition.Events
