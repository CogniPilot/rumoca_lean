import RumocaCore.Transition.Events.Choices

/-! A finite determined prefix need not have a determined continuation.
In particular, reservation can precede a nondeterministic host callback.
The prefix preserves exact finite traces and cannot introduce divergence. -/
namespace Rumoca.Transition.Events
variable {S E R : Type}

inductive Prefix (m : Machine S E R) : S → List E → S → Prop where
  | refl (s) : Prefix m s [] s
  | next : m.step s first t →
      (∀ events u, m.step s events u → events = first ∧ u = t) →
      Prefix m t rest u → Prefix m s (first ++ rest) u

namespace Prefix
variable {m : Machine S E R}

theorem trans (first : Prefix m s es t) (second : Prefix m t fs u) :
    Prefix m s (es ++ fs) u := by
  induction first with
  | refl => exact second
  | next head unique tail ih =>
    simpa only [List.append_assoc] using Prefix.next head unique (ih second)

theorem forced (path : Prefix m s events t) (rest : Forced m t tail result) :
    Forced m s (events ++ tail) result := by
  induction path with
  | refl => exact rest
  | next head unique tail ih =>
    simpa only [List.append_assoc] using Forced.next head unique (ih rest)

theorem terminates_iff (path : Prefix m s events t) :
    m.Behaves s (.terminates actual result) ↔
      ∃ tail, actual = events ++ tail ∧ m.Behaves t (.terminates tail result) := by
  induction path generalizing actual with
  | refl => simp
  | @next s first u rest t head unique path ih =>
    constructor
    · intro observed
      cases observed with
      | terminates run done =>
        cases run with
        | refl => exact False.elim (m.final_stuck done first u head)
        | next step continuation =>
          obtain ⟨rfl, rfl⟩ := unique _ _ step
          obtain ⟨tail, same, observed⟩ := ih.mp (.terminates continuation done)
          exact ⟨tail, by simp only [same, List.append_assoc], observed⟩
    · rintro ⟨tail, rfl, observed⟩
      have continued := ih.mpr ⟨tail, rfl, observed⟩
      cases continued with
      | terminates run done =>
        simpa only [List.append_assoc] using Machine.Behaves.terminates (Reaches.next head run) done

theorem wrong_iff (path : Prefix m s events t) :
    m.Behaves s (.wrong actual) ↔
      ∃ tail, actual = events ++ tail ∧ m.Behaves t (.wrong tail) := by
  induction path generalizing actual with
  | refl => simp
  | @next s first u rest t head unique path ih =>
    constructor
    · intro observed
      cases observed with
      | wrong run done stuck =>
        cases run with
        | refl => exact False.elim (stuck first u head)
        | next step continuation =>
          obtain ⟨rfl, rfl⟩ := unique _ _ step
          obtain ⟨tail, same, observed⟩ := ih.mp (.wrong continuation done stuck)
          exact ⟨tail, by simp only [same, List.append_assoc], observed⟩
    · rintro ⟨tail, rfl, observed⟩
      have continued := ih.mpr ⟨tail, rfl, observed⟩
      cases continued with
      | wrong run done stuck =>
        simpa only [List.append_assoc] using Machine.Behaves.wrong (Reaches.next head run) done stuck

/-- This implication makes no claim that arbitrary callbacks terminate.
It transports a separately proved absence of divergence at the continuation. -/
theorem no_divergence (path : Prefix m s events t)
    (finished : ∀ history, ¬ m.Behaves t (.diverges history)) :
    ∀ history, ¬ m.Behaves s (.diverges history) := by
  induction path with
  | refl => exact finished
  | next head unique tail ih =>
    intro history observed
    cases observed with
    | diverges states chunks initial steps recorded =>
      have first := unique _ _ (initial ▸ steps 0)
      obtain ⟨remaining, records⟩ := records_exists (fun n => chunks (n + 1))
      exact ih finished remaining (.diverges (fun n => states (n + 1))
        (fun n => chunks (n + 1)) first.2 (fun n => steps (n + 1)) records)

/-- Compose a finite prefix with a complete finite-outcome specification.
The suffix specification must account for every observation, including the
absence of divergence. It may admit any number of successful or stuck outcomes. -/
theorem finite_behaviors (path : Prefix m s events t)
    (returns : List E → R → Prop) (errors : List E → Prop)
    (complete : ∀ observation, m.Behaves t observation ↔ match observation with
      | .terminates trace result => returns trace result
      | .wrong trace => errors trace
      | .diverges _ => False) (observation) :
    m.Behaves s observation ↔ match observation with
      | .terminates actual result => ∃ tail, actual = events ++ tail ∧ returns tail result
      | .wrong actual => ∃ tail, actual = events ++ tail ∧ errors tail
      | .diverges _ => False := by
  cases observation with
  | terminates trace result =>
    rw [path.terminates_iff]
    simp only [complete]
  | wrong trace =>
    rw [path.wrong_iff]
    simp only [complete]
  | diverges history =>
    exact iff_false_intro (path.no_divergence (fun h observed => (complete (.diverges h)).mp observed) history)

end Prefix
end Rumoca.Transition.Events
