import RumocaCore.GALEC.BoundedIteration
import RumocaCore.Solve.Tensor.Environment

/-! Lift tensor-local loop executions into the existing typed environment,
retaining every other binding. Both evaluator and independent (possibly
partial or nondeterministic) relation correspondences are provided. -/
namespace Rumoca.GALEC.StoreIteration
open Rumoca.Tensor Rumoca.Solve.Tensor Iteration

theorem prefix_update (ref : Ref context shape) (body : Fin bound → Value α shape → Value α shape)
    (count : Nat) (within : count ≤ bound) (initial : Env α context) :
    (runPrefix (σ := Env α context)
      (fun i state => @Env.update α context shape state ref (body i (state ref))) count within @initial : Env α context) =
    @Env.update α context shape initial ref (runPrefix body count within (initial ref)) := by
  induction count with
  | zero => exact (Env.update_self initial ref).symm
  | succ count ih =>
    simp only [runPrefix, ih, Env.update_same, Env.update_twice]

theorem run_update (ref : Ref context shape) (body : Fin bound → Value α shape → Value α shape)
    (initial : Env α context) :
    (run (σ := Env α context)
      (fun i state => @Env.update α context shape state ref (body i (state ref))) @initial : Env α context) =
    @Env.update α context shape initial ref (run body (initial ref)) :=
  prefix_update ref body bound (Nat.le_refl _) initial

/-- Lifting retains exact scalar/tensor execution, not merely its evaluator.
The final frame is part of the result and is also sufficient for reconstruction. -/
theorem executes_iff (ref : Ref context shape)
    (step : Fin bound → Value α shape → Value α shape → Prop)
    (count : Nat) (initial final : Env α context) :
    Executes (σ := Env α context) (fun i before after =>
      ∃ tensor, step i (before ref) tensor ∧ Env.Updates before ref tensor after)
      count @initial @final ↔
    ∃ tensor, Executes step count (initial ref) tensor ∧ Env.Updates initial ref tensor final := by
  induction count generalizing final with
  | zero =>
    constructor
    · intro h
      cases h
      exact ⟨initial ref, .zero _, rfl, fun _ _ => rfl⟩
    · rintro ⟨tensor, executed, frame⟩
      cases executed
      have same := (Env.update_correct _ _ _ _).mp frame
      rw [Env.update_self] at same
      subst final
      exact .zero @initial
  | succ count ih =>
    constructor
    · intro h
      cases h with
      | @next _ _ beforeEnv _ within earlier last =>
        obtain ⟨beforeTensor, beforeSteps, beforeFrame⟩ := (ih _).mp earlier
        obtain ⟨afterTensor, lastStep, afterFrame⟩ := last
        have read : beforeEnv ref = beforeTensor := beforeFrame.1
        rw [read] at lastStep
        exact ⟨afterTensor, .next within beforeSteps lastStep, afterFrame.1,
          fun other different => (afterFrame.2 other different).trans (beforeFrame.2 other different)⟩
    · rintro ⟨tensor, executed, frame⟩
      cases executed with
      | @next count _ beforeTensor _ within earlier last =>
        apply Executes.next (before := @Env.update α context shape initial ref beforeTensor) within
        · exact (ih _).mpr ⟨beforeTensor, earlier, (Env.update_correct _ _ _ _).mpr rfl⟩
        · refine ⟨tensor, ?_, frame.1, ?_⟩
          · simpa only [Env.update_same] using last
          · intro otherShape other different
            exact (frame.2 other different).trans (Env.update_other initial ref beforeTensor other different).symm

end Rumoca.GALEC.StoreIteration
