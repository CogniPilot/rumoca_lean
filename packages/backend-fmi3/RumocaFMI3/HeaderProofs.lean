import RumocaFMI3.LiteralPreparation

/-! Invariants of the existing header-signature collector. This does not
assert that the ad-hoc header reader implements the complete C grammar. -/
namespace Rumoca.FMI3.Header
open CTree
set_option autoImplicit false

private theorem loop_invariant {α β : Type} (items : List α)
    (step : α → β → Except String (ForInStep β)) (invariant : β → Prop)
    (preserve : ∀ item before result, invariant before → step item before = .ok result →
      match result with | .done after | .yield after => invariant after)
    (before after : β) (initial : invariant before)
    (ran : forIn items before step = .ok after) : invariant after := by
  induction items generalizing before with
  | nil =>
      change Except.ok before = Except.ok after at ran
      cases ran
      exact initial
  | cons item rest ih =>
      simp only [List.forIn_cons] at ran
      cases result : step item before with
      | error error =>
          rw [result] at ran
          contradiction
      | ok next =>
          have kept := preserve item before next initial result
          cases next with
          | done value =>
              rw [result] at ran
              change Except.ok value = Except.ok after at ran
              cases ran
              exact kept
          | yield value =>
              rw [result] at ran
              change forIn rest value step = .ok after at ran
              exact ih value kept ran

private theorem append_unique (entries : List Signature) (sig : Signature)
    (unique : (entries.map Signature.name).Nodup)
    (absent : (entries.any (fun old => old.name == sig.name)) ≠ true) :
    ((entries ++ [sig]).map Signature.name).Nodup := by
  rw [List.map_append]
  refine List.nodup_append.mpr ⟨unique, by simp, ?_⟩
  intro a member b singleton same
  have name : b = sig.name := by simpa using singleton
  obtain ⟨old, inEntries, oldName⟩ := List.mem_map.mp member
  exact absent (List.any_eq_true.mpr ⟨old, inEntries, by simp [oldName, same, name]⟩)

theorem signatures_unique (source : String) (sigs : List Signature)
    (accepted : signatures source = .ok sigs) : (sigs.map Signature.name).Nodup := by
  unfold signatures at accepted
  simp only [bind, Except.bind] at accepted
  split at accepted
  · contradiction
  · rename_i result collected
    have unique : (result.map Signature.name).Nodup := by
      apply loop_invariant _ _ (fun entries : List Signature => (entries.map Signature.name).Nodup)
        ?_ [] result (by simp) collected
      intro declaration before next initial step
      simp only [pure, Except.pure] at step
      repeat' first
      | split at step
      | (simp only [Except.ok.injEq] at step; cases step)
      all_goals first
      | contradiction
      | exact initial
      | exact append_unique _ _ initial (by assumption)
    simp only [pure, Except.pure] at accepted
    split at accepted <;> simp_all

end Rumoca.FMI3.Header
