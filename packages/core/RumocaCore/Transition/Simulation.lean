import RumocaCore.Transition

/-! A step-for-step lowering preserves every observation when its state map
reflects steps as well as preserving them. The invariant is proved along the
source execution; termination is not assumed. -/
namespace Rumoca.Transition

structure FunctionalBisimulation (source : Machine S R) (target : Machine T R) where
  map : S → T
  Valid : S → Prop
  step : ∀ {s s'}, Valid s → source.step s s' →
    Valid s' ∧ target.step (map s) (map s')
  reflect : ∀ {s t'}, Valid s → target.step (map s) t' →
    ∃ s', source.step s s' ∧ t' = map s'
  final : ∀ s, Valid s → target.final (map s) = source.final s

namespace FunctionalBisimulation
variable {source : Machine S R} {target : Machine T R}
variable (sim : FunctionalBisimulation source target)

theorem reaches (path : Reaches source.step s u) (valid : sim.Valid s) :
    sim.Valid u ∧ Reaches target.step (sim.map s) (sim.map u) := by
  induction path with
  | refl => exact ⟨valid, .refl _⟩
  | next first rest ih =>
      obtain ⟨validNext, first'⟩ := sim.step valid first
      obtain ⟨validLast, rest'⟩ := ih validNext
      exact ⟨validLast, .next first' rest'⟩

theorem reflect_reaches (path : Reaches target.step t u) :
    ∀ s, sim.Valid s → t = sim.map s →
      ∃ s', Reaches source.step s s' ∧ sim.Valid s' ∧ u = sim.map s' := by
  induction path with
  | refl => intro s valid same; exact ⟨s, .refl _, valid, same⟩
  | next first rest ih =>
      intro s valid same
      obtain ⟨s', first', aligned⟩ := sim.reflect valid (same ▸ first)
      obtain ⟨s'', rest', validLast, result⟩ := ih s' (sim.step valid first').1 aligned
      exact ⟨s'', .next first' rest', validLast, result⟩

theorem preserves (valid : sim.Valid s) (behavior : source.Behaves s b) :
    target.Behaves (sim.map s) b := by
  cases behavior with
  | terminates path result =>
      obtain ⟨validLast, path'⟩ := sim.reaches path valid
      exact .terminates path' ((sim.final _ validLast).trans result)
  | wrong path result stuck =>
      obtain ⟨validLast, path'⟩ := sim.reaches path valid
      refine .wrong path' ((sim.final _ validLast).trans result) ?_
      intro out next
      obtain ⟨u, next', _⟩ := sim.reflect validLast next
      exact stuck u next'
  | diverges trace initial steps =>
      have traceValid : ∀ n, sim.Valid (trace n) := by
        intro n
        induction n with
        | zero => simpa only [initial] using valid
        | succ n ih => exact (sim.step ih (steps n)).1
      exact .diverges (fun n => sim.map (trace n)) (congrArg sim.map initial)
        (fun n => (sim.step (traceValid n) (steps n)).2)

theorem reflects (valid : sim.Valid s) (behavior : target.Behaves (sim.map s) b) :
    source.Behaves s b := by
  cases behavior with
  | terminates path result =>
      obtain ⟨last, path', validLast, same⟩ := sim.reflect_reaches path s valid rfl
      exact .terminates path' (by simpa only [same, sim.final last validLast] using result)
  | wrong path result stuck =>
      obtain ⟨last, path', validLast, same⟩ := sim.reflect_reaches path s valid rfl
      refine .wrong path' (by simpa only [same, sim.final last validLast] using result) ?_
      intro out next
      exact stuck (sim.map out) (same ▸ (sim.step validLast next).2)
  | diverges trace initial steps =>
      let nextState (n : Nat) (current : {state : S // sim.Valid state ∧ trace n = sim.map state}) :
          {state : S // sim.Valid state ∧ trace (n + 1) = sim.map state} :=
        let found := sim.reflect current.property.1 (current.property.2 ▸ steps n)
        ⟨Classical.choose found, (sim.step current.property.1 (Classical.choose_spec found).1).1,
          (Classical.choose_spec found).2⟩
      have nextStep (n : Nat) (current : {state : S // sim.Valid state ∧ trace n = sim.map state}) :
          source.step current.val (nextState n current).val :=
        (Classical.choose_spec (sim.reflect current.property.1 (current.property.2 ▸ steps n))).1
      let aligned : (n : Nat) → {state : S // sim.Valid state ∧ trace n = sim.map state} :=
        Nat.rec ⟨s, valid, initial⟩ nextState
      exact .diverges (fun n => (aligned n).val) rfl (fun n => nextStep n (aligned n))

theorem behaviors (valid : sim.Valid s) (behavior : Observation R) :
    target.Behaves (sim.map s) behavior ↔ source.Behaves s behavior :=
  ⟨sim.reflects valid, sim.preserves valid⟩

end FunctionalBisimulation
end Rumoca.Transition
