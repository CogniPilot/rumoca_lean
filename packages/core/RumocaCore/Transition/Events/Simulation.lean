import RumocaCore.Transition.Events

namespace Rumoca.Transition.Events
variable {S T E R : Type}

/-! Label-preserving generalization of the existing state-map bisimulation. -/
structure FunctionalBisimulation (source : Machine S E R) (target : Machine T E R) where
  map : S → T
  Valid : S → Prop
  step : ∀ {s s' events}, Valid s → source.step s events s' →
    Valid s' ∧ target.step (map s) events (map s')
  reflect : ∀ {s t' events}, Valid s → target.step (map s) events t' →
    ∃ s', source.step s events s' ∧ t' = map s'
  final : ∀ s, Valid s → target.final (map s) = source.final s

namespace FunctionalBisimulation
variable {source : Machine S E R} {target : Machine T E R}
variable (sim : FunctionalBisimulation source target)

theorem reaches (path : Reaches source.step s events u) (valid : sim.Valid s) :
    sim.Valid u ∧ Reaches target.step (sim.map s) events (sim.map u) := by
  induction path with
  | refl => exact ⟨valid, .refl _⟩
  | next first rest ih =>
      obtain ⟨validNext, first'⟩ := sim.step valid first
      obtain ⟨validLast, rest'⟩ := ih validNext
      exact ⟨validLast, .next first' rest'⟩

theorem reflect_reaches (path : Reaches target.step t events u) :
    ∀ s, sim.Valid s → t = sim.map s →
      ∃ s', Reaches source.step s events s' ∧ sim.Valid s' ∧ u = sim.map s' := by
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
      intro emitted out next
      obtain ⟨u, next', _⟩ := sim.reflect validLast next
      exact stuck emitted u next'
  | diverges trace chunks initial steps history =>
      have traceValid : ∀ n, sim.Valid (trace n) := by
        intro n
        induction n with
        | zero => simpa only [initial] using valid
        | succ n ih => exact (sim.step ih (steps n)).1
      exact .diverges (fun n => sim.map (trace n)) chunks (congrArg sim.map initial)
        (fun n => (sim.step (traceValid n) (steps n)).2) history

theorem reflects (valid : sim.Valid s) (behavior : target.Behaves (sim.map s) b) :
    source.Behaves s b := by
  cases behavior with
  | terminates path result =>
      obtain ⟨last, path', validLast, same⟩ := sim.reflect_reaches path s valid rfl
      exact .terminates path' (by simpa only [same, sim.final last validLast] using result)
  | wrong path result stuck =>
      obtain ⟨last, path', validLast, same⟩ := sim.reflect_reaches path s valid rfl
      refine .wrong path' (by simpa only [same, sim.final last validLast] using result) ?_
      intro emitted out next
      exact stuck emitted (sim.map out) (same ▸ (sim.step validLast next).2)
  | diverges trace chunks initial steps history =>
      let nextState (n : Nat) (current : {state : S // sim.Valid state ∧ trace n = sim.map state}) :
          {state : S // sim.Valid state ∧ trace (n + 1) = sim.map state} :=
        let found := sim.reflect current.property.1 (current.property.2 ▸ steps n)
        ⟨Classical.choose found, (sim.step current.property.1 (Classical.choose_spec found).1).1,
          (Classical.choose_spec found).2⟩
      have nextStep (n : Nat) (current : {state : S // sim.Valid state ∧ trace n = sim.map state}) :
          source.step current.val (chunks n) (nextState n current).val :=
        (Classical.choose_spec (sim.reflect current.property.1 (current.property.2 ▸ steps n))).1
      let aligned : (n : Nat) → {state : S // sim.Valid state ∧ trace n = sim.map state} :=
        Nat.rec ⟨s, valid, initial⟩ nextState
      exact .diverges (fun n => (aligned n).val) chunks rfl (fun n => nextStep n (aligned n)) history

theorem behaviors (valid : sim.Valid s) (behavior : Observation E R) :
    target.Behaves (sim.map s) behavior ↔ source.Behaves s behavior :=
  ⟨sim.reflects valid, sim.preserves valid⟩

end FunctionalBisimulation
end Rumoca.Transition.Events
