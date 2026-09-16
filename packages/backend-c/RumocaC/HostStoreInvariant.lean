import RumocaC.CallStoreInvariant
import RumocaC.InvocationLedger

namespace Rumoca.CStoreInvariant
open CTree CMemory CCalls
variable [CInterface] {E : Type} {R : Heap → Heap → Prop}

/-- Host entry/observation preserve memory, actual C execution uses the
existing store invariant, and only explicit host memory actions need the
additional environment contract. -/
theorem host_next (stable : Stable R) (foreign : ProgramPreserves R program)
    (memory : ∀ state thread heap, policy.memory state thread heap → R state.heap heap)
    (step : Host.Step program policy before thread action after) : R before.heap after.heap := by
  cases step with
  | invoke | complete => exact stable.refl _
  | execute executed => exact concurrent_next stable foreign executed
  | memory idle allowed => exact memory _ _ _ allowed

/-- Storage-stable relations cover complete raw public histories, including
arbitrary finite prefixes of incomplete calls and later thread reuse. -/
theorem host_history (stable : Stable R)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (foreign : ProgramPreserves R program)
    (memory : ∀ state thread heap, policy.memory state thread heap → R state.heap heap)
    (path : Host.History program policy before trace after) : R before.heap after.heap := by
  induction path with
  | refl => exact stable.refl _
  | next first rest ih =>
    obtain ⟨thread, action, _, step⟩ := first
    exact trans (host_next stable foreign memory step) ih

theorem recorded_history (stable : Stable R)
    (trans : ∀ {a b c}, R a b → R b c → R a c)
    (foreign : ProgramPreserves R program)
    (memory : ∀ state thread heap, policy.memory state thread heap → R state.heap heap)
    (path : Transition.Events.Reaches (Host.Recording.Step program policy) before ticks after) :
    R before.runtime.heap after.runtime.heap :=
  host_history stable trans foreign memory (Host.Recording.history_erases path)

end Rumoca.CStoreInvariant
