import RumocaC.CallSites
import RumocaC.HostCalls

namespace Rumoca.CCallSites
open CTree CMemory CCalls
variable [CInterface]

/-- Call restrictions persist through host-selected repeated invocations,
completion observations and explicit host memory actions. -/
theorem host_history (program : Events.Program E) (policy : Host.Policy)
    (functions : ProgramAdmits permitted program.internal) (sound : OperandSound program permitted calls)
    (entries : ∀ state thread name args, policy.admit state thread name args → calls name args)
    (ready : ThreadsReady permitted calls before)
    (path : Host.History program policy before trace after) : ThreadsReady permitted calls after := by
  exact Host.history_threads program policy (Ready permitted calls)
    (fun state ready heap => (ready_withHeap state heap).mpr ready)
    (fun _ _ _ _ admitted => ⟨entries _ _ _ _ admitted, True.intro⟩)
    (fun _ _ _ ready step => event_ready program functions sound ready step) ready path

end Rumoca.CCallSites
