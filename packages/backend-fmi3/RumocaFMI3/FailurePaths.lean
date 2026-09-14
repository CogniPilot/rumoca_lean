import RumocaFMI3.StaticErrorCalls

/-! Compose pure failure prefixes with the shared event-machine path relation. -/
noncomputable section
namespace Rumoca.FMI3.StaticErrors
open CTree CMemory CCalls

/-- A pure public body prefix is also a silent path in the event machine. -/
theorem prefix_path [CInterface] (program : Events.Program E) (fn : Function) (args : List Value)
    (before after : Heap) (p : Address) (text : String)
    (certified : GuardedCalls.FailurePrefix fn args before p text after)
    (defined : program.internal.definitions fn.signature.name = some (.tree fn)) :
    FailurePath program (.calling fn.signature.name args before .done) after p text := by
  obtain ⟨status, closed, env, later, tail, steps, bound, executed, unshadowed, instanceBound⟩ := certified
  obtain ⟨types, reached⟩ := Events.body_prefix_reaches program fn args env later before after
    (Runtime.fail text :: tail) .done steps defined bound closed executed
  rw [status] at reached
  exact ⟨later, types, tail, Events.internal_path program reached, unshadowed, instanceBound⟩

end Rumoca.FMI3.StaticErrors
end
