import RumocaFMI3.InitializationEnvironment
import RumocaFMI3.InitializationQuiet

noncomputable section
namespace Rumoca.FMI3.InitializationEnvironment
open CTree CMemory CBody StaticFactory

/-- Entry and exit apply independently to every heap with the corresponding
storage/mode premises. In particular, exit is not restricted to the heap
produced immediately by entry; intervening Float64 accesses may change it. -/
theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions InitializationExit.signature.name =
        some (.tree (Runtime.function model InitializationExit.signature)) →
      InitializationCalls.QuietExecutionContract program := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program enterDefined exitDefined
  constructor
  · intro heap p args kind admissible storage hk
    exact (calls header objects literals model program heap p args kind
      enterDefined exitDefined admissible storage hk).1
  · intro heap p kind hk hm behavior
    have kindLoaded : load heap (p.member "kind") = some (.integer (InitializationBodies.kindCode kind)) := by
      cases kind <;> exact hk
    have executed := InitializationBodies.exit_run (static := ⟨literals⟩) model InitializationExit.signature rfl
      heap p kind kindLoaded hm
    rw [← InitializationExit.finite_parameters] at executed
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model InitializationExit.signature) _ _ heap _ (.integer 0) 6
      exitDefined (InitializationExit.parameters_bound (static := ⟨literals⟩) _)
      (InitializationExit.closed model) (exit_agrees header model objects literals)
      executed rfl behavior
  · intro heap args behavior
    have executed := GuardedCalls.null_body (static := ⟨literals⟩)
      (InitializationCalls.parameters none args) heap
      (Runtime.modeGuard .enterInitialization ::
        Runtime.reject InitializationCalls.guard InitializationCalls.message :: InitializationCalls.tail)
      (by simp [InitializationCalls.parameters, CBody.bind])
      (by simp [InitializationCalls.parameters, CBody.bind])
      (by simp [InitializationCalls.parameters, CBody.bind])
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program InitializationCalls.function _ _ heap _ (.integer 3) 3 enterDefined
      (InitializationCalls.parameters_bound (static := ⟨literals⟩) _ _) InitializationCalls.closed
      (enter_agrees header objects literals) executed rfl behavior
  · intro heap behavior
    have executed := GuardedCalls.null_body (static := ⟨literals⟩)
      (InitializationExit.parameters none) heap
      (Runtime.modeGuard .exitInitialization :: InitializationExit.tail)
      (by simp [InitializationExit.parameters, CBody.bind])
      (by simp [InitializationExit.parameters, CBody.bind])
      (by simp [InitializationExit.parameters, CBody.bind])
    have body : (Runtime.function model InitializationExit.signature).body =
        Runtime.instancePrefix ++ (Runtime.modeGuard .exitInitialization :: InitializationExit.tail) := by
      simp only [Runtime.function, InitializationExit.body, Runtime.require,
        List.append_assoc, List.cons_append, List.nil_append]
    rw [← body] at executed
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals)
      (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model InitializationExit.signature) _ _ heap _ (.integer 3) 3 exitDefined
      (InitializationExit.parameters_bound (static := ⟨literals⟩) _) (InitializationExit.closed model)
      (exit_agrees header model objects literals) executed rfl behavior

end Rumoca.FMI3.InitializationEnvironment
end
