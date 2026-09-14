import RumocaFMI3.RuntimeEnvironment

noncomputable section
namespace Rumoca.FMI3.InitializationEnvironment
open CTree CMemory CBody StaticFactory CLiteral.Interface
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem enter_agrees (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals) InitializationCalls.code := by
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, InitializationCalls.code, InitializationCalls.tail,
    InitializationCalls.guard, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
    Runtime.allowedExpression, permittedModes, Runtime.initialTime, Runtime.put, Runtime.setMode,
    Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail, Runtime.branch, Runtime.ret,
    Runtime.any, Runtime.both, Runtime.either, Runtime.negate, Runtime.eqv, Runtime.lt,
    Runtime.field, Runtime.finite, Runtime.call, Runtime.v, Runtime.n, Expr.nullPointer,
    RuntimeEnvironment.interface, CFenv.Header.interface, CInterface.constants,
    objectConstants]

theorem exit_agrees (header : CFenv.Header) (model : Solve.FMI3Model source)
    (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model InitializationExit.signature) := by
  rw [InitializationExit.body]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, InitializationExit.tail,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.put, Runtime.setMode, Runtime.mode, Runtime.ok,
    Runtime.reject, Runtime.fail, Runtime.branch, Runtime.ret, Runtime.any,
    Runtime.both, Runtime.either, Runtime.negate, Runtime.eqv,
    Runtime.field, Runtime.call, Runtime.v, Runtime.n, Expr.nullPointer,
    RuntimeEnvironment.interface, CFenv.Header.interface, CInterface.constants,
    objectConstants]

/-- Successful public initialization uses the same explicit header/object
interface as subsequent CS calls; unrelated factory and library bindings need
not agree with the smaller initialization-body environment. -/
theorem calls {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
      (args : Initialization.Arguments) (kind : Kind),
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions InitializationExit.signature.name =
        some (.tree (Runtime.function model InitializationExit.signature)) →
      args.Admissible → InitializationCalls.EntryStorage heap p →
      load heap (p.member "kind") = some (.integer kind.code) →
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling InitializationCalls.signature.name
          (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, InitializationEntry.finalHeap heap p args⟩) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling InitializationExit.signature.name (InitializationExit.arguments (some p))
          (InitializationEntry.finalHeap heap p args) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, InitializationCalls.exitedHeap heap p args kind⟩) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap p args kind enterDefined exitDefined admissible storage kindValue
  constructor
  · intro behavior
    obtain ⟨clock, mode, ⟨oldStop, stop⟩, ⟨oldFlag, flag⟩⟩ := storage
    have executed := InitializationCalls.body_run (static := ⟨literals⟩) heap p args kind
      admissible clock oldStop oldFlag kindValue mode stop flag
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals) (RuntimeEnvironment.types_agree header objects literals) rfl
      program InitializationCalls.function _ _ heap _ (.integer 0) 12 enterDefined
      (InitializationCalls.parameters_bound (static := ⟨literals⟩) _ _) InitializationCalls.closed
      (enter_agrees header objects literals) executed rfl behavior
  · intro behavior
    have kindLoaded : load (InitializationEntry.finalHeap heap p args) (p.member "kind") =
        some (.integer (InitializationBodies.kindCode kind)) := by
      cases kind <;> exact (InitializationCalls.entered_kind heap p args).trans kindValue
    have executed := InitializationBodies.exit_run (static := ⟨literals⟩) model InitializationExit.signature rfl
      (InitializationEntry.finalHeap heap p args) p kind kindLoaded (InitializationCalls.entered_mode heap p args)
    rw [← InitializationExit.finite_parameters] at executed
    exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
      (RuntimeEnvironment.interface header objects literals) (RuntimeEnvironment.types_agree header objects literals) rfl
      program (Runtime.function model InitializationExit.signature) _ _ _ _ (.integer 0) 6 exitDefined
      (InitializationExit.parameters_bound (static := ⟨literals⟩) _) (InitializationExit.closed model)
      (exit_agrees header model objects literals) executed rfl behavior

end Rumoca.FMI3.InitializationEnvironment
end
