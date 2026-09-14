import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.StaticReset

noncomputable section
namespace Rumoca.FMI3.ResetEnvironment
open CTree CMemory CBody StaticFactory CLiteral.Interface

theorem body_agrees (header : CFenv.Header) (model : Solve.FMI3Model source)
    (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model Reset.signature) := by
  simp [Runtime.body, Reset.signature, CodeAgrees, StmtAgrees, ExprAgrees, names,
    CInitialization.Emission.statement, CInitialization.value_zero,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
    Runtime.allowedExpression, permittedModes, Runtime.put, Runtime.setMode,
    Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail, Runtime.branch,
    Runtime.ret, Runtime.any, Runtime.both, Runtime.either, Runtime.negate,
    Runtime.eqv, Runtime.field, Runtime.x, Runtime.call, Runtime.v, Runtime.n,
    Expr.nullPointer, RuntimeEnvironment.interface, CFenv.Header.interface,
    CInterface.constants, objectConstants]

theorem call_behaviors {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode),
      program.internal.definitions Reset.signature.name =
        some (.tree (Runtime.function model Reset.signature)) →
      Reset.Storage heap p → load heap (p.member "kind") = some (.integer kind.code) →
      load heap (p.member "mode") = some (.integer mode.code) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling Reset.signature.name [.pointer (some p)] heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, Reset.finalHeap heap p⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap p kind mode defined storage kindValue modeValue behavior
  have executed := Reset.body_run (static := ⟨literals⟩) model Reset.signature rfl
    heap p kind mode storage kindValue modeValue
  exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
    (RuntimeEnvironment.interface header objects literals) (RuntimeEnvironment.types_agree header objects literals) rfl
    program (Runtime.function model Reset.signature) _ _ heap _ (.integer 0) 12 defined
    (Reset.parameters_bound (static := ⟨literals⟩) p) (BodyEmbedding.body_closed model Reset.signature)
    (body_agrees header model objects literals) executed rfl behavior

theorem null_behaviors {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap),
      program.internal.definitions Reset.signature.name =
        some (.tree (Runtime.function model Reset.signature)) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling Reset.signature.name [.pointer none] heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap defined behavior
  let rest := Runtime.modeGuard .reset :: (CInitialization.emit model.solve Runtime.x).statement :: Reset.tail
  have executed := GuardedCalls.null_body (static := ⟨literals⟩) StateProofs.nullParameters heap rest
    (by simp [StateProofs.nullParameters]) (by simp [StateProofs.nullParameters]) (by simp [StateProofs.nullParameters])
  have body : (Runtime.function model Reset.signature).body = Runtime.instancePrefix ++ rest := by
    simp [Runtime.function, Runtime.body, Reset.signature, Runtime.require, Reset.tail, rest, List.append_assoc]
  rw [← body] at executed
  exact CCalls.Events.body_call_interface_behaviors (cInterface literals)
    (RuntimeEnvironment.interface header objects literals) (RuntimeEnvironment.types_agree header objects literals) rfl
    program (Runtime.function model Reset.signature) _ _ heap _ (.integer 3) 3 defined rfl
    (BodyEmbedding.body_closed model Reset.signature) (body_agrees header model objects literals) executed rfl behavior

theorem execution_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions Reset.signature.name =
        some (.tree (Runtime.function model Reset.signature)) → StaticReset.ExecutionContract program := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program defined
  exact ⟨fun heap p kind mode => call_behaviors header objects literals model program heap p kind mode defined,
    fun heap => null_behaviors header objects literals model program heap defined⟩

end Rumoca.FMI3.ResetEnvironment
end
