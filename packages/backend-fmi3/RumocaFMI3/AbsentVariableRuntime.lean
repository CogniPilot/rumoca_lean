import RumocaFMI3.AbsentVariables
import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.StaticErrorCalls

/-! The common absent-variable body in the actual static/runtime interfaces.
Its raw behavior includes defensive calls; legal FMI issuance is a separate
reference domain and is not inferred from the raw execution contract. -/
noncomputable section
namespace Rumoca.FMI3.AbsentVariables
open CTree CMemory CBody StaticFactory CLiteral CLiteral.Interface CCalls.Events

theorem body_agrees (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source)
    (ty : VariableType) (write : Bool) :
    CodeAgrees (cInterface literals) (RuntimeEnvironment.interface header objects literals)
      (Runtime.body model (signature ty write)) := by
  rw [body_eq]
  cases write <;> simp [accessCommand, CodeAgrees, StmtAgrees, ExprAgrees, names, suffix, Runtime.require,
    Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
    Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
    Runtime.negate, Runtime.eqv, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
    Expr.nullPointer, RuntimeEnvironment.interface, CFenv.Header.interface,
    CInterface.constants, objectConstants]

theorem body_agrees_static (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (ty : VariableType) (write : Bool) :
    CodeAgrees (cInterface literals) (executionInterface objects literals)
      (Runtime.body model (signature ty write)) := by
  rw [body_eq]
  cases write <;> simp [accessCommand, CodeAgrees, StmtAgrees, ExprAgrees, names, suffix, Runtime.require,
    Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail,
    Runtime.branch, Runtime.ret, Runtime.any, Runtime.both, Runtime.either,
    Runtime.negate, Runtime.eqv, Runtime.field, Runtime.call, Runtime.v, Runtime.n,
    Expr.nullPointer, executionInterface, CInterface.constants, objectConstants]

structure QuietContract [CInterface] (ty : VariableType) (write : Bool)
    (program : Program E) : Prop where
  empty : ∀ (heap : Heap) (p : Address) (references sizes values : Option Address)
    (kind : Kind) (mode : Mode),
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    Reference.Allowed (accessCommand write) kind mode →
    ∀ observed, (machine program).Behaves
      (.calling (signature ty write).name
        (arguments ty.hasSizes (some p) references sizes values 0 0) heap .done) observed ↔
      observed = .terminates [] ⟨.integer 0, heap⟩
  null : ∀ (heap : Heap) (references sizes values : Option Address) (n m : UInt64) observed,
    (machine program).Behaves
      (.calling (signature ty write).name
        (arguments ty.hasSizes none references sizes values n m) heap .done) observed ↔
      observed = .terminates [] ⟨.integer 3, heap⟩

theorem quiet_agreed {E : Type} (target : CInterface)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source)
    (ty : VariableType) (write : Bool)
    (types : (cInterface literals).types = target.types)
    (bytes : (cInterface literals).literals = target.literals)
    (agrees : CodeAgrees (cInterface literals) target (Runtime.body model (signature ty write))) :
    letI : CInterface := target
    ∀ (program : Program E),
      program.internal.definitions (signature ty write).name =
        some (.tree (Runtime.function model (signature ty write))) → QuietContract ty write program := by
  letI : CInterface := target
  intro program defined
  constructor
  · intro heap p references sizes values kind mode hk hm permitted observed
    have executed := empty_body (static := ⟨literals⟩) write
      (parameters ty.hasSizes (some p) references sizes values 0 0) heap p kind mode
      (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind, ite_apply])
      (by simp [parameters, CBody.bind, ite_apply]) (by simp [parameters, CBody.bind])
      (by simp [parameters, CBody.bind, ite_apply]) hk hm permitted
    rw [← body_eq model ty write] at executed
    exact body_call_interface_behaviors (cInterface literals) target types bytes
      program (Runtime.function model (signature ty write)) _ _ heap _ (.integer 0) 5 defined
      (parameters_bound (static := ⟨literals⟩) ty write _ _ _ _ _ _)
      (BodyEmbedding.body_closed model (signature ty write)) agrees executed rfl observed
  · intro heap references sizes values n m observed
    have executed := GuardedCalls.null_body (static := ⟨literals⟩)
      (parameters ty.hasSizes none references sizes values n m) heap (Runtime.modeGuard (accessCommand write) :: suffix)
      (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind, ite_apply])
      (by simp [parameters, CBody.bind, ite_apply])
    have shaped : (Runtime.function model (signature ty write)).body =
        Runtime.instancePrefix ++ Runtime.modeGuard (accessCommand write) :: suffix := by
      simp [Runtime.function, body_eq, Runtime.require, List.append_assoc]
    rw [← shaped] at executed
    exact body_call_interface_behaviors (cInterface literals) target types bytes
      program (Runtime.function model (signature ty write)) _ _ heap _ (.integer 3) 3 defined
      (parameters_bound (static := ⟨literals⟩) ty write _ _ _ _ _ _)
      (BodyEmbedding.body_closed model (signature ty write)) agrees executed rfl observed

theorem quiet_correct {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source)
    (ty : VariableType) (write : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Program E),
      program.internal.definitions (signature ty write).name =
        some (.tree (Runtime.function model (signature ty write))) → QuietContract ty write program :=
  quiet_agreed (RuntimeEnvironment.interface header objects literals) literals model ty write
    (RuntimeEnvironment.types_agree header objects literals) rfl
    (body_agrees header objects literals model ty write)

theorem quiet_static_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (ty : VariableType) (write : Bool) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : Program E),
      program.internal.definitions (signature ty write).name =
        some (.tree (Runtime.function model (signature ty write))) → QuietContract ty write program :=
  quiet_agreed (executionInterface objects literals) literals model ty write
    (StaticInitialization.interface_types objects literals) rfl
    (body_agrees_static objects literals model ty write)

end Rumoca.FMI3.AbsentVariables
end
