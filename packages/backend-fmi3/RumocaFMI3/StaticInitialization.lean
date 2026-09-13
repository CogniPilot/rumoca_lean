import RumocaFMI3.StaticFactoryEnvironment
import RumocaFMI3.InstanceInitialization
import RumocaFMI3.InitializationQuiet
import RumocaC.LiteralInterfaceBody

/-! Existing initialization bodies in the static runtime's global interface.
Lookup agreement is proved for their syntax; unrelated factories may use the
added globals. Public calls retain the same actual program and heaps. -/
noncomputable section
namespace Rumoca.FMI3.StaticInitialization
open CTree CMemory CBody StaticFactory CLiteral.Interface

theorem interface_types (objects : Objects) (literals : CLiteralAddresses) :
    (cInterface literals).types = (executionInterface objects literals).types := by
  funext name
  by_cases boolean : name = "_Bool"
  · subst name; rfl
  by_cases size : name = "const size_t"
  · subst name; rfl
  by_cases pointer : name = "volatile atomic_bool *"
  · subst name; rfl
  exact (types_unchanged name (by simp [boolean, size, pointer])).symm

theorem enter_agrees (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (executionInterface objects literals) InitializationCalls.code := by
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, InitializationCalls.code, InitializationCalls.tail,
    InitializationCalls.guard, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
    Runtime.allowedExpression, permittedModes, Runtime.initialTime, Runtime.put, Runtime.setMode,
    Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail, Runtime.branch, Runtime.ret,
    Runtime.any, Runtime.both, Runtime.either, Runtime.negate, Runtime.eqv, Runtime.lt,
    Runtime.field, Runtime.finite, Runtime.call, Runtime.v, Runtime.n, Expr.nullPointer,
    executionInterface, objectConstants]

theorem exit_agrees (model : Solve.FMI3Model source) (objects : Objects) (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (executionInterface objects literals)
      (Runtime.body model InitializationExit.signature) := by
  rw [InitializationExit.body]
  simp [CodeAgrees, StmtAgrees, ExprAgrees, names, InitializationExit.tail,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
    permittedModes, Runtime.put, Runtime.setMode, Runtime.mode, Runtime.ok,
    Runtime.reject, Runtime.fail, Runtime.branch, Runtime.ret, Runtime.any,
    Runtime.both, Runtime.either, Runtime.negate, Runtime.eqv,
    Runtime.field, Runtime.call, Runtime.v, Runtime.n, Expr.nullPointer,
    executionInterface, objectConstants]

/-- Creation supplies every writable initialization cell and its entry mode;
later initialization need not assume separately allocated or zero-filled data. -/
theorem entry_storage (initialized : InstanceInitialization.Initialized heap p kind environment logger logging) :
    InitializationCalls.EntryStorage heap p := by
  refine ⟨⟨initialized.storage.time, initialized.storage.minimum,
    initialized.storage.event, initialized.storage.completed⟩, ?_,
    initialized.storage.stop, initialized.storage.stopDefined⟩
  obtain ⟨old, stored⟩ := initialized.storage.mode
  have loaded := initialized.modeValue
  have payload : old = some (.integer 0) := by
    simp only [load, stored, Mode.code, Option.bind_eq_bind,
      Option.bind_some, reduceCtorEq, ↓reduceIte, Option.bind_eq_some_iff] at loaded
    obtain ⟨value, payload, checked, _, returned⟩ := loaded
    split at returned
    · exact (Option.some.inj returned) ▸ payload
    · contradiction
  rw [payload] at stored
  exact stored

theorem enter_call {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (args : Initialization.Arguments) (kind : Kind)
    (_defined : program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function))
    (_admissible : Initialization.Arguments.Admissible args)
    (_storage : InitializationCalls.EntryStorage heap p)
    (_hk : load heap (p.member "kind") = some (.integer kind.code)) (behavior),
    (CCalls.Events.machine program).Behaves
      (.calling InitializationCalls.signature.name
        (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, InitializationEntry.finalHeap heap p args⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap p args kind defined admissible storage hk behavior
  obtain ⟨clock, mode, ⟨stopOld, stop⟩, ⟨flagOld, flag⟩⟩ := storage
  have executed := InitializationCalls.body_run (static := ⟨literals⟩) heap p args kind
    admissible clock stopOld flagOld hk mode stop flag
  have agreement := body_run_agreement (cInterface literals) (executionInterface objects literals)
    (interface_types objects literals) rfl 12
    (.running InitializationCalls.code
      (InitializationCalls.parameters (some p) (InitializationCalls.Raw.ofFinite args)) heap)
    (enter_agrees objects literals)
  have parameters := (parameters_agreement (cInterface literals) (executionInterface objects literals)
    (interface_types objects literals) InitializationCalls.signature.parameters
    (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args))).symm.trans
      (InitializationCalls.parameters_bound (static := ⟨literals⟩) _ _)
  exact CCalls.Events.body_call_behaviors program InitializationCalls.function _ _ heap _ (.integer 0) 12
    defined parameters InitializationCalls.closed (agreement.symm.trans executed) rfl behavior

theorem exit_call {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (kind : Kind)
    (_defined : program.internal.definitions InitializationExit.signature.name =
      some (.tree (Runtime.function model InitializationExit.signature)))
    (_hk : load heap (p.member "kind") = some (.integer kind.code))
    (_mode : heap (p.member "mode") = some ⟨.int32, true, some (.integer 1)⟩) (behavior),
    (CCalls.Events.machine program).Behaves
      (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, InitializationBodies.exitHeap heap p kind⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap p kind defined hk mode behavior
  have kindLoaded : load heap (p.member "kind") = some (.integer (InitializationBodies.kindCode kind)) := by
    cases kind <;> exact hk
  have executed := InitializationBodies.exit_run (static := ⟨literals⟩) model InitializationExit.signature rfl
    heap p kind kindLoaded mode
  rw [← InitializationExit.finite_parameters] at executed
  have agreement := body_run_agreement (cInterface literals) (executionInterface objects literals)
    (interface_types objects literals) rfl 6
    (.running (Runtime.body model InitializationExit.signature) (InitializationExit.parameters (some p)) heap)
    (exit_agrees model objects literals)
  have parameters := (parameters_agreement (cInterface literals) (executionInterface objects literals)
    (interface_types objects literals) InitializationExit.signature.parameters (InitializationExit.arguments (some p))).symm.trans
      (InitializationExit.parameters_bound (static := ⟨literals⟩) _)
  exact CCalls.Events.body_call_behaviors program (Runtime.function model InitializationExit.signature) _ _ heap _ (.integer 0) 6
    defined parameters (InitializationExit.closed model) (agreement.symm.trans executed) rfl behavior

/-- Reuse a guarded function's null path without inspecting any instance
storage or foreign binding. The unused-global condition is local to its body. -/
theorem null_call {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (fn : Function) (rest : List Stmt)
      (args : List Value) (env : Locals) (heap : Heap),
      program.internal.definitions fn.signature.name = some (.tree fn) →
      @CCalls.parameters (cInterface literals) fn.signature.parameters args = some env →
      fn.body = Runtime.instancePrefix ++ rest → fn.signature.result = "fmi3Status" →
      fn.body.all CBodyEmbedding.closedBlocks = true →
      CodeAgrees (cInterface literals) (executionInterface objects literals) fn.body →
      env "instance" = some (.pointer none) → env "m" = none → env "fmi3Error" = none →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling fn.signature.name args heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program fn rest args env heap defined parameters body status closed agrees hi hn error behavior
  have executed := GuardedCalls.null_body (static := ⟨literals⟩) env heap rest hi hn error
  rw [← body] at executed
  have agreement := body_run_agreement (cInterface literals) (executionInterface objects literals)
    (interface_types objects literals) rfl 3 (.running fn.body env heap) agrees
  have bound := (parameters_agreement (cInterface literals) (executionInterface objects literals)
    (interface_types objects literals) fn.signature.parameters args).symm.trans parameters
  exact CCalls.Events.body_call_behaviors program fn args env heap _ (.integer 3) 3
    defined bound closed (agreement.symm.trans executed) (by rw [status]; rfl) behavior

/-- Both complete initialization calls now use the same object-aware program
as creation. This preserves the established successful and null-call contract;
logged invalid-argument/lifecycle paths require separate eventful composition. -/
theorem quiet_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
      program.internal.definitions InitializationExit.signature.name =
        some (.tree (Runtime.function model InitializationExit.signature)) →
      InitializationCalls.QuietExecutionContract program := by
  letI : CInterface := executionInterface objects literals
  intro program enterDefined exitDefined
  constructor
  · intro heap p args kind admissible storage hk behavior
    exact enter_call objects literals program heap p args kind enterDefined admissible storage hk behavior
  · intro heap p kind hk mode behavior
    exact exit_call objects literals model program heap p kind exitDefined hk mode behavior
  · intro heap args behavior
    apply null_call objects literals program InitializationCalls.function
      (Runtime.modeGuard .enterInitialization :: Runtime.reject InitializationCalls.guard InitializationCalls.message :: InitializationCalls.tail)
      (InitializationCalls.arguments none args) (InitializationCalls.parameters none args) heap enterDefined
      (InitializationCalls.parameters_bound (static := ⟨literals⟩) _ _)
      (by simp [InitializationCalls.function, InitializationCalls.code, Runtime.require, List.append_assoc])
      rfl InitializationCalls.closed (enter_agrees objects literals)
    all_goals simp [InitializationCalls.parameters, CBody.bind]
  · intro heap behavior
    apply null_call objects literals program (Runtime.function model InitializationExit.signature)
      (Runtime.modeGuard .exitInitialization :: InitializationExit.tail)
      (InitializationExit.arguments none) (InitializationExit.parameters none) heap exitDefined
      (InitializationExit.parameters_bound (static := ⟨literals⟩) _)
      (by simpa [Runtime.function, Runtime.require, List.append_assoc] using InitializationExit.body model)
      rfl (InitializationExit.closed model) (exit_agrees model objects literals)
    all_goals simp [InitializationExit.parameters, CBody.bind]

end Rumoca.FMI3.StaticInitialization

namespace Rumoca.FMI3.StaticInitialization
open CMemory StaticFactory

/-- Enter/exit initialization leaves the lease metadata untouched. -/
theorem exited_metadata (heap : Heap) (p : Address) (args : Initialization.Arguments) (kind : Kind) :
    load (InitializationCalls.exitedHeap heap p args kind) (p.member "slot") =
      load heap (p.member "slot") := by
  have same := InitializationCalls.exited_frame heap p (p.member "slot") args kind
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  simp only [load, same]

/-- The initialization writes cannot alter any shared reservation flag. This
uses object-block separation and the actual returned heaps, not a new host
ownership premise for the initialized state. -/
theorem exited_owners (objects : Objects) (heap : Heap) (slot : Fin objects.capacity)
    (args : Initialization.Arguments) (kind : Kind) (owners : SlotOwners.State objects.capacity)
    (represented : SlotOwners.Represents objects.flagsBlock heap owners) :
    SlotOwners.Represents objects.flagsBlock
      (InitializationCalls.exitedHeap heap (objects.instances.index slot.val) args kind) owners := by
  intro other
  have different (field : String) : AtomicSlots.address objects.flagsBlock other ≠
      (objects.instances.index slot.val).member field := by
    intro same
    exact objects.separate (congrArg Address.block same).symm
  rw [InitializationCalls.exited_frame heap (objects.instances.index slot.val)
    (AtomicSlots.address objects.flagsBlock other) args kind (different "time")
    (different "timeMin") (different "eventTime") (different "lastCompleted")
    (different "stop") (different "stopDefined") (different "mode")]
  exact represented other

end Rumoca.FMI3.StaticInitialization
