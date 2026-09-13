import RumocaFMI3.StaticInitialization
import RumocaFMI3.ResetContract

/-! Reset in the same object-aware interface as static creation. Successful
and null calls use the actual function table. Frames include other elements
of the shared instance array, not just objects in different memory blocks. -/
noncomputable section
namespace Rumoca.FMI3.StaticReset
open CTree CMemory CBody StaticFactory CLiteral.Interface

theorem body_agrees (model : Solve.FMI3Model source) (objects : Objects)
    (literals : CLiteralAddresses) :
    CodeAgrees (cInterface literals) (executionInterface objects literals)
      (Runtime.body model Reset.signature) := by
  simp [Runtime.body, Reset.signature, CodeAgrees, StmtAgrees, ExprAgrees, names,
    CInitialization.Emission.statement, CInitialization.value_zero,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
    Runtime.allowedExpression, permittedModes, Runtime.put, Runtime.setMode,
    Runtime.mode, Runtime.ok, Runtime.reject, Runtime.fail, Runtime.branch,
    Runtime.ret, Runtime.any, Runtime.both, Runtime.either, Runtime.negate,
    Runtime.eqv, Runtime.field, Runtime.x, Runtime.call, Runtime.v, Runtime.n,
    Expr.nullPointer, executionInterface, objectConstants]

theorem call_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
      (kind : Kind) (mode : Mode),
      program.internal.definitions Reset.signature.name =
        some (.tree (Runtime.function model Reset.signature)) →
      Reset.Storage heap p →
      load heap (p.member "kind") = some (.integer kind.code) →
      load heap (p.member "mode") = some (.integer mode.code) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling Reset.signature.name [.pointer (some p)] heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, Reset.finalHeap heap p⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap p kind mode defined storage hk hm behavior
  have executed := Reset.body_run (static := ⟨literals⟩) model Reset.signature rfl
    heap p kind mode storage hk hm
  have agreement := body_run_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) rfl 12
    (.running (Runtime.body model Reset.signature) (HistoryBodies.parameters p) heap)
    (body_agrees model objects literals)
  have parameters := (parameters_agreement (cInterface literals) (executionInterface objects literals)
    (StaticInitialization.interface_types objects literals) Reset.signature.parameters
    [.pointer (some p)]).symm.trans (Reset.parameters_bound (static := ⟨literals⟩) p)
  exact CCalls.Events.body_call_behaviors program (Runtime.function model Reset.signature)
    _ _ heap _ (.integer 0) 12 defined parameters (BodyEmbedding.body_closed model Reset.signature)
    (agreement.symm.trans executed) rfl behavior

theorem null_behaviors {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap),
      program.internal.definitions Reset.signature.name =
        some (.tree (Runtime.function model Reset.signature)) →
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling Reset.signature.name [.pointer none] heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program heap defined
  apply StaticInitialization.null_call objects literals program (Runtime.function model Reset.signature)
    (Runtime.modeGuard .reset :: (CInitialization.emit model.solve Runtime.x).statement :: Reset.tail)
    [.pointer none] StateProofs.nullParameters heap defined rfl
    (by simp [Runtime.function, Runtime.body, Reset.signature, Runtime.require, Reset.tail, List.append_assoc])
    rfl (BodyEmbedding.body_closed model Reset.signature) (body_agrees model objects literals)
  all_goals simp [StateProofs.nullParameters]

/-- Reset restores every cell required by another initialization. No claim
about the old model, clock or stop values is needed. -/
theorem entry_storage (heap : Heap) (p : Address) :
    InitializationCalls.EntryStorage (Reset.finalHeap heap p) p := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp [Reset.finalHeap, CInitialization.written, HistoryProofs.initialHeap,
      HistoryProofs.write, HistoryProofs.cell, LifecycleBodies.writeMode,
      replace, Mode.code]

theorem kind_value (heap : Heap) (p : Address) :
    load (Reset.finalHeap heap p) (p.member "kind") = load heap (p.member "kind") := by
  simp only [load, Reset.retained_field heap p "kind" (by simp)]

theorem metadata (heap : Heap) (p : Address) :
    load (Reset.finalHeap heap p) (p.member "slot") = load heap (p.member "slot") := by
  simp only [load, Reset.retained_field heap p "slot" (by simp)]

/-- All cells outside the reset instance survive, including arbitrary nested
tensor fields in a different element of the same instance array. -/
theorem record_frame (heap : Heap) (p q : Address) (outside : ¬ p.InRecord q) :
    Reset.finalHeap heap p q = heap q := by
  have different (name : String) : q ≠ p.member name := by
    intro same
    subst q
    exact outside (p.member_in_record name)
  apply Reset.frame
  · intro same
    subst q
    exact outside ((p.member_in_record "model").member "x")
  all_goals exact different _

theorem other_instance (heap : Heap) (base : Address) (i j : Nat) (query : Address)
    (different : i ≠ j) (inside : (base.index j).InRecord query) :
    Reset.finalHeap heap (base.index i) query = heap query := by
  apply record_frame
  intro own
  exact Address.records_separate base i j different own inside rfl

theorem owners (objects : Objects) (heap : Heap) (slot : Fin objects.capacity)
    (leases : SlotOwners.State objects.capacity)
    (represented : SlotOwners.Represents objects.flagsBlock heap leases) :
    SlotOwners.Represents objects.flagsBlock
      (Reset.finalHeap heap (objects.instances.index slot.val)) leases := by
  intro other
  rw [record_frame heap (objects.instances.index slot.val) (AtomicSlots.address objects.flagsBlock other) ?_]
  · exact represented other
  · intro inside
    exact objects.separate inside.1.symm

/-- The complete reset/reinitialization sequence preserves every cell outside
the selected record; this does not assume distinct top-level memory blocks. -/
theorem restarted_frame (heap : Heap) (p q : Address) (args : Initialization.Arguments)
    (kind : Kind) (outside : ¬ p.InRecord q) :
    InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args kind q = heap q := by
  have different (name : String) : q ≠ p.member name := by
    intro same
    subst q
    exact outside (p.member_in_record name)
  rw [InitializationCalls.exited_frame _ p q args kind (different "time")
    (different "timeMin") (different "eventTime") (different "lastCompleted")
    (different "stop") (different "stopDefined") (different "mode")]
  exact record_frame heap p q outside

theorem restarted_other_instance (heap : Heap) (base : Address) (i j : Nat)
    (args : Initialization.Arguments) (kind : Kind) (query : Address)
    (different : i ≠ j) (inside : (base.index j).InRecord query) :
    InitializationCalls.exitedHeap (Reset.finalHeap heap (base.index i))
      (base.index i) args kind query = heap query := by
  apply restarted_frame
  intro own
  exact Address.records_separate base i j different own inside rfl

theorem restarted_owners (objects : Objects) (heap : Heap) (slot : Fin objects.capacity)
    (args : Initialization.Arguments) (kind : Kind) (leases : SlotOwners.State objects.capacity)
    (represented : SlotOwners.Represents objects.flagsBlock heap leases) :
    SlotOwners.Represents objects.flagsBlock
      (InitializationCalls.exitedHeap (Reset.finalHeap heap (objects.instances.index slot.val))
        (objects.instances.index slot.val) args kind) leases :=
  StaticInitialization.exited_owners objects _ slot args kind leases
    (owners objects heap slot leases represented)

/-- This contract characterizes complete calls without constraining external
functions: valid represented instances and null need no callback execution. -/
structure ExecutionContract [interface : CInterface]
    (program : CCalls.Events.Program E) : Prop where
  successful : ∀ (heap : Heap) (p : Address) (kind : Kind) (mode : Mode),
    Reset.Storage heap p →
    load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling Reset.signature.name [.pointer (some p)] heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, Reset.finalHeap heap p⟩
  null : ∀ heap behavior, (CCalls.Events.machine program).Behaves
    (.calling Reset.signature.name [.pointer none] heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩

theorem execution_correct {E : Type} (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E),
      program.internal.definitions Reset.signature.name =
        some (.tree (Runtime.function model Reset.signature)) → ExecutionContract program := by
  letI : CInterface := executionInterface objects literals
  intro program defined
  exact ⟨fun heap p kind mode => call_behaviors objects literals model program heap p kind mode defined,
    fun heap => null_behaviors objects literals model program heap defined⟩

end Rumoca.FMI3.StaticReset
