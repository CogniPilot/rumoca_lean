import RumocaFMI3.InstanceSlotCode
import RumocaFMI3.InstanceStorage
import RumocaC.LoopProofs
import RumocaC.TypedMemory

/-! Slot metadata and complete initialization share one heap and C machine.
The index is bounded before the size_t store, and every existing instance
initialization postcondition is retained. Native declarations remain separate. -/
noncomputable section
namespace Rumoca.FMI3.InstanceSlot
open CTree CMemory CBody

structure Storage (heap : Heap) (p : Address) : Prop where
  fields : InstanceInitialization.Storage heap p
  index : Reset.Writable heap (p.member "slot") .size

def written (heap : Heap) (p : Address) (slot : Nat) : Heap :=
  replace heap (p.member "slot") ⟨.size, true, some (.integer slot)⟩

def finalHeap (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) : Heap :=
  InstanceInitialization.finalHeap (written heap p slot) p kind environment logger logging

theorem Storage.preserved (storage : Storage before p) (preserved : CStorage.Preserves before after) :
    Storage after p := by
  refine ⟨storage.fields.preserved preserved, ?_⟩
  obtain ⟨value, found⟩ := storage.index
  exact preserved.cell found

theorem store_index (heap : Heap) (p : Address) (slot : Nat)
    (writable : Reset.Writable heap (p.member "slot") .size) (bounded : slot < 2^64) :
    store heap (p.member "slot") (.integer slot) = some (written heap p slot) := by
  obtain ⟨value, found⟩ := writable
  exact store_converted heap (p.member "slot") .size value (.integer slot) (.integer slot)
    found (by decide +kernel) (CLoops.convert_size_nat slot bounded)

/-- The existing initializer never writes the independent slot metadata. -/
theorem initialization_frame (heap : Heap) (p : Address) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) :
    InstanceInitialization.finalHeap heap p kind environment logger logging (p.member "slot") =
      heap (p.member "slot") := by
  have different : p.member "slot" ≠ StateProofs.stateAddress p :=
    Ne.symm (HistoryBodies.state_ne_field p "slot")
  simp [InstanceInitialization.finalHeap, Reset.finalHeap, CInitialization.written,
    HistoryProofs.initialHeap, HistoryProofs.write, LifecycleBodies.writeMode, replace, different]

theorem final_index (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) :
    finalHeap heap p slot kind environment logger logging (p.member "slot") =
      some ⟨.size, true, some (.integer slot)⟩ := by
  rw [finalHeap, initialization_frame, written, replace_at]

theorem metadata (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (bounded : slot < 2^64) :
    load (finalHeap heap p slot kind environment logger logging) (p.member "slot") = some (.integer slot) := by
  exact load_converted _ (p.member "slot") .size true (.integer slot)
    (final_index heap p slot kind environment logger logging) (by decide +kernel)
    (CLoops.convert_size_nat slot bounded)

theorem storage_ready (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) :
    Storage (finalHeap heap p slot kind environment logger logging) p :=
  ⟨InstanceInitialization.storage_ready _ p kind environment logger logging,
    ⟨some (.integer slot), final_index heap p slot kind environment logger logging⟩⟩

theorem initialized (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) :
    InstanceInitialization.Initialized (finalHeap heap p slot kind environment logger logging)
      p kind environment logger logging :=
  InstanceInitialization.initialized _ p kind environment logger logging

theorem frame (heap : Heap) (p query : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (outside : ¬ p.InRecord query) :
    finalHeap heap p slot kind environment logger logging query = heap query := by
  have different : query ≠ p.member "slot" := by
    intro same
    subst query
    exact outside (p.member_in_record "slot")
  rw [finalHeap, InstanceInitialization.frame _ p query kind environment logger logging outside]
  exact replace_other _ _ _ _ different

variable [interface : CInterface]

theorem step (env : Locals) (types : CLoops.Types) (heap : Heap) (p : Address)
    (slot : Nat) (rest : List Stmt)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (selected : resolve env "slot" = some (.integer slot))
    (writable : Reset.Writable heap (p.member "slot") .size) (bounded : slot < 2^64) :
    CLoops.next (.running (statement :: rest) env types heap) =
      some (.running rest env types (written heap p slot)) := by
  simp [CLoops.next, CLoops.nextWith, CLoops.evalWith, legacyExpressions,
    statement, eval, evalWith, lvalue, lvalueWith, instanceBound, selected,
    Value.address, store_index heap p slot writable bounded]

theorem return_reaches (program : CCalls.Events.Program E) (model : Solve.Model source)
    (kind : Kind) (env : Locals) (types : CLoops.Types) (heap : Heap) (p : Address) (slot : Nat)
    (environment logger : Option Address) (logging : Bool) (stack : CCalls.Typed.Continuation)
    (storage : Storage heap p) (bound : InstanceInitialization.Bindings env p environment logger logging)
    (selected : resolve env "slot" = some (.integer slot)) (bounded : slot < 2^64)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (code model kind) env types heap) "fmi3Instance" stack)
      (.returning (.pointer (some p)) (finalHeap heap p slot kind environment logger logging) stack) := by
  have stored := store_index heap p slot storage.index bounded
  refine .next (CCalls.Events.body_step program
    (step env types heap p slot _ bound.instanceBound selected storage.index bounded) "fmi3Instance" stack) ?_
  exact InstanceInitialization.return_reaches program model kind env types (written heap p slot) p
    environment logger logging stack (storage.fields.preserved (CStorage.store_preserves stored)) bound double handle

theorem initialized_owners (program : CCalls.Events.Program E) (model : Solve.Model source)
    (kind : Kind) (env : Locals) (types : CLoops.Types) (heap : Heap) (p : Address) (slot : Nat)
    (environment logger : Option Address) (logging : Bool)
    (storage : Storage heap p) (bound : InstanceInitialization.Bindings env p environment logger logging)
    (bounded : slot < 2^64)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (owners : SlotOwners.State capacity) (represented : SlotOwners.Represents block heap owners) :
    SlotOwners.Represents block (finalHeap heap p slot kind environment logger logging) owners := by
  have stored := store_index heap p slot storage.index bounded
  exact InstanceInitialization.initialized_owners program model kind env types (written heap p slot) p
    environment logger logging (storage.fields.preserved (CStorage.store_preserves stored)) bound double handle
    owners (SlotOwners.ordinary_preserves represented (CAtomicBoolean.ordinary_store_preserves stored))

theorem complete (program : CCalls.Events.Program E) (model : Solve.Model source)
    (kind : Kind) (env : Locals) (types : CLoops.Types) (heap : Heap) (p : Address) (slot : Nat)
    (environment logger : Option Address) (logging : Bool)
    (storage : Storage heap p) (bound : InstanceInitialization.Bindings env p environment logger logging)
    (selected : resolve env "slot" = some (.integer slot)) (bounded : slot < 2^64)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.body (.running (code model kind) env types heap) "fmi3Instance" .done) behavior ↔
      behavior = .terminates [] ⟨.pointer (some p), finalHeap heap p slot kind environment logger logging⟩) ∧
    CStorage.Preserves heap (finalHeap heap p slot kind environment logger logging) ∧
    InstanceInitialization.Initialized (finalHeap heap p slot kind environment logger logging)
      p kind environment logger logging ∧
    load (finalHeap heap p slot kind environment logger logging) (p.member "slot") = some (.integer slot) ∧
    (∀ query, ¬ p.InRecord query → finalHeap heap p slot kind environment logger logging query = heap query) := by
  have path := return_reaches program model kind env types heap p slot environment logger logging .done
    storage bound selected bounded double handle
  refine ⟨?_, CStorage.internal_reaches program path, initialized heap p slot kind environment logger logging,
    metadata heap p slot kind environment logger logging bounded,
    fun query outside => frame heap p query slot kind environment logger logging outside⟩
  exact (CCalls.Events.internal_prefix program path
    (CCalls.Events.return_forced program (.pointer (some p))
      (finalHeap heap p slot kind environment logger logging))).behaviors

end Rumoca.FMI3.InstanceSlot
