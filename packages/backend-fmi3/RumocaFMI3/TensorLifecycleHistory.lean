import RumocaFMI3.TensorLifecycleModes
import RumocaFMI3.TensorContinuousStates
import RumocaFMI3.TensorFree

/-! A composed lifecycle history over the static tensor instance pool, as a
package-checked product.

From a created, Instantiated-mode instance record (the postcondition of the
factory), the Model Exchange lifecycle proceeds through
`fmi3EnterInitializationMode` and `fmi3ExitInitializationMode` into Event Mode by
two single-cell mode writes, and from that reached Event-Mode heap the instance
answers a continuous-state derivative query (`TensorContinuousStates.deriv_contract`)
and is released by `fmi3FreeInstance`. The theorem threads the heaps of the two
mode transitions explicitly (each writes only the `mode` cell), and consumes the
derivative-query contract and the release contract on the reached heap. It derives
the observed status of each call (`fmi3OK` for the two mode transitions and the
derivative query, void for free) and the final owner map of the pool (the released
slot restored to unowned).

The premises are explicit: the created-instance kind/mode/slot cells, the finite
kernel execution and the direct-resolution premise the derivative query needs, the
identification of the reached Event-Mode heap with a well-formed tensor instance
heap, and the reservation-flag representation and release bindings the free needs.
The derivative query and the free act on disjoint memory (the instance tensor
regions and the pool's reservation-flag block, respectively), so both are issued
from the reached Event-Mode heap.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the scalar adapter, `Runtime.lean` and every existing
contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.TensorLifecycleHistory
open CTree CMemory CBody CLoops
open Rumoca.CMemory.TensorView Rumoca.CMemory.TensorRegion Rumoca.FMI3.TensorInstance
open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile
open Rumoca.FMI3.LifecycleBodies (writeMode)

section
variable [static : StaticLiterals]
private local instance historyInterface : CInterface := cInterface static.addresses
variable (program : CCalls.Events.Program E)

/-- The Instantiated → Initialization → Event → (derivative query, free) history
on one tensor instance of the static pool. The two mode transitions are threaded
through their result heaps; the derivative query and the free issue from the
reached Event-Mode heap. -/
theorem lifecycle_history (tag : CAtomicBoolean.Calls.Event → E)
    (shape oshape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (pool : Address) (slot : Fin capacity) (block owner : Nat) (owners : SlotOwners.State capacity)
    (H0 backing2 : Heap) (time : Values Tensor.scalar) (state input result : Values shape)
    (output : Option (Values oshape)) (buffer : Address) (count : UInt64)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    -- installed function definitions
    (eiDef : program.internal.definitions
      (TensorLifecycleModes.signature .enterInitialization).name =
        some (.tree (TensorLifecycleModes.function .enterInitialization)))
    (xiDef : program.internal.definitions
      (TensorLifecycleModes.signature .exitInitialization).name =
        some (.tree (TensorLifecycleModes.function .exitInitialization)))
    (derivDef : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (TensorContinuousStates.derivFunction shape)))
    -- created-instance record cells (the factory postcondition)
    (hk0 : load H0 ((TensorInstance.record pool slot.val).member "kind") =
      some (.integer Kind.me.code))
    (hm0 : H0 ((TensorInstance.record pool slot.val).member "mode") =
      some ⟨.int32, true, some (.integer Mode.instantiated.code)⟩)
    (slotMeta0 : load H0 ((TensorInstance.record pool slot.val).member "slot") =
      some (.integer slot.val))
    -- the reached Event-Mode heap is a well-formed tensor instance heap
    (coherent : writeMode (writeMode H0 (TensorInstance.record pool slot.val) .initialization)
      (TensorInstance.record pool slot.val) .event =
      TensorInstance.store backing2 pool slot.val shape oshape time state input output)
    -- derivative-query data
    (executed : Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment state input) result)
    (writable : Writable (TensorInstance.store backing2 pool slot.val shape oshape time state input output)
      buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool slot.val derivativeName).index a ≠ buffer.index b)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool slot.val shape))
        (TensorInstance.store backing2 pool slot.val shape oshape time state input output) .done) v →
      CCalls.Events.Resolves program v)
    -- release data on the reached Event-Mode heap
    (bindings : StaticRelease.Bindings program tag)
    (flagsBound : historyInterface.constants "rumoca_instance_flags" =
      some (.pointer (some ⟨block, [], 0⟩)))
    (represented : SlotOwners.Represents block
      (TensorInstance.store backing2 pool slot.val shape oshape time state input output) owners)
    (owned : owners slot = some owner) :
    ∃ finalHeap : Heap,
      -- enter Initialization Mode: fmi3OK, writes the mode cell to Initialization
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (TensorLifecycleModes.signature .enterInitialization).name
          (TensorLifecycleModes.arguments (some (TensorInstance.record pool slot.val))) H0 .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0,
          writeMode H0 (TensorInstance.record pool slot.val) .initialization⟩) ∧
      -- exit Initialization Mode: fmi3OK, writes the mode cell to Event
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (TensorLifecycleModes.signature .exitInitialization).name
          (TensorLifecycleModes.arguments (some (TensorInstance.record pool slot.val)))
          (writeMode H0 (TensorInstance.record pool slot.val) .initialization) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0,
          writeMode (writeMode H0 (TensorInstance.record pool slot.val) .initialization)
            (TensorInstance.record pool slot.val) .event⟩) ∧
      -- the derivative query on the reached Event-Mode heap: fmi3OK, delivering der(x)
      Reads finalHeap (TensorInstance.field pool slot.val derivativeName) result ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3GetContinuousStateDerivatives"
          (DerivativeCalls.values (some (TensorInstance.record pool slot.val)) (some buffer) count)
          (TensorInstance.store backing2 pool slot.val shape oshape time state input output) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0,
          written finalHeap buffer result shape.volume⟩) ∧
      -- free releases exactly this slot, restoring the owner map
      SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling TensorFree.function.signature.name
          (TensorFree.arguments (some (TensorInstance.record pool slot.val)))
          (TensorInstance.store backing2 pool slot.val shape oshape time state input output) .done) behavior ↔
        behavior = .terminates [tag (.write (AtomicSlots.address block slot) false)]
          ⟨.void, replace (TensorInstance.store backing2 pool slot.val shape oshape time state input output)
            (AtomicSlots.address block slot) (CAtomicBoolean.cell false)⟩) := by
  set rp := TensorInstance.record pool slot.val with hrp
  -- member-cell framing through the two mode writes
  have kind_ne : rp.member "kind" ≠ rp.member "mode" := by simp
  have slot_ne : rp.member "slot" ≠ rp.member "mode" := by simp
  -- kind survives both mode writes
  have kind1 : load (writeMode H0 rp .initialization) (rp.member "kind") = some (.integer Kind.me.code) := by
    have h := LifecycleBodies.write_frame H0 rp (rp.member "kind") .initialization kind_ne
    simp only [load, h]; exact hk0
  -- the enter-init mode write establishes Initialization in the mode cell
  have mode1 : (writeMode H0 rp .initialization) (rp.member "mode") =
      some ⟨.int32, true, some (.integer Mode.initialization.code)⟩ := by
    simp [writeMode, replace]
  -- kind and slot survive the second mode write too (for the deriv/free premises)
  have kind2 : load (writeMode (writeMode H0 rp .initialization) rp .event) (rp.member "kind") =
      some (.integer Kind.me.code) := by
    have h := LifecycleBodies.write_frame (writeMode H0 rp .initialization) rp (rp.member "kind") .event kind_ne
    simp only [load, h]; exact kind1
  have mode2 : load (writeMode (writeMode H0 rp .initialization) rp .event) (rp.member "mode") =
      some (.integer Mode.event.code) :=
    LifecycleBodies.write_mode (writeMode H0 rp .initialization) rp .event
  have slot2 : load (writeMode (writeMode H0 rp .initialization) rp .event) (rp.member "slot") =
      some (.integer slot.val) := by
    have h2 := LifecycleBodies.write_frame (writeMode H0 rp .initialization) rp (rp.member "slot") .event slot_ne
    have h1 := LifecycleBodies.write_frame H0 rp (rp.member "slot") .initialization slot_ne
    simp only [load, h2, h1]; exact slotMeta0
  -- enter Initialization Mode
  have ei := TensorLifecycleModes.call_behaviors .enterInitialization program H0 rp Kind.me
    Mode.instantiated eiDef hk0 hm0 (by exact rfl)
  -- exit Initialization Mode
  have xi := TensorLifecycleModes.call_behaviors .exitInitialization program
    (writeMode H0 rp .initialization) rp Kind.me Mode.initialization xiDef kind1 mode1 (by exact rfl)
  -- derivative query on the reached Event-Mode heap
  have hk : load (TensorInstance.store backing2 pool slot.val shape oshape time state input output)
      (rp.member "kind") = some (.integer Kind.me.code) := by rw [← coherent]; exact kind2
  have hm : load (TensorInstance.store backing2 pool slot.val shape oshape time state input output)
      (rp.member "mode") = some (.integer Mode.event.code) := by rw [← coherent]; exact mode2
  obtain ⟨finalHeap, reads, _others, derivBehaviors⟩ :=
    TensorContinuousStates.deriv_behaviors program shape oshape definitions linked library found
      backing2 pool slot.val time state input result output buffer count Kind.me Mode.event
      matched bounded derivDef hk hm ⟨rfl, Or.inr (Or.inl rfl)⟩ executed writable separate resolves
  -- free on the reached Event-Mode heap
  have metaCoherent : load (TensorInstance.store backing2 pool slot.val shape oshape time state input output)
      (rp.member "slot") = some (.integer slot.val) := by rw [← coherent]; exact slot2
  have free := TensorFree.free_owned program tag
    (TensorInstance.store backing2 pool slot.val shape oshape time state input output) pool block owners
    slot owner bindings flagsBound represented owned metaCoherent
  refine ⟨finalHeap, ei, xi, reads, derivBehaviors, free.1, ?_⟩
  simpa only [TensorFree.function, AtomicSlots.address] using free.2.2.2.2

end

end Rumoca.FMI3.TensorLifecycleHistory
