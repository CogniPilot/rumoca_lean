import RumocaFMI3.StaticRelease
import RumocaFMI3.TensorInstanceStorage

/-! Tensor `fmi3FreeInstance` over the static tensor instance pool, as a
package-checked product.

The free body is entirely model-agnostic: it reads only the reserved slot index
`m->slot` stored at creation and the pool's reservation-flag block, and performs
one atomic store that clears the slot's flag. It never reads or writes a tensor
region, so the tensor free is exactly the shared `StaticRelease.function`,
instantiated for the tensor pool record `TensorInstance.record pool i =
pool.index i`. This file re-exports the shared release theorems specialized to the
tensor pool and bundles them as a `FunctionContract` mirroring the release portion
of the scalar `StaticRuntime.FunctionContract`, so a tensor adapter contract can
consume them.

Every theorem is universal in the pool root, the reservation-flag block, the pool
capacity, the owner map, and the released slot. This is a package-checked product
only: no production artifact is emitted, no CLI or grammar case is added, and the
scalar adapter, `Runtime.lean` and every existing contract are unchanged. -/
noncomputable section
namespace Rumoca.FMI3.TensorFree
open CTree CMemory CBody

/-- The tensor free function is the shared model-agnostic release function. -/
def function : CTree.Function := StaticRelease.function

def arguments (handle : Option Address) : List Value := [.pointer handle]

section
variable [interface : CInterface]

/-- Releasing an owned slot of the tensor pool discharges exactly its lease,
restoring the owner map to `update owners slot none`, performing one atomic store,
preserving every other cell, and returning void. The slot-metadata premise is the
index stored by the tensor factory at creation. Instantiates
`StaticRelease.release_owned` for the tensor pool record. -/
theorem free_owned (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (heap : Heap) (pool : Address) (block : Nat) (owners : SlotOwners.State capacity)
    (slot : Fin capacity) (owner : Nat) (bindings : StaticRelease.Bindings program tag)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨block, [], 0⟩)))
    (represented : SlotOwners.Represents block heap owners) (owned : owners slot = some owner)
    (metadata : load heap ((TensorInstance.record pool slot.val).member "slot") = some (.integer slot.val)) :
    let after := replace heap (AtomicSlots.address block slot) (CAtomicBoolean.cell false)
    SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
      SlotOwners.Represents block after (SlotOwners.update owners slot none) ∧
      CStorage.Preserves heap after ∧
      (∀ query, query ≠ AtomicSlots.address block slot → after query = heap query) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling function.signature.name (arguments (some (TensorInstance.record pool slot.val))) heap .done)
        behavior ↔
      behavior = .terminates [tag (.write (AtomicSlots.address block slot) false)] ⟨.void, after⟩ :=
  StaticRelease.release_owned program tag heap pool block owners slot owner bindings flagsBound
    represented owned metadata

/-- A null handle releases nothing and changes no cell. Instantiates
`StaticRelease.null_behaviors`. -/
theorem null_behaviors (program : CCalls.Events.Program E) (heap : Heap)
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (handle : interface.types "fmi3Instance" = some .pointer)
    (pointer : interface.types "Instance *" = some .pointer)
    (voidPointer : interface.types "void *" = some .pointer) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling function.signature.name (arguments none) heap .done) behavior ↔
      behavior = .terminates [] ⟨.void, heap⟩ :=
  StaticRelease.null_behaviors program heap defined handle pointer voidPointer behavior

/-- The tensor free function contract, mirroring the release portion of the
scalar `StaticRuntime.FunctionContract`. -/
structure Contract (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E) : Prop where
  bindings : StaticRelease.Bindings program tag
  freed : ∀ (heap : Heap) (pool : Address) (block : Nat) (owners : SlotOwners.State capacity)
    (slot : Fin capacity) (owner : Nat),
    interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨block, [], 0⟩)) →
    SlotOwners.Represents block heap owners → owners slot = some owner →
    load heap ((TensorInstance.record pool slot.val).member "slot") = some (.integer slot.val) →
    let after := replace heap (AtomicSlots.address block slot) (CAtomicBoolean.cell false)
    SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
      SlotOwners.Represents block after (SlotOwners.update owners slot none) ∧
      CStorage.Preserves heap after ∧
      (∀ query, query ≠ AtomicSlots.address block slot → after query = heap query) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling function.signature.name (arguments (some (TensorInstance.record pool slot.val))) heap .done)
        behavior ↔
      behavior = .terminates [tag (.write (AtomicSlots.address block slot) false)] ⟨.void, after⟩
  null : ∀ (heap : Heap),
    interface.types "fmi3Instance" = some .pointer →
    interface.types "Instance *" = some .pointer →
    interface.types "void *" = some .pointer →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling function.signature.name (arguments none) heap .done) behavior ↔
      behavior = .terminates [] ⟨.void, heap⟩

theorem contract (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (bindings : StaticRelease.Bindings program tag) : Contract program tag where
  bindings := bindings
  freed heap pool block owners slot owner flagsBound represented owned metadata :=
    free_owned program tag heap pool block owners slot owner bindings flagsBound represented owned metadata
  null heap handle pointer voidPointer :=
    null_behaviors program heap bindings.defined handle pointer voidPointer

end

end Rumoca.FMI3.TensorFree
