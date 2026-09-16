import RumocaC.HostStoreInvariant
import RumocaFMI3.RuntimeStorage
import RumocaFMI3.StaticStorage

namespace Rumoca.FMI3.RuntimeStorage
open CTree CMemory CCalls CCalls.Events CStoreInvariant CStorage RuntimeLinkage
variable [CInterface]

/-- Actual public histories preserve the complete object layout and writable
descriptors. Values may change; callbacks and explicit host memory actions
must preserve descriptors, not freeze the instance's numerical state. -/
theorem logged_host_storage (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : CInterface.types "_Bool" = some .boolean)
    (size : CInterface.types "size_t" = some .size)
    (integer : CInterface.types "int" = some .int32)
    (double : CInterface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName))
    (callback : ∀ args before result after, effect.execute args before result after → Preserves before after)
    (policy : Host.Policy)
    (memory : ∀ state thread heap, policy.memory state thread heap → Preserves state.heap heap)
    (path : Host.History (logged model sigs covered tag boolean size integer double observed range logger effect)
      policy before trace after) : Preserves before.heap after.heap :=
  CStoreInvariant.host_history stable Preserves.trans
    (logged_storage model sigs covered tag boolean size integer double observed range logger effect callback)
    memory path

/-- The authored static declaration initialization supplies every slot's
writable layout at every reached public-history prefix. No separately assumed
writable instance heap at the reservation step is needed. -/
theorem logged_initial_slots (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : CInterface.types "_Bool" = some .boolean)
    (size : CInterface.types "size_t" = some .size)
    (integer : CInterface.types "int" = some .int32)
    (double : CInterface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName))
    (callback : ∀ args before result after, effect.execute args before result after → Preserves before after)
    (policy : Host.Policy)
    (memory : ∀ state thread heap, policy.memory state thread heap → Preserves state.heap heap)
    (objects : StaticFactory.Objects) (initialHeap : Heap)
    (path : Host.History (logged model sigs covered tag boolean size integer double observed range logger effect)
      policy ⟨StaticStorage.initial objects initialHeap, fun _ => none⟩ trace current) :
    ∀ slot : Fin objects.capacity, InstanceSlot.Storage current.heap (objects.instances.index slot.val) := by
  have descriptors := logged_host_storage model sigs covered tag boolean size integer double observed range logger effect
    callback policy memory path
  exact fun slot => (StaticStorage.initial_fields objects initialHeap slot).preserved descriptors

end Rumoca.FMI3.RuntimeStorage
