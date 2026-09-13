import RumocaFMI3.InstanceInitializationCalls
import RumocaFMI3.SlotOwners
import RumocaC.StorageTransfer

/-! Instance storage and atomic reservation bookkeeping share one heap.
Reservation preserves the storage needed by initialization, and initialization
preserves every existing slot lease. Complete public acquisition/release and
native storage declarations remain separate obligations. -/
noncomputable section
namespace Rumoca.FMI3.InstanceInitialization
open CMemory

private theorem writable_preserved (preserved : CStorage.Preserves before after)
    (writable : Reset.Writable before p type) : Reset.Writable after p type := by
  obtain ⟨value, found⟩ := writable
  exact preserved.cell found

theorem Storage.preserved (storage : Storage before p) (preserved : CStorage.Preserves before after) :
    Storage after p := by
  rcases storage with ⟨⟨hx, ht, hn, he, hc, hs, hd, hm⟩, hk, hv, hl, hg⟩
  exact ⟨⟨writable_preserved preserved hx, writable_preserved preserved ht,
    writable_preserved preserved hn, writable_preserved preserved he,
    writable_preserved preserved hc, writable_preserved preserved hs,
    writable_preserved preserved hd, writable_preserved preserved hm⟩,
    writable_preserved preserved hk, writable_preserved preserved hv,
    writable_preserved preserved hl, writable_preserved preserved hg⟩

/-- The actual atomic exchange cannot invalidate any instance object's storage,
including the selected slot and other instances in the same array. -/
theorem reserved_storage (storage : Storage before p)
    (exchanged : CAtomicBoolean.exchange before flag true = some (busy, after)) : Storage after p :=
  storage.preserved (CAtomicBoolean.exchange_storage exchanged)

variable [interface : CInterface]

theorem initialized_owners (program : CCalls.Events.Program E) (model : Solve.Model source)
    (kind : Kind) (env : CBody.Locals) (types : CLoops.Types) (heap : Heap) (p : Address)
    (environment logger : Option Address) (logging : Bool)
    (storage : Storage heap p) (bound : Bindings env p environment logger logging)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (owners : SlotOwners.State capacity) (represented : SlotOwners.Represents block heap owners) :
    SlotOwners.Represents block (finalHeap heap p kind environment logger logging) owners := by
  have path := return_reaches program model kind env types heap p environment logger logging .done
    storage bound double handle
  have framed : CAtomicBoolean.Preserves heap (finalHeap heap p kind environment logger logging) := by
    have general : ∀ before after,
        Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t) before after →
        CAtomicBoolean.Preserves (CReadOnly.typedHeap before) (CReadOnly.typedHeap after) := by
      intro before after reached
      induction reached with
      | refl => exact .refl _
      | next first rest ih => exact (CAtomicBoolean.internal_preserves program first).trans ih
    exact general _ _ path
  exact SlotOwners.ordinary_preserves represented framed

end Rumoca.FMI3.InstanceInitialization
