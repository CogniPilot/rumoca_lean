import RumocaC.StoreRunInvariant
import RumocaC.AtomicFrame
import RumocaFMI3.InitializationQuiet

noncomputable section
namespace Rumoca.FMI3.InitializationStorage
open CMemory

/-- Exact initialization heap updates retain the original typed objects.
The auxiliary literal interface only reuses the existing body-execution proof;
this memory proposition has no interface or literal-address premise. -/
theorem entered (heap : Heap) (p : Address) (args : Initialization.Arguments) (kind : Kind)
    (admissible : args.Admissible) (storage : InitializationCalls.EntryStorage heap p)
    (kindValue : load heap (p.member "kind") = some (.integer kind.code)) :
    CStorage.Preserves heap (InitializationEntry.finalHeap heap p args) ∧
      CAtomicBoolean.Preserves heap (InitializationEntry.finalHeap heap p args) := by
  let literals : CLiteralAddresses := fun _ => none
  letI : CInterface := cInterface literals
  obtain ⟨clock, mode, ⟨stopOld, stop⟩, ⟨flagOld, flag⟩⟩ := storage
  have run := InitializationCalls.body_run (static := ⟨literals⟩) heap p args kind
    admissible clock stopOld flagOld kindValue mode stop flag
  exact ⟨CStoreInvariant.body_run ⟨CStorage.Preserves.refl, fun _ _ _ _ => CStorage.store_preserves⟩
    (fun a b => a.trans b) run,
    CStoreInvariant.body_run CAtomicBoolean.ordinary_stable (fun a b => a.trans b) run⟩

theorem exited (heap : Heap) (p : Address) (kind : Kind)
    (mode : heap (p.member "mode") = some ⟨.int32, true, some (.integer 1)⟩) :
    CStorage.Preserves heap (InitializationBodies.exitHeap heap p kind) ∧
      CAtomicBoolean.Preserves heap (InitializationBodies.exitHeap heap p kind) := by
  have stored : store heap (p.member "mode") (.integer (nextMode .exitInitialization kind .initialization).code) =
      some (InitializationBodies.exitHeap heap p kind) := by
    cases kind <;> simp [store, mode, convert, InitializationBodies.exitHeap, me_initialization, cs_initialization, Mode.code]
  exact ⟨CStorage.store_preserves stored, CAtomicBoolean.ordinary_store_preserves stored⟩

end Rumoca.FMI3.InitializationStorage
end
