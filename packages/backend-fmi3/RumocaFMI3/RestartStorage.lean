import RumocaFMI3.InitializationStorage
import RumocaFMI3.ResetStorage
import RumocaFMI3.StaticReset

noncomputable section
namespace Rumoca.FMI3.InitializationStorage
open CMemory

/-- The ordinary reset/entry/exit sequence preserves all supplied storage
for either interface and every admissible initialization argument set. -/
theorem restarted (model : Solve.FMI3Model source) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (storage : Reset.Storage heap p)
    (kindValue : load heap (p.member "kind") = some (.integer kind.code))
    (modeValue : load heap (p.member "mode") = some (.integer mode.code))
    (args : Initialization.Arguments) (admissible : args.Admissible) :
    CStorage.Preserves heap (InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args kind) := by
  have initial := (Reset.preserves model heap p kind mode storage kindValue modeValue).1
  have entry := (entered (Reset.finalHeap heap p) p args kind admissible
    (StaticReset.entry_storage heap p) ((StaticReset.kind_value heap p).trans kindValue)).1
  have initializedMode : InitializationEntry.finalHeap (Reset.finalHeap heap p) p args (p.member "mode") =
      some ⟨.int32, true, some (.integer 1)⟩ := by simp [InitializationEntry.finalHeap, replace]
  exact initial.trans (entry.trans (exited _ p kind initializedMode).1)

end Rumoca.FMI3.InitializationStorage
end
