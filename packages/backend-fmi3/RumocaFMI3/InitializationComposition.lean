import RumocaFMI3.InitializationCalls

noncomputable section
namespace Rumoca.FMI3.InitializationCalls
open Initialization
open CTree CMemory CBody

def exitedHeap (heap : Heap) (p : Address) (args : Initialization.Arguments) (kind : Kind) : Heap :=
  InitializationBodies.exitHeap (InitializationEntry.finalHeap heap p args) p kind

theorem entered_kind (heap : Heap) (p : Address) (args : Initialization.Arguments) :
    load (InitializationEntry.finalHeap heap p args) (p.member "kind") = load heap (p.member "kind") := by
  have same := InitializationEntry.frame heap p (p.member "kind") args
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
  simp only [load, same]

theorem entered_mode (heap : Heap) (p : Address) (args : Initialization.Arguments) :
    InitializationEntry.finalHeap heap p args (p.member "mode") =
      some ⟨.int32, true, some (.integer 1)⟩ := by
  simp [InitializationEntry.finalHeap]

theorem exited_frame (heap : Heap) (p q : Address) (args : Initialization.Arguments) (kind : Kind)
    (ht : q ≠ p.member "time") (hn : q ≠ p.member "timeMin")
    (he : q ≠ p.member "eventTime") (hl : q ≠ p.member "lastCompleted")
    (hs : q ≠ p.member "stop") (hd : q ≠ p.member "stopDefined")
    (hm : q ≠ p.member "mode") : exitedHeap heap p args kind q = heap q := by
  rw [exitedHeap, InitializationBodies.exit_frame _ _ _ _ hm]
  exact InitializationEntry.frame heap p q args ht hn he hl hs hd hm

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem exited_time_guard (heap : Heap) (p : Address) (args : Initialization.Arguments)
    (kind : Kind) (admissible : Arguments.Admissible args) (time : Binary64.Value) :
    eval (TimeProofs.locals p (Binary64.toBits time).val) (exitedHeap heap p args kind) Runtime.invalidTime =
      some (boolean false) ↔ (Time.Window.initial args.start args.stopTime).Admissible time := by
  apply HistoryProofs.stored_guard_reference (exitedHeap heap p args kind) p
    (Time.Clock.initial args.start) (Time.History.initial args.start args.stopTime) time
    (InitializationBodies.exit_history (stored heap p args) kind) (Time.initial_represents _ _)
  · have same : load (exitedHeap heap p args kind) (p.member "stopDefined") =
        load (InitializationEntry.finalHeap heap p args) (p.member "stopDefined") := by
      simp [exitedHeap, InitializationBodies.exitHeap, load, replace]
    rw [same]
    simpa only [Time.History.initial, Time.Window.initial, stopTime_defined args admissible]
      using (InitializationEntry.stop heap p args).2
  · intro bound hb
    have hbits := stopTime_bits args admissible bound hb
    have same : load (exitedHeap heap p args kind) (p.member "stop") =
        load (InitializationEntry.finalHeap heap p args) (p.member "stop") := by
      simp [exitedHeap, InitializationBodies.exitHeap, load, replace]
    rw [same]
    simpa only [Value.finite, hbits] using (InitializationEntry.stop heap p args).1


end
end Rumoca.FMI3.InitializationCalls
