import RumocaFMI3.SlotOwners
import RumocaC.ConcurrentCalls
import RumocaC.AtomicCalls

/-! Slot ownership over actual interleaved C transitions. Atomic effects are
derived from the selected typed bindings; ordinary C steps preserve the flags.
Other foreign effects must establish a flag frame, and release requires the
current logical lease. These are explicit protocol obligations: the complete
factory/release code, native bindings and host-handle history must still prove
that they obey them. No native caller validity check is asserted here. -/
noncomputable section
namespace Rumoca.FMI3.SlotExecution
open CMemory

structure State (capacity : Nat) where
  execution : CCalls.Concurrent.State
  owners : SlotOwners.State capacity

def Represents (block : Nat) (state : State capacity) : Prop :=
  SlotOwners.Represents block state.execution.heap state.owners

def returned (state : CCalls.Concurrent.State) (thread : Nat) (result : Value)
    (heap : Heap) (stack : CCalls.Typed.Continuation) : CCalls.Concurrent.State :=
  ⟨heap, CCalls.Concurrent.update state.threads thread (.returning result heap stack)⟩

def reserveOwners (owners : SlotOwners.State capacity) (slot : Fin capacity)
    (lease : Nat) (busy : Bool) : SlotOwners.State capacity :=
  if busy then owners else SlotOwners.update owners slot (some lease)

variable [interface : CInterface]

/-- The release lease is a protocol premise; the scalar flag records occupancy,
not an owner's identity. The lease assignment does not impose serialization
between independent host threads or instances. -/
inductive Step (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean) (block : Nat)
    (lease : Nat → Nat) : State capacity → Nat → List E → State capacity → Prop where
  | framed {before : State capacity} {after : CCalls.Concurrent.State}
      {thread : Nat} {events : List E}
      (executed : CCalls.Concurrent.Step program before.execution thread events after)
      (preserved : CAtomicBoolean.Preserves before.execution.heap after.heap) :
      Step program tag boolean block lease before thread events ⟨after, before.owners⟩
  | reserve {before : State capacity} {thread : Nat} {slot : Fin capacity}
      {args : List Value} {stack : CCalls.Typed.Continuation} {busy : Bool} {heap : Heap}
      (found : before.execution.threads thread = some (CCalls.Concurrent.control
        (.calling "atomic_exchange" args before.execution.heap stack)))
      (bound : program.externals "atomic_exchange" =
        some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
      (converted : CCalls.Events.convertedArguments CAtomicBoolean.Calls.exchangeSignature.parameters args =
        some [.pointer (some (AtomicSlots.address block slot)), CAtomicBoolean.value true])
      (operation : CAtomicBoolean.exchange before.execution.heap (AtomicSlots.address block slot) true =
        some (busy, heap)) :
      Step program tag boolean block lease before thread
        [tag (.exchange (AtomicSlots.address block slot) busy true)]
        ⟨returned before.execution thread (CAtomicBoolean.value busy) heap stack,
          reserveOwners before.owners slot (lease thread) busy⟩
  | release {before : State capacity} {thread : Nat} {slot : Fin capacity}
      {args : List Value} {stack : CCalls.Typed.Continuation} {heap : Heap}
      (found : before.execution.threads thread = some (CCalls.Concurrent.control
        (.calling "atomic_store" args before.execution.heap stack)))
      (bound : program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag))
      (converted : CCalls.Events.convertedArguments CAtomicBoolean.Calls.writeSignature.parameters args =
        some [.pointer (some (AtomicSlots.address block slot)), CAtomicBoolean.value false])
      (owned : before.owners slot = some (lease thread))
      (operation : CAtomicBoolean.write before.execution.heap (AtomicSlots.address block slot) false = some heap) :
      Step program tag boolean block lease before thread [tag (.write (AtomicSlots.address block slot) false)]
        ⟨returned before.execution thread .void heap stack, SlotOwners.update before.owners slot none⟩

/-- Erasing ghost ownership yields the existing concurrent C machine, with
exactly the same shared memory, control transitions and observable events. -/
theorem executes (step : Step program tag boolean block lease before thread events after) :
    CCalls.Concurrent.Step program before.execution thread events after.execution := by
  cases step with
  | framed executed preserved => exact executed
  | @reserve thread slot args stack busy heap found bound converted operation =>
    apply CCalls.Concurrent.Step.run (result := .returning (CAtomicBoolean.value busy) heap stack) found
    simpa only [CCalls.Concurrent.control_resume, CCalls.Concurrent.withHeap] using
      CAtomicBoolean.Calls.exchange_step program tag boolean bound converted operation
  | @release thread slot args stack heap found bound converted owned operation =>
    apply CCalls.Concurrent.Step.run (result := .returning .void heap stack) found
    simpa only [CCalls.Concurrent.control_resume, CCalls.Concurrent.withHeap] using
      CAtomicBoolean.Calls.write_step program tag bound converted operation

theorem preserves (represented : Represents block before)
    (step : Step program tag boolean block lease before thread events after) : Represents block after := by
  cases step with
  | framed executed preserved => exact SlotOwners.ordinary_preserves represented preserved
  | @reserve thread slot args stack busy heap found bound converted operation =>
    cases busy
    · exact (SlotOwners.exchange_reserves represented operation _).2
    · exact (SlotOwners.exchange_busy represented operation).2
  | release found bound converted owned operation =>
    exact (SlotOwners.write_releases represented owned operation).2

/-- Internal evaluation is admitted without a supplied flag-frame premise:
the frame follows from the actual C evaluator's ordinary-store discipline. -/
theorem internal {before : State capacity} {thread : Nat} {saved result : CCalls.Typed.State}
    (found : before.execution.threads thread = some saved)
    (executed : CCalls.Events.internalNext program
      (CCalls.Concurrent.withHeap saved before.execution.heap) = some result) :
    Step program tag boolean block lease before thread []
      ⟨⟨CReadOnly.typedHeap result, CCalls.Concurrent.update before.execution.threads thread result⟩,
        before.owners⟩ := by
  apply Step.framed (CCalls.Concurrent.Step.run found (.internal executed))
  simpa only [CCalls.Concurrent.heap_withHeap] using CAtomicBoolean.internal_preserves program executed

theorem reaches_preserves
    (represented : Represents block before)
    (path : Transition.Events.Reaches
      (fun before events after => ∃ thread, Step program tag boolean block lease before thread events after)
      before events after) : Represents block after := by
  induction path with
  | refl => exact represented
  | next first rest ih =>
    obtain ⟨thread, step⟩ := first
    exact ih (preserves represented step)

theorem reaches_executes
    (path : Transition.Events.Reaches
      (fun before events after => ∃ thread, Step program tag boolean block lease before thread events after)
      before events after) :
    Transition.Events.Reaches
      (fun before events after => ∃ thread, CCalls.Concurrent.Step program before thread events after)
      before.execution events after.execution := by
  induction path with
  | refl => exact .refl _
  | next first rest ih =>
    obtain ⟨thread, step⟩ := first
    exact .next ⟨thread, executes step⟩ ih

end Rumoca.FMI3.SlotExecution
