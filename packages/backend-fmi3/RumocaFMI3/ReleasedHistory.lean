import RumocaFMI3.ResourceHistory

namespace Rumoca.FMI3.InstanceAuthority.Resources
open CTree CMemory CCalls
variable [CInterface] {E : Type} {program : Events.Program E} {policy : Host.Policy}
  {capacity : Nat} {before after : Configuration capacity}

def initial (capacity : Nat) (heap : Heap) : Configuration capacity :=
  ⟨⟨⟨heap, fun _ => none⟩, Host.Recording.initial⟩, fun _ => none⟩

/-- Starting from the empty actual host ledger, every active resource has
the corresponding original public invocation and exact instance argument. -/
theorem initial_history_origins
    (path : Transition.Events.Reaches (Step program policy instances flags) (initial capacity heap) ticks after) :
    CallOrigins after.authority after.recorded.ledger instances ∧
    Host.Recording.Aligned after.recorded.runtime after.recorded.ledger ∧
    Host.Recording.Fresh after.recorded.ledger ∧ Host.Recording.Unique after.recorded.ledger := by
  exact history_origins path (empty_call_origins _ _) (Host.Recording.initial_aligned heap)
    Host.Recording.initial_fresh Host.Recording.initial_unique

/-- At the actual pending clear, the existing authorized operation consumes
the original call's only resource ticket. This supplies the starting invariant
for arbitrary later resource histories; no later absence annotation is needed. -/
theorem clear_retires (start : Configuration capacity) (call : Host.Recording.Invocation)
    (handle : Handle capacity)
    (origins : CallOrigins start.authority start.recorded.ledger instances)
    (fresh : Host.Recording.Fresh start.recorded.ledger)
    (unique : Host.Recording.Unique start.recorded.ledger)
    (active : start.recorded.ledger.active thread = some call)
    (name : call.name = StaticRelease.function.signature.name)
    (args : call.args = [handle.value instances])
    (calling : start.recorded.runtime.threads thread = some (.calling "atomic_store"
      [.pointer (some (AtomicSlots.address flags handle.slot)), CAtomicBoolean.value false] heap stack))
    (cleared : InstanceAuthority.clear start.authority handle call.serial = some following)
    (actual : Host.Step program policy start.recorded.runtime thread (.execute events) target) :
    let result : Configuration capacity := ⟨⟨target, start.recorded.ledger⟩, following⟩
    Step program policy instances flags start
      [Host.Recording.stamp start.recorded.ledger thread (.execute events)] result ∧
    CallOrigins result.authority result.recorded.ledger instances ∧
    NoTicket result.authority call.serial ∧ call.serial < result.recorded.ledger.next := by
  exact ⟨.record actual (.clear active name args calling cleared), clear_call_origins origins cleared,
    cleared_no_ticket origins.arguments unique cleared, fresh thread call active⟩

/-- Slot reuse and later calls cannot recreate the retired release ticket.
Its real void completion removes only its invocation descriptor and preserves
the entire current authority map, publication map and heap. This theorem does
not assert memory/callback frames or admission of arbitrary importer histories. -/
theorem released_history_complete (start : Configuration capacity)
    (call : Host.Recording.Invocation)
    (origins : CallOrigins start.authority start.recorded.ledger instances)
    (aligned : Host.Recording.Aligned start.recorded.runtime start.recorded.ledger)
    (fresh : Host.Recording.Fresh start.recorded.ledger)
    (unique : Host.Recording.Unique start.recorded.ledger)
    (retired : NoTicket start.authority call.serial) (earlier : call.serial < start.recorded.ledger.next)
    (path : Transition.Events.Reaches (Step program policy instances flags) start ticks before)
    (active : before.recorded.ledger.active thread = some call)
    (name : call.name = StaticRelease.function.signature.name)
    (actual : Host.Step program policy before.recorded.runtime thread (.complete .void) target) :
    let ledger := Host.Recording.advance (E := E) before.recorded.ledger thread (.complete .void)
    NoTicket before.authority call.serial ∧ CallOrigins before.authority ledger instances ∧
    Step program policy instances flags before [Host.Recording.stamp before.recorded.ledger thread (.complete .void)]
      ⟨⟨target, ledger⟩, before.authority⟩ ∧ target.heap = before.recorded.runtime.heap ∧
    ∀ publications : PublicationRegistry.State capacity, PublicationRegistry.Step program policy instances flags ⟨before.recorded, publications⟩
      [Host.Recording.stamp before.recorded.ledger thread (.complete .void)] ⟨⟨target, ledger⟩, publications⟩ := by
  have absent := (history_retired path retired earlier).1
  have current := (history_origins path origins aligned fresh unique).1
  have nonfactory : ¬ ReservationOrigin.factory call.name := by
    rw [name]
    simp [ReservationOrigin.factory, StaticRelease.function]
  refine ⟨absent, complete_without_ticket (E := E) current active absent .void,
    .record actual (.completeUnowned active absent (.inl nonfactory)), ?_, ?_⟩
  · rw [(Host.complete_iff.mp actual).2]
  · intro publications
    exact .record actual

end Rumoca.FMI3.InstanceAuthority.Resources
