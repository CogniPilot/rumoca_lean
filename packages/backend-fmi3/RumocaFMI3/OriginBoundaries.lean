import RumocaFMI3.RetiredTickets
import RumocaFMI3.InstanceAuthorityActions

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable [interface : CInterface] {E : Type} {capacity : Nat}

/-- Actual ordinary entry preserves the complete resource/API origin relation.
The ledger's idle condition comes from real host idleness and recorded-history
alignment, rather than being assumed independently for each new resource. -/
theorem method_enter_origins (program : Events.Program E) (policy : Host.Policy)
    (before : PublicationRegistry.Configuration capacity) (authority : State capacity)
    (instances flags thread : Nat) (handle : Handle capacity) (api : PublicAPI.Entry) (tail : List Value)
    (ordinary : api.ordinary = true) (linked : Linked authority before.publications)
    (origins : CallOrigins authority before.recorded.ledger instances)
    (aligned : Host.Recording.Aligned before.recorded.runtime before.recorded.ledger)
    (owned : Owns authority handle)
    (actual : Host.Step program policy before.recorded.runtime thread
      (.invoke api.signature.name (handle.value instances :: tail)) after) :
    let action := Host.Action.invoke (E := E) api.signature.name (handle.value instances :: tail)
    let ledger := Host.Recording.advance before.recorded.ledger thread action
    ∃ following,
      enter authority handle before.recorded.ledger.next .use = some following ∧
      Borrowing following ledger thread handle instances ∧ Linked following before.publications ∧
      CallOrigins following ledger instances ∧
      PublicationRegistry.Step program policy instances flags before
        [Host.Recording.stamp before.recorded.ledger thread action]
        ⟨⟨after, ledger⟩, before.publications⟩ := by
  obtain ⟨following, entered, borrowing, related, step⟩ :=
    method_enter program policy before authority instances flags thread handle api tail ordinary linked owned actual
  have idle := (aligned thread).mp (Host.invoke_iff.mp actual).1
  exact ⟨following, entered, borrowing, related,
    enter_call_origins origins idle entered ⟨api, ordinary, rfl⟩, step⟩

/-- Actual release entry establishes a releasing API origin with its exact
single handle argument, preserving all other active resource origins. -/
theorem release_enter_origins (program : Events.Program E) (policy : Host.Policy)
    (before : PublicationRegistry.Configuration capacity) (authority : State capacity)
    (instances flags thread : Nat) (handle : Handle capacity)
    (linked : Linked authority before.publications)
    (origins : CallOrigins authority before.recorded.ledger instances)
    (aligned : Host.Recording.Aligned before.recorded.runtime before.recorded.ledger)
    (owned : Owns authority handle)
    (actual : Host.Step program policy before.recorded.runtime thread
      (.invoke StaticRelease.function.signature.name [handle.value instances]) after) :
    let action := Host.Action.invoke (E := E) StaticRelease.function.signature.name [handle.value instances]
    let ledger := Host.Recording.advance before.recorded.ledger thread action
    ∃ following,
      enter authority handle before.recorded.ledger.next .release = some following ∧
      Releasing following ledger thread handle instances ∧ Linked following before.publications ∧
      CallOrigins following ledger instances ∧
      PublicationRegistry.Step program policy instances flags before
        [Host.Recording.stamp before.recorded.ledger thread action]
        ⟨⟨after, ledger⟩, before.publications⟩ := by
  obtain ⟨following, entered, releasing, related, step, _⟩ :=
    release_enter program policy before authority instances flags thread handle linked owned actual
  have idle := (aligned thread).mp (Host.invoke_iff.mp actual).1
  exact ⟨following, entered, releasing, related,
    enter_call_origins origins idle entered ⟨rfl, rfl⟩, step⟩

/-- Successful factory observation creates the current handle resource and
preserves every existing method/release origin when retiring the factory call. -/
theorem factory_complete_origins (program : Events.Program E) (policy : Host.Policy)
    (before : PublicationRegistry.Configuration capacity) (authority : State capacity)
    (instances flags thread : Nat) (slot : Fin capacity) (call : Host.Recording.Invocation)
    (linked : Linked authority before.publications)
    (origins : CallOrigins authority before.recorded.ledger instances)
    (unique : Host.Recording.Unique before.recorded.ledger)
    (active : before.recorded.ledger.active thread = some call)
    (factory : ReservationOrigin.factory call.name)
    (privateEntry : before.publications slot = some ⟨call.serial, false⟩)
    (actual : Host.Step program policy before.recorded.runtime thread
      (.complete (.pointer (some (AtomicSlots.address instances slot)))) after) :
    let handle : Handle capacity := ⟨slot, call.serial⟩
    let action := Host.Action.complete (E := E) (handle.value instances)
    let published := PublicationRegistry.advance before.publications instances flags before.recorded thread action
    let ledger := Host.Recording.advance before.recorded.ledger thread action
    ∃ following,
      publish authority handle = some following ∧ Owns following handle ∧ Linked following published ∧
      CallOrigins following ledger instances ∧
      PublicationRegistry.Published published slot call.serial ∧
      PublicationRegistry.Step program policy instances flags before
        [Host.Recording.stamp before.recorded.ledger thread action] ⟨⟨after, ledger⟩, published⟩ := by
  obtain ⟨following, issued, owned, related, published, _, step⟩ :=
    factory_complete program policy before authority instances flags thread slot call linked active factory privateEntry actual
  exact ⟨following, issued, owned, related,
    publish_call_origins origins unique active factory issued _, published, step⟩

/-- The actual ordinary completion returns only its own resource and preserves
full API origins. The weaker argument-origin premise is now derived. -/
theorem method_complete_origins (program : Events.Program E) (policy : Host.Policy)
    (before : PublicationRegistry.Configuration capacity) (authority : State capacity)
    (instances flags thread : Nat) (handle : Handle capacity)
    (linked : Linked authority before.publications)
    (origins : CallOrigins authority before.recorded.ledger instances)
    (unique : Host.Recording.Unique before.recorded.ledger)
    (borrowing : Borrowing authority before.recorded.ledger thread handle instances)
    (actual : Host.Step program policy before.recorded.runtime thread (.complete value) after) :
    let ledger := Host.Recording.advance (E := E) before.recorded.ledger thread (.complete value)
    ∃ call, before.recorded.ledger.active thread = some call ∧
      Owns (completeUse authority call.serial) handle ∧ Linked (completeUse authority call.serial) before.publications ∧
      CallOrigins (completeUse authority call.serial) ledger instances ∧
      (∀ slot, slot ≠ handle.slot → completeUse authority call.serial slot = authority slot) ∧
      after.heap = before.recorded.runtime.heap ∧
      PublicationRegistry.Step program policy instances flags before
        [Host.Recording.stamp before.recorded.ledger thread (.complete value)] ⟨⟨after, ledger⟩, before.publications⟩ := by
  obtain ⟨call, active, owned, related, frame, heap, step⟩ :=
    method_complete program policy before authority instances flags thread handle linked borrowing origins.arguments unique actual
  obtain ⟨original, api, tail, originalActive, _, _, _, borrowed⟩ := borrowing
  cases Option.some.inj (originalActive.symm.trans active)
  exact ⟨call, active, owned, related, complete_call_origins origins unique active borrowed value, frame, heap, step⟩

/-- Observing the real void completion after resource consumption leaves the
current resource map and publications unchanged, even after slot reuse. -/
theorem released_complete_origins (program : Events.Program E) (policy : Host.Policy)
    (before : PublicationRegistry.Configuration capacity) (authority : State capacity)
    (instances flags thread : Nat) (call : Host.Recording.Invocation)
    (origins : CallOrigins authority before.recorded.ledger instances)
    (active : before.recorded.ledger.active thread = some call)
    (absent : NoTicket authority call.serial)
    (actual : Host.Step program policy before.recorded.runtime thread (.complete .void) after) :
    let ledger := Host.Recording.advance (E := E) before.recorded.ledger thread (.complete .void)
    CallOrigins authority ledger instances ∧ after.heap = before.recorded.runtime.heap ∧
      PublicationRegistry.Step program policy instances flags before
        [Host.Recording.stamp before.recorded.ledger thread (.complete .void)] ⟨⟨after, ledger⟩, before.publications⟩ := by
  exact ⟨complete_without_ticket origins active absent .void,
    by rw [(Host.complete_iff.mp actual).2], .record actual⟩

end Rumoca.FMI3.InstanceAuthority
