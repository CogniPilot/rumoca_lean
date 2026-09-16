import RumocaFMI3.ResourcePublication
import RumocaC.InvocationRetention

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CCalls
variable {capacity : Nat}

/-- Claiming another slot or observing this slot busy cannot replace any
existing reservation, including a private initializer's reservation. -/
theorem claim_keeps (present : publications slot = some entry) (selected : Fin capacity) (serial : Nat) :
    PublicationRegistry.synchronize publications
      (ConcurrentSlots.claimOwners (PublicationRegistry.reservations publications) selected serial) slot = some entry := by
  cases selectedEntry : publications selected with
  | some occupied =>
    rw [PublicationRegistry.synchronize_claim_busy selectedEntry]
    exact present
  | none =>
    rw [PublicationRegistry.synchronize_claim_free selectedEntry]
    have different : slot ≠ selected := by
      intro same
      subst slot
      rw [selectedEntry] at present
      contradiction
    simpa only [if_neg different] using present

/-- The computed actual-control update preserves an existing private record
on non-clearing execution; it does not assume a per-step reservation frame. -/
theorem execute_keeps (present : publications slot = some entry)
    (notClear : ¬ ReservationRegistry.AtCall before.runtime thread "atomic_store") :
    PublicationRegistry.advance publications instances flags before thread (Host.Action.execute (E := E) events) slot = some entry := by
  unfold PublicationRegistry.advance ReservationRegistry.executeUpdate
  split
  next name args heap stack found =>
    have nonclear : name ≠ "atomic_store" := by
      intro same
      subst name
      exact notClear ⟨args, heap, stack, found⟩
    unfold ReservationRegistry.callUpdate
    split
    next =>
      split
      next =>
        split
        next selected call decoded active => exact claim_keeps present selected call.serial
        next => simpa only [PublicationRegistry.synchronize_reservations] using present
      next => simpa only [PublicationRegistry.synchronize_reservations] using present
    next => simpa only [if_neg nonclear, PublicationRegistry.synchronize_reservations] using present
  next => simpa only [PublicationRegistry.synchronize_reservations] using present

end Rumoca.FMI3.InstanceAuthority.Resources.Publication

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CCalls
variable {capacity : Nat} {publications : PublicationRegistry.State capacity} {slot : Fin capacity}

/-- An authorized release cannot clear a private initializer slot: its
resource must be linked to a published reservation at the cleared address. -/
theorem clear_keeps {handle : Handle capacity}
    (linked : Linked authority publications)
    (privateEntry : publications slot = some ⟨lease, false⟩)
    (cleared : InstanceAuthority.clear authority handle serial = some following)
    (calling : before.runtime.threads thread = some (.calling "atomic_store"
      [.pointer (some (AtomicSlots.address flags handle.slot)), CAtomicBoolean.value false] heap stack)) :
    PublicationRegistry.advance publications instances flags before thread (Host.Action.execute (E := E) events) slot =
      some ⟨lease, false⟩ := by
  have vacant := private_vacant linked privateEntry
  have account := (clear_iff.mp cleared).1
  have different : slot ≠ handle.slot := by
    intro same
    subst slot
    rw [account] at vacant
    contradiction
  rw [PublicationRegistry.advance_clear _ _ _ _ _ _ _ calling]
  simpa only [if_neg different] using privateEntry

/-- While the original descriptor remains active, another observed return
cannot publish or replace its private reservation. Exact ledger identity,
rather than thread or pointer reuse, distinguishes the returning invocation. -/
theorem complete_keeps (unique : Host.Recording.Unique ledger)
    (active : ledger.active tracked = some original)
    (stillActive : (Host.Recording.advance (E := E) ledger thread (.complete value)).active tracked = some original)
    (privateEntry : publications slot = some ⟨original.serial, false⟩) :
    PublicationRegistry.observe publications instances ledger thread value slot = some ⟨original.serial, false⟩ := by
  have differentThread : thread ≠ tracked := by
    intro same
    subst thread
    simp [Host.Recording.advance, Host.Recording.bind] at stillActive
  cases value with
  | pointer address =>
    cases address with
    | none => exact privateEntry
    | some address =>
      cases current : ledger.active thread with
      | none => simpa only [PublicationRegistry.observe, current] using privateEntry
      | some call =>
        have differentSerial : call.serial ≠ original.serial := by
          intro same
          exact differentThread (unique thread call tracked original current active same).1
        by_cases factory : ReservationOrigin.factory call.name
        · simp only [PublicationRegistry.observe, current, if_pos factory]
          cases decoded : ReservationRegistry.slotAt instances capacity address with
          | none => simpa only [decoded] using privateEntry
          | some selected =>
            dsimp only
            by_cases same : slot = selected
            · subst selected
              rw [PublicationRegistry.publish_wrong_lease privateEntry differentSerial.symm]
              exact privateEntry
            · simpa only [PublicationRegistry.publish, if_neg same] using privateEntry
        · simpa only [PublicationRegistry.observe, current, if_neg factory] using privateEntry
  | _ => exact privateEntry

end Rumoca.FMI3.InstanceAuthority.Resources.Publication

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CCalls
variable [CInterface] {E : Type} {program : Events.Program E} {policy : Host.Policy}
  {capacity : Nat} {before after : Configuration capacity}

/-- A still-active original invocation retains its private reservation across
the actual coupled step. The resource/publication invariant rules out another
call clearing it; fresh invocation identity rules out another call publishing it. -/
theorem Step.private_reservation (step : Step program policy instances flags before ticks after)
    (invariant : Invariant instances before)
    (privateEntry : before.publications slot = some ⟨call.serial, false⟩)
    (active : before.resources.recorded.ledger.active tracked = some call)
    (stillActive : after.resources.recorded.ledger.active tracked = some call) :
    after.publications slot = some ⟨call.serial, false⟩ := by
  cases step with
  | @record thread action target before authority following publications actual changed factoryResult =>
    cases action with
    | invoke | memory => exact privateEntry
    | execute events =>
      cases changed with
      | execute notClear => exact execute_keeps (E := E) (instances := instances) (events := events) privateEntry notClear
      | clear current name args calling cleared =>
        exact clear_keeps (E := E) (instances := instances) (events := events) invariant.linked privateEntry cleared calling
    | complete value =>
      exact complete_keeps (E := E) (instances := instances) (value := value) invariant.unique active stillActive privateEntry

end Rumoca.FMI3.InstanceAuthority.Resources.Publication

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CCalls
variable [CInterface] {E : Type} {program : Events.Program E} {policy : Host.Policy}
  {capacity : Nat} {before after : Configuration capacity}

/-- An original invocation still active at the end retains its private
reservation through the entire history. Intermediate descriptor retention
follows from the monotone ledger; it is not supplied at every prefix. -/
theorem history_private_reservation
    (path : Transition.Events.Reaches (Step program policy instances flags) before ticks after)
    (invariant : Invariant instances before)
    (privateEntry : before.publications slot = some ⟨call.serial, false⟩)
    (active : before.resources.recorded.ledger.active tracked = some call)
    (stillActive : after.resources.recorded.ledger.active tracked = some call) :
    after.publications slot = some ⟨call.serial, false⟩ := by
  induction path with
  | refl => exact privateEntry
  | next first rest ih =>
    have nextInvariant := first.invariant invariant
    have suffix := Resources.history_erases (history_invariant rest nextInvariant).2.1
    have advance := (Host.Recording.history_issued
      (Transition.Events.Reaches.next first.resources.erases (.refl _))).1
    have nextActive := Host.Recording.history_retained suffix
      (Nat.lt_of_lt_of_le (invariant.fresh tracked call active) advance) stillActive
    exact ih nextInvariant (first.private_reservation invariant privateEntry active nextActive) nextActive stillActive

end Rumoca.FMI3.InstanceAuthority.Resources.Publication
