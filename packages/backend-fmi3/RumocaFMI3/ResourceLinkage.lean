import RumocaFMI3.ResourceHistory

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable {capacity : Nat}

/-- An exchange can create a private reservation only in a vacant slot;
it cannot replace a published reservation carrying an existing resource. -/
theorem Linked.claim (linked : Linked authority publications) (slot : Fin capacity) (serial : Nat) :
    Linked authority (PublicationRegistry.synchronize publications
      (ConcurrentSlots.claimOwners (PublicationRegistry.reservations publications) slot serial)) := by
  cases present : publications slot with
  | some entry =>
    rw [PublicationRegistry.synchronize_claim_busy present]
    exact linked
  | none =>
    rw [PublicationRegistry.synchronize_claim_free present]
    intro other account found
    have old := linked other account found
    have different : other ≠ slot := by
      intro same
      subst other
      simp [PublicationRegistry.Published, present] at old
    simpa only [PublicationRegistry.Published, if_neg different] using old

/-- Actual-control reservation bookkeeping preserves resource linkage on
every execute step other than a clear, including a successful or busy claim. -/
theorem Linked.execute (linked : Linked authority publications)
    (notClear : ¬ ReservationRegistry.AtCall before.runtime thread "atomic_store") :
    Linked authority (PublicationRegistry.synchronize publications
      (ReservationRegistry.executeUpdate (PublicationRegistry.reservations publications) flags before thread)) := by
  unfold ReservationRegistry.executeUpdate
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
        next slot call decoded active => exact linked.claim slot call.serial
        next => simpa only [PublicationRegistry.synchronize_reservations] using linked
      next => simpa only [PublicationRegistry.synchronize_reservations] using linked
    next => simpa only [if_neg nonclear, PublicationRegistry.synchronize_reservations] using linked
  next => simpa only [PublicationRegistry.synchronize_reservations] using linked

/-- A current use ticket determines the exact original ordinary invocation;
its API classification is derived, not assumed again at completion. -/
theorem borrowing_from_origins (origins : CallOrigins authority ledger instances)
    (unique : Host.Recording.Unique ledger) (active : ledger.active thread = some call)
    {handle : Handle capacity}
    (borrowed : authority handle.slot = some ⟨handle.lease, .using call.serial⟩) :
    Borrowing authority ledger thread handle instances := by
  obtain ⟨chosen, original, api, tail, originalActive, serial, ordinary, name, args⟩ :=
    origins handle.slot ⟨handle.lease, .using call.serial⟩ borrowed
  have identity := (unique chosen original thread call originalActive active serial).2
  subst original
  exact ⟨call, api, tail, active, ordinary, name, args, borrowed⟩

/-- A non-factory completion, or a null factory result, has no publication
effect regardless of its native return type. -/
theorem unowned_observation (active : ledger.active thread = some call)
    (unowned : ¬ ReservationOrigin.factory call.name ∨ value = .pointer none) :
    PublicationRegistry.observe publications instances ledger thread value = publications := by
  rcases unowned with notFactory | rfl
  · cases value with
    | pointer address => cases address <;> simp [PublicationRegistry.observe, active, notFactory]
    | _ => rfl
  · rfl

namespace Resources

/-- A successful factory observation must still own its private reservation.
Initializer/history proofs establish this boundary; no linked map is assumed
after a step and no other action needs a reservation-retention annotation. -/
def FactoryResult (publications : PublicationRegistry.State capacity)
    (before : Host.Recording.State) (thread instances : Nat) (action : Host.Action E) : Prop :=
  ∀ call (slot : Fin capacity), before.ledger.active thread = some call →
    ReservationOrigin.factory call.name → action = .complete (Handle.value instances ⟨slot, call.serial⟩) →
    publications slot = some ⟨call.serial, false⟩

theorem Change.linked (change : Change instances flags before thread action authority following)
    (linked : Linked authority publications)
    (origins : CallOrigins authority before.ledger instances)
    (unique : Host.Recording.Unique before.ledger)
    (factoryResult : FactoryResult publications before thread instances action) :
    Linked following (PublicationRegistry.advance publications instances flags before thread action) := by
  cases change with
  | enter matching entered => exact enter_linked linked entered
  | unowned => exact linked
  | execute notClear => exact linked.execute notClear
  | clear active name args calling cleared =>
    have related := clear_linked linked cleared
    rw [PublicationRegistry.synchronize_clear] at related
    rw [PublicationRegistry.advance_clear _ _ _ _ _ _ _ calling]
    exact related
  | publish active factory issued =>
    have privateEntry := factoryResult _ _ active factory rfl
    have related := publish_linked linked privateEntry issued
    simpa only [PublicationRegistry.advance, PublicationRegistry.observe, Handle.value, active,
      if_pos factory, ReservationRegistry.slotAt_address] using related
  | completeUse active borrowed =>
    obtain ⟨call, api, tail, originalActive, ordinary, name, args, own⟩ :=
      borrowing_from_origins origins unique active borrowed
    simp only [PublicationRegistry.advance]
    rw [method_observation originalActive ordinary name]
    exact complete_linked linked
  | completeUnowned active absent notFactory =>
    simpa only [PublicationRegistry.advance, unowned_observation active notFactory] using linked
  | memory => exact linked

end Resources

end Rumoca.FMI3.InstanceAuthority
