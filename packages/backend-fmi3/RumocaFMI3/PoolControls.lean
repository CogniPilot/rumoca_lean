import RumocaC.WriteInterference
import RumocaC.AtomicWriteFrames
import RumocaFMI3.InitializerProtection
import RumocaFMI3.PrivateReservations

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CCalls
variable {capacity : Nat}

/-- Destinations that cannot corrupt another private initializer: caller
objects outside this static pool, a record borrowed by this invocation, or its
invocation's own retained private reservation. This is a protection condition,
not a complete public API or caller-buffer validity specification. -/
def Writable (instances : Nat) (before : Configuration capacity) (thread : Nat)
    (address : Address) : Prop :=
  address.block ≠ instances ∨
    (∃ slot account call, before.resources.recorded.ledger.active thread = some call ∧
      before.resources.authority slot = some account ∧ account.phase.ticket = some call.serial ∧
      (AtomicSlots.address instances slot).InRecord address) ∨
    ∃ slot call, before.resources.recorded.ledger.active thread = some call ∧
      before.publications slot = some ⟨call.serial, false⟩ ∧
      (AtomicSlots.address instances slot).InRecord address

/-- Explicit importer memory boundary: host memory actions preserve the FMU's
instance pool. Buffer validity and the separate atomic-flag boundary are not
implied. No host-memory behavior is changed by defining this proposition. -/
def MemoryPolicy (policy : Host.Policy) (instances : Nat) : Prop :=
  ∀ state thread heap, policy.memory state thread heap →
    Set.EqOn state.heap heap {q | q.block = instances}

variable [CInterface] {E : Type} {program : Events.Program E}
  {before : Configuration capacity}

/-- Conditions on current selected controls, with ordinary writes computed
from the existing C machine and current foreign effects stated separately. -/
def Controls (program : Events.Program E) (instances : Nat)
    (before : Configuration capacity) : Prop :=
  ∀ thread saved, before.resources.recorded.runtime.threads thread = some saved →
    (∀ address, CWriteFootprint.current
      (Concurrent.withHeap saved before.resources.recorded.runtime.heap) = some address →
      Writable instances before thread address) ∧
    CWriteFootprint.ForeignFrame {q | ¬ Writable instances before thread q}
      program (Concurrent.withHeap saved before.resources.recorded.runtime.heap)

omit [CInterface] in
theorem writable_excludes_private (invariant : Invariant instances before)
    (active : before.resources.recorded.ledger.active tracked = some original)
    (privateEntry : before.publications slot = some ⟨original.serial, false⟩)
    (different : thread ≠ tracked)
    (inside : (AtomicSlots.address instances slot).InRecord address) :
    ¬ Writable instances before thread address := by
  rintro (outside | ⟨other, account, owner, ownerActive, owned, ticket, within⟩ | ⟨other, call, found, reserved, within⟩)
  · exact outside inside.1
  · exact private_record_separate invariant.linked privateEntry owned instances within inside rfl
  · have serials : call.serial ≠ original.serial :=
      fun same => different (invariant.unique thread call tracked original found active same).1
    exact PublicationRegistry.reserved_records_separate reserved privateEntry serials within inside rfl

/-- Current permissions discharge every internal frame for the tracked
private record. Only explicit host-memory and current external effects remain
environment obligations. -/
theorem controls_private (invariant : Invariant instances before)
    (active : before.resources.recorded.ledger.active tracked = some original)
    (privateEntry : before.publications slot = some ⟨original.serial, false⟩)
    (controls : Controls program instances before) (memory : MemoryPolicy policy instances) :
    Host.Recording.InterferenceControls {q | (AtomicSlots.address instances slot).InRecord q}
      program policy tracked original.serial before.resources.recorded := by
  intro _
  constructor
  · intro thread different saved found
    obtain ⟨writes, externalFrame⟩ := controls thread saved found
    refine ⟨?_, externalFrame.mono ?_⟩
    · intro address selected inside
      exact writable_excludes_private invariant active privateEntry different inside (writes address selected)
    · intro address inside
      exact writable_excludes_private invariant active privateEntry different inside
  · intro thread heap _ allowed query inside
    exact memory _ thread heap allowed inside.1

/-- The actual claimed-initializer invariant establishes its current write
permission and excludes foreign effects, including its saved helper return.
The original call and retained reservation identify the permitted record. -/
theorem initializer_controls
    (active : before.resources.recorded.ledger.active thread = some call)
    (reserved : before.publications slot = some ⟨call.serial, false⟩)
    (ready : StaticFactory.ClaimInitialization.Ready model kind env types
      ⟨instances, [], 0⟩ flags capacity slot.val environment logger logging reference state) :
    (∀ address, CWriteFootprint.current state = some address → Writable instances before thread address) ∧
    CWriteFootprint.ForeignFrame {q | ¬ Writable instances before thread q} program state := by
  refine ⟨?_, ready.foreign_frame⟩
  intro address selected
  refine Or.inr (Or.inr ⟨slot, call, active, reserved, ?_⟩)
  simpa only [Address.index, AtomicSlots.address, Nat.zero_add] using ready.destination selected

end Rumoca.FMI3.InstanceAuthority.Resources.Publication

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CCalls
variable [interface : CInterface] {E : Type} {capacity : Nat}
  {before : Configuration capacity}

omit interface in
/-- The real ordinary-method borrow supplies this invocation's permission;
possession of some unrelated published handle does not suffice. -/
theorem borrowed_writable
    (borrowed : Borrowing before.resources.authority before.resources.recorded.ledger thread handle instances)
    (inside : (AtomicSlots.address instances handle.slot).InRecord address) :
    Writable instances before thread address := by
  obtain ⟨call, api, tail, active, ordinary, named, args, resource⟩ := borrowed
  exact Or.inr (Or.inl ⟨handle.slot, ⟨handle.lease, .using call.serial⟩, call,
    active, resource, rfl, inside⟩)

/-- The actual atomic reservation binding has no internal memory destination,
and its external write is outside the instance pool. Parameter conversion and
the one-cell effect are discharged by the generic atomic theorem. -/
theorem exchange_controls (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_exchange" =
      some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (outside : address.block ≠ instances) :
    (∀ query, CWriteFootprint.current
      (.calling "atomic_exchange" [.pointer (some address), CAtomicBoolean.value desired] heap stack) = some query →
      Writable instances before thread query) ∧
    CWriteFootprint.ForeignFrame {q | ¬ Writable instances before thread q} program
      (.calling "atomic_exchange" [.pointer (some address), CAtomicBoolean.value desired] heap stack) := by
  refine ⟨?_, CAtomicBoolean.Calls.exchange_foreign_frame program tag boolean pointer bound ?_⟩
  · intro query selected
    simp [CWriteFootprint.current] at selected
  · exact fun forbidden => forbidden (Or.inl outside)

theorem release_controls (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (bound : program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag))
    (outside : address.block ≠ instances) :
    (∀ query, CWriteFootprint.current
      (.calling "atomic_store" [.pointer (some address), CAtomicBoolean.value desired] heap stack) = some query →
      Writable instances before thread query) ∧
    CWriteFootprint.ForeignFrame {q | ¬ Writable instances before thread q} program
      (.calling "atomic_store" [.pointer (some address), CAtomicBoolean.value desired] heap stack) := by
  refine ⟨?_, CAtomicBoolean.Calls.write_foreign_frame program tag boolean pointer bound ?_⟩
  · intro query selected
    simp [CWriteFootprint.current] at selected
  · exact fun forbidden => forbidden (Or.inl outside)

end Rumoca.FMI3.InstanceAuthority.Resources.Publication

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CCalls
variable {E : Type} {capacity : Nat} {before : Host.Recording.State}
  {authority following : InstanceAuthority.State capacity}
  {publications : PublicationRegistry.State capacity}

/-- Entering a new invocation preserves each other thread's existing write
permission. Borrowing a client resource cannot revoke another active borrow:
the client phase has no invocation ticket. -/
theorem invoke_writable_other
    (changed : Resources.Change (E := E) instances flags before chosen (.invoke name args) authority following)
    (different : thread ≠ chosen)
    (permitted : Writable instances ⟨⟨before, authority⟩, publications⟩ thread address) :
    Writable instances
      ⟨⟨⟨runtime, Host.Recording.advance (E := E) before.ledger chosen (.invoke name args)⟩, following⟩, publications⟩
      thread address := by
  rcases permitted with outside | ⟨slot, account, call, active, owned, ticket, inside⟩ |
      ⟨slot, call, active, privateEntry, inside⟩
  · exact Or.inl outside
  · have current : (Host.Recording.advance (E := E) before.ledger chosen (.invoke name args)).active thread = some call := by
      simpa only [Host.Recording.advance, Host.Recording.bind, if_neg different] using active
    have retained : following slot = some account := by
      cases changed with
      | enter matching entered =>
        rename_i access tail handle
        have client := (enter_iff.mp entered).1
        by_cases same : slot = handle.slot
        · subst slot
          have sameAccount := Option.some.inj (owned.symm.trans client)
          subst account
          simp [Phase.ticket] at ticket
        · exact (enter_other entered same).trans owned
      | unowned => exact owned
    exact Or.inr (Or.inl ⟨slot, account, call, current, retained, ticket, inside⟩)
  · exact Or.inr (Or.inr ⟨slot, call,
      by simpa only [Host.Recording.advance, Host.Recording.bind, if_neg different] using active,
      privateEntry, inside⟩)

end Rumoca.FMI3.InstanceAuthority.Resources.Publication

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CCalls
variable [CInterface] {E : Type} {program : Events.Program E}
  {capacity : Nat} {before : Configuration capacity}

/-- Actual public entry preserves all control permissions. The new call uses
an actual internal definition; other threads retain their borrowed or private
destinations. The new state is the same computed recorded/resource update. -/
theorem invoke_controls (controls : Controls program instances before)
    (defined : program.internal.definitions name = some fn)
    (actual : Host.Step program policy before.resources.recorded.runtime chosen (.invoke name args) runtime)
    (changed : Resources.Change (E := E) instances flags before.resources.recorded chosen (.invoke name args)
      before.resources.authority following) :
    Controls program instances
      ⟨⟨⟨runtime, Host.Recording.advance (E := E) before.resources.recorded.ledger chosen (.invoke name args)⟩,
        following⟩, before.publications⟩ := by
  rw [(Host.invoke_iff.mp actual).2.2]
  intro thread saved found
  by_cases same : thread = chosen
  · subst thread
    simp only [Concurrent.update, ↓reduceIte, Option.some.injEq] at found
    subst saved
    simp only [Concurrent.control, Concurrent.withHeap]
    refine ⟨?_, CWriteFootprint.internal_entry_foreign_frame defined⟩
    intro address selected
    simp [CWriteFootprint.current] at selected
  · have previous : before.resources.recorded.runtime.threads thread = some saved := by
      simpa only [Concurrent.update, if_neg same] using found
    obtain ⟨writes, frame⟩ := controls thread saved previous
    refine ⟨?_, frame.mono ?_⟩
    · intro address selected
      exact invoke_writable_other changed same (writes address selected)
    · intro address excluded permitted
      exact excluded (invoke_writable_other changed same permitted)

end Rumoca.FMI3.InstanceAuthority.Resources.Publication

namespace Rumoca.FMI3.InstanceAuthority
variable {capacity : Nat} {state : State capacity} {slot : Fin capacity}

/-- Observing one call returns only its own borrow. A different invocation's
borrow or pending release retains the exact account and generation. -/
theorem complete_preserves_ticket (owned : state slot = some account)
    (ticket : account.phase.ticket = some serial) (different : serial ≠ invocation) :
    completeUse state invocation slot = some account := by
  cases account with
  | mk lease phase =>
    cases phase <;> simp_all [Phase.ticket, completeUse]

end Rumoca.FMI3.InstanceAuthority


namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CCalls
variable {E : Type} {capacity : Nat} {before : Host.Recording.State}
  {authority following : InstanceAuthority.State capacity}
  {publications : PublicationRegistry.State capacity}

/-- Actual return observation preserves every other active invocation's
permitted destinations. Fresh ledger identities distinguish borrowed tickets;
a factory can publish only a vacant resource. Private reservations remain tied
to the still-active original call. -/
theorem complete_writable_other (unique : Host.Recording.Unique before.ledger)
    (changed : Resources.Change (E := E) instances flags before chosen (.complete value) authority following)
    (different : thread ≠ chosen)
    (permitted : Writable instances ⟨⟨before, authority⟩, publications⟩ thread address) :
    Writable instances
      ⟨⟨⟨runtime, Host.Recording.advance (E := E) before.ledger chosen (.complete value)⟩, following⟩,
        PublicationRegistry.advance (E := E) publications instances flags before chosen (.complete value)⟩
      thread address := by
  rcases permitted with outside | ⟨slot, account, call, active, owned, ticket, inside⟩ |
      ⟨slot, call, active, privateEntry, inside⟩
  · exact Or.inl outside
  · have current : (Host.Recording.advance (E := E) before.ledger chosen (.complete value)).active thread = some call := by
      simpa only [Host.Recording.advance, Host.Recording.bind, if_neg different] using active
    have retained : following slot = some account := by
      cases changed with
      | publish returning factory issued =>
        obtain ⟨vacant, rfl⟩ := publish_iff.mp issued
        rename_i completed selected
        have separate : slot ≠ selected := by
          intro same
          subst slot
          have impossible : some account = none := owned.symm.trans vacant
          contradiction
        simpa only [Function.update_of_ne separate] using owned
      | completeUse returning borrowed =>
        apply complete_preserves_ticket owned ticket
        intro same
        exact different (unique _ _ _ _ active returning same).1
      | completeUnowned => exact owned
    exact Or.inr (Or.inl ⟨slot, account, call, current, retained, ticket, inside⟩)
  · have current : (Host.Recording.advance (E := E) before.ledger chosen (.complete value)).active thread = some call := by
      simpa only [Host.Recording.advance, Host.Recording.bind, if_neg different] using active
    exact Or.inr (Or.inr ⟨slot, call, current,
      complete_keeps (E := E) unique active current privateEntry, inside⟩)

end Rumoca.FMI3.InstanceAuthority.Resources.Publication


namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CCalls
variable [CInterface] {E : Type} {program : Events.Program E}
  {capacity : Nat} {before : Configuration capacity}

/-- Observing a real halted result preserves current-control safety for all
remaining threads. Neither their saved controls nor the shared heap change,
and the computed resource/publication updates retain their permissions. -/
theorem complete_controls (controls : Controls program instances before)
    (unique : Host.Recording.Unique before.resources.recorded.ledger)
    (actual : Host.Step program policy before.resources.recorded.runtime chosen (.complete value) runtime)
    (changed : Resources.Change (E := E) instances flags before.resources.recorded chosen (.complete value)
      before.resources.authority following) :
    Controls program instances
      ⟨⟨⟨runtime, Host.Recording.advance (E := E) before.resources.recorded.ledger chosen (.complete value)⟩,
        following⟩,
        PublicationRegistry.advance (E := E) before.publications instances flags before.resources.recorded chosen (.complete value)⟩ := by
  rw [(Host.complete_iff.mp actual).2]
  intro thread saved found
  have different : thread ≠ chosen := by
    intro same
    subst thread
    simp [Host.retire] at found
  have previous : before.resources.recorded.runtime.threads thread = some saved := by
    simpa only [Host.retire, if_neg different] using found
  obtain ⟨writes, frame⟩ := controls thread saved previous
  refine ⟨?_, frame.mono ?_⟩
  · intro address selected
    exact complete_writable_other unique changed different (writes address selected)
  · intro address excluded permitted
    exact excluded (complete_writable_other unique changed different permitted)

end Rumoca.FMI3.InstanceAuthority.Resources.Publication
