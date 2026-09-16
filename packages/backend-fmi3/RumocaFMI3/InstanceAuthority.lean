import RumocaFMI3.PublicationTransitions
import RumocaFMI3.PublicationMemory
import RumocaFMI3.StaticReleaseCode

namespace Rumoca.FMI3.InstanceAuthority
open CMemory CCalls

structure Handle (capacity : Nat) where
  slot : Fin capacity
  lease : Nat
  deriving DecidableEq

def Handle.value (instances : Nat) (handle : Handle capacity) : Value :=
  .pointer (some (AtomicSlots.address instances handle.slot))

inductive Access where
  | use
  | release
  deriving DecidableEq

inductive Phase where
  | client
  | using (invocation : Nat)
  | releasing (invocation : Nat)
  deriving DecidableEq

structure Account where
  lease : Nat
  phase : Phase
  deriving DecidableEq

abbrev State (capacity : Nat) := Fin capacity → Option Account

def Owns (state : State capacity) (handle : Handle capacity) : Prop :=
  state handle.slot = some ⟨handle.lease, .client⟩

instance (state : State capacity) (handle : Handle capacity) : Decidable (Owns state handle) :=
  inferInstanceAs (Decidable (state handle.slot = some ⟨handle.lease, .client⟩))

def Access.phase (access : Access) (invocation : Nat) : Phase :=
  match access with | .use => .using invocation | .release => .releasing invocation

/-- Issue authority only when the surrounding actual factory-completion rule
has produced this logical handle. The physical publication link is separate. -/
def publish (state : State capacity) (handle : Handle capacity) : Option (State capacity) :=
  if state handle.slot = none then
    some (Function.update state handle.slot (some ⟨handle.lease, .client⟩)) else none

/-- Temporarily remove client authority for an ordinary call, or consume it
for release. The invocation number is the recorded original public entry. -/
def enter (state : State capacity) (handle : Handle capacity) (invocation : Nat) (access : Access) :
    Option (State capacity) :=
  if Owns state handle then
    some (Function.update state handle.slot (some ⟨handle.lease, access.phase invocation⟩)) else none

/-- An authorized actual clear consumes the releasing account immediately.
The old void-return suffix then holds no slot resource that could block reuse. -/
def clear (state : State capacity) (handle : Handle capacity) (invocation : Nat) : Option (State capacity) :=
  if state handle.slot = some ⟨handle.lease, .releasing invocation⟩ then
    some (Function.update state handle.slot none) else none

/-- Completing an ordinary call returns only its own borrowed authority.
This operation is not used for a FreeInstance completion. -/
def completeUse (state : State capacity) (invocation : Nat) : State capacity :=
  fun slot => match state slot with
  | some ⟨lease, .using current⟩ =>
      if current = invocation then some ⟨lease, .client⟩ else state slot
  | _ => state slot

/-- Every available, borrowed or releasing resource names a currently
published reservation. This alone does not create any client resource. -/
def Linked (state : State capacity) (published : PublicationRegistry.State capacity) : Prop :=
  ∀ slot account, state slot = some account → PublicationRegistry.Published published slot account.lease

theorem publish_iff : publish state handle = some after ↔
    state handle.slot = none ∧ after = Function.update state handle.slot (some ⟨handle.lease, .client⟩) := by
  by_cases vacant : state handle.slot = none <;> simp [publish, vacant, eq_comm]

theorem enter_iff : enter state handle invocation access = some after ↔
    Owns state handle ∧ after = Function.update state handle.slot (some ⟨handle.lease, access.phase invocation⟩) := by
  by_cases owns : Owns state handle <;> simp [enter, owns, eq_comm]

theorem clear_iff : clear state handle invocation = some after ↔
    state handle.slot = some ⟨handle.lease, .releasing invocation⟩ ∧
      after = Function.update state handle.slot none := by
  by_cases releasing : state handle.slot = some ⟨handle.lease, .releasing invocation⟩ <;>
    simp [clear, releasing, eq_comm]

theorem published_owns (step : publish state handle = some after) : Owns after handle := by
  rw [(publish_iff.mp step).2]
  simp [Owns]

/-- Copies of the same logical handle cannot start overlapping uses of this
instance. Other slots remain available independently. -/
theorem entered_excludes (step : enter state handle invocation access = some after)
    (lease call : Nat) (otherAccess : Access) :
    enter after ⟨handle.slot, lease⟩ call otherAccess = none := by
  rw [(enter_iff.mp step).2]
  cases access <;> simp [enter, Owns, Access.phase]

theorem enter_other (step : enter state handle invocation access = some after)
    (different : slot ≠ handle.slot) : after slot = state slot := by
  rw [(enter_iff.mp step).2]
  simp [different]

/-- Equal native pointer bits do not equate logical generations. -/
theorem stale_rejected (present : state handle.slot = some account) (stale : handle.lease ≠ account.lease)
    (invocation : Nat) (access : Access) : enter state handle invocation access = none := by
  have notOwned : ¬ Owns state handle := by
    intro owned
    have same : account = ⟨handle.lease, .client⟩ := Option.some.inj (present.symm.trans owned)
    exact stale (congrArg Account.lease same).symm
  simp [enter, notOwned]

theorem handle_erasure (slot : Fin capacity) (old new instances : Nat) :
    Handle.value instances ⟨slot, old⟩ = Handle.value instances ⟨slot, new⟩ := rfl

theorem clear_vacant (step : clear state handle invocation = some after) : after handle.slot = none := by
  rw [(clear_iff.mp step).2]
  simp

theorem complete_owned (borrowed : state handle.slot = some ⟨handle.lease, .using invocation⟩) :
    Owns (completeUse state invocation) handle := by
  simp [Owns, completeUse, borrowed]

theorem complete_other_call (borrowed : state slot = some ⟨lease, .using current⟩)
    (different : current ≠ invocation) : completeUse state invocation slot = state slot := by
  simp [completeUse, borrowed, different]

theorem complete_releasing (releasing : state slot = some ⟨lease, .releasing current⟩) :
    completeUse state invocation slot = state slot := by simp [completeUse, releasing]

theorem enter_linked (linked : Linked state published) (step : enter state handle invocation access = some after) :
    Linked after published := by
  obtain ⟨owns, rfl⟩ := enter_iff.mp step
  intro slot account found
  by_cases same : slot = handle.slot
  · subst slot
    simp only [Function.update_self, Option.some.injEq] at found
    subst account
    exact linked handle.slot ⟨handle.lease, .client⟩ owns
  · exact linked _ _ (by simpa [same] using found)

theorem complete_linked (linked : Linked state published) : Linked (completeUse state invocation) published := by
  intro slot account found
  unfold completeUse at found
  split at found
  next lease current borrowed =>
    split at found
    next =>
      cases Option.some.inj found
      exact linked slot ⟨lease, .using current⟩ borrowed
    next => exact linked _ _ found
  next => exact linked _ _ found


/-- Issuing a logical handle is linked to publication of that same factory
lease. No authority for another slot changes. -/
theorem publish_linked (linked : Linked state published)
    (owned : published handle.slot = some ⟨handle.lease, previous⟩)
    (step : publish state handle = some after) :
    Linked after (PublicationRegistry.publish published handle.slot handle.lease) := by
  obtain ⟨_, rfl⟩ := publish_iff.mp step
  intro slot account found
  by_cases same : slot = handle.slot
  · subst slot
    simp only [Function.update_self, Option.some.injEq] at found
    subst account
    exact PublicationRegistry.publish_owned owned
  · have earlier := linked slot account (by simpa [same] using found)
    simpa [PublicationRegistry.Published, PublicationRegistry.publish, same] using earlier

/-- The caller resource supplies the physical lease needed by the existing
release semantics. Publication alone is never used to mint this resource. -/
theorem releasing_reservation {handle : Handle capacity} (linked : Linked state published)
    (releasing : state handle.slot = some ⟨handle.lease, .releasing invocation⟩) :
    PublicationRegistry.reservations published handle.slot = some handle.lease :=
  PublicationRegistry.published_reservation (linked _ _ releasing)

/-- A real clear removes exactly its releasing resource, keeping all other
resources linked to their unchanged publications. -/
theorem clear_linked (linked : Linked state published)
    (step : clear state handle invocation = some after) :
    Linked after (PublicationRegistry.synchronize published
      (SlotOwners.update (PublicationRegistry.reservations published) handle.slot none)) := by
  obtain ⟨_, rfl⟩ := clear_iff.mp step
  rw [PublicationRegistry.synchronize_clear]
  intro slot account found
  by_cases same : slot = handle.slot
  · subst slot
    simp at found
  · have earlier := linked slot account (by simpa [same] using found)
    simpa [PublicationRegistry.Published, same] using earlier

/-- Completing a different call leaves even a newly reused client resource
unchanged. The release completion rule itself never runs completeUse. -/
theorem complete_client (client : state slot = some ⟨lease, .client⟩) :
    completeUse state invocation slot = state slot := by simp [completeUse, client]


/-- A release permission belongs to the original public invocation with the
exact erased handle. Matching a raw pointer to the current publication does
not supply this premise. -/
def Releasing (state : State capacity) (ledger : Host.Recording.Ledger)
    (thread : Nat) (handle : Handle capacity) (instances : Nat) : Prop :=
  ∃ call, ledger.active thread = some call ∧
    call.name = StaticRelease.function.signature.name ∧
    call.args = [handle.value instances] ∧
    state handle.slot = some ⟨handle.lease, .releasing call.serial⟩

/-- An unpublished reservation cannot carry importer authority. -/
theorem private_vacant (linked : Linked state published)
    (privateEntry : published slot = some ⟨lease, false⟩) : state slot = none := by
  cases present : state slot with
  | none => rfl
  | some account =>
    have observed := linked slot account present
    simp [PublicationRegistry.Published, privateEntry] at observed

end Rumoca.FMI3.InstanceAuthority
