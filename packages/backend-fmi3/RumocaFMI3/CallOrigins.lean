import RumocaFMI3.ArgumentOrigins

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable {capacity : Nat}

/-- A resource held by a call carries that call's actual API class, original
serial and erased handle argument. Client resources need no active call. -/
def CallOrigin (ledger : Host.Recording.Ledger) (instances : Nat) (slot : Fin capacity) (account : Account) : Prop :=
  match account.phase with
  | .client => True
  | .using serial =>
      ∃ thread call api tail, ledger.active thread = some call ∧ call.serial = serial ∧
        PublicAPI.Entry.ordinary api = true ∧ call.name = api.signature.name ∧
        call.args = Handle.value instances ⟨slot, account.lease⟩ :: tail
  | .releasing serial =>
      ∃ thread call, ledger.active thread = some call ∧ call.serial = serial ∧
        call.name = StaticRelease.function.signature.name ∧ call.args = [Handle.value instances ⟨slot, account.lease⟩]

def CallOrigins (state : State capacity) (ledger : Host.Recording.Ledger) (instances : Nat) : Prop :=
  ∀ slot account, state slot = some account → CallOrigin ledger instances slot account

/-- Transport an origin only by retaining the active descriptor bearing its
own ticket. Unrelated entries can change or retire without changing it. -/
theorem CallOrigin.map (origin : CallOrigin ledger instances slot account)
    (keep : ∀ thread call, ledger.active thread = some call → account.phase.ticket = some call.serial →
      following.active thread = some call) : CallOrigin following instances slot account := by
  rcases account with ⟨lease, phase⟩
  cases phase with
  | client => trivial
  | «using» serial =>
    obtain ⟨thread, call, api, tail, active, identity, ordinary, named, args⟩ := origin
    exact ⟨thread, call, api, tail, keep thread call active (by simpa [Phase.ticket] using congrArg some identity.symm),
      identity, ordinary, named, args⟩
  | releasing serial =>
    obtain ⟨thread, call, active, identity, named, args⟩ := origin
    exact ⟨thread, call, keep thread call active (by simpa [Phase.ticket] using congrArg some identity.symm), identity, named, args⟩

/-- The stronger API correspondence supplies the already checked argument
invariant used by ordinary completion and single-slot ticket uniqueness. -/
theorem CallOrigins.arguments (origins : CallOrigins state ledger instances) : ArgumentOrigins state ledger instances := by
  intro slot account serial found ticket
  have original := origins slot account found
  rcases account with ⟨lease, phase⟩
  cases phase with
  | client => contradiction
  | «using» current =>
    have same : current = serial := by simpa [Phase.ticket] using ticket
    subst current
    obtain ⟨thread, call, api, tail, active, identity, _, _, args⟩ := original
    exact ⟨thread, call, tail, active, identity, args⟩
  | releasing current =>
    have same : current = serial := by simpa [Phase.ticket] using ticket
    subst current
    obtain ⟨thread, call, active, identity, _, args⟩ := original
    exact ⟨thread, call, [], active, identity, args⟩

/-- A factory invocation cannot be the ordinary-use or release ticket of an
existing resource. This follows from actual API names, not pointer identity. -/
theorem factory_no_ticket (origins : CallOrigins state ledger instances) (unique : Host.Recording.Unique ledger)
    (active : ledger.active thread = some call) (factory : ReservationOrigin.factory call.name)
    (present : state slot = some account) : account.phase.ticket ≠ some call.serial := by
  intro ticket
  have original := origins slot account present
  rcases account with ⟨lease, phase⟩
  cases phase with
  | client => contradiction
  | «using» current =>
    obtain ⟨chosen, previous, api, tail, chosenActive, identity, ordinary, named, _⟩ := original
    have serial : previous.serial = call.serial := identity.trans (by simpa [Phase.ticket] using ticket)
    have same := (unique chosen previous thread call chosenActive active serial).2
    subst previous
    exact (PublicAPI.ordinary_signature api ordinary).2.2.2 (named ▸ factory)
  | releasing current =>
    obtain ⟨chosen, previous, chosenActive, identity, named, _⟩ := original
    have serial : previous.serial = call.serial := identity.trans (by simpa [Phase.ticket] using ticket)
    have same := (unique chosen previous thread call chosenActive active serial).2
    subst previous
    rw [named] at factory
    simp [ReservationOrigin.factory, StaticRelease.function] at factory

/-- Retiring a different ticket preserves the descriptor needed by this
resource's API correspondence. -/
theorem CallOrigin.retire (origin : CallOrigin ledger instances slot account)
    (active : ledger.active thread = some call) (different : account.phase.ticket ≠ some call.serial)
    (value : Value) :
    CallOrigin (Host.Recording.advance ledger thread (Host.Action.complete (E := E) value)) instances slot account := by
  apply origin.map
  intro chosen previous chosenActive ticket
  have distinct : chosen ≠ thread := by
    intro same
    subst chosen
    have sameCall := Option.some.inj (chosenActive.symm.trans active)
    subst previous
    exact different ticket
  simpa [Host.Recording.advance, Host.Recording.bind, distinct] using chosenActive

/-- Issuing a resource for a private factory result cannot orphan any active
method or release while the factory descriptor is retired. -/
theorem publish_call_origins (origins : CallOrigins state ledger instances) (unique : Host.Recording.Unique ledger)
    (active : ledger.active thread = some call) (factory : ReservationOrigin.factory call.name)
    (issued : publish state handle = some following) (value : Value) :
    CallOrigins following (Host.Recording.advance ledger thread (Host.Action.complete (E := E) value)) instances := by
  obtain ⟨_, rfl⟩ := publish_iff.mp issued
  intro slot account found
  by_cases same : slot = handle.slot
  · subst slot
    simp only [Function.update_self, Option.some.injEq] at found
    subst account
    trivial
  · have present : state slot = some account := by simpa [same] using found
    exact (origins slot account present).retire active (factory_no_ticket origins unique active factory present) value

/-- Clearing a releasing resource changes neither the recorded invocation nor
any other resource's origin. The old release may still finish independently. -/
theorem clear_call_origins (origins : CallOrigins state ledger instances)
    (cleared : clear state handle serial = some following) : CallOrigins following ledger instances := by
  obtain ⟨_, rfl⟩ := clear_iff.mp cleared
  intro slot account found
  by_cases same : slot = handle.slot
  · subst slot
    simp at found
  · exact origins slot account (by simpa [same] using found)

end Rumoca.FMI3.InstanceAuthority
