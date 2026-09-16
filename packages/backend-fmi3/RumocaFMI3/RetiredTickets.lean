import RumocaFMI3.CallOriginActions

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable {capacity : Nat}

/-- No resource is held by this invocation. A released call may remain active
in its heap-independent return suffix while other calls reuse the same slot. -/
def NoTicket (state : State capacity) (serial : Nat) : Prop :=
  ∀ slot account, state slot = some account → account.phase.ticket ≠ some serial

/-- Consuming the actual releasing resource removes this invocation's only
possible ticket, using the derived argument/identity uniqueness invariant. -/
theorem cleared_no_ticket {handle : Handle capacity}
    (origins : ArgumentOrigins state ledger instances) (unique : Host.Recording.Unique ledger)
    (cleared : clear state handle invocation = some following) : NoTicket following invocation := by
  obtain ⟨releasing, rfl⟩ := clear_iff.mp cleared
  intro slot account found ticket
  by_cases same : slot = handle.slot
  · subst slot
    simp at found
  · have present : state slot = some account := by simpa [same] using found
    exact same (ticket_unique origins unique present releasing ticket rfl)

/-- Publishing another initialized handle cannot recreate a consumed ticket. -/
theorem NoTicket.publish (absent : NoTicket state serial)
    (issued : publish state handle = some following) : NoTicket following serial := by
  obtain ⟨_, rfl⟩ := publish_iff.mp issued
  intro slot account found
  by_cases same : slot = handle.slot
  · subst slot
    simp only [Function.update_self, Option.some.injEq] at found
    subst account
    simp [Phase.ticket]
  · exact absent slot account (by simpa [same] using found)

/-- A later, fresh invocation can borrow reused storage without resurrecting
an earlier invocation's resource. Freshness is supplied by the actual ledger. -/
theorem NoTicket.enter (absent : NoTicket state serial) (different : invocation ≠ serial)
    (entered : enter state handle invocation access = some following) : NoTicket following serial := by
  obtain ⟨_, rfl⟩ := enter_iff.mp entered
  intro slot account found
  by_cases same : slot = handle.slot
  · subst slot
    simp only [Function.update_self, Option.some.injEq] at found
    subst account
    cases access <;> simpa [Access.phase, Phase.ticket] using different
  · exact absent slot account (by simpa [same] using found)

theorem NoTicket.clear (absent : NoTicket state serial)
    (cleared : clear state handle invocation = some following) : NoTicket following serial := by
  obtain ⟨_, rfl⟩ := clear_iff.mp cleared
  intro slot account found
  by_cases same : slot = handle.slot
  · subst slot
    simp at found
  · exact absent slot account (by simpa [same] using found)

/-- Ordinary completion only returns resources to the client, never to a
completed or still-returning invocation. -/
theorem NoTicket.completeUse (absent : NoTicket state serial) : NoTicket (completeUse state invocation) serial := by
  intro slot account found
  cases previous : state slot with
  | none => simp [Rumoca.FMI3.InstanceAuthority.completeUse, previous] at found
  | some old =>
    rcases old with ⟨lease, phase⟩
    cases phase with
    | client =>
      simp only [Rumoca.FMI3.InstanceAuthority.completeUse, previous, Option.some.injEq] at found
      subst account
      simp [Phase.ticket]
    | releasing call =>
      simp only [Rumoca.FMI3.InstanceAuthority.completeUse, previous, Option.some.injEq] at found
      subst account
      exact absent slot _ previous
    | «using» call =>
      by_cases same : call = invocation
      · simp only [Rumoca.FMI3.InstanceAuthority.completeUse, previous, same, ↓reduceIte, Option.some.injEq] at found
        subst account
        simp [Phase.ticket]
      · simp only [Rumoca.FMI3.InstanceAuthority.completeUse, previous, if_neg same, Option.some.injEq] at found
        subst account
        exact absent slot _ previous

/-- A completion after resource consumption leaves every other API origin
intact, even when the old storage has a new client or is borrowed again. -/
theorem complete_without_ticket (origins : CallOrigins state ledger instances)
    (active : ledger.active thread = some call) (absent : NoTicket state call.serial) (value : Value) :
    CallOrigins state (Host.Recording.advance ledger thread (Host.Action.complete (E := E) value)) instances := by
  intro slot account found
  exact (origins slot account found).retire active (absent slot account found) value

/-- The nullable FreeInstance no-op cannot own any nonnull instance resource.
This uses the original argument, not a guess from current publication state. -/
theorem null_release_no_ticket (origins : CallOrigins state ledger instances) (unique : Host.Recording.Unique ledger)
    (active : ledger.active thread = some call) (named : call.name = StaticRelease.function.signature.name)
    (args : call.args = [.pointer none]) : NoTicket state call.serial := by
  intro slot account found ticket
  have original := origins slot account found
  rcases account with ⟨lease, phase⟩
  cases phase with
  | client => contradiction
  | «using» current =>
    obtain ⟨chosen, previous, api, tail, chosenActive, identity, ordinary, methodName, _⟩ := original
    have serial : previous.serial = call.serial := identity.trans (by simpa [Phase.ticket] using ticket)
    have same := (unique chosen previous thread call chosenActive active serial).2
    subst previous
    exact (PublicAPI.ordinary_signature api ordinary).2.2.1 (methodName.symm.trans named)
  | releasing current =>
    obtain ⟨chosen, previous, chosenActive, identity, _, argument⟩ := original
    have serial : previous.serial = call.serial := identity.trans (by simpa [Phase.ticket] using ticket)
    have same := (unique chosen previous thread call chosenActive active serial).2
    subst previous
    rw [args] at argument
    simp [Handle.value] at argument

end Rumoca.FMI3.InstanceAuthority
