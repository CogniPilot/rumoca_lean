import RumocaFMI3.CallOrigins

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable {capacity : Nat}

/-- Relate resource access mode to the actual public name and argument tail.
An arbitrary function name cannot select its own ownership rule. -/
def Access.Matches (access : Access) (name : String) (tail : List Value) : Prop :=
  match access with
  | .use => ∃ api : PublicAPI.Entry, api.ordinary = true ∧ name = api.signature.name
  | .release => name = StaticRelease.function.signature.name ∧ tail = []

theorem empty_call_origins (ledger : Host.Recording.Ledger) (instances : Nat) :
    CallOrigins (fun _ : Fin capacity => none) ledger instances := by
  intro slot account found
  contradiction

/-- Actual classified entry supplies the new API origin, while the idle
thread condition protects every earlier invocation descriptor. -/
theorem enter_call_origins {handle : Handle capacity}
    (origins : CallOrigins state ledger instances) (idle : ledger.active thread = none)
    (entered : enter state handle ledger.next access = some following)
    (matched : access.Matches name tail) :
    CallOrigins following
      (Host.Recording.advance ledger thread (Host.Action.invoke (E := E) name (handle.value instances :: tail))) instances := by
  obtain ⟨_, rfl⟩ := enter_iff.mp entered
  intro slot account found
  by_cases same : slot = handle.slot
  · subst slot
    simp only [Function.update_self, Option.some.injEq] at found
    subst account
    cases access with
    | use =>
      obtain ⟨api, ordinary, named⟩ := matched
      exact ⟨thread, ⟨ledger.next, name, handle.value instances :: tail⟩, api, tail,
        by simp [Host.Recording.advance, Host.Recording.bind], rfl, ordinary, named, rfl⟩
    | release =>
      obtain ⟨named, rfl⟩ := matched
      exact ⟨thread, ⟨ledger.next, name, [handle.value instances]⟩,
        by simp [Host.Recording.advance, Host.Recording.bind], rfl, named, rfl⟩
  · have present : state slot = some account := by simpa [same] using found
    apply (origins slot account present).map
    intro chosen call active _
    have different : chosen ≠ thread := by
      intro equality
      subst chosen
      rw [idle] at active
      contradiction
    simpa [Host.Recording.advance, Host.Recording.bind, different] using active

/-- Returning the ordinary call's resource preserves full API and argument
origins for every other active resource as its own descriptor is retired. -/
theorem complete_call_origins {handle : Handle capacity}
    (origins : CallOrigins state ledger instances) (unique : Host.Recording.Unique ledger)
    (active : ledger.active thread = some call)
    (borrowed : state handle.slot = some ⟨handle.lease, .using call.serial⟩) (value : Value) :
    CallOrigins (completeUse state call.serial)
      (Host.Recording.advance ledger thread (Host.Action.complete (E := E) value)) instances := by
  intro slot account found
  by_cases same : slot = handle.slot
  · subst slot
    have returned : completeUse state call.serial handle.slot = some ⟨handle.lease, .client⟩ := complete_owned borrowed
    cases Option.some.inj (found.symm.trans returned)
    trivial
  · have unchanged := complete_frame origins.arguments unique borrowed same
    have present : state slot = some account := unchanged ▸ found
    have different : account.phase.ticket ≠ some call.serial := by
      intro ticket
      exact same (ticket_unique origins.arguments unique present borrowed ticket rfl)
    exact (origins slot account present).retire active different value

end Rumoca.FMI3.InstanceAuthority
