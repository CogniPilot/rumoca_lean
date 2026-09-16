import RumocaFMI3.MethodAuthority

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable {capacity : Nat}

/-- There are initially no borrowed resources needing an argument origin. -/
theorem empty_argument_origins (ledger : Host.Recording.Ledger) (instances : Nat) :
    ArgumentOrigins (fun _ : Fin capacity => none) ledger instances := by
  intro slot account serial found
  contradiction

/-- Borrowing/release entry installs the actual first argument under the next
recorded serial. Ledger idleness prevents overwriting another active origin. -/
theorem enter_argument_origins {handle : Handle capacity}
    (origins : ArgumentOrigins state ledger instances) (idle : ledger.active thread = none)
    (step : enter state handle ledger.next access = some following) (name : String) (tail : List Value) :
    ArgumentOrigins following
      (Host.Recording.advance ledger thread (Host.Action.invoke (E := E) name (handle.value instances :: tail))) instances := by
  obtain ⟨_, rfl⟩ := enter_iff.mp step
  intro slot account serial found ticket
  by_cases same : slot = handle.slot
  · subst slot
    simp only [Function.update_self, Option.some.injEq] at found
    subst account
    have identity : ledger.next = serial := by cases access <;> simpa [Access.phase, Phase.ticket] using ticket
    subst serial
    exact ⟨thread, ⟨ledger.next, name, handle.value instances :: tail⟩, tail,
      by simp [Host.Recording.advance, Host.Recording.bind], rfl, rfl⟩
  · have old : state slot = some account := by simpa [same] using found
    obtain ⟨chosen, call, args, active, identity, original⟩ := origins slot account serial old ticket
    have different : chosen ≠ thread := by
      intro equality
      subst chosen
      rw [idle] at active
      contradiction
    exact ⟨chosen, call, args, by simpa [Host.Recording.advance, Host.Recording.bind, different] using active,
      identity, original⟩

/-- Actual method completion can retire its invocation descriptor without
orphaning another borrowed resource. Uniqueness derives from recorded call
identity and instance arguments, not an arbitrary ownership-map annotation. -/
theorem complete_argument_origins {handle : Handle capacity}
    (origins : ArgumentOrigins state ledger instances) (unique : Host.Recording.Unique ledger)
    (active : ledger.active thread = some call)
    (borrowed : state handle.slot = some ⟨handle.lease, .using call.serial⟩) (value : Value) :
    ArgumentOrigins (completeUse state call.serial)
      (Host.Recording.advance ledger thread (Host.Action.complete (E := E) value)) instances := by
  intro slot account serial found ticket
  have retained : ∀ account, state slot = some account → account.phase.ticket = some serial → serial ≠ call.serial →
      ∃ chosen original tail,
        (Host.Recording.advance ledger thread (Host.Action.complete (E := E) value)).active chosen = some original ∧
        original.serial = serial ∧ original.args = .pointer (some (AtomicSlots.address instances slot)) :: tail := by
    intro previous present previousTicket differentSerial
    obtain ⟨chosen, original, tail, chosenActive, identity, args⟩ := origins slot previous serial present previousTicket
    have differentThread : chosen ≠ thread := by
      intro same
      subst chosen
      have sameCall := Option.some.inj (chosenActive.symm.trans active)
      exact differentSerial (identity.symm.trans (congrArg Host.Recording.Invocation.serial sameCall))
    exact ⟨chosen, original, tail,
      by simpa [Host.Recording.advance, Host.Recording.bind, differentThread] using chosenActive, identity, args⟩
  cases original : state slot with
  | none => simp [completeUse, original] at found
  | some previous =>
    rcases previous with ⟨lease, phase⟩
    cases phase with
    | client =>
      simp only [completeUse, original, Option.some.injEq] at found
      subst account
      contradiction
    | «using» current =>
      by_cases same : current = call.serial
      · simp only [completeUse, original, same, ↓reduceIte, Option.some.injEq] at found
        subst account
        contradiction
      · simp only [completeUse, original, if_neg same, Option.some.injEq] at found
        subst account
        have identity : current = serial := by simpa [Phase.ticket] using ticket
        exact retained _ original ticket (identity ▸ same)
    | releasing current =>
      simp only [completeUse, original, Option.some.injEq] at found
      subst account
      have identity : current = serial := by simpa [Phase.ticket] using ticket
      have different : serial ≠ call.serial := by
        intro same
        have slots := ticket_unique origins unique original borrowed (same ▸ ticket) rfl
        subst slot
        have accounts := Option.some.inj (original.symm.trans borrowed)
        cases accounts
      exact retained _ original ticket different

end Rumoca.FMI3.InstanceAuthority
