import RumocaFMI3.RetiredTickets

namespace Rumoca.FMI3.InstanceAuthority
open CTree CMemory CCalls
variable {capacity : Nat}

/-- Adding an idle invocation without borrowing a resource preserves the
original descriptors of every outstanding borrow and release. -/
theorem idle_call_origins (origins : CallOrigins state ledger instances)
    (idle : ledger.active thread = none) (name : String) (args : List Value) :
    CallOrigins state (Host.Recording.advance (E := E) ledger thread (.invoke name args)) instances := by
  intro slot account present
  apply (origins slot account present).map
  intro chosen call active _
  have different : chosen ≠ thread := by
    intro same
    subst chosen
    rw [idle] at active
    contradiction
  simpa [Host.Recording.advance, Host.Recording.bind, different] using active

namespace Resources

structure Configuration (capacity : Nat) where
  recorded : Host.Recording.State
  authority : State capacity

/-- Resource effects are tied to actual recorded actions. Only entry borrows
a resource, using the ledger's next serial. Successful factory observation
uses that factory's original serial. Clear uses the original release and the
actual pending atomic operands. This relation specifies resource accounting;
storage frames and publication retention remain separate proof obligations. -/
inductive Change (instances flags : Nat) (before : Host.Recording.State)
    (thread : Nat) : Host.Action E → State capacity → State capacity → Prop where
  | enter (matching : Access.Matches access name tail)
      (entered : InstanceAuthority.enter authority handle before.ledger.next access = some following) :
      Change instances flags before thread (.invoke name (handle.value instances :: tail)) authority following
  | unowned (api : PublicAPI.Entry) (ordinary : api.ordinary = false)
      (admitted : api.signature.name ≠ StaticRelease.function.signature.name ∨ args = [.pointer none]) :
      Change instances flags before thread (.invoke api.signature.name args) authority authority
  | execute (notClear : ¬ ReservationRegistry.AtCall before.runtime thread "atomic_store") :
      Change instances flags before thread (.execute events) authority authority
  | clear (active : before.ledger.active thread = some call)
      (name : call.name = StaticRelease.function.signature.name)
      (args : call.args = [handle.value instances])
      (calling : before.runtime.threads thread = some (.calling "atomic_store"
        [.pointer (some (AtomicSlots.address flags handle.slot)), CAtomicBoolean.value false] heap stack))
      (cleared : InstanceAuthority.clear authority handle call.serial = some following) :
      Change instances flags before thread (.execute events) authority following
  | publish (active : before.ledger.active thread = some call)
      (factory : ReservationOrigin.factory call.name)
      (issued : InstanceAuthority.publish authority ⟨slot, call.serial⟩ = some following) :
      Change instances flags before thread
        (.complete (Handle.value instances ⟨slot, call.serial⟩)) authority following
  | completeUse {handle : Handle capacity} (active : before.ledger.active thread = some call)
      (borrowed : authority handle.slot = some ⟨handle.lease, .using call.serial⟩) :
      Change instances flags before thread (.complete value) authority (InstanceAuthority.completeUse authority call.serial)
  | completeUnowned (active : before.ledger.active thread = some call)
      (absent : NoTicket authority call.serial)
      (notSuccessfulFactory : ¬ ReservationOrigin.factory call.name ∨ value = .pointer none) :
      Change instances flags before thread (.complete value) authority authority
  | memory : Change instances flags before thread .memory authority authority

/-- The actual host transition supplies the action and next runtime. The
ledger is computed, not a per-step annotation supplied by the importer. -/
inductive Step [CInterface] (program : Events.Program E) (policy : Host.Policy) (instances flags : Nat) :
    Configuration capacity → List (Host.Recording.Tick E) → Configuration capacity → Prop where
  | record (actual : Host.Step program policy before.runtime thread action after)
      (changed : Change instances flags before thread action authority following) :
      Step program policy instances flags ⟨before, authority⟩ [Host.Recording.stamp before.ledger thread action]
        ⟨⟨after, Host.Recording.advance before.ledger thread action⟩, following⟩

variable [CInterface] {E : Type} {program : Events.Program E} {policy : Host.Policy}
  {before after : Configuration capacity}

theorem Step.erases (step : Step program policy instances flags before ticks after) :
    Host.Recording.Step program policy before.recorded ticks after.recorded := by
  cases step with
  | record actual changed => exact .record actual

/-- Resource bookkeeping never replaces or weakens an actual C/host step. -/
theorem history_erases
    (path : Transition.Events.Reaches (Step program policy instances flags) before ticks after) :
    Transition.Events.Reaches (Host.Recording.Step program policy) before.recorded ticks after.recorded := by
  induction path with
  | refl => exact .refl _
  | next first rest ih => exact .next first.erases ih

/-- Strong API origins follow every admitted resource update on the same
recorded history. No origin map is supplied for later states. -/
theorem step_origins (step : Step program policy instances flags before ticks after)
    (origins : CallOrigins before.authority before.recorded.ledger instances)
    (aligned : Host.Recording.Aligned before.recorded.runtime before.recorded.ledger)
    (unique : Host.Recording.Unique before.recorded.ledger) :
    CallOrigins after.authority after.recorded.ledger instances := by
  cases step with
  | record actual changed =>
    cases changed with
    | enter matching entered =>
      exact enter_call_origins (E := E) origins ((aligned _).mp (Host.invoke_iff.mp actual).1) entered matching
    | unowned api ordinary admitted =>
      exact idle_call_origins (E := E) origins ((aligned _).mp (Host.invoke_iff.mp actual).1) _ _
    | execute notClear => exact origins
    | clear active name args calling cleared => exact clear_call_origins origins cleared
    | publish active factory issued => exact publish_call_origins (E := E) origins unique active factory issued .void
    | completeUse active borrowed => exact complete_call_origins (E := E) origins unique active borrowed .void
    | completeUnowned active absent notSuccessfulFactory => exact complete_without_ticket (E := E) origins active absent .void
    | memory => exact origins

/-- Once a call's ticket is absent, no later fresh entry, factory publication,
clear or method completion can recreate it. The strict bound refers to the
computed next counter, including after the original thread has been reused. -/
theorem step_retired (step : Step program policy instances flags before ticks after)
    (absent : NoTicket before.authority serial) (earlier : serial < before.recorded.ledger.next) :
    NoTicket after.authority serial ∧ serial < after.recorded.ledger.next := by
  cases step with
  | record actual changed =>
    dsimp only at earlier
    cases changed with
    | enter matching entered =>
      exact ⟨absent.enter (by omega) entered, Nat.lt_trans earlier (Nat.lt_succ_self _)⟩
    | unowned => exact ⟨absent, Nat.lt_trans earlier (Nat.lt_succ_self _)⟩
    | execute => exact ⟨absent, earlier⟩
    | clear active name args calling cleared => exact ⟨absent.clear cleared, earlier⟩
    | publish active factory issued => exact ⟨absent.publish issued, earlier⟩
    | completeUse => exact ⟨absent.completeUse, earlier⟩
    | completeUnowned => exact ⟨absent, earlier⟩
    | memory => exact ⟨absent, earlier⟩

theorem history_retired
    (path : Transition.Events.Reaches (Step program policy instances flags) before ticks after)
    (absent : NoTicket before.authority serial) (earlier : serial < before.recorded.ledger.next) :
    NoTicket after.authority serial ∧ serial < after.recorded.ledger.next := by
  induction path with
  | refl => exact ⟨absent, earlier⟩
  | next first rest ih =>
    obtain ⟨absent, earlier⟩ := step_retired first absent earlier
    exact ih absent earlier

theorem history_origins
    (path : Transition.Events.Reaches (Step program policy instances flags) before ticks after)
    (origins : CallOrigins before.authority before.recorded.ledger instances)
    (aligned : Host.Recording.Aligned before.recorded.runtime before.recorded.ledger)
    (fresh : Host.Recording.Fresh before.recorded.ledger)
    (unique : Host.Recording.Unique before.recorded.ledger) :
    CallOrigins after.authority after.recorded.ledger instances ∧
    Host.Recording.Aligned after.recorded.runtime after.recorded.ledger ∧
    Host.Recording.Fresh after.recorded.ledger ∧ Host.Recording.Unique after.recorded.ledger := by
  induction path with
  | refl => exact ⟨origins, aligned, fresh, unique⟩
  | next first rest ih =>
    have nextOrigins := step_origins first origins aligned unique
    cases first with
    | record actual changed =>
      exact ih nextOrigins (Host.Recording.step_aligned aligned actual)
        (Host.Recording.advance_fresh fresh _ _) (Host.Recording.advance_unique unique fresh _ _)

end Resources

end Rumoca.FMI3.InstanceAuthority
