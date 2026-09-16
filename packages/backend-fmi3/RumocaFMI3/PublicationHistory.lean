import RumocaFMI3.PublicationActions

noncomputable section
namespace Rumoca.FMI3.PublicationRegistry
open CTree CMemory CCalls

structure Configuration (capacity : Nat) where
  recorded : Host.Recording.State
  publications : State capacity

def Configuration.reservationState (state : Configuration capacity) : ReservationRegistry.Configuration capacity :=
  ⟨state.recorded, reservations state.publications⟩

/-- Add only computed publication bookkeeping to the same actual host step. -/
inductive Step [CInterface] (program : Events.Program E) (policy : Host.Policy) (instances flags : Nat) :
    Configuration capacity → List (Host.Recording.Tick E) → Configuration capacity → Prop where
  | record (actual : Host.Step program policy before thread action after) :
      Step program policy instances flags ⟨⟨before, ledger⟩, publications⟩
        [Host.Recording.stamp ledger thread action]
        ⟨⟨after, Host.Recording.advance ledger thread action⟩,
          advance publications instances flags ⟨before, ledger⟩ thread action⟩

variable [interface : CInterface] {E : Type}

theorem Step.erases (step : Step program policy instances flags before ticks after) :
    Host.Recording.Step program policy before.recorded ticks after.recorded := by
  cases step with
  | record actual => exact .record actual

theorem Step.reservations (step : Step program policy instances flags before ticks after) :
    ReservationRegistry.Step program policy flags before.reservationState ticks after.reservationState := by
  cases step with
  | record actual =>
    simpa only [Configuration.reservationState, reservations_advance] using
      (ReservationRegistry.Step.record (owners := PublicationRegistry.reservations _) actual)

/-- Every recorded actual history has this computed publication history.
This does not assert that arbitrary host actions have legal handle authority. -/
theorem history_lift (program : Events.Program E) (policy : Host.Policy) (instances flags : Nat)
    (path : Transition.Events.Reaches (Host.Recording.Step program policy) before ticks after)
    (publications : State capacity) :
    ∃ following, Transition.Events.Reaches (Step program policy instances flags)
      ⟨before, publications⟩ ticks ⟨after, following⟩ := by
  induction path generalizing publications with
  | refl => exact ⟨publications, .refl _⟩
  | next first rest ih =>
    cases first with
    | record actual =>
      obtain ⟨following, later⟩ := ih (advance publications instances flags _ _ _)
      exact ⟨following, .next (.record actual) later⟩

theorem history_erases
    (path : Transition.Events.Reaches (Step program policy instances flags) before ticks after) :
    Transition.Events.Reaches (Host.Recording.Step program policy) before.recorded ticks after.recorded := by
  induction path with
  | refl => exact .refl _
  | next first rest ih => exact .next first.erases ih

theorem history_reservations
    (path : Transition.Events.Reaches (Step program policy instances flags) before ticks after) :
    Transition.Events.Reaches (ReservationRegistry.Step program policy flags)
      before.reservationState ticks after.reservationState := by
  induction path with
  | refl => exact .refl _
  | next first rest ih => exact .next first.reservations ih

/-- A publication witness is the actual host completion tick with its original
factory invocation and exact bounded instance address. -/
def Observed (instances : Nat) (slot : Fin capacity) (lease : Nat) (tick : Host.Recording.Tick E) : Prop :=
  ∃ call, tick.origin = some call ∧ call.serial = lease ∧ ReservationOrigin.factory call.name ∧
    tick.action = .complete (.pointer (some (AtomicSlots.address instances slot)))

theorem step_publication_origin (step : Step program policy instances flags before ticks after)
    (published : Published after.publications slot lease) :
    Published before.publications slot lease ∨ ∃ tick ∈ ticks, Observed instances slot lease tick := by
  cases step with
  | record actual =>
    rcases advance_origin published with old | ⟨call, active, serial, factory, rfl, _⟩
    · exact .inl old
    · exact .inr ⟨_, List.mem_cons_self, call,
        by simpa [Host.Recording.stamp, Host.Recording.origin] using active, serial, factory, rfl⟩

/-- Every live publication in a history comes from an earlier actual factory
completion, unless it was explicitly part of the initial state. Claims and
clears cannot manufacture such a witness. -/
theorem history_publication_origin
    (path : Transition.Events.Reaches (Step program policy instances flags) before ticks after) :
    Published after.publications slot lease → Published before.publications slot lease ∨
      ∃ tick ∈ ticks, Observed instances slot lease tick := by
  induction path with
  | refl => exact fun published => .inl published
  | next first rest ih =>
    intro published
    rcases ih published with middle | ⟨tick, member, observed⟩
    · rcases step_publication_origin first middle with initial | ⟨tick, member, observed⟩
      · exact .inl initial
      · exact .inr ⟨tick, List.mem_append_left _ member, observed⟩
    · exact .inr ⟨tick, List.mem_append_right _ member, observed⟩

end Rumoca.FMI3.PublicationRegistry
