import RumocaFMI3.ResourceLinkage
import RumocaFMI3.ReleasedHistory

namespace Rumoca.FMI3.InstanceAuthority.Resources.Publication
open CTree CMemory CCalls
variable {capacity : Nat}

structure Configuration (capacity : Nat) where
  resources : Resources.Configuration capacity
  publications : PublicationRegistry.State capacity

def Configuration.published (state : Configuration capacity) : PublicationRegistry.Configuration capacity :=
  ⟨state.resources.recorded, state.publications⟩

/-- Couple resource effects to the existing computed physical/publication
update. The successful-factory retention boundary is explicit; caller buffers,
callbacks and all C execution still use the original host policy and program. -/
inductive Step [CInterface] (program : Events.Program E) (policy : Host.Policy) (instances flags : Nat) :
    Configuration capacity → List (Host.Recording.Tick E) → Configuration capacity → Prop where
  | record (actual : Host.Step program policy before.runtime thread action after)
      (changed : Resources.Change instances flags before thread action authority following)
      (factoryResult : Resources.FactoryResult publications before thread instances action) :
      Step program policy instances flags ⟨⟨before, authority⟩, publications⟩
        [Host.Recording.stamp before.ledger thread action]
        ⟨⟨⟨after, Host.Recording.advance before.ledger thread action⟩, following⟩,
          PublicationRegistry.advance publications instances flags before thread action⟩

structure Invariant (instances : Nat) (state : Configuration capacity) : Prop where
  linked : Linked state.resources.authority state.publications
  origins : CallOrigins state.resources.authority state.resources.recorded.ledger instances
  aligned : Host.Recording.Aligned state.resources.recorded.runtime state.resources.recorded.ledger
  fresh : Host.Recording.Fresh state.resources.recorded.ledger
  unique : Host.Recording.Unique state.resources.recorded.ledger

def initial (capacity : Nat) (heap : Heap) : Configuration capacity :=
  ⟨Resources.initial capacity heap, fun _ => none⟩

variable [CInterface] {E : Type} {program : Events.Program E} {policy : Host.Policy}
  {before after : Configuration capacity}

theorem Step.resources (step : Step program policy instances flags before ticks after) :
    Resources.Step program policy instances flags before.resources ticks after.resources := by
  cases step with
  | record actual changed factoryResult => exact .record actual changed

theorem Step.publications (step : Step program policy instances flags before ticks after) :
    PublicationRegistry.Step program policy instances flags before.published ticks after.published := by
  cases step with
  | record actual changed factoryResult => exact .record actual

/-- Both maps remain linked to the same recorded program execution. Only the
initial invariant is supplied; later resource origins and links are derived. -/
theorem Step.invariant (step : Step program policy instances flags before ticks after)
    (invariant : Invariant instances before) : Invariant instances after := by
  have origins := Resources.step_origins step.resources invariant.origins invariant.aligned invariant.unique
  cases step with
  | record actual changed factoryResult =>
    exact ⟨changed.linked invariant.linked invariant.origins invariant.unique factoryResult,
      origins, Host.Recording.step_aligned invariant.aligned actual,
      Host.Recording.advance_fresh invariant.fresh _ _,
      Host.Recording.advance_unique invariant.unique invariant.fresh _ _⟩

/-- Resource and publication histories are projections of one history, not
independent annotations or unrelated successful executions. -/
theorem history_invariant
    (path : Transition.Events.Reaches (Step program policy instances flags) before ticks after)
    (invariant : Invariant instances before) :
    Invariant instances after ∧
    Transition.Events.Reaches (Resources.Step program policy instances flags) before.resources ticks after.resources ∧
    Transition.Events.Reaches (PublicationRegistry.Step program policy instances flags) before.published ticks after.published := by
  induction path with
  | refl => exact ⟨invariant, .refl _, .refl _⟩
  | next first rest ih =>
    obtain ⟨following, resources, publications⟩ := ih (first.invariant invariant)
    exact ⟨following, .next first.resources resources, .next first.publications publications⟩

theorem initial_history
    (path : Transition.Events.Reaches (Step program policy instances flags) (initial capacity heap) ticks after) :
    Invariant instances after ∧
    Transition.Events.Reaches (Resources.Step program policy instances flags)
      (Resources.initial capacity heap) ticks after.resources ∧
    Transition.Events.Reaches (PublicationRegistry.Step program policy instances flags)
      (initial capacity heap).published ticks after.published := by
  apply history_invariant path
  refine ⟨?_, empty_call_origins _ _, Host.Recording.initial_aligned heap,
    Host.Recording.initial_fresh, Host.Recording.initial_unique⟩
  intro slot account present
  contradiction



/-- Every usable handle in the coupled history originates in an actual
observed factory return with exactly that slot and original invocation serial.
No initial handle or per-state publication witness is supplied. -/
theorem initial_handle_origin
    (path : Transition.Events.Reaches (Step program policy instances flags) (initial capacity heap) ticks after)
    (owned : Owns after.resources.authority handle) :
    ∃ tick ∈ ticks, PublicationRegistry.Observed instances handle.slot handle.lease tick := by
  obtain ⟨invariant, _, publications⟩ := initial_history path
  have published := invariant.linked _ _ owned
  rcases PublicationRegistry.history_publication_origin publications published with absent | observed
  · change (none : Option PublicationRegistry.Entry) = some ⟨handle.lease, true⟩ at absent
    contradiction
  · exact observed

end Rumoca.FMI3.InstanceAuthority.Resources.Publication
