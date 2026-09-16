import RumocaFMI3.ClaimInitialization
import RumocaFMI3.InitializedRegion
import RumocaC.InvocationRegion

namespace Rumoca.FMI3.StaticFactory.ClaimInitialization
open CTree CMemory CBody CCalls CCalls.Host.Recording
open CAtomicScan.ConcurrentInvariant
variable [interface : CInterface] {E : Type}

/-- Track the actual successful helper continuation through the factory and
host completion boundary, without supplying a reached initializer entry. -/
theorem claimed_history (program : Events.Program E) (policy : Host.Policy)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (base flags : Address) (capacity slot tracked : Nat)
    (environment logger : Option Address) (logging : Bool)
    (before after : Host.Recording.State) (call : Invocation) (saved : Typed.State)
    (scope : Scope env base flags capacity environment logger logging)
    (storage : InstanceSlot.Storage before.runtime.heap (base.index slot))
    (inside : slot < capacity) (bounded : slot < 2^64)
    (size : interface.types "size_t" = some .size)
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (fresh : Fresh before.ledger) (active : before.ledger.active tracked = some call)
    (found : before.runtime.threads tracked = some saved)
    (control : ClaimedReady flags capacity slot (caller model kind env types) saved)
    (path : Transition.Events.Reaches
      (fun a ticks b => Host.Recording.Step program policy a ticks b ∧
        InterferenceFrame {q | (base.index slot).InRecord q} tracked call.serial a ticks b) before ticks after) :
    CurrentSelected (Ready model kind env types base flags capacity slot environment logger logging before.runtime.heap)
      tracked call.serial after ∧ Host.History program policy before.runtime (erase ticks) after.runtime := by
  have initial : CurrentSelected
      (Ready model kind env types base flags capacity slot environment logger logging before.runtime.heap)
      tracked call.serial before := by
    intro original chosen originalActive origin chosenFound
    have same : chosen = saved := Option.some.inj (chosenFound.symm.trans found)
    subst chosen
    exact .scan (control.withHeap before.runtime.heap) (by rw [Concurrent.heap_withHeap]; intro _ _; rfl)
  obtain ⟨_, invariant, actual⟩ := current_selected_history program policy _ {q | (base.index slot).InRecord q}
    (fun _ _ ready frame => ready.withHeap frame)
    (fun _ _ _ ready step => (step_ready program scope storage inside bounded size pointer double handle ready step).2)
    (fresh tracked call active) initial path
  exact ⟨invariant, history_erases actual⟩

/-- Observed completion of this successful reservation is the initialized
nonnull handle. Other invocations may execute throughout. The private-region
frame and initial typed storage remain explicit importer/ownership obligations. -/
theorem claimed_observed (program : Events.Program E) (policy : Host.Policy)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (base flags : Address) (capacity slot tracked : Nat)
    (environment logger : Option Address) (logging : Bool)
    (before after : Host.Recording.State) (call : Invocation) (saved : Typed.State)
    (scope : Scope env base flags capacity environment logger logging)
    (storage : InstanceSlot.Storage before.runtime.heap (base.index slot))
    (inside : slot < capacity) (bounded : slot < 2^64)
    (size : interface.types "size_t" = some .size)
    (pointer : interface.types "Instance *" = some .pointer)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (fresh : Fresh before.ledger) (active : before.ledger.active tracked = some call)
    (found : before.runtime.threads tracked = some saved)
    (control : ClaimedReady flags capacity slot (caller model kind env types) saved)
    (path : Transition.Events.Reaches
      (fun a ticks b => Host.Recording.Step program policy a ticks b ∧
        InterferenceFrame {q | (base.index slot).InRecord q} tracked call.serial a ticks b) before ticks after)
    (stillActive : after.ledger.active tracked = some call)
    (completed : Host.Step program policy after.runtime tracked (.complete value) following) :
    value = .pointer (some (base.index slot)) ∧
    InstanceInitialization.Initialized following.heap (base.index slot) kind environment logger logging ∧
    InstanceSlot.Storage following.heap (base.index slot) ∧
    load following.heap ((base.index slot).member "slot") = some (.integer slot) ∧
    Host.History program policy before.runtime (erase ticks ++ [(tracked, .complete value)]) following := by
  obtain ⟨ready, actual⟩ := claimed_history program policy model kind env types base flags capacity slot tracked
    environment logger logging before after call saved scope storage inside bounded size pointer double handle
    fresh active found control path
  obtain ⟨⟨result, halted, identity⟩, followingEq⟩ := Host.complete_iff.mp completed
  have finished := (ready call (.halted result) stillActive rfl halted).halted
  obtain ⟨initialized, writable, metadata⟩ := InstanceSlot.initialized_region finished.2 bounded
  refine ⟨identity.symm.trans finished.1, ?_, ?_, ?_, ?_⟩
  · simpa only [followingEq] using initialized
  · simpa only [followingEq] using writable
  · simpa only [followingEq] using metadata
  · have last : Host.History program policy after.runtime [(tracked, .complete value)] following :=
      .next (show Host.emits program policy after.runtime [(tracked, .complete value)] following from
        ⟨tracked, .complete value, rfl, completed⟩) (.refl _)
    exact actual.trans last

end Rumoca.FMI3.StaticFactory.ClaimInitialization
