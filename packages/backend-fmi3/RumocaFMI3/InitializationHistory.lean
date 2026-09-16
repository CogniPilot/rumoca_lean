import RumocaFMI3.InstanceInitializationRegion
import RumocaFMI3.InitializedRegion
import RumocaC.InvocationRegion

namespace Rumoca.FMI3.InstanceSlot
open CTree CMemory CBody CCalls CCalls.Host.Recording CCalls.InitializationRegion
variable [interface : CInterface] {E : Type}

/-- A reached generated initializer follows the original invocation through
the real host history. Other threads and idle-host memory actions may proceed
under the stated private-record frame; no scheduler is replaced or serialized. -/
theorem initialization_history (program : Events.Program E) (policy : Host.Policy)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (before after : Host.Recording.State) (p : Address) (slot tracked : Nat)
    (environment logger : Option Address) (logging : Bool) (call : Invocation) (saved : Typed.State)
    (storage : Storage before.runtime.heap p)
    (bound : InstanceInitialization.Bindings env p environment logger logging)
    (selected : resolve env "slot" = some (.integer slot)) (bounded : slot < 2^64)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (fresh : Fresh before.ledger) (active : before.ledger.active tracked = some call)
    (found : before.runtime.threads tracked = some saved)
    (entry : Concurrent.withHeap saved before.runtime.heap =
      .body (.running (code model kind) env types before.runtime.heap) "fmi3Instance" .done)
    (path : Transition.Events.Reaches
      (fun a ticks b => Host.Recording.Step program policy a ticks b ∧
        InterferenceFrame {q | p.InRecord q} tracked call.serial a ticks b) before ticks after) :
    CurrentSelected
      (CompleteReady {q | p.InRecord q} env types (.cast "fmi3Instance" (.id "m")) "fmi3Instance"
        ⟨.pointer (some p), finalHeap before.runtime.heap p slot kind environment logger logging⟩
        (.pointer (some p))) tracked call.serial after ∧
      Host.History program policy before.runtime (erase ticks) after.runtime := by
  have cast : returnCast "fmi3Instance" (.pointer (some p)) = some (.pointer (some p)) := by
    simp [returnCast, CBody.cast, handle, convert]
  have initial : CurrentSelected
      (CompleteReady {q | p.InRecord q} env types (.cast "fmi3Instance" (.id "m")) "fmi3Instance"
        ⟨.pointer (some p), finalHeap before.runtime.heap p slot kind environment logger logging⟩
        (.pointer (some p))) tracked call.serial before := by
    intro original control originalActive origin controlFound
    have same : control = saved := Option.some.inj (controlFound.symm.trans found)
    subst control
    rw [entry]
    exact initialization_ready model kind env types before.runtime.heap p slot environment logger logging
      storage bound selected bounded double handle
  obtain ⟨_, invariant, actual⟩ := current_selected_history program policy _ {q | p.InRecord q}
    (fun _ _ ready frame => ready.withHeap frame)
    (fun _ _ _ ready step => (complete_step_ready program rfl cast ready step).2)
    (fresh tracked call active) initial path
  exact ⟨invariant, history_erases actual⟩

/-- The observed completion is the actual nonnull handle and contains the
initialized model, clock, callback fields, writable storage and slot metadata.
The initial suffix entry and legal interference remain explicit obligations
for composition with the complete public factory and lifetime protocol. -/
theorem initialization_observed (program : Events.Program E) (policy : Host.Policy)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (before after : Host.Recording.State) (p : Address) (slot tracked : Nat)
    (environment logger : Option Address) (logging : Bool) (call : Invocation) (saved : Typed.State)
    (storage : Storage before.runtime.heap p)
    (bound : InstanceInitialization.Bindings env p environment logger logging)
    (selected : resolve env "slot" = some (.integer slot)) (bounded : slot < 2^64)
    (double : interface.types "double" = some .float64)
    (handle : interface.types "fmi3Instance" = some .pointer)
    (fresh : Fresh before.ledger) (active : before.ledger.active tracked = some call)
    (found : before.runtime.threads tracked = some saved)
    (entry : Concurrent.withHeap saved before.runtime.heap =
      .body (.running (code model kind) env types before.runtime.heap) "fmi3Instance" .done)
    (path : Transition.Events.Reaches
      (fun a ticks b => Host.Recording.Step program policy a ticks b ∧
        InterferenceFrame {q | p.InRecord q} tracked call.serial a ticks b) before ticks after)
    (stillActive : after.ledger.active tracked = some call)
    (completed : Host.Step program policy after.runtime tracked (.complete value) following) :
    value = .pointer (some p) ∧
    InstanceInitialization.Initialized following.heap p kind environment logger logging ∧
    Storage following.heap p ∧ load following.heap (p.member "slot") = some (.integer slot) ∧
    Host.History program policy before.runtime (erase ticks ++ [(tracked, .complete value)]) following := by
  obtain ⟨ready, actual⟩ := initialization_history program policy model kind env types before after p slot tracked
    environment logger logging call saved storage bound selected bounded double handle fresh active found entry path
  obtain ⟨⟨result, halted, identity⟩, followingEq⟩ := Host.complete_iff.mp completed
  have finished := (ready call (.halted result) stillActive rfl halted).halted
  obtain ⟨initialized, writable, metadata⟩ := initialized_region finished.2 bounded
  refine ⟨identity.symm.trans finished.1, ?_, ?_, ?_, ?_⟩
  · simpa only [followingEq] using initialized
  · simpa only [followingEq] using writable
  · simpa only [followingEq] using metadata
  · have last : Host.History program policy after.runtime [(tracked, .complete value)] following :=
      .next (show Host.emits program policy after.runtime [(tracked, .complete value)] following from
        ⟨tracked, .complete value, rfl, completed⟩) (.refl _)
    exact actual.trans last

end Rumoca.FMI3.InstanceSlot
