import RumocaC.InvocationContinuation
import RumocaC.AtomicScanClaim
import RumocaFMI3.FactoryAfterScan

namespace Rumoca.FMI3.ConcurrentSlots
open CTree CMemory CCalls CCallSites CAtomicScan.ConcurrentInvariant

/-- After success, the helper returns through the actual factory suffix.
Its later calls are in the closed domain; the whole invocation cannot reserve
again, including after the original helper interval has ended. -/
def PostClaim (model : Solve.Model source) (kind : Kind) (flags : Address) (count k : Nat)
    (env : CBody.Locals) (types : CLoops.Types) (state : Typed.State) : Prop :=
  ClaimedReady flags count k (.caller (.declare "size_t" "slot")
    (StaticFactory.guard :: StaticFactory.initializeInstance model kind) env types "fmi3Instance" .done) state ∨
  CCallSites.Ready ReservationOrigin.Permitted (fun name _ => ReservationOrigin.allowed name = true) state

theorem post_claim_heap (ready : PostClaim model kind flags count k env types state) (heap : Heap) :
    PostClaim model kind flags count k env types (Concurrent.withHeap state heap) := by
  rcases ready with claimed | closed
  · exact Or.inl (claimed.withHeap heap)
  · exact Or.inr ((ready_withHeap _ _).mpr closed)

theorem post_claim_call (ready : PostClaim model kind flags count k env types (.calling name args heap stack)) :
    ReservationOrigin.allowed name = true := by
  rcases ready with claimed | closed
  · exact False.elim claimed.no_call
  · exact closed.1

variable [interface : CInterface] {E : Type}

theorem post_claim_step (model : Solve.FMI3Model source) (sigs : List Signature)
    (program : Events.Program E) (actual : program.internal = LiteralPreparation.program model sigs)
    (onlyNamed : ∀ name, ReservationOrigin.allowed name = false → NamedOnly program name)
    (size : interface.types "size_t" = some .size) (bounded : k < 2^64)
    (ready : PostClaim model.solve kind flags count k env types before)
    (step : Events.Step program before events after) : PostClaim model.solve kind flags count k env types after := by
  rcases ready with claimed | closed
  · by_cases returned : Concurrent.Exit (.caller (.declare "size_t" "slot")
        (StaticFactory.guard :: StaticFactory.initializeInstance model.solve kind) env types "fmi3Instance" .done) before
    · obtain ⟨value, heap, rfl⟩ := returned
      exact Or.inr (ReservationOrigin.event_ready model sigs program actual onlyNamed
        (ReservationOrigin.factory_return_closed model.solve kind value heap env types) step)
    · exact Or.inl (claimed_step program size bounded claimed returned step).2
  · exact Or.inr (ReservationOrigin.event_ready model sigs program actual onlyNamed closed step)

/-- A successful claim excludes every later reservation by the same recorded
factory invocation across an arbitrary finite host suffix. Thread reuse and
fresh public calls remain possible; they do not inherit this invocation's ID.
This is a control property, not a future ownership or heap-frame assertion. -/
theorem post_claim_history (model : Solve.FMI3Model source) (sigs : List Signature)
    (program : Events.Program E) (actual : program.internal = LiteralPreparation.program model sigs)
    (onlyNamed : ∀ name, ReservationOrigin.allowed name = false → NamedOnly program name)
    (policy : Host.Policy) (size : interface.types "size_t" = some .size) (bounded : k < 2^64)
    (active : before.ledger.active tracked = some call) (issued : call.serial < before.ledger.next)
    (claimed : ∃ saved, before.runtime.threads tracked = some saved ∧
      ClaimedReady flags count k (.caller (.declare "size_t" "slot")
        (StaticFactory.guard :: StaticFactory.initializeInstance model.solve kind) env types "fmi3Instance" .done) saved)
    (path : Transition.Events.Reaches (Host.Recording.Step program policy) before ticks after) :
    ∀ laterCall name args heap stack, after.ledger.active tracked = some laterCall → laterCall.serial = call.serial →
      after.runtime.threads tracked = some (.calling name args heap stack) → ReservationOrigin.allowed name = true := by
  have ready : Host.Recording.Selected (PostClaim model.solve kind flags count k env types) tracked call.serial before := by
    intro current saved selected _ found
    cases Option.some.inj (selected.symm.trans active)
    obtain ⟨original, present, claimed⟩ := claimed
    cases Option.some.inj (found.symm.trans present)
    exact Or.inl claimed
  have final := (Host.Recording.selected_history program policy (PostClaim model.solve kind flags count k env types)
    (fun _ ready heap => post_claim_heap ready heap)
    (fun _ _ _ ready step => post_claim_step model sigs program actual onlyNamed size bounded ready step)
    issued ready path).2
  intro laterCall name args heap stack active same calling
  exact post_claim_call (final laterCall _ active same calling)

end Rumoca.FMI3.ConcurrentSlots
