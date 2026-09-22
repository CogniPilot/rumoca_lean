import RumocaFMI3.FactoryRejection
import RumocaFMI3.ReservationOriginPolicy
import RumocaC.CallContextBoundary

namespace Rumoca.FMI3.FactoryRejection
open CTree CMemory CBody CCalls CCallSites

abbrev Closed := Ready ReservationOrigin.Permitted (fun name _ => ReservationOrigin.allowed name = true)

/-- Rejection's unconditional return cuts off the arbitrary creation tail.
The tail need not pass the non-reservation call policy: it is unreachable.
An optional callback keeps its literal return continuation while executing. -/
inductive Control (message : String) (tail : List Stmt) (env : Locals) (types : CLoops.Types) :
    Typed.State → Prop where
  | dispatch (heap : Heap) : Control message tail env types
      (.body (.running (code message ++ tail) env types heap) "fmi3Instance" .done)
  | callback (heap : Heap) : Control message tail env types
      (.body (.running (logCall message :: .ret (some (.id "NULL")) :: tail) env types heap) "fmi3Instance" .done)
  | suspended (ready : Context.Suspended Closed
      (.caller .discard (.ret (some (.id "NULL")) :: tail) env types "fmi3Instance" .done) state) :
      Control message tail env types state
  | returnNull (heap : Heap) : Control message tail env types
      (.body (.running (.ret (some (.id "NULL")) :: tail) env types heap) "fmi3Instance" .done)
  | closed (ready : Closed state) : Control message tail env types state

theorem Control.withHeap (ready : Control message tail env types state) (heap : Heap) :
    Control message tail env types (Concurrent.withHeap state heap) := by
  cases ready with
  | dispatch => exact .dispatch heap
  | callback => exact .callback heap
  | suspended ready => exact .suspended (Context.suspended_heap ready heap
      (fun state ready heap => (ready_withHeap state heap).mpr ready))
  | returnNull => exact .returnNull heap
  | closed ready => exact .closed ((ready_withHeap _ _).mpr ready)

theorem Control.call_allowed (ready : Control message tail env types (.calling name args heap stack)) :
    ReservationOrigin.allowed name = true := by
  cases ready with
  | suspended ready =>
    obtain ⟨_, _, ready⟩ := Context.suspended_call ready
    exact ready.1
  | closed ready => exact ready.1

variable [interface : CInterface] {E : Type}

/-- Every actual rejection step stays before the unconditional return or in
the closed post-return domain, including every admitted callback outcome.
No completed callback or successful factory execution is assumed. -/
theorem control_step (model : Solve.FMI3Model source) (sigs : List Signature)
    (program : Events.Program E) (actual : program.internal = LiteralPreparation.program model sigs)
    (onlyNamed : ∀ name, ReservationOrigin.allowed name = false → NamedOnly program name)
    (logger : Option Address) (logging : Bool)
    (loggerBound : resolve env "logMessage" = some (.pointer logger))
    (loggingBound : resolve env "loggingOn" = some (boolean logging))
    (nullBound : resolve env "NULL" = some (.pointer none))
    (ready : Control message tail env types before)
    (step : Events.Step program before events after) : Control message tail env types after := by
  cases ready with
  | dispatch heap =>
    obtain ⟨_, rfl⟩ := Events.internal_unique program
      (dispatch program message env types heap tail .done logger logging loggerBound loggingBound) _ _ step
    cases enabled : logger.isSome && logging <;> simp only [Bool.false_eq_true, ↓reduceIte,
      List.nil_append, List.cons_append] <;> first | exact .callback heap | exact .returnNull heap
  | callback heap =>
    cases step with
    | internal moved =>
      change (do
        let name ← Events.resolve program env heap (.id "logMessage")
        let values ← arguments env heap
          [.id "instanceEnvironment", .id "fmi3Error", .str "logStatus", .str message]
        pure (Typed.State.calling name values heap
          (.caller .discard (.ret (some (.id "NULL")) :: tail) env types "fmi3Instance" .done))) = some after at moved
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at moved
      obtain ⟨name, resolved, args, evaluated, emitted⟩ := moved
      cases Option.some.inj emitted
      have permitted := ReservationOrigin.operand_sound program onlyNamed
        ⟨.discard, .id "logMessage", [.id "instanceEnvironment", .id "fmi3Error", .str "logStatus", .str message]⟩
        (by change ReservationOrigin.allowed "logMessage" = true; decide +kernel) env heap name args resolved evaluated
      exact .suspended ⟨.calling name args heap .done, rfl, ⟨permitted, True.intro⟩,
        by simp [Context.Live]⟩
  | suspended ready =>
    by_cases exited : Concurrent.Exit
        (.caller .discard (.ret (some (.id "NULL")) :: tail) env types "fmi3Instance" .done) before
    · obtain ⟨value, heap, rfl⟩ := exited
      obtain ⟨_, rfl⟩ := Events.internal_unique program (by rfl) _ _ step
      exact .returnNull heap
    · exact .suspended (Context.suspended_step program
        (fun _ _ _ ready step => ReservationOrigin.event_ready model sigs program actual onlyNamed ready step)
        ready exited step)
  | returnNull heap =>
    have next : Events.internalNext program
        (.body (.running (.ret (some (.id "NULL")) :: tail) env types heap) "fmi3Instance" .done) =
        some (.body (.returned ⟨.pointer none, heap⟩) "fmi3Instance" .done) := by
      simp [Events.internalNext, Events.internalNextWith, Typed.nextWithExpressions,
        CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, CBody.eval,
        CBody.evalWith, nullBound]
    obtain ⟨_, rfl⟩ := Events.internal_unique program next _ _ step
    exact .closed ⟨True.intro, True.intro⟩
  | closed ready => exact .closed (ReservationOrigin.event_ready model sigs program actual onlyNamed ready step)

end Rumoca.FMI3.FactoryRejection
