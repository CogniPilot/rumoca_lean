import Rumoca.FMI3AdapterProofs
import Rumoca.FMI3InitializationCalls
import RumocaFMI3.TimeHistory

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CBody StaticFactory

/-- The actual adapter contains this public function and supplies its complete
time-admission and error cases in the same prepared object environment. -/
theorem adapter_time (contract : AdapterContract a adapter) :
    ∃ signatures pool before after,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      adapter = before ++ (Runtime.function a.solve.prepareFMI3 TimeCalls.signature).render ++ after ∧
      TimeCalls.FunctionContract a.solve.prepareFMI3 signatures
        (Runtime.function a.solve.prepareFMI3 TimeCalls.signature).render ∧
      TimeCalls.PreparedContract a.solve.prepareFMI3 signatures pool := by
  obtain ⟨signatures, _, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, _, _, _, _, _, time, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 signatures
    TimeCalls.signature time.member
  exact ⟨signatures, pool, before, after, made, printed, printed ▸ located,
    time, time.prepared pool made⟩

/-- Updating the trial-time cell retains the source IVP selected by the model
value. It does not assert that this value solves the ODE at the new trial time. -/
theorem TimeCalls.source_frame
    (initialized : InitializationCalls.SourceInitialized source heap p start trajectory)
    (bits : BitVec 64) :
    InitializationCalls.SourceInitialized source
      (StateProofs.written heap (p.member "time") bits) p start trajectory := by
  obtain ⟨valid, state, loaded, initial⟩ := initialized
  refine ⟨valid, state, ?_, initial⟩
  simpa only [load, TimeProofs.model_frame] using loaded

/-- The actual public call implements the independent ME trial-time history
transition, preserving the model, source initialization relation and all other
cells. Prior valid storage/history and the importer-selected time are explicit;
no successful target execution or monotone trial-time assumption is supplied. -/
theorem adapter_time_history (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := executionInterface objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        ∀ (heap : Heap) (p : Address) (clock : Time.Clock) (history : Time.History)
          (time : Binary64.Value) (state : ModelExchange.State),
        load heap (p.member "kind") = some (.integer 0) →
        load heap (p.member "mode") = some (.integer 3) →
        HistoryProofs.Stored heap p clock → Time.Represents history clock →
        StateProofs.Represents heap p state →
        load heap (p.member "stopDefined") = some (boolean history.window.stopTime.isSome) →
        (∀ stop, history.window.stopTime = some stop → load heap (p.member "stop") = some (.finite stop)) →
        history.window.Admissible time →
        let after := StateProofs.written heap (p.member "time") (Binary64.toBits time).val
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling TimeCalls.signature.name (TimeCalls.arguments (some p) (Binary64.toBits time).val) heap .done) behavior ↔
          behavior = .terminates [] ⟨.integer 0, after⟩) ∧
        HistoryProofs.Stored after p (clock.setTime time) ∧
        Time.Represents (history.setTime time) (clock.setTime time) ∧
        StateProofs.Represents after p state ∧
        TimeCalls.Bounds after p history.window clock.minimum ∧
        (∀ query, query ≠ p.member "time" → after query = heap query) ∧
        (∀ start trajectory, InitializationCalls.SourceInitialized a.parsed.ast heap p start trajectory →
          InitializationCalls.SourceInitialized a.parsed.ast after p start trajectory) := by
  obtain ⟨signatures, _, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, _, _, _, _, _, timeContract, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E objects firstBlock
  letI : CInterface := executionInterface objects (pool.addresses firstBlock)
  intro program actual heap p clock history time state hk hm clockStored historyStored stateStored
    stopDefined stopValue admissible
  have quiet := (timeContract.prepared pool made).quiet E objects firstBlock program actual
  obtain ⟨called, clockAfter, historyAfter, stateAfter, boundsAfter, framed⟩ :=
    TimeCalls.history_call program quiet heap p clock history time state hk hm clockStored historyStored
      stateStored stopDefined stopValue admissible
  exact ⟨called, clockAfter, historyAfter, stateAfter, boundsAfter, framed,
    fun _ _ initialized => TimeCalls.source_frame initialized _⟩

end Rumoca.FMI3
