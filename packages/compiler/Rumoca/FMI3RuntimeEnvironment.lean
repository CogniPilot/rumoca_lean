import Rumoca.FMI3TimeProofs
import Rumoca.FMI3ModelAdvance
import RumocaFMI3.RuntimeEnvironment

/-! The actual adapter supplies one definition table and literal pool for
every admitted fenv header profile. Public CS admission and native header/
environment correspondence are separate obligations. -/
noncomputable section
namespace Rumoca.FMI3
open CTree CMemory StaticFactory

theorem adapter_runtime_environment (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
          CInterface.constants "FE_TONEAREST" = some (.integer header.nearest) ∧
          TimeCalls.QuietContract program ∧
          ∀ (heap : Heap) (p : Address) (x : Binary64.Value) (count : CStatements.Counter),
          heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite x)⟩ →
          let after := StateProofs.written heap (StateProofs.stateAddress p)
            (Binary64.toBits (a.solve.run x count.val)).val
          (∀ behavior, (CCalls.Events.machine program).Behaves
            (.calling "model_advance" [.pointer (some (p.member "model")), .integer count.val]
              heap .done) behavior ↔ behavior = .terminates [] ⟨.void, after⟩) ∧
          after (StateProofs.stateAddress p) =
            some ⟨.float64, true, some (.finite (a.solve.run x count.val))⟩ ∧
          (∀ query, query ≠ StateProofs.stateAddress p → after query = heap query) ∧
          (∀ start trajectory,
            InitializationCalls.SourceInitialized a.parsed.ast heap p start trajectory →
            |Binary64.value (a.solve.run x count.val) -
              trajectory (Binary64.value start + (count.val : ℝ))| ≤ (count.val : ℝ)) := by
  obtain ⟨signatures, unique, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, derivative, _, _, _, _, _, _, _, time, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro header E objects firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual
  refine ⟨rfl, ?_, ?_⟩
  · apply RuntimeEnvironment.time_quiet header objects (pool.addresses firstBlock)
      a.solve.prepareFMI3 program
    rw [actual]
    exact LiteralPreparation.function_bound a.solve.prepareFMI3 signatures unique TimeCalls.signature time.member
  · intro heap p x count stored
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact RuntimeEnvironment.model_advance_behaviors header objects (pool.addresses firstBlock)
        a.solve.prepareFMI3 signatures derivative.numerical.fresh program actual
        heap (p.member "model") x count stored
    · simp [StateProofs.written, Value.finite]
    · intro query other
      exact StateProofs.written_frame heap _ query _ other
    · intro start trajectory initialized
      exact ModelAdvance.source_error a.solve heap p x start count.val initialized stored

/-- The existing ME history transition and source-IVP frame also hold in
the shared header/object environment. A trial-time update does not integrate
the state; importer state updates and complete mixed histories remain open. -/
theorem adapter_runtime_time_history (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (header : CFenv.Header) (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        ∀ (heap : Heap) (p : Address) (clock : Time.Clock) (history : Time.History)
          (time : Binary64.Value) (state : ModelExchange.State),
        load heap (p.member "kind") = some (.integer 0) →
        load heap (p.member "mode") = some (.integer 3) →
        HistoryProofs.Stored heap p clock → Time.Represents history clock →
        StateProofs.Represents heap p state →
        load heap (p.member "stopDefined") = some (CBody.boolean history.window.stopTime.isSome) →
        (∀ stop, history.window.stopTime = some stop → load heap (p.member "stop") = some (.finite stop)) →
        history.window.Admissible time →
        let after := StateProofs.written heap (p.member "time") (Binary64.toBits time).val
        (∀ behavior, (CCalls.Events.machine program).Behaves
          (.calling TimeCalls.signature.name (TimeCalls.arguments (some p) (Binary64.toBits time).val)
            heap .done) behavior ↔ behavior = .terminates [] ⟨.integer 0, after⟩) ∧
        HistoryProofs.Stored after p (clock.setTime time) ∧
        Time.Represents (history.setTime time) (clock.setTime time) ∧
        StateProofs.Represents after p state ∧
        TimeCalls.Bounds after p history.window clock.minimum ∧
        (∀ query, query ≠ p.member "time" → after query = heap query) ∧
        (∀ start trajectory, InitializationCalls.SourceInitialized a.parsed.ast heap p start trajectory →
          InitializationCalls.SourceInitialized a.parsed.ast after p start trajectory) := by
  obtain ⟨signatures, pool, made, printed, calls⟩ := adapter_runtime_environment contract
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro header E objects firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual heap p clock history time state kind mode clockStored historyStored stateStored
    stopDefined stopValue admissible
  have quiet := (calls header E objects firstBlock program actual).2.1
  obtain ⟨called, clockAfter, historyAfter, stateAfter, boundsAfter, framed⟩ :=
    TimeCalls.history_call program quiet heap p clock history time state kind mode clockStored
      historyStored stateStored stopDefined stopValue admissible
  exact ⟨called, clockAfter, historyAfter, stateAfter, boundsAfter, framed,
    fun _ _ initialized => TimeCalls.source_frame initialized _⟩

end Rumoca.FMI3
end
