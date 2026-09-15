import Rumoca.FMI3AdapterProofs
import Rumoca.FMI3InitializationSemantics
import RumocaFMI3.MEHistory

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory StaticFactory

/-- The ME event-control functions occur in the independently checked adapter.
Their tokenization and complete call contracts share its actual definition
table and prepared literal pool. -/
theorem adapter_me_calls (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      (∀ entry, ∃ before after,
        adapter = before ++ (Runtime.function a.solve.prepareFMI3 (EventEntry.signature entry)).render ++ after ∧
        EventEntry.FunctionContract a.solve.prepareFMI3 entry signatures
          (Runtime.function a.solve.prepareFMI3 (EventEntry.signature entry)).render ∧
        EventEntry.PreparedContract a.solve.prepareFMI3 entry signatures pool) ∧
      (∃ before after,
        adapter = before ++ (Runtime.function a.solve.prepareFMI3 CompletedCalls.signature).render ++ after ∧
        CompletedCalls.FunctionContract a.solve.prepareFMI3 signatures
          (Runtime.function a.solve.prepareFMI3 CompletedCalls.signature).render ∧
        CompletedCalls.PreparedContract a.solve.prepareFMI3 signatures pool) ∧
      (∃ before after,
        adapter = before ++ (Runtime.function a.solve.prepareFMI3 DiscreteCalls.signature).render ++ after ∧
        DiscreteCalls.FunctionContract a.solve.prepareFMI3 signatures
          (Runtime.function a.solve.prepareFMI3 DiscreteCalls.signature).render ∧
        DiscreteCalls.PreparedContract a.solve.prepareFMI3 signatures pool) ∧
      (∃ before after,
        adapter = before ++ (Runtime.function a.solve.prepareFMI3 DiscreteEvaluation.signature).render ++ after ∧
        DiscreteEvaluation.FunctionContract a.solve.prepareFMI3 signatures
          (Runtime.function a.solve.prepareFMI3 DiscreteEvaluation.signature).render ∧
        DiscreteEvaluation.PreparedContract a.solve.prepareFMI3 signatures pool) := by
  obtain ⟨signatures, _, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, entries, completed, discrete, _, _, _, evaluationContract⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_, ?_, ?_, ?_⟩
  · intro entry
    obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 signatures
      (EventEntry.signature entry) (entries entry).member
    exact ⟨before, after, printed ▸ located, entries entry, (entries entry).prepared pool made⟩
  · obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 signatures
      CompletedCalls.signature completed.member
    exact ⟨before, after, printed ▸ located, completed, completed.prepared pool made⟩
  · obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 signatures
      DiscreteCalls.signature discrete.member
    exact ⟨before, after, printed ▸ located, discrete, discrete.prepared pool made⟩
  · obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 signatures
      DiscreteEvaluation.signature evaluationContract.member
    exact ⟨before, after, printed ▸ located, evaluationContract, evaluationContract.prepared pool made⟩

/-- The history frame retains the model's selected source IVP. It does not
identify an unchanged state with the solution at a later importer trial time. -/
theorem MEHistory.source_frame
    (initialized : InitializationCalls.SourceInitialized source heap p start trajectory)
    (outside : MEHistory.Buffers.Outside p addresses)
    (framed : ∀ query, MEHistory.Outside p addresses query → after query = heap query) :
    InitializationCalls.SourceInitialized source after p start trajectory := by
  have location : MEHistory.Outside p addresses (StateProofs.stateAddress p) := by
    refine ⟨HistoryBodies.state_ne_field p "time", HistoryBodies.state_ne_field p "mode",
      HistoryBodies.state_ne_field p "eventTime", HistoryBodies.state_ne_field p "timeMin",
      HistoryBodies.state_ne_field p "lastCompleted", ?_⟩
    intro name member same
    have blocks := congrArg Address.block same
    exact outside name member (by simpa [StateProofs.stateAddress] using blocks.symm)
  obtain ⟨valid, state, loaded, initial⟩ := initialized
  refine ⟨valid, state, ?_, initial⟩
  simpa only [load, framed _ location] using loaded

/-- The actual adapter implements every finite admitted ME control history
with explicit event-iteration readiness, outputs and intermediate heaps. The
initial valid instance and caller buffers are supplied; their continued validity
is derived. Importer integration, state setters and concurrent/error histories
remain separate obligations. -/
theorem adapter_me_history (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∀ (E : Type) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := executionInterface objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E),
        program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
        ∀ (heap : Heap) (p : Address) (clock : Time.Clock) (reference final : MEHistory.ReferenceState)
          (state : ModelExchange.State) (addresses : String → Address) (actions : List MEHistory.Action),
        MEHistory.Stored heap p clock reference state addresses →
        MEHistory.ReferenceTrace reference actions final →
        ∃ after finalClock,
          MEHistory.Calls program p addresses heap actions after ∧
          MEHistory.Stored after p finalClock final state addresses ∧
          (∀ query, MEHistory.Outside p addresses query → after query = heap query) ∧
          (∀ start trajectory, InitializationCalls.SourceInitialized a.parsed.ast heap p start trajectory →
            InitializationCalls.SourceInitialized a.parsed.ast after p start trajectory) := by
  obtain ⟨signatures, _, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, _, _, _, _, _, time, entries, completed, discrete, _, _, _, evaluationContract⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  refine ⟨signatures, pool, made, printed, ?_⟩
  intro E objects firstBlock
  letI : CInterface := executionInterface objects (pool.addresses firstBlock)
  intro program actual heap p clock reference final state addresses actions stored admitted
  have quiet : MEHistory.Quiet program :=
    ⟨(time.prepared pool made).quiet E objects firstBlock program actual,
      fun entry => ((entries entry).prepared pool made).quiet E objects firstBlock program actual,
      (completed.prepared pool made).quiet E objects firstBlock program actual,
      (discrete.prepared pool made).quiet E objects firstBlock program actual,
      (evaluationContract.prepared pool made).staticQuiet E objects firstBlock program actual⟩
  obtain ⟨after, finalClock, called, storedAfter, framed⟩ := MEHistory.trace_frame program quiet stored admitted
  exact ⟨after, finalClock, called, storedAfter, framed,
    fun _ _ initialized => MEHistory.source_frame initialized stored.outside framed⟩

end Rumoca.FMI3
