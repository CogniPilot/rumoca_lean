import RumocaFMI3.CSHistory
import Rumoca.FMI3StepProofs
import Rumoca.FMI3InitializationSemantics

noncomputable section
namespace Rumoca.FMI3
open CMemory CTree StaticFactory

/-- The continuous source solution is tied to the original initialized state.
Its error at the final communication time includes the accumulated clock drift. -/
theorem CSHistory.source_error (model : Solve.Model source) (seed start : Binary64.Value)
    (heap : Heap) (p : Address) (buffers : StepEntry.Buffers) (stop : Option Binary64.Value)
    (initialized : InitializationCalls.SourceInitialized source heap p start trajectory)
    (stored : CSHistory.Stored model seed heap p buffers ⟨start, 0⟩ stop)
    (final : CSHistory.ReferenceState) :
    |Binary64.value (model.run seed final.elapsed) - trajectory (Binary64.value final.time)| ≤
      (final.elapsed : ℝ) + |Binary64.value final.time - (Binary64.value start + (final.elapsed : ℝ))| := by
  have represented : StateProofs.Represents heap p ⟨seed⟩ := by
    simp [StateProofs.Represents, load, stored.state, Solve.Model.run, convert, Value.finite]
  rw [InitializationCalls.source_initialized_unique initialized represented]
  exact model.run_error_at_time seed final.elapsed (Binary64.value start) (Binary64.value final.time)

/-- The mandatory contract for the function in the actual adapter derives a
whole finite accepted CS history. Only initial storage is supplied by the host;
each subsequent call's storage, outputs and exact numerical state are proved. -/
theorem adapter_cs_history (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      (∃ before after, adapter = before ++ (Runtime.function a.solve.prepareFMI3 StepEntry.signature).render ++ after) ∧
      ∀ (E : Type) (header : CFenv.Header) (objects : Objects) (firstBlock : Nat),
        letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
        ∀ (program : CCalls.Events.Program E)
          (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
          program.internal = LiteralPreparation.program a.solve.prepareFMI3 signatures →
          program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
          program.externals "floor" = some (CMathCalls.floorExternal rfl) →
          ∀ (seed start : Binary64.Value) (heap : Heap) (p : Address) (buffers : StepEntry.Buffers)
            (stop : Option Binary64.Value) (trajectory : ℝ → ℝ),
          InitializationCalls.SourceInitialized a.parsed.ast heap p start trajectory →
          CSHistory.Stored a.solve seed heap p buffers ⟨start, 0⟩ stop →
          ∀ (requests : List CSHistory.Request) (final : CSHistory.ReferenceState),
          CSHistory.ReferenceTrace stop ⟨start, 0⟩ requests final →
          ∃ after,
            CSHistory.Calls program p buffers heap ⟨start, 0⟩ requests after final ∧
            CSHistory.Stored a.solve seed after p buffers final stop ∧
            (∀ query, CSHistory.Outside p buffers query → after query = heap query) ∧
            |Binary64.value (a.solve.run seed final.elapsed) - trajectory (Binary64.value final.time)| ≤
              (final.elapsed : ℝ) + |Binary64.value final.time - (Binary64.value start + (final.elapsed : ℝ))| := by
  obtain ⟨signatures, pool, made, printed, before, after, located, _, prepared⟩ := adapter_cs_calls contract
  refine ⟨signatures, pool, made, printed, ⟨before, after, located⟩, ?_⟩
  intro E header objects firstBlock
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program range actual rounding floorBound seed start heap p buffers stop trajectory initialized stored requests final admitted
  obtain ⟨after, calls, finalStored, frame⟩ := CSHistory.trace_frame header objects (pool.addresses firstBlock)
    a.solve.prepareFMI3 signatures seed p buffers stop
    (fun reference request => (prepared.quiet (request.query header p buffers reference stop) objects firstBlock).2)
    program range actual rounding floorBound heap ⟨start, 0⟩ final requests stored admitted
  exact ⟨after, calls, finalStored, frame, CSHistory.source_error a.solve seed start heap p buffers stop initialized stored final⟩

end Rumoca.FMI3
end
