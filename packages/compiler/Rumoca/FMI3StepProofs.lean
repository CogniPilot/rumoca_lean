import Rumoca.FMI3AdapterProofs

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory

/-- The complete public CS function contract belongs to the same actual
adapter bytes, prepared literal pool and source-derived Solve product.
This is a single-call guarantee; histories and native ABI remain separate. -/
theorem adapter_cs_calls (contract : AdapterContract a adapter) :
    ∃ signatures pool,
      LiteralPreparation.prepare a.solve.prepareFMI3 signatures = some pool ∧
      Runtime.render a.solve.prepareFMI3 signatures = adapter ∧
      ∃ before after,
        adapter = before ++ (Runtime.function a.solve.prepareFMI3 StepEntry.signature).render ++ after ∧
        StepCalls.FunctionContract a.solve.prepareFMI3 signatures
          (Runtime.function a.solve.prepareFMI3 StepEntry.signature).render ∧
        StepCalls.PreparedContract a.solve.prepareFMI3 signatures pool := by
  obtain ⟨signatures, _, _, printed, _, _, _, _, _, poolReady,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, step, _⟩ := contract
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp poolReady
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 signatures
    StepEntry.signature step.member
  exact ⟨signatures, pool, made, printed, before, after, printed ▸ located, step, step.prepared pool made⟩

end Rumoca.FMI3
end
