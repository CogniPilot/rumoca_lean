import Rumoca.FMI3Float64SetProofs
import Rumoca.FMI3InitializationCalls

noncomputable section
namespace Rumoca.FMI3
open CTree CLiteral

/-- Both actual initialization fragments and the source IVP consequence use
the same compiled source, prepared Solve model, function table and literal pool.
Allocation and native host/ABI behavior remain explicit boundaries. -/
theorem initialization_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Rumoca.ArtifactContract a c .internal ∧
    (∀ state d, Source.Equation a.parsed.ast d ↔
      d a.parsed.ast.state = Binary64.value (ModelExchange.derivative a.solve state)) ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before after : String, adapter = before ++
        (Runtime.function a.solve.prepareFMI3 InitializationCalls.signature).render ++ after) ∧
      (∃ before after : String, adapter = before ++
        (Runtime.function a.solve.prepareFMI3 InitializationExit.signature).render ++ after) ∧
      InitializationCalls.FunctionContract a.solve.prepareFMI3 sigs
        (Runtime.function a.solve.prepareFMI3 InitializationCalls.signature).render
        (Runtime.function a.solve.prepareFMI3 InitializationExit.signature).render ∧
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      InitializationCalls.PreparedContract a.solve.prepareFMI3 sigs pool ∧
      LiteralPreparation.EventPreparedContract a.solve.prepareFMI3 sigs pool ∧
      (∀ (firstBlock : Nat) (E : Type)
        (program : @CCalls.Events.Program (cInterface (pool.addresses firstBlock)) E),
        @CCalls.Events.Program.internal (cInterface (pool.addresses firstBlock)) E program =
          LiteralPreparation.program a.solve.prepareFMI3 sigs →
        @InitializationCalls.SourceExecutionContract (cInterface (pool.addresses firstBlock)) E a.parsed.ast program) := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready, _, _, events, _, _, _, _, _, initialization⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨enterBefore, enterAfter, enterLocated⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    InitializationCalls.signature initialization.enterMember
  obtain ⟨exitBefore, exitAfter, exitLocated⟩ := LiteralPreparation.rendered_member a.solve.prepareFMI3 sigs
    InitializationExit.signature initialization.exitMember
  have prepared := initialization.prepared pool made
  refine ⟨compiled, contract.numerical, derivative_value_source a.solve, sigs, pool, printed, grammar,
    ⟨enterBefore, enterAfter, printed ▸ enterLocated⟩, ⟨exitBefore, exitAfter, printed ▸ exitLocated⟩,
    initialization, made, prepared, events pool made, ?_⟩
  intro firstBlock E program same
  exact InitializationCalls.QuietExecutionContract.source_contract
    (interface := cInterface (pool.addresses firstBlock)) a.solve.prepareFMI3 program
    (prepared.quiet firstBlock E program same)

end Rumoca.FMI3
