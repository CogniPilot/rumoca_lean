import Rumoca.FMI3BuildProofs
import RumocaFMI3.CountMetadata
import RumocaFMI3.CountPool

/-! Source/Solve, actual adapter functions and actual XML share the count
contract. Native headers, layout, enabled callbacks and machine compilation
remain outside these authored typed-C execution guarantees. -/
noncomputable section
namespace Rumoca.FMI3
open CMemory CTree CLiteral
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

/-- Both count functions return the scalar metadata's counts, with the state
count equal to the same compiled Solve IVP's volume. Every behavior terminates
with exactly the described store; all other cells are retained. -/
theorem counts_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) (events : Bool)
    (heap : Heap) (p buffer : Address) (kind : Kind) (mode : Mode) (old : Option Value)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getCounts kind mode)
    (storage : heap buffer = some ⟨.size, true, old⟩) :
    compile input = .ok a ∧ CountMetadata.Contract a.solve.prepareFMI3 metadata ∧
    ∃ sigs,
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before text after : String, adapter = before ++ text ++ after ∧
        Printer.FunctionTokenization RuntimePrinter.typedefs text
          (Runtime.function a.solve.prepareFMI3 (CountQueries.signature events))) ∧
      (∀ behavior, (CCalls.Typed.machine (LiteralPreparation.program a.solve.prepareFMI3 sigs)).Behaves
        (.calling (CountQueries.signature events).name (CountQueries.arguments (some p) (some buffer))
          heap .done) behavior ↔
        behavior = .terminates ⟨.integer 0, CountQueries.written events heap buffer⟩) ∧
      load (CountQueries.written events heap buffer) buffer =
        some (.integer (if events then 0 else a.solve.prepareFMI3.problem.stateShape.volume)) ∧
      (∀ q, q ≠ buffer → CountQueries.written events heap buffer q = heap q) := by
  obtain ⟨sigs, unique, _, printed, _, grammar, _, _, queries, _, _⟩ := contract.adapter
  have query := queries static events
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member _ sigs _ query.member
  refine ⟨compiled, CountMetadata.artifact_counts _ _ contract.metadata, sigs, printed, grammar,
    ⟨before, _, after, printed ▸ located, query.tokenization⟩,
    query.successful heap p buffer kind mode old hk hm allowed storage, ?_, CountQueries.frame events heap buffer⟩
  cases events <;> exact CountQueries.stored_count _ heap buffer

omit static in
/-- Actual-byte and metadata binding with nonempty, constructed static storage
for both rejected count calls. No literal address is supplied by the caller.
The fresh-block premise describes allocation in the symbolic memory model. -/
theorem counts_failure_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ CountMetadata.Contract a.solve.prepareFMI3 metadata ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      ∀ (events missing : Bool) (before : Heap) (firstBlock : Nat) (signed : Bool),
        (∀ entry ∈ pool.entries, ∀ address,
          address.block = firstBlock + entry.slot → before address = none) →
        ∀ (p : Address) (buffer : Option Address) (kind : Kind) (mode : Mode) (logger : Option Address),
          load before (p.member "kind") = some (.integer kind.code) →
          before (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
          load before (p.member "logger") = some (.pointer logger) →
          load before (p.member "logging") = some (.integer 0) →
          CountQueries.FailureCondition missing kind mode buffer →
          (∀ behavior, (@CCalls.Typed.machine (cInterface (pool.addresses firstBlock))
            (LiteralPreparation.program a.solve.prepareFMI3 sigs)).Behaves
            (.calling (CountQueries.signature events).name (CountQueries.arguments (some p) buffer)
              (pool.install before firstBlock signed) .done) behavior ↔
            behavior = .terminates ⟨.integer 3,
              LifecycleBodies.writeMode (pool.install before firstBlock signed) p .terminated⟩) ∧
          (∀ q, q ≠ p.member "mode" →
            LifecycleBodies.writeMode (pool.install before firstBlock signed) p .terminated q =
              pool.install before firstBlock signed q) ∧
          Valid (pool.addresses firstBlock) signed
            (LifecycleBodies.writeMode (pool.install before firstBlock signed) p .terminated) := by
  obtain ⟨sigs, unique, _, printed, _, grammar, _, _, queries, ready, _⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  refine ⟨compiled, CountMetadata.artifact_counts _ _ contract.metadata, sigs, pool,
    printed, grammar, made, ?_⟩
  intro events missing before firstBlock signed fresh p buffer kind mode logger hk hm hl hg condition
  exact CountQueries.prepared_failure _ sigs made unique events missing
    (CountQueries.FunctionContract.member (static := ⟨fun _ => none⟩)
      (queries ⟨fun _ => none⟩ events)) before firstBlock signed fresh p buffer kind mode logger
    hk hm hl hg condition

end Rumoca.FMI3
