import Rumoca.FMI3BuildProofs
import RumocaFMI3.VersionMetadata

/-! The actual version function, both XML files and immutable return bytes
share one compiled artifact and definition table. Instance/lifecycle state is
unrestricted. Native headers, byte layout and ABI remain explicit boundaries. -/
noncomputable section
namespace Rumoca.FMI3
open CMemory CTree CLiteral

/-- Every complete version call returns the zero-terminated version shared by
the actual model/build descriptions. The constructed literal objects remain
immutable, and the call leaves all heap cells unchanged. -/
theorem version_source (compiled : compile input = .ok a)
    (contract : SourceBuildContract a c description adapter metadata) :
    compile input = .ok a ∧ Version.MetadataContract metadata description "3.0" ∧
    ∃ sigs, ∃ pool : Pool (LiteralPreparation.excluded ++
        (LiteralPreparation.functions a.solve.prepareFMI3 sigs).flatMap functionNames),
      Runtime.render a.solve.prepareFMI3 sigs = adapter ∧
      AdapterPrinter.FunctionsContract a.solve.prepareFMI3 sigs adapter ∧
      (∃ before text after : String, adapter = before ++ text ++ after ∧
        Printer.FunctionTokenization RuntimePrinter.typedefs text
          (Runtime.function a.solve.prepareFMI3 Version.signature)) ∧
      LiteralPreparation.prepare a.solve.prepareFMI3 sigs = some pool ∧
      ∀ (before : Heap) (firstBlock : Nat) (signed : Bool), ∃ base,
        pool.addresses firstBlock "3.0" = some base ∧
        (∀ behavior, (@CCalls.Typed.machine (cInterface (pool.addresses firstBlock))
          (LiteralPreparation.program a.solve.prepareFMI3 sigs)).Behaves
          (.calling Version.signature.name [] (pool.install before firstBlock signed) .done) behavior ↔
          behavior = .terminates ⟨.pointer (some base), pool.install before firstBlock signed⟩) ∧
        Stored signed (pool.install before firstBlock signed) base "3.0" ∧
        (∀ index byte, (bytes "3.0")[index]? = some byte →
          readByte (pool.install before firstBlock signed) (base.index index) = some byte) := by
  obtain ⟨sigs, _, _, printed, _, grammar, _, _, _, ready, version, _⟩ := contract.adapter
  obtain ⟨pool, made⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member _ sigs _ version.member
  refine ⟨compiled, Version.metadata_correct _ contract.metadata contract.build,
    sigs, pool, printed, grammar, ⟨before, _, after, printed ▸ located, version.tokenization⟩,
    made, ?_⟩
  exact version.prepared pool made

end Rumoca.FMI3
