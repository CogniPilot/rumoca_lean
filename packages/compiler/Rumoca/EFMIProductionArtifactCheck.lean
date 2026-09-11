import Rumoca.EFMIArtifactCheck
import Rumoca.EFMIProductionProofs
import RumocaEFMI.Directory

/-! Fixed adapter extending the actual Algorithm Code theorem with the
independently read complete Production C member. It never evaluates producer
proof commands. The final root includes both grammars and both code files. -/
namespace Rumoca.EFMIProductionArtifactCheck
open Lean Elab Command

def check (input : EFMICheckOptions.Code) (c : String) : CommandElabM Unit := do
  let ⟨_, _, algorithm, grammar, algGrammar⟩ := input
  -- These comparisons can reject early; only the subsequent kernel theorem
  -- can authorize acceptance of the independently read files.
  let .ok candidate := compile input.input | throwError "source compilation failed"
  let .ok expected := candidate.productionSource | throwError "Production C lowering failed"
  if c != expected then throwError "actual Production C differs from the prepared Solve product"
  if algorithm != candidate.algorithmSource then throwError "actual GALEC differs from the source product"
  EFMIArtifactCheck.check input
  let inputTerm ← input.inputTerm
  let alg := Syntax.mkStrLit algorithm
  let out := Syntax.mkStrLit c
  let ebnf := Syntax.mkStrLit grammar
  let algEbnf := Syntax.mkStrLit algGrammar
  let algorithmRoot := mkIdent `Rumoca.CheckedEFMIFiles.source_to_algorithm
  let theoremName := `Rumoca.CheckedEFMIFiles.source_to_production
  let theoremId := mkIdent theoremName
  elabCommand (← `(command|
    theorem $theoremId:ident :
        Generated.source = $ebnf ∧ GALEC.Generated.source = $algEbnf ∧
        ∃ a : Artifact $inputTerm, compile $inputTerm = .ok a ∧ EFMI.ProductionContract a $alg $out := by
      obtain ⟨g₁, g₂, a, compiled, algorithm⟩ := $algorithmRoot:ident
      refine ⟨g₁, g₂, a, compiled, EFMI.production_correct a algorithm ?_⟩
      simp only [EFMI.production_source_is_unit, EFMI.CSyntax.render_unit]
      decide +kernel))
  let axioms ← collectAxioms theoremName
  for dependency in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in Production C contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {axioms.toList}"

elab "verify_efmi_production_files" : command => do
  let root : System.FilePath := ← EFMICheckOptions.required rumoca.efmi.root
  let algorithm ← IO.FS.readFile (root / EFMI.Directory.algorithmDirectory / EFMI.Directory.algorithmName)
  let c ← IO.FS.readFile (root / EFMI.Directory.productionDirectory / EFMI.Directory.productionName)
  check (← EFMICheckOptions.readCode algorithm) c

end Rumoca.EFMIProductionArtifactCheck
