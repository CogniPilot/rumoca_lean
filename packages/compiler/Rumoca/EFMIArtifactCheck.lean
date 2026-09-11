import Rumoca.EFMIProofs
import Rumoca.EFMICheckOptions

open _root_.Parser

/-! Trusted actual-file adapter for the new Algorithm Code member. It fixes
the proposition from independently read Modelica, GALEC and grammar files.
Producer-supplied commands or theorem statements are never executed. -/
namespace Rumoca.EFMIArtifactCheck
open Lean Elab Command

def check (input : EFMICheckOptions.Code) : CommandElabM Unit := do
  let ⟨_, source, emitted, grammar, algGrammar⟩ := input
  if grammar != Generated.source || algGrammar != GALEC.Generated.source then
    throwError "actual EBNF differs from its certified source"
  let .ok candidate := compile input.input | throwError "source compilation failed"
  let m := candidate.parsed.ast
  let src := Syntax.mkStrLit source
  let inputTerm ← input.inputTerm
  let out := Syntax.mkStrLit emitted
  let ebnf := Syntax.mkStrLit grammar
  let algEbnf := Syntax.mkStrLit algGrammar
  let name := Syntax.mkStrLit m.name
  let state := Syntax.mkStrLit m.state
  let der := Syntax.mkStrLit m.derivativeName
  let ending := Syntax.mkStrLit m.endName
  let theoremName := `Rumoca.CheckedEFMIFiles.source_to_algorithm
  let theoremId := mkIdent theoremName
  let modelId := mkIdent `Rumoca.CheckedEFMIFiles.source_ast
  let parsedId := mkIdent `Rumoca.CheckedEFMIFiles.source_parsed
  let modelNameId := mkIdent `Rumoca.CheckedEFMIFiles.source_model_name
  elabCommand (← `(command|
    def $modelId:ident : AST.Model := ⟨$name, $state, $der, $ending⟩))
  elabCommand (← `(command|
    def $parsedId:ident : Parsed $src :=
      ⟨($modelId).tokens, $modelId, by rfl, parseTokens_complete $modelId⟩))
  elabCommand (← `(command|
    theorem $modelNameId:ident (parsed : Parsed $src) : parsed.ast.name = $name := by
      have same : parsed = $parsedId :=
        Except.ok.inj ((parse_eq_parsed parsed).symm.trans (parse_eq_parsed $parsedId))
      exact congrArg (fun p : Parsed $src => p.ast.name) same))
  elabCommand (← `(command|
    theorem $theoremId:ident :
        Generated.source = $ebnf ∧ GALEC.Generated.source = $algEbnf ∧
        ∃ a : Artifact $inputTerm, compile $inputTerm = .ok a ∧ EFMI.AlgorithmContract a $out := by
      refine ⟨by rfl, by rfl, ?_⟩
      let model := $modelId
      let parsed := $parsedId
      have resolved : AST.Resolved model := ⟨by decide +kernel, by decide +kernel⟩
      let a : Artifact $inputTerm := Artifact.ofParsed $inputTerm parsed resolved
      have hc : compile $inputTerm = .ok a := compile_eq_parsed $inputTerm parsed resolved
      refine ⟨a, EFMI.compile_algorithm_verified hc ?_⟩
      change EFMI.renderAlgorithm a.algorithmCode = $out
      rw [EFMI.emission_is_unit]
      decide +kernel))
  let axioms ← collectAxioms theoremName
  for dependency in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in Algorithm Code contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {axioms.toList}"

elab "verify_efmi_algorithm_files" : command => do
  let algorithm ← IO.FS.readFile (← EFMICheckOptions.required rumoca.efmi.algorithm)
  check (← EFMICheckOptions.readCode algorithm)

end Rumoca.EFMIArtifactCheck
