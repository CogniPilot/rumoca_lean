import Rumoca.EFMITensorArchiveProofs
import Rumoca.EFMICheckOptions

open _root_.Parser

/-! Trusted actual-file adapter for the tensor square Algorithm Code member. It
fixes the proposition from independently read Modelica, GALEC and grammar files,
compiles the source through the array/tensor path (`compileTensor`), and binds the
pinned tensor square Algorithm Code to the parsed square profile. Producer-supplied
commands or theorem statements are never executed. -/
namespace Rumoca.EFMITensorArtifactCheck
open Lean Elab Command

def check (input : EFMICheckOptions.Code) : CommandElabM Unit := do
  let ⟨_, source, emitted, grammar, algGrammar⟩ := input
  if grammar != Generated.source || algGrammar != GALEC.Generated.source then
    throwError "actual EBNF differs from its certified source"
  let .ok _candidate := compileTensor input.input | throwError "tensor source compilation failed"
  if emitted != EFMI.tensorUnitSource then
    throwError "actual tensor Algorithm Code differs from the pinned tensor square profile"
  let inputTerm ← input.inputTerm
  let src := Syntax.mkStrLit source
  let out := Syntax.mkStrLit emitted
  let ebnf := Syntax.mkStrLit grammar
  let algEbnf := Syntax.mkStrLit algGrammar
  let theoremName := `Rumoca.CheckedTensorEFMIFiles.source_to_algorithm
  let theoremId := mkIdent theoremName
  elabCommand (← `(command|
    theorem $theoremId:ident :
        Generated.source = $ebnf ∧ GALEC.Generated.source = $algEbnf ∧
        ∃ a : TensorArtifact $inputTerm, compileTensor $inputTerm = .ok a ∧
          TensorAlgorithmContract a $out := by
      refine ⟨by rfl, by rfl, ?_⟩
      let parsed : ArrayProfile.Parsed $src :=
        ⟨squareAst.tokens, squareAst, by rfl,
          ParserActions.parseTokens_complete ArrayProfile.actions squareAst⟩
      let a : TensorArtifact $inputTerm :=
        TensorArtifact.ofParsed $inputTerm parsed squareAst_resolved
      have hc : compileTensor $inputTerm = .ok a :=
        compileTensor_eq_parsed $inputTerm parsed squareAst_resolved
      refine ⟨a, hc, ?_⟩
      have hast : a.prepared.parsed.parsed.ast = squareAst := rfl
      exact tensor_algorithm_correct a hast (by decide +kernel)))
  let axioms ← collectAxioms theoremName
  for dependency in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in tensor Algorithm Code contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {axioms.toList}"

elab "verify_tensor_efmi_algorithm_files" : command => do
  let algorithm ← IO.FS.readFile (← EFMICheckOptions.required rumoca.efmi.algorithm)
  check (← EFMICheckOptions.readCode algorithm)

end Rumoca.EFMITensorArtifactCheck
