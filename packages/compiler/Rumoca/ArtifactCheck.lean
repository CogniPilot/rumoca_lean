import Rumoca.Verified
import Lean

open _root_.Parser

/-! Trusted file-to-proposition adapter. It reads the two actual files itself,
constructs literals and a fixed theorem, and audits that theorem's dependencies.
No producer-supplied Lean commands, propositions, or audit text are executed.
File I/O and this small adapter belong to the explicit trusted boundary. -/
namespace Rumoca.ArtifactCheck
open Lean Elab Command

def check (source emitted grammar : String) (linkage : C.Linkage := .external) : CommandElabM Unit := do
  -- This fast check can only reject. Success still requires the kernel to
  -- check equality of the independently read literal in the fixed theorem.
  if grammar != Generated.source then
    throwError "actual EBNF source differs from the certified grammar"
  let .ok candidate := compile source | throwError "source compilation failed"
  if emitted != candidate.cSource linkage then
    throwError "actual numerical C differs from the certified compiler output"
  let m := candidate.parsed.ast
  let src := Syntax.mkStrLit source
  let out := Syntax.mkStrLit emitted
  let ebnf := Syntax.mkStrLit grammar
  let name := Syntax.mkStrLit m.name
  let state := Syntax.mkStrLit m.state
  let der := Syntax.mkStrLit m.derivativeName
  let ending := Syntax.mkStrLit m.endName
  let linkageTerm ← match linkage with
    | .external => `(term| C.Linkage.external)
    | .internal => `(term| C.Linkage.internal)
  let theoremName := `Rumoca.CheckedFiles.source_to_c
  let theoremId := mkIdent theoremName
  let nameId := mkIdent `Rumoca.CheckedFiles.source_model_name
  elabCommand (← `(command|
    theorem $nameId:ident (p : Parsed $src) : p.ast.name = $name := by
      let model : AST.Model := ⟨$name, $state, $der, $ending⟩
      let parsed : Parsed $src :=
        ⟨model.tokens, model, by rfl, parseTokens_complete model⟩
      have eq : p = parsed := Except.ok.inj ((parse_eq_parsed p).symm.trans (parse_eq_parsed parsed))
      exact congrArg (fun q => q.ast.name) eq))
  -- Native compilation supplies only a candidate AST. Every check below is
  -- subsequently kernel checked against the actual, independently read strings.
  elabCommand (← `(command|
    theorem $theoremId:ident : Generated.source = $ebnf ∧ ∃ a : Artifact $src,
        compile $src = .ok a ∧ ArtifactContract a $out $linkageTerm := by
      refine ⟨by rfl, ?_⟩
      let model : AST.Model := ⟨$name, $state, $der, $ending⟩
      let parsed : Parsed $src :=
        ⟨model.tokens, model, by rfl, parseTokens_complete model⟩
      have resolved : AST.Resolved model := ⟨by decide +kernel, by decide +kernel⟩
      let a : Artifact $src := ⟨parsed, Solve.lower (DAE.lower (Flat.lower model resolved))⟩
      have hc : compile $src = .ok a := by
        simp only [compile, parse_eq_parsed parsed]
        change (fun h : PLift (AST.Resolved model) =>
          (⟨parsed, Solve.lower (DAE.lower (Flat.lower model h.down))⟩ : Artifact $src)) <$>
            AST.resolve model = _
        rw [AST.resolve_complete model resolved]
        rfl
      exact ⟨a, compile_verified hc
        (by rw [emitted_text_is_unit a $linkageTerm]; decide +kernel)⟩))
  let axioms ← collectAxioms theoremName
  for dependency in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in file contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {axioms.toList}"

elab "verify_artifact_files" : command => do
  let some sourcePath ← IO.getEnv "RUMOCA_SOURCE" | throwError "RUMOCA_SOURCE is required"
  let some cPath ← IO.getEnv "RUMOCA_C" | throwError "RUMOCA_C is required"
  let grammarPath := (← IO.getEnv "RUMOCA_GRAMMAR").getD "packages/modelica-parser/grammar/Modelica.ebnf"
  check (← IO.FS.readFile sourcePath) (← IO.FS.readFile cPath) (← IO.FS.readFile grammarPath)

end Rumoca.ArtifactCheck
