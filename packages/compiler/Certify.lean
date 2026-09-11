import Rumoca.Compiler

open Rumoca

/-- The generator is untrusted: Lean checks the embedded source, emitted bytes,
source parsing, target grammar, and the complete execution/refinement contract. -/
def certificate (source actualC : String) (m : AST.Model) : String :=
  "import Rumoca\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 8000000\n\n" ++
  "namespace Rumoca.CheckedArtifact\n\n" ++
  s!"def source : String := {repr source}\n\n" ++
  s!"def emitted : String := {repr actualC}\n\n" ++
  s!"def model : AST.Model := ⟨{repr m.name}, {repr m.state}, {repr m.derivativeName}, {repr m.endName}⟩\n\n" ++
  "def parsed : Parsed source :=\n" ++
  "  ⟨model.tokens, model, by rfl, parseTokens_complete model⟩\n\n" ++
  "theorem resolved : AST.Resolved model := ⟨by decide +kernel, by decide +kernel⟩\n\n" ++
  "def artifact : Artifact source :=\n" ++
  "  Artifact.ofParsed parsed resolved\n\n" ++
  "theorem compilation_checked : compile source = .ok artifact := by\n" ++
  "  exact compile_eq_parsed parsed resolved\n\n" ++
  "theorem emitted_checked : artifact.cSource = emitted := by decide +kernel\n\n" ++
  "theorem c_grammar_checked : CSyntax.Denotes emitted\n" ++
  "    (CExecution.program artifact.solve) :=\n" ++
  "  (artifact_correct artifact emitted_checked).c_grammar\n\n" ++
  "theorem source_to_c : compile source = .ok artifact ∧ ArtifactContract artifact emitted :=\n" ++
  "  compile_verified compilation_checked emitted_checked\n\n" ++
  "theorem binary64_samples (x : Binary64.Value) (n : Nat) :\n" ++
  "    ExecutionContract (CExecution.program artifact.solve) model x n :=\n" ++
  "  source_to_c.2.execution x n\n\n" ++
  "#print axioms compilation_checked\n#print axioms emitted_checked\n" ++
  "#print axioms c_grammar_checked\n#print axioms source_to_c\n" ++
  "#print axioms binary64_samples\n\n" ++
  "end Rumoca.CheckedArtifact\n"

def main (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, cPath, proofPath] =>
    try
      let source ← IO.FS.readFile sourcePath
      let actualC ← IO.FS.readFile cPath
      match compile source with
      | .error e => IO.eprintln s!"{e.phase}: {e.message}"; return (1 : UInt32)
      | .ok a =>
        -- Even a mismatching C file produces a candidate whose proof must fail.
        IO.FS.writeFile proofPath (certificate source actualC a.parsed.ast)
        return (0 : UInt32)
    catch e => IO.eprintln (toString e); return (1 : UInt32)
  | _ =>
    IO.eprintln "usage: certify SOURCE.mo EMITTED.c CERTIFICATE.lean"
    return 2
