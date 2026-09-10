import ModelicaParser.Parser
import RumocaC.Codegen

open _root_.Parser

namespace Rumoca

/-- Each output is tied to the actual parsed source and its lowering chain. -/
structure Artifact (source : String) where
  parsed : Parsed source
  solve : Solve.Model parsed.ast

def Artifact.target (a : Artifact source) : C.Module := C.lower a.solve
def Artifact.cSource (a : Artifact source) : String := C.render a.target

def compile (source : String) : Except Diagnostic (Artifact source) := do
  let parsed ← parse source
  let resolved ← AST.resolve parsed.ast
  return ⟨parsed, Solve.lower (DAE.lower (Flat.lower parsed.ast resolved.down))⟩

theorem compile_complete (source : String) (m : AST.Model)
    (syntaxValid : Lexes source.toList m.tokens) (resolved : AST.Resolved m) :
    ∃ a, compile source = .ok a ∧ a.parsed.ast = m := by
  obtain ⟨p, hp, hm⟩ := parse_complete source m syntaxValid
  subst m
  refine ⟨⟨p, Solve.lower (DAE.lower (Flat.lower p.ast resolved))⟩, ?_, rfl⟩
  simp only [compile, hp]
  change (fun h : PLift (AST.Resolved p.ast) =>
    (⟨p, Solve.lower (DAE.lower (Flat.lower p.ast h.down))⟩ : Artifact source)) <$>
      AST.resolve p.ast = _
  rw [AST.resolve_complete p.ast resolved]
  rfl

end Rumoca
