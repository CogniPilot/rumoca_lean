import ModelicaParser.LocatedTotal
import RumocaC.Codegen

open _root_.Parser

namespace Rumoca

/-- Every artifact requires exact source locations and the lowering chain for
that same parse. Source provenance cannot be absent or supplied by reparsing. -/
structure Artifact (source : String) where
  located : LocatedParsed source
  solve : Solve.Model located.parsed.ast

def Artifact.parsed (a : Artifact source) : Parsed source := a.located.parsed

def Artifact.target (a : Artifact source) : C.Module := C.lower a.solve
def Artifact.cSource (a : Artifact source) (linkage : C.Linkage := .external) : String :=
  C.render a.target linkage

def Artifact.ofLocated (parsed : LocatedParsed source) (resolved : AST.Resolved parsed.parsed.ast) :
    Artifact source :=
  ⟨parsed, Solve.lower (DAE.lower (Flat.lower parsed.parsed.ast resolved))⟩

/-- Total construction used by source-file certificates. The located frontend's
completeness proof justifies the actual attachment computation. -/
def Artifact.ofParsed (parsed : Parsed source) (resolved : AST.Resolved parsed.ast) :
    Artifact source := Artifact.ofLocated parsed.located resolved

def compile (source : String) : Except (Source.Diagnostic source) (Artifact source) := do
  let parsed ← parseLocated source
  let resolved ← parsed.resolve
  return Artifact.ofLocated parsed resolved.down

/-- The located driver implements the same successful parse and resolution.
There is no additional location-success assumption. -/
theorem compile_eq_parsed (parsed : Parsed source) (resolved : AST.Resolved parsed.ast) :
    compile source = .ok (Artifact.ofParsed parsed resolved) := by
  simp only [compile, parsed.parseLocated_eq, bind, Except.bind]
  rw [LocatedParsed.resolve_complete _ resolved]
  rfl

theorem compile_complete (source : String) (m : AST.Model)
    (syntaxValid : Lexes source.toList m.tokens) (resolved : AST.Resolved m) :
    ∃ a, compile source = .ok a ∧ a.parsed.ast = m :=
  ⟨Artifact.ofParsed (parsedOfSyntax source m syntaxValid) resolved,
    compile_eq_parsed _ resolved, rfl⟩

end Rumoca
