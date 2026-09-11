import ModelicaParser.LocatedTotal
import RumocaC.Codegen

open _root_.Parser

namespace Rumoca

/-- Every artifact requires exact source locations and the lowering chain for
that same parse. Source provenance cannot be absent or supplied by reparsing. -/
structure Artifact (input : Source.InputRef) where
  located : LocatedParsed input.source
  solve : Solve.Model located.parsed.ast
  context_matches : solve.dae.flat.context = Provenance.Context.ofLocated input located

def Artifact.parsed (a : Artifact input) : Parsed input.source := a.located.parsed

def Artifact.target (a : Artifact source) : C.Module := C.lower a.solve
def Artifact.cSource (a : Artifact source) (linkage : C.Linkage := .external) : String :=
  C.render a.target linkage

def Artifact.ofLocated (input : Source.InputRef) (parsed : LocatedParsed input.source)
    (resolved : AST.Resolved parsed.parsed.ast) : Artifact input :=
  ⟨parsed, Solve.lower (DAE.lower (Flat.lower (Provenance.Context.ofLocated input parsed) resolved)), rfl⟩

/-- Total construction used by source-file certificates. The located frontend's
completeness proof justifies the actual attachment computation. -/
def Artifact.ofParsed (input : Source.InputRef) (parsed : Parsed input.source)
    (resolved : AST.Resolved parsed.ast) : Artifact input := Artifact.ofLocated input parsed.located resolved

def compile (input : Source.InputRef) : Except (Source.Diagnostic input.source) (Artifact input) := do
  let parsed ← parseLocated input.source
  let resolved ← parsed.resolve
  return Artifact.ofLocated input parsed resolved.down

/-- The located driver implements the same successful parse and resolution.
There is no additional location-success assumption. -/
theorem compile_eq_parsed (input : Source.InputRef) (parsed : Parsed input.source)
    (resolved : AST.Resolved parsed.ast) :
    compile input = .ok (Artifact.ofParsed input parsed resolved) := by
  simp only [compile, parsed.parseLocated_eq, bind, Except.bind]
  rw [LocatedParsed.resolve_complete _ resolved]
  rfl

theorem compile_complete (input : Source.InputRef) (m : AST.Model)
    (syntaxValid : Lexes input.source.toList m.tokens) (resolved : AST.Resolved m) :
    ∃ a, compile input = .ok a ∧ a.parsed.ast = m :=
  ⟨Artifact.ofParsed input (parsedOfSyntax input.source m syntaxValid) resolved,
    compile_eq_parsed input _ resolved, rfl⟩

end Rumoca
