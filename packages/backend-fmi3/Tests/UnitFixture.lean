import RumocaCore.Solve.FMI3

/-! Shared, named in-memory Modelica input for the existing FMI execution
controls. The same checked parser/location path supplies their mandatory IR
origins; no hand-built span or unlocated compiler constructor is used. -/
namespace Rumoca.FMI3.UnitFixture

def source : AST.Model := ⟨"M", "x", "x", "M"⟩

def input : Parser.Source.InputRef :=
  .single "rumoca-check:/fmi3/M.mo" "model M Real x; equation der(x) = 1; end M;"

def parsed : Parsed input.source :=
  ⟨source.tokens, source, by rfl, parseTokens_complete source⟩

def prepared : Solve.FMI3Model source :=
  (Solve.lower (DAE.lower
    (Flat.lower (Provenance.Context.ofLocated input parsed.located) ⟨rfl, rfl⟩))).prepareFMI3

end Rumoca.FMI3.UnitFixture
