import ModelicaParser.LocatedParser
import Parser.Provenance

/-! Source origins for the fixed AST action profile. Ranges are composed from
the actual parser's terminals, without searching for equal text. The caller
supplies the immutable input table and the checked file identity. -/
namespace Rumoca.Origins
open _root_.Parser
open _root_.Parser.Provenance

/-- Semantic source occurrences in the admitted unit model. -/
inductive Field where
  | model | modelName | declaration | stateName | equation
  | derivative | derivativeName | constant | endName
  deriving Repr, DecidableEq

def Field.index : Field → Fin 9
  | .model => 0 | .modelName => 1 | .declaration => 2 | .stateName => 3
  | .equation => 4 | .derivative => 5 | .derivativeName => 6 | .constant => 7 | .endName => 8

def span (parsed : LocatedParsed source) : Field → Source.Span source
  | .model => (parsed.fieldSpan 0).cover (parsed.fieldSpan 15)
  | .modelName => parsed.fieldSpan 1
  | .declaration => (parsed.fieldSpan 2).cover (parsed.fieldSpan 4)
  | .stateName => parsed.fieldSpan 3
  | .equation => (parsed.fieldSpan 6).cover (parsed.fieldSpan 12)
  | .derivative => (parsed.fieldSpan 6).cover (parsed.fieldSpan 9)
  | .derivativeName => parsed.fieldSpan 8
  | .constant => parsed.fieldSpan 11
  | .endName => parsed.fieldSpan 14

def site (inputs : Array Source.Input) (file : Fin inputs.size)
    (parsed : LocatedParsed inputs[file].source) (field : Field) : SourceRef inputs :=
  ⟨file, span parsed field⟩

def sites (inputs : Array Source.Input) (file : Fin inputs.size)
    (parsed : LocatedParsed inputs[file].source) : Array (SourceRef inputs) :=
  let occurrence := site inputs file parsed
  #[occurrence .model, occurrence .modelName, occurrence .declaration, occurrence .stateName,
    occurrence .equation, occurrence .derivative, occurrence .derivativeName,
    occurrence .constant, occurrence .endName]

/-- The reusable engine does not know Modelica fields or compiler lowering rules.
This frontend instantiates its source table; later stages append rule records. -/
def table (Rule : Type) (inputs : Array Source.Input) (file : Fin inputs.size)
    (parsed : LocatedParsed inputs[file].source) : Table (SourceRef inputs) Rule :=
  Table.fromSources (sites inputs file parsed)

def ref (Rule : Type) (inputs : Array Source.Input) (file : Fin inputs.size)
    (parsed : LocatedParsed inputs[file].source) (field : Field) :
    Ref (table Rule inputs file parsed) :=
  ⟨⟨field.index.val, by simp [table, Table.fromSources, sites]⟩⟩

end Rumoca.Origins
