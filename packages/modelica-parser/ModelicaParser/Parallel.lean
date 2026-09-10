import ModelicaParser.LocatedParser
import Parser.Parallel

open _root_.Parser

namespace Rumoca.Parallel

/-- A snapshot keeps file identity outside local byte ranges. Two files with
identical text remain distinct entries. No hash uniqueness assumption is used. -/
structure Input where
  name : String
  source : String

structure Result where
  input : Input
  parsed : Except (Parser.Source.Diagnostic input.source) (LocatedParsed input.source)
  correct : parsed = Rumoca.parseLocated input.source

def parseOne (input : Input) : Result := ⟨input, Rumoca.parseLocated input.source, rfl⟩

def parse (jobs : Nat) (inputs : List Input) : List Result := Parser.Parallel.map jobs parseOne inputs

theorem parse_eq_sequential (jobs : Nat) (inputs : List Input) :
    parse jobs inputs = inputs.map parseOne := Parser.Parallel.map_eq _ _ _

theorem parse_input_order (jobs : Nat) (inputs : List Input) :
    (parse jobs inputs).map (·.input) = inputs := by
  simp [parse_eq_sequential, List.map_map, Function.comp_def, parseOne]

theorem Result.source_sound (r : Result) (p : LocatedParsed r.input.source)
    (_h : r.parsed = .ok p) :
    Rumoca.parse r.input.source = .ok p.parsed := p.erases

end Rumoca.Parallel
