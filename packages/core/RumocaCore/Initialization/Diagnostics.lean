import RumocaCore.IR
import ModelicaParser.LocatedParser

/-! Shared compiler/LSP notices for the completed unit initialization.
These are nonfatal diagnostics; transport chooses warning severity. -/
namespace Rumoca.Initialization

def Notice.message (notice : Notice) (state : String) (initial : Nat) : String :=
  match notice with
  | .fallbackUsed => s!"No start value is specified for {state}; using the Modelica Real fallback 0."
  | .unfixedStartSelected =>
      s!"Selected default initial condition {state} = {initial}; the source does not fix the initial state."

def diagnostics (plan : Plan Nat) (state : String) (span : Parser.Source.Span source) :
    List (Parser.Source.Diagnostic source) :=
  plan.notices.map fun notice => ⟨"initialization", span, notice.message state plan.initial, []⟩

def forModel (input : Parser.Source.InputRef) (parsed : LocatedParsed input.source)
    (resolved : AST.Resolved parsed.parsed.ast) : List (Parser.Source.Diagnostic input.source) :=
  let context := Provenance.Context.ofLocated input parsed
  let solve := Solve.lower (DAE.lower (Flat.lower context resolved))
  diagnostics solve.initial parsed.parsed.ast.state (parsed.fieldSpan 3)

end Rumoca.Initialization
