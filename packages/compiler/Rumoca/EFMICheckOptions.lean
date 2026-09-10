import Lean


/-! Explicit arguments to the fixed Lean checking entry points. The CLI passes
these as individual process arguments; no shell expansion, environment state
or producer-supplied Lean commands are used. -/
register_option rumoca.efmi.source : String := { defValue := "", descr := "Actual Modelica source file" }
register_option rumoca.efmi.root : String := { defValue := "", descr := "Prepared eFMI directory or archive" }
register_option rumoca.efmi.algorithm : String := { defValue := "", descr := "Standalone GALEC file" }
register_option rumoca.efmi.grammar : String :=
  { defValue := "packages/modelica-parser/grammar/Modelica.ebnf", descr := "Actual Modelica EBNF" }
register_option rumoca.efmi.galecGrammar : String :=
  { defValue := "packages/galec-parser/grammar/GALEC.ebnf", descr := "Actual GALEC EBNF" }

namespace Rumoca.EFMICheckOptions
open Lean Elab Command

structure Code where
  source : String
  algorithm : String
  grammar : String
  galecGrammar : String

def required (option : Lean.Option String) : CommandElabM String := do
  let value := option.get (← getOptions)
  if value.isEmpty then throwError "missing {option.name}; use rumoca verify-efmi or verify-algorithm --help"
  return value

def readCode (algorithm : String) : CommandElabM Code := do
  let options ← getOptions
  return {
    source := (← IO.FS.readFile (← required rumoca.efmi.source)), algorithm,
    grammar := (← IO.FS.readFile (rumoca.efmi.grammar.get options : String)),
    galecGrammar := (← IO.FS.readFile (rumoca.efmi.galecGrammar.get options : String)) }

end Rumoca.EFMICheckOptions
