import RumocaEFMI.ProductionCode
import Parser.Scanner
import RumocaC.Identifier

open _root_.Parser

/-! Independent concrete grammar for the straight-line Production C profile.
Printer correctness is proved against these tokens and character rules;
no executable C reader is needed. The fixed preamble remains an explicitly
reviewed preprocessing boundary. -/
namespace Rumoca.EFMI.CSyntax

set_option maxRecDepth 10000

def identifier (s : String) : Bool :=
  CIdentifier.valid ["Model", "EfmiReal", "EfmiStatus", "int32_t"] s

inductive Atom where
  | variable (name : String)
  | member (base field : String)
  | zero | one
  deriving Repr, BEq, DecidableEq

def Atom.valid : Atom → Bool
  | .variable n => identifier n
  | .member b f => identifier b && identifier f
  | .zero | .one => true

def Atom.tokens : Atom → List String
  | .variable n => [n]
  | .member b f => ["(", b, "->", f, ")"]
  | .zero => ["(", "(", "double", ")", "0", ")"]
  | .one => ["(", "(", "double", ")", "1", ")"]

def Atom.tree : Atom → CTree.Expr
  | .variable n => .id n
  | .member b f => .field (.id b) f true
  | .zero => .cast "double" (.nat 0)
  | .one => .cast "double" (.nat 1)

inductive Term where
  | atom (a : Atom)
  | add (a b : Atom)
  deriving Repr, BEq, DecidableEq

def Term.valid : Term → Bool
  | .atom a => a.valid
  | .add a b => a.valid && b.valid
def Term.tokens : Term → List String
  | .atom a => a.tokens
  | .add a b => ["("] ++ a.tokens ++ ["+"] ++ b.tokens ++ [")"]
def Term.tree : Term → CTree.Expr
  | .atom a => a.tree
  | .add a b => .bin .add a.tree b.tree

inductive Statement where
  | declare (name : String) (value : Term)
  | assign (target : Atom) (value : Term)
  deriving Repr, BEq, DecidableEq

def Statement.valid : Statement → Bool
  | .declare n e => identifier n && e.valid
  | .assign (.variable n) e => identifier n && e.valid
  | .assign (.member b f) e => identifier b && identifier f && e.valid
  | .assign _ _ => false
def Statement.tokens : Statement → List String
  | .declare n e => ["double", n, "="] ++ e.tokens ++ [";"]
  | .assign a e => a.tokens ++ ["="] ++ e.tokens ++ [";"]
def Statement.tree : Statement → CTree.Stmt
  | .declare n e => .declare "double" n e.tree
  | .assign a e => .assign a.tree e.tree

structure Function where
  name : String
  parameter : String
  statements : List Statement
  deriving Repr, BEq, DecidableEq

def Function.valid (f : Function) : Bool :=
  identifier f.name && identifier f.parameter && f.statements.all Statement.valid
def Function.tokens (f : Function) : List String :=
  ["EfmiStatus", f.name, "(", "Model", "*", f.parameter, ")", "{"] ++
  f.statements.flatMap Statement.tokens ++ ["return", "0", ";", "}"]
def Function.tree (f : Function) : CTree.Function :=
  ⟨⟨"EfmiStatus", f.name, [⟨"Model *", f.parameter, false⟩]⟩,
    f.statements.map Statement.tree ++ [.ret (some (.nat 0))], false⟩

structure Program where
  startup : Function
  recalibrate : Function
  doStep : Function
  deriving Repr, BEq, DecidableEq

def Program.valid (p : Program) : Bool := p.startup.valid && p.recalibrate.valid && p.doStep.valid
def Program.tokens (p : Program) : List String :=
  p.startup.tokens ++ p.recalibrate.tokens ++ p.doStep.tokens
def Program.tree (p : Program) : Production.Module :=
  ⟨p.startup.tree, p.recalibrate.tree, p.doStep.tree⟩

def config : Scanner.Config where
  wordStart := identStart
  wordRest := identRest
  numberRest := fun c => identRest c || c == '.'
  classify := Token.literal
  single := fun c => ['(', ')', '{', '}', '*', ';', '=', '+'].contains c
  pair := fun c => if c == '-' then some '>' else none

def Denotes (source : String) (p : Program) : Prop :=
  p.valid = true ∧ ∃ body, source.toList = Production.preamble.toList ++ body ∧
    Scanner.Lexes config body (p.tokens.map Token.literal)

end Rumoca.EFMI.CSyntax
