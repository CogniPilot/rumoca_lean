import Std

namespace Parser

inductive Symbol where
  | ident
  | literal (text : String)
  deriving Repr, BEq, DecidableEq

inductive Token where
  | ident (name : String)
  | literal (text : String)
  deriving Repr, BEq, DecidableEq

def Token.symbol : Token → Symbol
  | .ident _ => .ident
  | .literal s => .literal s

/-- Character offsets, not UTF-8 byte offsets. -/
structure Diagnostic where
  phase : String
  offset : Nat
  message : String
  deriving Repr, BEq

instance : ToString Diagnostic where
  toString d := s!"{d.phase} at character {d.offset}: {d.message}"

def asciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def identStart (c : Char) : Bool := asciiLetter c || c == '_'
def identRest (c : Char) : Bool := identStart c || c.isDigit
def asciiSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r' || c == '\n'

def Token.text : Token → String
  | .ident s | .literal s => s

end Parser
