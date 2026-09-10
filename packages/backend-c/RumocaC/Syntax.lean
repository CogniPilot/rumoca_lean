import RumocaC.Codegen
import Parser.Token

open _root_.Parser

/-! An independent concrete C grammar for the emitted function profile.
The fixed header selects the target ABI. Function syntax and expressions have declarative lexical/token rules.
Structural printer theorems connect rendered text to this grammar;
no executable C reader is needed. -/
namespace Rumoca.CSyntax

def numberRest (c : Char) : Bool := identRest c || c == '.'
def punctuation (c : Char) : Bool := ['(', ')', '{', '}', ';', '+', '=', '-', ','].contains c
inductive Lexes : List Char → List String → Prop where
  | nil : Lexes [] []
  | space : asciiSpace c = true → Lexes cs ts → Lexes (c :: cs) ts
  | word : asciiSpace c = false → identStart c = true →
      Lexes (cs.dropWhile identRest) ts →
      Lexes (c :: cs) (String.ofList (c :: cs.takeWhile identRest) :: ts)
  | number : asciiSpace c = false → identStart c = false → c.isDigit = true →
      Lexes (cs.dropWhile numberRest) ts →
      Lexes (c :: cs) (String.ofList (c :: cs.takeWhile numberRest) :: ts)
  | ne : Lexes cs ts → Lexes ('!' :: '=' :: cs) ("!=" :: ts)
  | punct : asciiSpace c = false → identStart c = false → c.isDigit = false →
      (c == '!') = false → punctuation c = true → Lexes cs ts →
      Lexes (c :: cs) (String.singleton c :: ts)

def exprTokens : C.Expr → List String
  | .one => ["1.0"]
  | .arg => ["x"]
  | .add a b => ["("] ++ exprTokens a ++ ["+"] ++ exprTokens b ++ [")"]

structure Program where
  rhs : C.Expr
  step : C.Expr
  sample : C.Expr
  deriving Repr, BEq, DecidableEq

def fromTarget (m : C.Module) : Program := ⟨m.rhs, m.step, m.step⟩

/-- Independent declaration specifiers, with C11 internal linkage for `static`. -/
def linkageTokens : C.Linkage → List String
  | .external => []
  | .internal => ["static", "inline"]

def rhsPrefix (linkage : C.Linkage := .external) : List String :=
  linkageTokens linkage ++ ["double", "rumoca_rhs", "(", "void", ")", "{", "return"]
def stepPrefix (linkage : C.Linkage := .external) : List String :=
  [";", "}"] ++ linkageTokens linkage ++ ["double", "rumoca_step", "(", "double", "x", ")", "{", "return"]
def samplePrefix (linkage : C.Linkage := .external) : List String :=
  [";", "}"] ++ linkageTokens linkage ++ ["double", "rumoca_sample", "(", "double", "x", ",", "uint64_t", "n", ")", "{",
   "while", "(", "n", "!=", "0", ")", "{", "x", "="]
def sampleSuffix : List String :=
  [";", "n", "=", "n", "-", "UINT64_C", "(", "1", ")", ";", "}", "return", "x", ";", "}"]

def Program.tokens (p : Program) (linkage : C.Linkage := .external) : List String :=
  rhsPrefix linkage ++ exprTokens p.rhs ++ stepPrefix linkage ++ exprTokens p.step ++
    samplePrefix linkage ++ exprTokens p.sample ++ sampleSuffix

/-- Declarative membership in the admitted C text grammar, including its ABI header. -/
def Denotes (source : String) (p : Program) (linkage : C.Linkage := .external) : Prop :=
  ∃ body, source.toList = C.preamble.toList ++ body ∧ Lexes body (p.tokens linkage)

end Rumoca.CSyntax
