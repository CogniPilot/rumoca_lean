import Parser.Token

/-! EBNF syntax types, independent of the text reader and its implementation. -/
namespace Parser.EBNF

inductive Lexeme where
  | name (s : String)
  | text (s : String)
  | punct (c : Char)
  deriving Repr, BEq, DecidableEq

inductive Expr where
  | terminal (s : Symbol)
  | ref (name : String)
  | seq (a b : Expr)
  | alt (a b : Expr)
  | optional (a : Expr)
  | many (a : Expr)
  deriving Repr, BEq, DecidableEq, ReflBEq, LawfulBEq

abbrev Grammar := List (String × Expr)

end Parser.EBNF
