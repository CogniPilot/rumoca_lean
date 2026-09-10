import Std

/-! Structured C construction for the ABI adapter. This is a syntax tree,
not a formalization of C types, memory or execution. The independently proved
numerical C language remains RumocaC. No arbitrary statement-text escape is
provided here. External type names come from the pinned FMI headers. -/
namespace Rumoca.CTree

inductive BinOp where | eq | ne | lt | le | gt | ge | and | or | add | sub
  deriving Repr
def BinOp.render : BinOp → String
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "&&" | .or => "||" | .add => "+" | .sub => "-"
inductive Expr where
  | id (name : String)
  | nat (value : Nat)
  | str (value : String)
  | bin (op : BinOp) (a b : Expr)
  | not (a : Expr)
  | deref (a : Expr)
  | address (a : Expr)
  | field (a : Expr) (name : String) (pointer : Bool := false)
  | index (a i : Expr)
  | call (fn : Expr) (args : List Expr)
  | cast (type : String) (value : Expr)
  | sizeof (type : String)
  deriving Repr

def quote (s : String) : String := "\"" ++ String.join (s.toUTF8.data.toList.map fun b =>
  if b.toNat = 34 then "\\\"" else if b.toNat = 92 then "\\\\"
  else if b.toNat ≥ 32 && b.toNat ≤ 126 then String.singleton (Char.ofNat b.toNat)
  else s!"\\{b.toNat / 64}{b.toNat % 64 / 8}{b.toNat % 8}") ++ "\""

def Expr.render : Expr → String
  | .id s => s | .nat n => toString n | .str s => quote s
  | .bin op a b => "(" ++ a.render ++ " " ++ op.render ++ " " ++ b.render ++ ")"
  | .not a => "(!" ++ a.render ++ ")"
  | .deref a => "(*" ++ a.render ++ ")"
  | .address a => "(&" ++ a.render ++ ")"
  | .field a n p => "(" ++ a.render ++ (if p then "->" else ".") ++ n ++ ")"
  | .index a i => a.render ++ "[" ++ i.render ++ "]"
  | .call f xs => f.render ++ "(" ++ String.intercalate ", " (xs.map Expr.render) ++ ")"
  | .cast t a => "((" ++ t ++ ")" ++ a.render ++ ")"
  | .sizeof t => "sizeof(" ++ t ++ ")"

inductive Stmt where
  | declare (type name : String) (value : Expr)
  | assign (target value : Expr)
  | eval (value : Expr)
  | ret (value : Option Expr)
  | branch (condition : Expr) (yes no : List Stmt)
  | whileLoop (condition : Expr) (body : List Stmt)
  deriving Repr

def Stmt.render (s : Stmt) (depth : Nat := 1) : String :=
  let indent := String.ofList (List.replicate (2 * depth) ' ')
  match s with
  | .declare t n e => indent ++ t ++ " " ++ n ++ " = " ++ e.render ++ ";\n"
  | .assign a b => indent ++ a.render ++ " = " ++ b.render ++ ";\n"
  | .eval e => indent ++ e.render ++ ";\n"
  | .ret none => indent ++ "return;\n"
  | .ret (some e) => indent ++ "return " ++ e.render ++ ";\n"
  | .branch c yes no =>
    indent ++ "if (" ++ c.render ++ ") {\n" ++
      String.join (yes.map fun x => x.render (depth + 1)) ++ indent ++ "}" ++
      (if no.isEmpty then "\n" else " else {\n" ++
        String.join (no.map fun x => x.render (depth + 1)) ++ indent ++ "}\n")
  | .whileLoop c body => indent ++ "while (" ++ c.render ++ ") {\n" ++
      String.join (body.map fun x => x.render (depth + 1)) ++ indent ++ "}\n"

structure Parameter where
  type : String
  name : String
  array : Bool := false
  deriving Repr
def Parameter.render (p : Parameter) : String := p.type ++ " " ++ p.name ++ if p.array then "[]" else ""

structure Signature where
  result : String
  name : String
  parameters : List Parameter
  deriving Repr
def Signature.render (s : Signature) : String := s.result ++ " " ++ s.name ++ "(" ++
  (if s.parameters.isEmpty then "void" else String.intercalate ", " (s.parameters.map Parameter.render)) ++ ")"

structure Function where
  signature : Signature
  body : List Stmt
  static : Bool := false
  deriving Repr
def Function.render (f : Function) : String :=
  (if f.static then "static " else "") ++ f.signature.render ++ " {\n" ++
    String.join (f.body.map fun s => s.render 1) ++ "}\n\n"

end Rumoca.CTree
