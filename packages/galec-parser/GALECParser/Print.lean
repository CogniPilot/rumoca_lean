import GALECParser.AST

/-! GALEC text from a syntax tree, in one fixed layout: four-space nesting,
`method X` and `algorithm` on separate lines, section keywords alone on a line,
`", "` list separators and spaced binary operators. Parentheses are printed only
where the tree has a `parens` node. Printing is total and structural; it makes
no parsing or semantic claim. -/
namespace Rumoca.GALEC.Print
open _root_.Parser

mutual
  def expr : AST.Expr → String
    | .reference ref => reference ref
    | .literal spelling => spelling.text
    | .binary op left right => expr left ++ " " ++ op.text ++ " " ++ expr right
    | .parens body => "(" ++ expr body ++ ")"
    | .call callee arguments => callee.text ++ "(" ++ exprs arguments ++ ")"
    | .size ref axis => "size(" ++ reference ref ++ ", " ++ expr axis ++ ")"

  def exprs : List AST.Expr → String
    | [] => ""
    | first :: rest => expr first ++ separated rest

  def separated : List AST.Expr → String
    | [] => ""
    | next :: rest => ", " ++ expr next ++ separated rest

  def reference : AST.Reference → String
    | ⟨base, fields⟩ => component base ++ path fields

  def path : List AST.Component → String
    | [] => ""
    | next :: rest => "." ++ component next ++ path rest

  def component : AST.Component → String
    | ⟨name, []⟩ => name.text
    | ⟨name, first :: rest⟩ => name.text ++ "[" ++ exprs (first :: rest) ++ "]"
end

def range (start : AST.Expr) (step : Option AST.Expr) (stop : AST.Expr) : String :=
  match step with
  | none => expr start ++ ":" ++ expr stop
  | some step => expr start ++ ":" ++ expr step ++ ":" ++ expr stop

mutual
  def statement (indent : String) : AST.Statement → String
    | .assign target value => indent ++ reference target ++ " := " ++ expr value ++ ";\n"
    | .forLoop binder start step stop body =>
        indent ++ "for " ++ binder.text ++ " in " ++ range start step stop ++ " loop\n" ++
          statements (indent ++ "    ") body ++ indent ++ "end for;\n"

  def statements (indent : String) : List AST.Statement → String
    | [] => ""
    | first :: rest => statement indent first ++ statements indent rest
end

def kind : AST.Kind → String
  | .variable => ""
  | .input => "input "
  | .output => "output "
  | .constant => "constant "

def declaration (d : AST.Declaration) : String :=
  let extents := match d.extents with
    | [] => ""
    | first :: rest => "[" ++ exprs (first :: rest) ++ "]"
  "    " ++ kind d.kind ++ d.typeName.text ++ " " ++ d.name.text ++ extents ++ ";\n"

def declarations (ds : List AST.Declaration) : String :=
  String.join (ds.map declaration)

def method (m : AST.Method) : String :=
  "    method " ++ m.name.text ++ "\n    algorithm\n" ++ statements "        " m.body ++
    "    end " ++ m.endName.text ++ ";\n"

def block (b : AST.Block) : String :=
  "block " ++ b.name.text ++ "\n" ++ declarations b.publicDeclarations ++
    "protected\n" ++ declarations b.protectedDeclarations ++
    "public\n" ++ String.join (b.methods.map method) ++
    "end " ++ b.endName.text ++ ";\n"

end Rumoca.GALEC.Print
