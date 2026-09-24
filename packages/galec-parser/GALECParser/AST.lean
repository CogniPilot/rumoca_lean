import Parser.Token

/-! GALEC frontend syntax.
Names keep the original token, including its category. In particular, raw token
parsing must not silently turn a `Token.number` (also classified IDENT by the
shared token API) into an identifier. Scanner and resolution contracts remain
separate. Declaration extents are unevaluated source expressions (G-2
constant dimensions), not inferred or enumerated tensor shapes.
Computed reference indices belong to each path component. Loop bounds remain
unresolved expressions; their representation does not establish boundedness. -/
namespace Rumoca.GALEC.AST
open _root_.Parser

abbrev Name := Token

mutual
  inductive Expr where
    | reference (ref : Reference)
    | literal (spelling : Token)
    | binary (operator : Token) (left right : Expr)
    | parens (body : Expr)
    | call (callee : Name) (arguments : List Expr)
    | size (ref : Reference) (axis : Expr)
    deriving Repr

  structure Reference where
    base : Component
    fields : List Component
    deriving Repr

  structure Component where
    name : Name
    indices : List Expr
    deriving Repr
end

/-- Construct an unindexed path without discarding any parsed indices. -/
def Reference.unindexed (base : Name) (fields : List Name) : Reference :=
  ⟨⟨base, []⟩, fields.map (fun name => ⟨name, []⟩)⟩

inductive Statement where
  | assign (target : Reference) (value : Expr)
  | forLoop (binder : Name) (start : Expr) (step : Option Expr) (stop : Expr)
      (body : List Statement)
  deriving Repr

/-- The block section containing a declaration. -/
inductive Visibility where
  | «public» | «protected»
  deriving Repr, DecidableEq

/-- Declaration kind. The grammar makes a direction and `constant` exclusive;
a declaration with neither is a variable. -/
inductive Kind where
  | variable | input | output | constant
  deriving Repr, DecidableEq

structure Declaration where
  kind : Kind
  typeName : Name
  extents : List Expr
  name : Name
  deriving Repr

def Declaration.rank (d : Declaration) : Nat := d.extents.length

structure Method where
  name : Name
  body : List Statement
  endName : Name
  deriving Repr

/-- The two declaration sections exactly as written: the leading (public)
section before `protected`, then the protected section. -/
structure Block where
  name : Name
  publicDeclarations : List Declaration
  protectedDeclarations : List Declaration
  methods : List Method
  endName : Name
  deriving Repr

/-- All declarations in source order, each paired with its section. -/
def Block.declarations (b : Block) : List (Visibility × Declaration) :=
  b.publicDeclarations.map (.public, ·) ++ b.protectedDeclarations.map (.protected, ·)

end Rumoca.GALEC.AST
