import Parser.Token

/-! GALEC frontend syntax, deliberately independent of profile IRs.
Names keep the original token, including its category. In particular, raw token
parsing must not silently turn a `Token.number` (also classified IDENT by the
shared token API) into an identifier. Scanner and resolution contracts remain
separate. Extents are source syntax, not inferred or enumerated tensor shapes.
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

inductive Visibility where
  | «public» | «protected»
  deriving Repr, DecidableEq

inductive Direction where
  | local | input | output
  deriving Repr, DecidableEq

inductive Variability where
  | variable | constant
  deriving Repr, DecidableEq

structure Declaration where
  visibility : Visibility
  direction : Direction
  variability : Variability
  typeName : Name
  extents : List Token
  name : Name
  deriving Repr, DecidableEq

def Declaration.rank (d : Declaration) : Nat := d.extents.length

structure Method where
  visibility : Visibility
  name : Name
  body : List Statement
  endName : Name
  deriving Repr

structure Block where
  name : Name
  declarations : List Declaration
  methods : List Method
  endName : Name
  deriving Repr

end Rumoca.GALEC.AST
