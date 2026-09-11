import RumocaC.StatementOrigins

namespace Rumoca.CTree
open _root_.Parser.Provenance (Table)

/-- The parameter root includes its scalar/array declaration form. -/
structure Parameter.Origins (table : Table Site Rule) (_parameter : Parameter) where
  declaration : Origin table
  typeName : Origin table
  name : Origin table

structure Signature.Origins (table : Table Site Rule) (signature : Signature) where
  declaration : Origin table
  resultType : Origin table
  name : Origin table
  parameters : OriginList (Parameter.Origins table) signature.parameters

/-- The function root covers its definition, including storage-class policy.
Both the signature and every body occurrence require complete annotations. -/
structure Function.Origins (table : Table Site Rule) (function : Function) where
  definition : Origin table
  signature : Signature.Origins table function.signature
  body : OriginList (Stmt.Origins table) function.body

def Parameter.Origins.Every (origins : Parameter.Origins table parameter)
    (check : Origin table → Prop) : Prop :=
  check origins.declaration ∧ check origins.typeName ∧ check origins.name

def Parameter.Origins.EveryList (check : Origin table → Prop) :
    OriginList (Parameter.Origins table) parameters → Prop
  | .nil => True
  | .cons head tail => head.Every check ∧ EveryList check tail

def Signature.Origins.Every (origins : Signature.Origins table signature)
    (check : Origin table → Prop) : Prop :=
  check origins.declaration ∧ check origins.resultType ∧ check origins.name ∧
    Parameter.Origins.EveryList check origins.parameters

def Function.Origins.Every (origins : Function.Origins table function)
    (check : Origin table → Prop) : Prop :=
  check origins.definition ∧ origins.signature.Every check ∧ Stmt.Origins.EveryList check origins.body

end Rumoca.CTree
