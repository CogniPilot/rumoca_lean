import RumocaCore.Provenance.Source
import RumocaCore.Initialization.Scalar

namespace Rumoca.Flat
open _root_.Parser.Provenance (Ref)

/-- Pure expressions describe meaning. Their compiler occurrences below require
an origin for each operator and each resolved reference. -/
inductive Expr where
  | der (state : Fin 1)
  | one
  deriving Repr, BEq, DecidableEq

inductive Expr.Origins (table : Provenance.Table context) : Expr → Type where
  | der (operator reference : Ref table) : Origins table (.der state)
  | one (literal : Ref table) : Origins table .one

def Expr.Origins.root : Expr.Origins table expr → Ref table
  | .der operator _ => operator
  | .one literal => literal

def Expr.Origins.reference : Expr.Origins table (.der state) → Ref table
  | .der _ reference => reference

/-- Correspondence to the exact source occurrences is stronger than merely
having valid, in-bounds origin references. -/
def Expr.Origins.SourceFields {context : Provenance.Context source}
    {table : Provenance.Table context} : {expr : Expr} → Expr.Origins table expr → Prop
  | .der _, .der operator reference =>
      table.get operator = .source (context.site .derivative) ∧
      table.get reference = .source (context.site .derivativeName)
  | .one, .one literal => table.get literal = .source (context.site .constant)

private theorem Expr.Origins.fields_cast (origins : Expr.Origins table expr)
    (equal : expr = other) (fields : origins.SourceFields) :
    (equal ▸ origins).SourceFields := by cases equal; exact fields

private theorem Expr.Origins.der_source {context : Provenance.Context source}
    {table : Provenance.Table context} (origins : Expr.Origins table (.der state))
    (fields : origins.SourceFields) :
    table.get origins.root = .source (context.site .derivative) ∧
    table.get origins.reference = .source (context.site .derivativeName) := by
  cases origins
  exact fields

private theorem Expr.Origins.one_source {context : Provenance.Context source}
    {table : Provenance.Table context} (origins : Expr.Origins table expr)
    (equal : expr = .one) (fields : origins.SourceFields) :
    table.get origins.root = .source (context.site .constant) := by
  cases equal
  cases origins
  exact fields

structure Origins (context : Provenance.Context source) (lhs rhs : Expr) where
  table : Provenance.Table context
  model : Ref table
  declaration : Ref table
  state : Ref table
  equation : Ref table
  left : Expr.Origins table lhs
  right : Expr.Origins table rhs
  model_source : table.get model = .source (context.site .model)
  declaration_source : table.get declaration = .source (context.site .declaration)
  state_source : table.get state = .source (context.site .stateName)
  equation_source : table.get equation = .source (context.site .equation)
  left_source : left.SourceFields
  right_source : right.SourceFields

def origins (context : Provenance.Context source) : Origins context (.der 0) .one where
  table := context.origins
  model := context.ref .model
  declaration := context.ref .declaration
  state := context.ref .stateName
  equation := context.ref .equation
  left := .der (context.ref .derivative) (context.ref .derivativeName)
  right := .one (context.ref .constant)
  model_source := context.lookup .model
  declaration_source := context.lookup .declaration
  state_source := context.lookup .stateName
  equation_source := context.lookup .equation
  left_source := ⟨context.lookup .derivative, context.lookup .derivativeName⟩
  right_source := context.lookup .constant

structure Model (source : AST.Model) where
  context : Provenance.Context source
  resolved : AST.Resolved source
  lhs : Expr
  rhs : Expr
  lhs_source : lhs = .der 0
  rhs_source : rhs = .one
  origins : Origins context lhs rhs
  /-- No initialization modifiers are admitted by the current AST. -/
  initialization : Initialization.Settings Nat
  initialization_source : initialization = ⟨none, none, false⟩

def lower (context : Provenance.Context source) (h : AST.Resolved source) : Model source :=
  ⟨context, h, .der 0, .one, rfl, rfl, origins context, ⟨none, none, false⟩, rfl⟩

/-- The initialization settings refer to the required declaration origin, even
when binding/start/fixed modifiers are absent. -/
def Model.initializationOrigin (model : Model source) : Ref model.origins.table :=
  model.origins.declaration

def Model.derivativeOrigins (model : Model source) :
    Expr.Origins model.origins.table (.der 0) := model.lhs_source ▸ model.origins.left

theorem Model.derivative_source (model : Model source) :
    model.origins.table.get model.derivativeOrigins.root =
      .source (model.context.site .derivative) ∧
    model.origins.table.get model.derivativeOrigins.reference =
      .source (model.context.site .derivativeName) :=
  model.derivativeOrigins.der_source
    (model.origins.left.fields_cast model.lhs_source model.origins.left_source)

theorem Model.literal_source (model : Model source) :
    model.origins.table.get model.origins.right.root =
      .source (model.context.site .constant) :=
  model.origins.right.one_source model.rhs_source model.origins.right_source

theorem Model.initialization_origin (model : Model source) :
    model.origins.table.get model.initializationOrigin =
      .source (model.context.site .declaration) := model.origins.declaration_source

end Rumoca.Flat
