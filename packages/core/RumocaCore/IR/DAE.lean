import RumocaCore.IR.Flat
import Parser.ProvenanceExtension

namespace Rumoca.DAE
open _root_.Parser.Provenance (Ref Node TracesTo)

/-- Appendix B coordinates replace source temporal syntax. -/
inductive Expr where
  | derivative (slot : Fin 1)
  | one
  | sub (left right : Expr)
  deriving Repr, BEq, DecidableEq

def lowerExpr : Flat.Expr → Expr
  | .der state => .derivative state
  | .one => .one

inductive Expr.Origins (table : Provenance.Table context) : Expr → Type where
  | derivative (operator reference : Ref table) : Origins table (.derivative state)
  | one (literal : Ref table) : Origins table .one
  | sub (operator : Ref table) (left : Origins table lhs) (right : Origins table rhs) :
      Origins table (.sub lhs rhs)

def Expr.Origins.root : Expr.Origins table expr → Ref table
  | .derivative operator _ => operator
  | .one literal => literal
  | .sub operator _ _ => operator

/-- Each new residual/coordinate operator names its rule and exact parents.
Unchanged references and literals retain their indices in the extended table. -/
def Expr.Origins.Correct (flat : Flat.Model source) {table : Provenance.Table flat.context} :
    {expr : Expr} → Expr.Origins table expr → Prop
  | .derivative _, .derivative operator reference =>
      table.get operator = .derived .derivativeCoordinate
        flat.derivativeOrigins.root.index.val #[] ∧
      reference.index.val = flat.derivativeOrigins.reference.index.val
  | .one, .one literal => literal.index.val = flat.origins.right.root.index.val
  | .sub _ _, .sub operator left right =>
      table.get operator = .derived .equationResidual flat.origins.equation.index.val
        #[left.root.index.val, right.root.index.val] ∧
      left.Correct flat ∧ right.Correct flat

private theorem Expr.Origins.correct_cast {flat : Flat.Model source}
    {table : Provenance.Table flat.context} (origin : Expr.Origins table expr)
    (equal : expr = other) (correct : origin.Correct flat) :
    (equal ▸ origin).Correct flat := by cases equal; exact correct

theorem Expr.Origins.root_cast (origin : Expr.Origins table expr) (equal : expr = other) :
    (equal ▸ origin).root = origin.root := by cases equal; rfl

theorem Expr.Origins.sub_ancestry (flat : Flat.Model source)
    {table : Provenance.Table flat.context} (extension : flat.origins.table.Extension table)
    (origin : Expr.Origins table (.sub lhs rhs)) (correct : origin.Correct flat) :
    TracesTo table origin.root (flat.context.site .equation) := by
  cases origin with
  | sub operator left right =>
    have source := (extension.lookup flat.origins.equation).trans flat.origins.equation_source
    apply TracesTo.parent (parent := extension.ref flat.origins.equation) _ (.source source)
    simp only [Correct] at correct
    change (extension.ref flat.origins.equation).index.val ∈ (table.get operator).parents
    rw [correct.1]
    simp [Node.parents, _root_.Parser.Provenance.Table.Extension.ref]

private theorem Expr.Origins.residual_ancestry (flat : Flat.Model source)
    {table : Provenance.Table flat.context} (extension : flat.origins.table.Extension table)
    (origin : Expr.Origins table expr) (correct : origin.Correct flat)
    (equal : expr = .sub lhs rhs) : TracesTo table origin.root (flat.context.site .equation) := by
  cases equal
  exact Expr.Origins.sub_ancestry flat extension origin correct

structure Origins (flat : Flat.Model source) (residual : Expr) where
  table : Provenance.Table flat.context
  extension : flat.origins.table.Extension table
  expression : Expr.Origins table residual
  correct : expression.Correct flat

namespace OriginLowering

private def batch (flat : Flat.Model source) :
    Array (Node (_root_.Parser.Provenance.SourceRef flat.context.input.inputs) Provenance.Rule) :=
  #[.derived .derivativeCoordinate flat.derivativeOrigins.root.index.val #[],
    .derived .equationResidual flat.origins.equation.index.val
      #[flat.origins.table.nodes.size, flat.origins.right.root.index.val]]

private theorem batch_prior (flat : Flat.Model source) (index : Nat)
    (bound : index < (batch flat).size) (parent : Nat)
    (member : parent ∈ (batch flat)[index].parents) :
    parent < flat.origins.table.nodes.size + index := by
  cases index with
  | zero =>
      simp [batch, Node.parents] at member
      subst parent
      exact flat.derivativeOrigins.root.index.isLt
  | succ index =>
    cases index with
    | zero =>
        simp [batch, Node.parents] at member
        rcases member with same | same | same
        · subst parent; have := flat.origins.equation.index.isLt; omega
        · subst parent; omega
        · subst parent; have := flat.origins.right.root.index.isLt; omega
    | succ index => simp [batch] at bound; omega

def table (flat : Flat.Model source) : Provenance.Table flat.context :=
  flat.origins.table.append (batch flat) (batch_prior flat)

theorem extension (flat : Flat.Model source) : flat.origins.table.Extension (table flat) :=
  flat.origins.table.append_extension (batch flat) (batch_prior flat)

private def coordinate (flat : Flat.Model source) : Ref (table flat) :=
  flat.origins.table.appendedRef (batch flat) (batch_prior flat) ⟨0, by simp [batch]⟩

private def residual (flat : Flat.Model source) : Ref (table flat) :=
  flat.origins.table.appendedRef (batch flat) (batch_prior flat) ⟨1, by simp [batch]⟩

private def canonical (flat : Flat.Model source) :
    Expr.Origins (table flat) (.sub (.derivative 0) .one) :=
  .sub (residual flat)
    (.derivative (coordinate flat) ((extension flat).ref flat.derivativeOrigins.reference))
    (.one ((extension flat).ref flat.origins.right.root))

private theorem canonical_correct (flat : Flat.Model source) : (canonical flat).Correct flat := by
  have first := flat.origins.table.appended_lookup (batch flat) (batch_prior flat)
    ⟨0, by simp [batch]⟩
  have second := flat.origins.table.appended_lookup (batch flat) (batch_prior flat)
    ⟨1, by simp [batch]⟩
  simp only [canonical, Expr.Origins.Correct, Expr.Origins.root]
  refine ⟨?_, ⟨?_, rfl⟩, rfl⟩
  · simpa [table, residual, coordinate, _root_.Parser.Provenance.Table.appendedRef,
      _root_.Parser.Provenance.Table.Extension.ref, batch] using second
  · simpa only [table, coordinate, batch] using first

private theorem shape (flat : Flat.Model source) :
    .sub (.derivative 0) .one = Expr.sub (lowerExpr flat.lhs) (lowerExpr flat.rhs) := by
  rw [flat.lhs_source, flat.rhs_source]
  rfl

def lower (flat : Flat.Model source) :
    Origins flat (.sub (lowerExpr flat.lhs) (lowerExpr flat.rhs)) where
  table := table flat
  extension := extension flat
  expression := shape flat ▸ canonical flat
  correct := (canonical flat).correct_cast (shape flat) (canonical_correct flat)

end OriginLowering

structure Model (source : AST.Model) where
  flat : Flat.Model source
  residual : Expr
  residual_source : residual = .sub (lowerExpr flat.lhs) (lowerExpr flat.rhs)
  origins : Origins flat residual
  initialization : Initialization.Settings Nat
  initialization_source : initialization = flat.initialization

def lower (flat : Flat.Model source) : Model source :=
  ⟨flat, .sub (lowerExpr flat.lhs) (lowerExpr flat.rhs), rfl, OriginLowering.lower flat,
    flat.initialization, rfl⟩

def Model.initializationOrigin (model : Model source) : Ref model.origins.table :=
  model.origins.extension.ref model.flat.initializationOrigin

theorem Model.sourceExtension (model : Model source) :
    model.flat.context.origins.Extension model.origins.table :=
  model.flat.origins.extension.trans model.origins.extension

def Model.sourceOrigin (model : Model source) (field : Rumoca.Origins.Field) :
    Ref model.origins.table := model.sourceExtension.ref (model.flat.context.ref field)

theorem Model.source_origin (model : Model source) (field : Rumoca.Origins.Field) :
    model.origins.table.get (model.sourceOrigin field) = .source (model.flat.context.site field) :=
  (model.sourceExtension.lookup _).trans (model.flat.context.lookup field)

/-- Every completed residual traces to the written equation through the actual
origin records, even for a caller-constructed model satisfying the invariants. -/
theorem Model.residual_ancestry (model : Model source) :
    TracesTo model.origins.table model.origins.expression.root
      (model.flat.context.site .equation) :=
  Expr.Origins.residual_ancestry model.flat model.origins.extension model.origins.expression
    model.origins.correct model.residual_source

theorem Model.initialization_origin (model : Model source) :
    model.origins.table.get model.initializationOrigin =
      .source (model.flat.context.site .declaration) :=
  (model.origins.extension.lookup _).trans model.flat.initialization_origin

theorem Model.initialization_default (model : Model source) :
    model.initialization = ⟨none, none, false⟩ :=
  model.initialization_source.trans model.flat.initialization_source

theorem Model.initialization_succeeds (model : Model source) :
    ∃ plan, Initialization.prepare model.initialization 0 = .ok plan := by
  rw [model.initialization_default]
  exact ⟨_, rfl⟩

end Rumoca.DAE
