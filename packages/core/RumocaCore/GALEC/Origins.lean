import RumocaCore.GALEC.Syntax
import Parser.ProvenanceExtension

/-! Required expression, operand, method and assignment origins, indexed by
the exact GALEC syntax and whole tensor shape. -/
namespace Rumoca.GALEC
open _root_.Parser.Provenance (Ref Table Node)

variable {Site Rule : Type} {table before after : Table Site Rule}

inductive Expr.Origins (table : Table Site Rule) : Expr shape → Type where
  | state (reference : Ref table) : Origins table .state
  | zero (literal : Ref table) : Origins table .zero
  | one (literal : Ref table) : Origins table .one
  | add (operator : Ref table) (left : Origins table lhs) (right : Origins table rhs) :
      Origins table (.add lhs rhs)

def Expr.Origins.root : Expr.Origins table expr → Ref table
  | .state reference => reference
  | .zero literal => literal
  | .one literal => literal
  | .add operator _ _ => operator

def Expr.Origins.extend (extension : before.Extension after) :
    Expr.Origins before expr → Expr.Origins after expr
  | .state reference => .state (extension.ref reference)
  | .zero literal => .zero (extension.ref literal)
  | .one literal => .one (extension.ref literal)
  | .add operator left right =>
      .add (extension.ref operator) (left.extend extension) (right.extend extension)

theorem Expr.Origins.extend_root (extension : before.Extension after)
    (origins : Expr.Origins before expr) :
    (origins.extend extension).root = extension.ref origins.root := by
  cases origins <;> rfl

/-- A predicate on each actual origin record, including its generating rule
and parent indices. Extending the table must preserve every such predicate. -/
def Expr.Origins.Every (check : Node Site Rule → Prop) :
    {expr : Expr shape} → Expr.Origins table expr → Prop
  | _, .state reference => check (table.get reference)
  | _, .zero literal => check (table.get literal)
  | _, .one literal => check (table.get literal)
  | _, .add operator left right =>
      check (table.get operator) ∧ left.Every check ∧ right.Every check

theorem Expr.Origins.extend_every (extension : before.Extension after)
    (check : Node Site Rule → Prop) (origins : Expr.Origins before expr) :
    (origins.extend extension).Every check ↔ origins.Every check := by
  induction origins with
  | state reference => simp only [extend, Every, extension.lookup]
  | zero literal => simp only [extend, Every, extension.lookup]
  | one literal => simp only [extend, Every, extension.lookup]
  | add operator left right ihLeft ihRight =>
      simp only [extend, Every, extension.lookup, ihLeft, ihRight]

/-- Even an empty generated method has a required origin. Assignment metadata
covers its target occurrence separately from the value expression. -/
inductive BodyOrigins (table : Table Site Rule) : Option (Expr shape) → Type where
  | empty (method : Ref table) : BodyOrigins table none
  | assign (method assignment target : Ref table) (value : Expr.Origins table expr) :
      BodyOrigins table (some expr)

def BodyOrigins.extend (extension : before.Extension after) :
    BodyOrigins before body → BodyOrigins after body
  | .empty method => .empty (extension.ref method)
  | .assign method assignment target value =>
      .assign (extension.ref method) (extension.ref assignment) (extension.ref target)
        (value.extend extension)

structure Block.Origins (table : Table Site Rule) (block : Block shape) where
  model : Ref table
  stateDeclaration : Ref table
  startup : BodyOrigins table block.startup
  recalibrate : BodyOrigins table block.recalibrate
  doStep : BodyOrigins table block.doStep
  periodDeclaration : Ref table
  periodAssignment : Ref table
  periodTarget : Ref table
  periodValue : Expr.Origins table block.startupPeriod

def Block.Origins.extend (extension : before.Extension after)
    (origins : Block.Origins before block) : Block.Origins after block where
  model := extension.ref origins.model
  stateDeclaration := extension.ref origins.stateDeclaration
  startup := origins.startup.extend extension
  recalibrate := origins.recalibrate.extend extension
  doStep := origins.doStep.extend extension
  periodDeclaration := extension.ref origins.periodDeclaration
  periodAssignment := extension.ref origins.periodAssignment
  periodTarget := extension.ref origins.periodTarget
  periodValue := origins.periodValue.extend extension

end Rumoca.GALEC
