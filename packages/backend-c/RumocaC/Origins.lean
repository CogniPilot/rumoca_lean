import RumocaC.Tree
import Parser.ProvenanceMapping

/-! Complete C expression occurrences. A typed list retains a trace for each
argument without repeated indexed lookup through the argument list. These
generic traces impose no source-language or backend rule vocabulary. -/
namespace Rumoca.CTree
open _root_.Parser.Provenance (Table)
abbrev Origin (table : Table Site Rule) := _root_.Parser.Provenance.Ref table

inductive OriginList {Syntax : Type} (Trace : Syntax → Type) : List Syntax → Type where
  | nil : OriginList Trace []
  | cons (head : Trace node) (tail : OriginList Trace rest) : OriginList Trace (node :: rest)

inductive Expr.Origins (table : Table Site Rule) : Expr → Type where
  | id (name : Origin table) : Origins table (.id identifier)
  | nat (literal : Origin table) : Origins table (.nat value)
  | str (literal : Origin table) : Origins table (.str value)
  | bin (operation : Origin table) (left : Origins table lhs) (right : Origins table rhs) :
      Origins table (.bin op lhs rhs)
  | not (operation : Origin table) (value : Origins table expr) : Origins table (.not expr)
  | deref (operation : Origin table) (value : Origins table expr) : Origins table (.deref expr)
  | address (operation : Origin table) (value : Origins table expr) : Origins table (.address expr)
  | field (operation member : Origin table) (base : Origins table expr) :
      Origins table (.field expr name pointer)
  | index (operation : Origin table) (base : Origins table expr) (offset : Origins table subscript) :
      Origins table (.index expr subscript)
  | call (operation : Origin table) (callee : Origins table fn)
      (arguments : OriginList (Origins table) args) : Origins table (.call fn args)
  | cast (operation typeName : Origin table) (value : Origins table expr) :
      Origins table (.cast type expr)
  | sizeof (operation typeName : Origin table) : Origins table (.sizeof type)

def Expr.Origins.root : Expr.Origins table expr → Origin table
  | .id name => name
  | .nat literal | .str literal => literal
  | .bin operation _ _ | .not operation _ | .deref operation _ | .address operation _ |
    .field operation _ _ | .index operation _ _ | .call operation _ _ |
    .cast operation _ _ | .sizeof operation _ => operation

mutual
/-- One explicit generation rule may explain all syntax of a generated
storage access. This never supplies an unknown or absent origin. -/
def Expr.Origins.uniform (origin : Origin table) : (expr : Expr) → Origins table expr
  | .id _ => .id origin
  | .nat _ => .nat origin
  | .str _ => .str origin
  | .bin _ lhs rhs => .bin origin (uniform origin lhs) (uniform origin rhs)
  | .not expr => .not origin (uniform origin expr)
  | .deref expr => .deref origin (uniform origin expr)
  | .address expr => .address origin (uniform origin expr)
  | .field expr _ _ => .field origin origin (uniform origin expr)
  | .index expr offset => .index origin (uniform origin expr) (uniform origin offset)
  | .call fn args => .call origin (uniform origin fn) (uniformList origin args)
  | .cast _ expr => .cast origin origin (uniform origin expr)
  | .sizeof _ => .sizeof origin origin

def Expr.Origins.uniformList (origin : Origin table) : (args : List Expr) →
    OriginList (Origins table) args
  | [] => .nil
  | expr :: rest => .cons (uniform origin expr) (uniformList origin rest)
end

theorem Expr.Origins.uniform_root (origin : Origin table) (expr : Expr) :
    (uniform origin expr).root = origin := by cases expr <;> rfl

mutual
def Expr.Origins.Every (check : Origin table → Prop) : Expr.Origins table expr → Prop
  | .id name => check name
  | .nat literal | .str literal => check literal
  | .bin operation left right | .index operation left right =>
      check operation ∧ left.Every check ∧ right.Every check
  | .not operation value | .deref operation value | .address operation value =>
      check operation ∧ value.Every check
  | .field operation member base | .cast operation member base =>
      check operation ∧ check member ∧ base.Every check
  | .call operation callee arguments =>
      check operation ∧ callee.Every check ∧ EveryList check arguments
  | .sizeof operation typeName => check operation ∧ check typeName

def Expr.Origins.EveryList (check : Origin table → Prop) :
    OriginList (Expr.Origins table) args → Prop
  | .nil => True
  | .cons head tail => head.Every check ∧ EveryList check tail
end

mutual
theorem Expr.Origins.uniform_every (origin : Origin table) (check : Origin table → Prop)
    (accepted : check origin) (expr : Expr) : (uniform origin expr).Every check := by
  cases expr with
  | id | nat | str => simpa only [uniform, Every] using accepted
  | bin _ lhs rhs | index lhs rhs =>
      simp only [uniform, Every]
      exact ⟨accepted, uniform_every origin check accepted lhs,
        uniform_every origin check accepted rhs⟩
  | not value | deref value | address value =>
      simp only [uniform, Every]
      exact ⟨accepted, uniform_every origin check accepted value⟩
  | field value _ _ | cast _ value =>
      simp only [uniform, Every]
      exact ⟨accepted, accepted, uniform_every origin check accepted value⟩
  | call fn args =>
      simp only [uniform, Every]
      exact ⟨accepted, uniform_every origin check accepted fn,
        uniformList_every origin check accepted args⟩
  | sizeof => simpa only [uniform, Every] using (And.intro accepted accepted)

theorem Expr.Origins.uniformList_every (origin : Origin table) (check : Origin table → Prop)
    (accepted : check origin) (args : List Expr) : EveryList check (uniformList origin args) := by
  cases args with
  | nil => simp only [uniformList, EveryList]
  | cons expr rest =>
      simp only [uniformList, EveryList]
      exact ⟨uniform_every origin check accepted expr, uniformList_every origin check accepted rest⟩
end

end Rumoca.CTree
