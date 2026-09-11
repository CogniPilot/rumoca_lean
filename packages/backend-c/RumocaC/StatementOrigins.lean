import RumocaC.Origins

/-! Complete occurrences for the existing C statement syntax. Lists are
containers, not additional semantic nodes; every contained statement has a
required root and complete expression/declaration/child annotations. -/
namespace Rumoca.CTree
open _root_.Parser.Provenance (Table)

inductive Stmt.Origins (table : Table Site Rule) : Stmt → Type where
  | declare (operation typeName declaration : Origin table) (value : Expr.Origins table expr) :
      Origins table (.declare type name expr)
  | assign (operation : Origin table) (target : Expr.Origins table lhs)
      (value : Expr.Origins table rhs) : Origins table (.assign lhs rhs)
  | eval (operation : Origin table) (value : Expr.Origins table expr) : Origins table (.eval expr)
  | retVoid (operation : Origin table) : Origins table (.ret none)
  | retValue (operation : Origin table) (value : Expr.Origins table expr) :
      Origins table (.ret (some expr))
  | branch (operation : Origin table) (condition : Expr.Origins table expr)
      (yes : OriginList (Origins table) whenTrue) (no : OriginList (Origins table) whenFalse) :
      Origins table (.branch expr whenTrue whenFalse)
  | whileLoop (operation : Origin table) (condition : Expr.Origins table expr)
      (body : OriginList (Origins table) statements) : Origins table (.whileLoop expr statements)

def Stmt.Origins.root : Stmt.Origins table stmt → Origin table
  | .declare operation _ _ _ | .assign operation _ _ | .eval operation _ |
    .retVoid operation | .retValue operation _ | .branch operation _ _ _ |
    .whileLoop operation _ _ => operation

mutual
def Stmt.Origins.Every (check : Origin table → Prop) : Stmt.Origins table stmt → Prop
  | .declare operation typeName declaration value =>
      check operation ∧ check typeName ∧ check declaration ∧ value.Every check
  | .assign operation target value => check operation ∧ target.Every check ∧ value.Every check
  | .eval operation value | .retValue operation value => check operation ∧ value.Every check
  | .retVoid operation => check operation
  | .branch operation condition yes no =>
      check operation ∧ condition.Every check ∧ EveryList check yes ∧ EveryList check no
  | .whileLoop operation condition body =>
      check operation ∧ condition.Every check ∧ EveryList check body

def Stmt.Origins.EveryList (check : Origin table → Prop) :
    OriginList (Stmt.Origins table) statements → Prop
  | .nil => True
  | .cons head tail => head.Every check ∧ EveryList check tail
end

theorem Stmt.Origins.every_root (origins : Stmt.Origins table stmt)
    (check : Origin table → Prop) (checked : origins.Every check) : check origins.root := by
  cases origins <;> simp only [Every, root] at checked ⊢ <;>
    first | exact checked | exact checked.1

end Rumoca.CTree
