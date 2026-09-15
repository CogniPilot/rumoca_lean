import RumocaC.Tree

/-! Complete structural call inventory and conservative rank checks. External and indirect targets need separate contracts. -/
namespace Rumoca.CCallPolicy
open CTree

def expressionCalls : Expr → List Expr
  | .call fn args => fn :: (expressionCalls fn ++ args.flatMap expressionCalls)
  | .bin _ a b | .index a b => expressionCalls a ++ expressionCalls b
  | .not a | .deref a | .address a | .field a _ _ | .cast _ a => expressionCalls a
  | .id _ | .nat _ | .str _ | .sizeof _ => []

def statementCalls : Stmt → List Expr
  | .declare _ _ e | .eval e | .ret (some e) => expressionCalls e
  | .assign a b => expressionCalls a ++ expressionCalls b
  | .ret none => []
  | .branch c yes no => expressionCalls c ++ yes.flatMap statementCalls ++ no.flatMap statementCalls
  | .whileLoop c body => expressionCalls c ++ body.flatMap statementCalls

/-- The policy applies at every call expression, even if short-circuiting or
a later return makes that expression unreachable in a particular execution. -/
def ExpressionAdmits (permitted : Expr → Prop) : Expr → Prop
  | .call fn args => permitted fn ∧ ExpressionAdmits permitted fn ∧
      ∀ arg ∈ args, ExpressionAdmits permitted arg
  | .bin _ a b | .index a b => ExpressionAdmits permitted a ∧ ExpressionAdmits permitted b
  | .not a | .deref a | .address a | .field a _ _ | .cast _ a => ExpressionAdmits permitted a
  | .id _ | .nat _ | .str _ | .sizeof _ => True

def StatementAdmits (permitted : Expr → Prop) : Stmt → Prop
  | .declare _ _ e | .eval e | .ret (some e) => ExpressionAdmits permitted e
  | .assign a b => ExpressionAdmits permitted a ∧ ExpressionAdmits permitted b
  | .ret none => True
  | .branch c yes no => ExpressionAdmits permitted c ∧
      (∀ stmt ∈ yes, StatementAdmits permitted stmt) ∧
      ∀ stmt ∈ no, StatementAdmits permitted stmt
  | .whileLoop c body => ExpressionAdmits permitted c ∧
      ∀ stmt ∈ body, StatementAdmits permitted stmt

/-- Visit the expression directly, without materializing concatenated call
inventories. Membership evidence supplies termination and is erased at runtime. -/
def checkExpression (check : Expr → Bool) : Expr → Bool
  | .call fn args => check fn && checkExpression check fn &&
      args.attach.all (fun item => checkExpression check item.val)
  | .bin _ a b | .index a b => checkExpression check a && checkExpression check b
  | .not a | .deref a | .address a | .field a _ _ | .cast _ a => checkExpression check a
  | .id _ | .nat _ | .str _ | .sizeof _ => true
termination_by expr => sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have bound := List.sizeOf_lt_of_mem item.property; omega)

def checkStatement (check : Expr → Bool) : Stmt → Bool
  | .declare _ _ e | .eval e | .ret (some e) => checkExpression check e
  | .assign a b => checkExpression check a && checkExpression check b
  | .ret none => true
  | .branch c yes no => checkExpression check c &&
      yes.attach.all (fun item => checkStatement check item.val) &&
      no.attach.all (fun item => checkStatement check item.val)
  | .whileLoop c body => checkExpression check c &&
      body.attach.all (fun item => checkStatement check item.val)
termination_by stmt => sizeOf stmt
decreasing_by
  all_goals simp_wf
  all_goals have bound := List.sizeOf_lt_of_mem item.property
  all_goals omega

def checkFunction (check : Expr → Bool) (fn : Function) : Bool :=
  fn.body.all (checkStatement check)

/-- A rank is supplied for each generated definition. Names without a rank
remain external boundaries; the enclosing artifact contract must classify them. -/
def rankCallee (rank : String → Option Nat) (caller : Nat) : Expr → Bool
  | .id name => match rank name with
      | some callee => decide (callee < caller)
      | none => true
  | _ => true

def checkRank (rank : String → Option Nat) (fn : Function) : Bool :=
  match rank fn.signature.name with
  | none => false
  | some caller => checkFunction (rankCallee rank caller) fn

def checkRanks (rank : String → Option Nat) (functions : List Function) : Bool :=
  functions.all (checkRank rank)

/-- Every definition has a rank and every syntactic direct call to another
ranked name decreases it. This includes calls in nested expressions and in
unreachable branches; indirect calls have separate resolution obligations. -/
def Ranked (rank : String → Option Nat) (functions : List Function) : Prop :=
  ∀ fn ∈ functions, ∃ caller, rank fn.signature.name = some caller ∧
    ∀ name, .id name ∈ fn.body.flatMap statementCalls →
      ∀ callee, rank name = some callee → callee < caller

end Rumoca.CCallPolicy
