import RumocaC.DeclaredMembers

set_option maxRecDepth 8192
set_option maxHeartbeats 800000

/-! Structural compatibility for numerical helper bodies. No machine definition
is copied, no declaration/object restriction or successful execution is assumed. -/
namespace Rumoca.CDeclaredMembers.FieldFree
open CTree CMemory

mutual
def expression : Expr → Bool
  | .field _ _ _ => false
  | .id _ | .nat _ | .decimal _ _ _ | .str _ | .sizeof _ => true
  | .not a | .deref a | .address a | .cast _ a => expression a
  | .bin _ a b | .index a b => expression a && expression b
  | .call fn args => expression fn && argumentList args

def argumentList : List Expr → Bool
  | [] => true
  | a :: rest => expression a && argumentList rest
end

theorem argumentList_all (args : List Expr) : argumentList args = args.all expression := by
  induction args with
  | nil => rfl
  | cons a rest ih => simp [argumentList, ih]

mutual
/-- All expression sites, including assignment lvalues and both branches,
nested loops, call targets and arguments (the latter traversed by expression). -/
def expressions : Stmt → List Expr
  | .declare _ _ value => [value]
  | .assign target value => [target, value]
  | .eval value => [value]
  | .ret value => value.toList
  | .branch condition yes no => condition :: (sites yes ++ sites no)
  | .whileLoop condition body => condition :: sites body

def sites : List Stmt → List Expr
  | [] => []
  | s :: rest => expressions s ++ sites rest
end

theorem sites_flatMap (code : List Stmt) : sites code = code.flatMap expressions := by
  induction code with
  | nil => rfl
  | cons s rest ih => simp [sites, ih]

def statement (s : Stmt) : Bool := (expressions s).all expression
def body (code : List Stmt) : Bool := (code.flatMap expressions).all expression
def AdmittedBody (code : List Stmt) : Prop := body code = true

theorem body_nil : AdmittedBody [] := rfl

theorem body_cons (s : Stmt) (rest : List Stmt) :
    body (s :: rest) = (statement s && body rest) := by
  simp [body, statement, List.all_append]

theorem body_append (left right : List Stmt) :
    body (left ++ right) = (body left && body right) := by
  simp [body, List.all_append]

theorem branch_parts (valid : statement (.branch condition yes no) = true) :
    expression condition = true ∧ AdmittedBody yes ∧ AdmittedBody no := by
  simpa [statement, expressions, sites_flatMap, AdmittedBody, body, List.all_append, Bool.and_eq_true, and_assoc] using valid

theorem loop_parts (valid : statement (.whileLoop condition code) = true) :
    expression condition = true ∧ AdmittedBody code := by
  simpa [statement, expressions, sites_flatMap, AdmittedBody, body, Bool.and_eq_true] using valid

theorem body_member (valid : AdmittedBody code) (s : Stmt) (member : s ∈ code) :
    statement s = true := by
  apply List.all_eq_true.mpr
  intro e occurrence
  exact List.all_eq_true.mp valid e (List.mem_flatMap.mpr ⟨s, member, occurrence⟩)

theorem expression_member (valid : AdmittedBody code) (e : Expr)
    (member : e ∈ code.flatMap expressions) : expression e = true :=
  List.all_eq_true.mp valid e member

section
variable [interface : CInterface]

private theorem other_call (fn a : Expr) (other : fn ≠ .id "isfinite") :
    CDeclaredMembers.eval declarations objects env heap (.call fn [a]) = none := by
  cases fn <;> simp_all [CDeclaredMembers.eval, CBody.evalWith]

private theorem old_other_call (fn a : Expr) (other : fn ≠ .id "isfinite") :
    CBody.eval env heap (.call fn [a]) = none := by
  cases fn <;> simp_all [CBody.eval, CBody.evalWith]

/-- No fields anywhere in the expression implies agreement under ARBITRARY
declarations/objects, including invalid metadata and arrays elsewhere. -/
theorem agreement (declarations : Declarations) (objects : Objects)
    (env : CBody.Locals) (heap : Heap) (e : Expr) (free : expression e = true) :
    CDeclaredMembers.eval declarations objects env heap e = CBody.eval env heap e ∧
    CDeclaredMembers.lvalue declarations objects env heap e = CBody.lvalue env heap e := by
  revert free
  induction e using Expr.rec (motive_2 := fun args => ∀ a ∈ args, expression a = true →
      CDeclaredMembers.eval declarations objects env heap a = CBody.eval env heap a ∧
      CDeclaredMembers.lvalue declarations objects env heap a = CBody.lvalue env heap a) with
  | id | nat | decimal | str | sizeof =>
      intro free
      simp [CDeclaredMembers.eval, CBody.evalWith, CDeclaredMembers.lvalue, CBody.lvalueWith, CBody.eval, CBody.lvalue]
  | bin op a b ha hb =>
      intro free
      have parts : expression a = true ∧ expression b = true := by
        simpa only [expression, Bool.and_eq_true] using free
      have left := ha parts.1
      have right := hb parts.2
      cases op <;> simp [CDeclaredMembers.eval, CBody.evalWith, CDeclaredMembers.lvalue, CBody.lvalueWith, CBody.eval, CBody.lvalue, left.1, right.1]
  | index a b ha hb =>
      intro free
      have parts : expression a = true ∧ expression b = true := by
        simpa only [expression, Bool.and_eq_true] using free
      have left := ha parts.1
      have right := hb parts.2
      simp only [CDeclaredMembers.eval, CBody.evalWith, CDeclaredMembers.lvalue, CBody.lvalueWith, CBody.eval, CBody.lvalue, left.1, left.2, right.1]
      constructor <;> trivial
  | not a ha | deref a ha | address a ha | cast type a ha =>
      intro free
      have same := ha free
      simp [CDeclaredMembers.eval, CBody.evalWith, CDeclaredMembers.lvalue, CBody.lvalueWith, CBody.eval, CBody.lvalue, same.1, same.2]
  | field a name pointer ha =>
      intro free
      cases free
  | call fn args hfn hargs =>
      intro free
      have parts : expression fn = true ∧ args.all expression = true := by
        simpa only [expression, argumentList_all, Bool.and_eq_true] using free
      refine ⟨?_, by simp [CDeclaredMembers.lvalue, CBody.lvalueWith, CBody.lvalue]⟩
      cases args with
      | nil => cases fn <;> simp [CDeclaredMembers.eval, CBody.evalWith, CBody.eval]
      | cons a rest =>
          cases rest with
          | cons b rest => cases fn <;> simp [CDeclaredMembers.eval, CBody.evalWith, CBody.eval]
          | nil =>
              have same := hargs a (by simp) (List.all_eq_true.mp parts.2 a (by simp))
              by_cases intrinsic : fn = .id "isfinite"
              · subst fn; simp [CDeclaredMembers.eval, CBody.evalWith, CBody.eval, same.1]
              · rw [other_call fn a intrinsic, old_other_call fn a intrinsic]
  | nil => simp_all
  | cons a rest ha hr =>
      rename_i value member free
      rcases List.mem_cons.mp member with rfl | member
      · exact ha free
      · exact hr value member free

theorem body_expression_agreement (declarations : Declarations) (objects : Objects)
    (env : CBody.Locals) (heap : Heap) (code : List Stmt)
    (valid : AdmittedBody code) (e : Expr) (member : e ∈ code.flatMap expressions) :
    CDeclaredMembers.eval declarations objects env heap e = CBody.eval env heap e ∧
    CDeclaredMembers.lvalue declarations objects env heap e = CBody.lvalue env heap e :=
  agreement declarations objects env heap e (expression_member valid e member)

end
end Rumoca.CDeclaredMembers.FieldFree
