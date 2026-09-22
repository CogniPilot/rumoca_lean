import RumocaC.Calls

/-! Call-site classification and expression-parametric target resolution.
No function-designator dereference, cast or native signature/ABI rule is added. -/
namespace Rumoca.CCalls.Indirect
open CTree CMemory

inductive Target where
  | named (name : String)
  | pointer (address : Address)
  deriving DecidableEq

structure Operand where
  destination : Destination
  callee : Expr
  args : List Expr

def operand : Stmt → Option Operand
  | .assign target (.call callee args) => some ⟨.assign target, callee, args⟩
  | .declare type name (.call callee args) => some ⟨.declare type name, callee, args⟩
  | .eval (.call callee args) => some ⟨.discard, callee, args⟩
  | .ret (some (.call callee args)) => some ⟨.ret, callee, args⟩
  | _ => none

def valueTarget : Value → Option Target
  | .pointer (some address) => some (.pointer address)
  | _ => none

/-- All evaluated designators use the supplied value evaluator, including
identifiers. Only an unresolved identifier falls back to a named function. -/
def resolveWith (expressions : CBody.Expressions) (env : CBody.Locals) (heap : Heap) :
    Expr → Option Target
  | .id name =>
      match expressions.value env heap (.id name) with
      | none => some (.named name)
      | some value => valueTarget value
  | callee@(.field ..) | callee@(.index ..) => do
      valueTarget (← expressions.value env heap callee)
  | _ => none

variable [interface : CInterface]

noncomputable abbrev resolve := resolveWith CBody.legacyExpressions

/-- Only the existing identifier/field/index fragment is supported. -/
inductive Supported : Expr → Prop where
  | identifier : Supported (.id name)
  | field : Supported (.field object name pointer)
  | index : Supported (.index array position)

omit interface in
theorem resolved_supported_with (expressions : CBody.Expressions)
    (found : resolveWith expressions env heap callee = some target) : Supported callee := by
  cases callee <;> try { simp [resolveWith] at found }
  all_goals constructor

theorem resolved_supported (found : resolve env heap callee = some target) : Supported callee :=
  resolved_supported_with CBody.legacyExpressions found

omit interface in
theorem value_pointer_iff : valueTarget value = some (.pointer address) ↔
    value = .pointer (some address) := by
  cases value <;> simp [valueTarget]
  split <;> simp_all

omit interface in
theorem named_iff_with (expressions : CBody.Expressions) :
    resolveWith expressions env heap (.id name) = some (.named name) ↔
      expressions.value env heap (.id name) = none := by
  cases evaluated : expressions.value env heap (.id name) with
  | none => simp [resolveWith, evaluated]
  | some value =>
      cases value <;> simp [resolveWith, evaluated, valueTarget]
      split <;> simp_all

omit interface in
theorem evaluated_pointer_with (expressions : CBody.Expressions) (supported : Supported callee)
    (evaluated : expressions.value env heap callee = some (.pointer (some address))) :
    resolveWith expressions env heap callee = some (.pointer address) := by
  cases supported <;> simp [resolveWith, evaluated, valueTarget]

omit interface in
theorem evaluated_null_with (expressions : CBody.Expressions) (supported : Supported callee)
    (evaluated : expressions.value env heap callee = some (.pointer none)) :
    resolveWith expressions env heap callee = none := by
  cases supported <;> simp [resolveWith, evaluated, valueTarget]

theorem local_pointer (found : env name = some (.pointer (some address))) :
    resolve env heap (.id name) = some (.pointer address) := by
  apply evaluated_pointer_with CBody.legacyExpressions .identifier
  simp [CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.resolve, found]

theorem local_null (found : env name = some (.pointer none)) :
    resolve env heap (.id name) = none := by
  apply evaluated_null_with CBody.legacyExpressions .identifier
  simp [CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.resolve, found]

theorem named_iff : resolve env heap (.id name) = some (.named name) ↔
    env name = none ∧ interface.constants name = none := by
  rw [resolve, named_iff_with]
  change CBody.resolve env name = none ↔ _
  simp [CBody.resolve, CBody.constants]

theorem field_pointer
    (owner : CBody.eval env heap object = some (.pointer (some p)))
    (loaded : load heap (p.member field) = some (.pointer (some address))) :
    resolve env heap (.field object field true) = some (.pointer address) := by
  apply evaluated_pointer_with CBody.legacyExpressions .field
  change CBody.eval env heap (.field object field true) = _
  simp only [CBody.eval, CBody.evalWith] at owner ⊢
  simp [owner, Value.address, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt,
    CDeclaredMembers.fieldAt, loaded]

theorem resolve_legacy (env : CBody.Locals) (heap : Heap) (callee : Expr) :
    resolveWith CBody.legacyExpressions env heap callee = resolve env heap callee := rfl

end Rumoca.CCalls.Indirect
