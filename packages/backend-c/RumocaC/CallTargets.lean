import RumocaC.Calls

/-! Reusable call-site classification and target resolution.
The scalar pointer representation does not
justify arbitrary function-designator dereference or signature compatibility;
those need separate typed judgments before extending beyond emitted calls. -/
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

variable [interface : CInterface]

def resolve (env : CBody.Locals) (heap : Heap) : Expr → Option Target
  | .id name =>
      match CBody.resolve env name with
      | none => some (.named name)
      | some value => valueTarget value
  | callee@(.field ..) | callee@(.index ..) => do valueTarget (← CBody.eval env heap callee)
  | _ => none

/-- Only unambiguous pointer-valued identifier/field/array accesses are in
this call-site fragment. Function-designator dereference and casts need C
function types before they can be admitted; they are rejected here. -/
inductive Supported : Expr → Prop where
  | identifier : Supported (.id name)
  | field : Supported (.field object name pointer)
  | index : Supported (.index array position)

theorem resolved_supported (found : resolve env heap callee = some target) : Supported callee := by
  cases callee <;> try { simp [resolve] at found }
  all_goals constructor

omit interface in
theorem value_pointer_iff : valueTarget value = some (.pointer address) ↔
    value = .pointer (some address) := by
  cases value <;> simp [valueTarget]
  split <;> simp_all

theorem local_pointer (found : env name = some (.pointer (some address))) :
    resolve env heap (.id name) = some (.pointer address) := by
  simp [resolve, CBody.resolve, found, valueTarget]

theorem local_null (found : env name = some (.pointer none)) :
    resolve env heap (.id name) = none := by
  simp [resolve, CBody.resolve, found, valueTarget]

theorem named_iff : resolve env heap (.id name) = some (.named name) ↔
    env name = none ∧ interface.constants name = none := by
  cases localValue : env name with
  | none =>
      cases global : interface.constants name with
      | none => simp [resolve, CBody.resolve, CBody.constants, localValue, global]
      | some value =>
          cases value <;> simp [resolve, CBody.resolve, CBody.constants, localValue, global, valueTarget]
          split <;> simp_all
  | some value =>
      cases value <;> simp [resolve, CBody.resolve, localValue, valueTarget]
      split <;> simp_all

theorem field_pointer
    (owner : CBody.eval env heap object = some (.pointer (some p)))
    (loaded : load heap (p.member field) = some (.pointer (some address))) :
    resolve env heap (.field object field true) = some (.pointer address) := by
  simp [resolve, CBody.eval, owner, Value.address, loaded, valueTarget]

end Rumoca.CCalls.Indirect
