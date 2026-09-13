import RumocaC.Tree
import RumocaC.Interface
import RumocaCore.Real.Comparison
import RumocaCore.Transition

/-! Small-step execution of the existing generated C tree's memory-access
fragment. No rule recognizes FMI function names or replaces an FMI body by
its intended behavior. Only `isfinite` is an intrinsic here; `CCalls` extends
this machine with ordinary call/return execution and a proved lifting. Expressions
in this fragment are side-effect free. Local assignment/addresses/block scopes, general
integer arithmetic and other C operators require further rules and proofs. -/
namespace Rumoca.CBody
open CTree CMemory

abbrev Locals := String → Option Value
def bind (env : Locals) (name : String) (v : Value) : Locals :=
  fun key => if key = name then some v else env key

variable [interface : CInterface]

def constants : String → Option Value := interface.constants

def resolve (env : Locals) (name : String) : Option Value := (env name).orElse (fun _ => constants name)
def boolean (b : Bool) : Value := .integer (if b then 1 else 0)

omit interface in
@[simp] theorem truth_boolean (b : Bool) : (boolean b).truth = some b := by
  cases b <;> rfl

def cast (type : String) (v : Value) : Option Value := do
  convert (← interface.types type) v

/-- The supported integer null-constant syntax. This is intentionally a
syntax judgment: a variable whose runtime value is zero is not such a constant. -/
def zeroLiteral : Expr → Bool
  | .nat 0 => true
  | _ => false

omit interface in
@[simp] theorem zeroLiteral_true (operand : Expr) :
    zeroLiteral operand = true ↔ operand = .nat 0 := by
  cases operand <;> simp [zeroLiteral]
  split <;> simp_all

omit interface in
@[simp] theorem zeroLiteral_false (operand : Expr) :
    zeroLiteral operand = false ↔ operand ≠ .nat 0 := by
  rw [Bool.eq_false_iff]
  exact not_congr (zeroLiteral_true operand)

/-- A literal zero converted to a pointer has the null value. All other
supported casts retain ordinary typed conversion. Broader C integer constant
expressions and implementation-defined integer-to-pointer casts are separate. -/
def expressionCast (type : String) (operand : Expr) (value : Value) : Option Value :=
  if zeroLiteral operand && decide (interface.types type = some .pointer) then
    some (.pointer none)
  else cast type value

@[simp] theorem expressionCast_ordinary (ordinary : zeroLiteral operand = false) :
    expressionCast type operand value = cast type value := by
  simp only [expressionCast, ordinary, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

@[simp] theorem expressionCast_nonpointer (other : interface.types type ≠ some .pointer) :
    expressionCast type operand value = cast type value := by
  simp [expressionCast, other]

def floatComparison (op : BinOp) (a b : BitVec 64) : Option Value :=
  let compare := fun r => some (boolean (Rumoca.Float64.test r a b))
  match op with
  | .eq => compare .eq | .ne => compare .ne
  | .lt => compare .lt | .le => compare .le
  | .gt => compare .gt | .ge => compare .ge
  | _ => none

def comparison (op : BinOp) (a b : Value) : Option Value :=
  match a, b with
  | .integer x, .integer y =>
    match op with
    | .eq => some (boolean (x == y)) | .ne => some (boolean (x != y))
    | .lt => some (boolean (x < y)) | .le => some (boolean (x ≤ y))
    | .gt => some (boolean (x > y)) | .ge => some (boolean (x ≥ y))
    | _ => none
  | .pointer p, .pointer q =>
    match op with
    | .eq => if p.isNone || q.isNone then some (boolean (p.isNone && q.isNone)) else none
    | .ne => if p.isNone || q.isNone then some (boolean (p.isSome || q.isSome)) else none
    | _ => none
  | .float64 x, .float64 y => floatComparison op x y
  | .float64 x, y => do
    let .float64 bits ← convert .float64 y | none
    floatComparison op x bits
  | x, .float64 y => do
    let .float64 bits ← convert .float64 x | none
    floatComparison op bits y
  | _, _ => none

mutual
  def eval (env : Locals) (heap : Heap) : Expr → Option Value
    | .id name => resolve env name
    | .nat n => some (.integer n)
    | .str s => (interface.literals s).map (fun p => .pointer (some p))
    | .cast type a => do expressionCast type a (← eval env heap a)
    | .not a => do return boolean (!(← (← eval env heap a).truth))
    | .bin .and a b => do
      if !(← (← eval env heap a).truth) then return boolean false
      return boolean (← (← eval env heap b).truth)
    | .bin .or a b => do
      if ← (← eval env heap a).truth then return boolean true
      return boolean (← (← eval env heap b).truth)
    | .bin op a b => do comparison op (← eval env heap a) (← eval env heap b)
    | .deref a => do load heap (← (← eval env heap a).address)
    | .address a => do return .pointer (some (← lvalue env heap a))
    | .field a name pointer => do
      let p ← if pointer then do (← eval env heap a).address else lvalue env heap a
      load heap (p.member name)
    | .index a i => do
      let p ← (← eval env heap a).address
      let .integer n ← eval env heap i | none
      if n < 0 then none else load heap (p.index n.toNat)
    | .call (.id "isfinite") [a] => do return boolean (← (← eval env heap a).isFinite)
    | _ => none

  def lvalue (env : Locals) (heap : Heap) : Expr → Option Address
    | .deref a => do (← eval env heap a).address
    | .field a name pointer => do
      let p ← if pointer then do (← eval env heap a).address else lvalue env heap a
      return p.member name
    | .index a i => do
      let p ← (← eval env heap a).address
      let .integer n ← eval env heap i | none
      if n < 0 then none else some (p.index n.toNat)
    | _ => none
end

structure Result where
  value : Value
  heap : Heap

inductive State where
  | running (code : List Stmt) (locals : Locals) (heap : Heap)
  | returned (result : Result)

def next : State → Option State
  | .returned _ | .running [] _ _ => none
  | .running (.declare type name expr :: rest) env heap => do
    let value ← cast type (← eval env heap expr)
    if (env name).isSome then none else
      return .running rest (bind env name value) heap
  | .running (.assign target expr :: rest) env heap => do
    let value ← eval env heap expr
    let address ← lvalue env heap target
    let heap' ← store heap address value
    return .running rest env heap'
  | .running (.eval expr :: rest) env heap => do
    let _ ← eval env heap expr
    return .running rest env heap
  | .running (.ret none :: _) _ heap => some (.returned ⟨.void, heap⟩)
  | .running (.ret (some expr) :: _) env heap => do
    return .returned ⟨← eval env heap expr, heap⟩
  | .running (.branch condition yes no :: rest) env heap => do
    let takeYes ← (← eval env heap condition).truth
    return .running ((if takeYes then yes else no) ++ rest) env heap
  | .running (.whileLoop condition body :: rest) env heap => do
    let again ← (← eval env heap condition).truth
    return .running (if again then body ++ .whileLoop condition body :: rest else rest) env heap

def machine : Transition.Machine State Result where
  step s t := next s = some t
  final | .returned result => some result | _ => none
  deterministic ha hb := Option.some.inj (ha.symm.trans hb)
  final_stuck := by
    intro s result hs t
    cases s <;> simp_all [next]

def run : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => do run n (← next s)

/-- Compose executed blocks through the exact intermediate machine state. -/
theorem run_add (n m : Nat) (s : State) :
    run (n + m) s = (run n s).bind (run m) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    cases hs : next s <;> simp [Nat.succ_add, run, hs, ih]

theorem run_reaches (h : run n s = some t) : Transition.Reaches machine.step s t := by
  induction n generalizing s with
  | zero => cases Option.some.inj h; exact .refl _
  | succ n ih =>
    cases hn : next s with
    | none => simp [run, hn] at h
    | some u =>
      simp only [run, hn] at h
      exact .next hn (ih h)

theorem behaviors_of_run (h : run n s = some (.returned result)) (b) :
    machine.Behaves s b ↔ b = .terminates result :=
  machine.behavior_iff (run_reaches h) rfl

end Rumoca.CBody
