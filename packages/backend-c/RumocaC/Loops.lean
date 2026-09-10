import RumocaC.Arithmetic

/-! The C loop fragment used by tensor emission. Local declared types are
retained for assignment conversions and unsigned counter arithmetic. Loop and
branch bodies may not declare locals, so flattening them does not lose a C
block scope. Calls, local addresses and general mixed arithmetic are excluded.
The existing symbolic array cells and expression rules are reused. -/
noncomputable section
namespace Rumoca.CLoops
open CTree CMemory
variable [interface : CInterface]

abbrev Types := String → Option CType

def bindType (types : Types) (name : String) (type : CType) : Types :=
  fun key => if key = name then some type else types key

/-- Increment a declared unsigned size value with its C modulo semantics.
The emitted-loop proof establishes that wrapping is unreachable. -/
def increment (value : Value) : Option Value := do
  let .integer n ← convert .size value | none
  return .integer ((n + 1) % (2 ^ 64))

def eval (env : CBody.Locals) (types : Types) (heap : Heap) : Expr → Option Value
  | .bin .add (.id name) (.nat 1) => do
      if types name = some .size then increment (← env name)
      else none
  | .bin .add a b => do CArithmetic.floatAdd (← CBody.eval env heap a) (← CBody.eval env heap b)
  | .bin .mul a b => do CArithmetic.floatMul (← CBody.eval env heap a) (← CBody.eval env heap b)
  | e => CBody.eval env heap e

def noDeclarations : Stmt → Bool
  | .declare .. => false
  | .branch _ yes no => yes.attach.all (fun s => noDeclarations s.val) && no.attach.all (fun s => noDeclarations s.val)
  | .whileLoop _ body => body.attach.all (fun s => noDeclarations s.val)
  | _ => true
termination_by s => sizeOf s
decreasing_by
  all_goals
    have h := List.sizeOf_lt_of_mem s.property
    simp only [Stmt.branch.sizeOf_spec, Stmt.whileLoop.sizeOf_spec]
    omega

inductive State where
  | running (code : List Stmt) (locals : CBody.Locals) (types : Types) (heap : Heap)
  | returned (result : CBody.Result)

def next : State → Option State
  | .returned _ | .running [] _ _ _ => none
  | .running (.declare type name expr :: rest) env types heap => do
      let declared ← interface.types type
      let value ← convert declared (← eval env types heap expr)
      if (env name).isSome then none else
        return .running rest (CBody.bind env name value) (bindType types name declared) heap
  | .running (.assign (.id name) expr :: rest) env types heap => do
      let _ ← env name
      let declared ← types name
      let value ← convert declared (← eval env types heap expr)
      return .running rest (CBody.bind env name value) types heap
  | .running (.assign target expr :: rest) env types heap => do
      let value ← eval env types heap expr
      let address ← CBody.lvalue env heap target
      let heap' ← store heap address value
      return .running rest env types heap'
  | .running (.eval expr :: rest) env types heap => do
      let _ ← eval env types heap expr
      return .running rest env types heap
  | .running (.ret none :: _) _ _ heap => some (.returned ⟨.void, heap⟩)
  | .running (.ret (some expr) :: _) env types heap => do
      return .returned ⟨← eval env types heap expr, heap⟩
  | .running (.branch condition yes no :: rest) env types heap => do
      if !(yes.all noDeclarations && no.all noDeclarations) then none else do
        let takeYes ← (← eval env types heap condition).truth
        return .running ((if takeYes then yes else no) ++ rest) env types heap
  | .running (.whileLoop condition body :: rest) env types heap => do
      if !(body.all noDeclarations) then none else do
        let again ← (← eval env types heap condition).truth
        return .running (if again then body ++ .whileLoop condition body :: rest else rest) env types heap

def machine : Transition.Machine State CBody.Result where
  step s t := next s = some t
  final | .returned result => some result | _ => none
  deterministic ha hb := Option.some.inj (ha.symm.trans hb)
  final_stuck := by intro s result hs t; cases s <;> simp_all [next]

def run : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => do run n (← next s)

theorem run_add (n m : Nat) (s : State) : run (n + m) s = (run n s).bind (run m) := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih => cases hs : next s <;> simp [Nat.succ_add, run, hs, ih]

theorem run_reaches (h : run n s = some t) : Transition.Reaches machine.step s t := by
  induction n generalizing s with
  | zero => cases Option.some.inj h; exact .refl _
  | succ n ih =>
    cases hn : next s with
    | none => simp [run, hn] at h
    | some u =>
      simp only [run, hn] at h
      exact .next hn (ih h)

theorem behaviors_of_run (h : run n s = some (.returned result)) (behavior) :
    machine.Behaves s behavior ↔ behavior = .terminates result :=
  machine.behavior_iff (run_reaches h) rfl

omit interface in
theorem increment_exact (n : Nat) (bound : n + 1 < 2 ^ 64) :
    increment (.integer n) = some (.integer (n + 1)) := by
  have hn : (0 : Int) ≤ n ∧ (n : Int) < 2 ^ 64 := by constructor <;> omega
  have hs : (0 : Int) ≤ n + 1 := by omega
  have hb : (n : Int) + 1 < 2 ^ 64 := by exact_mod_cast bound
  simp only [increment, convert, if_pos hn, bind, Option.bind_some, pure,
    Int.emod_eq_of_lt hs hb]

end Rumoca.CLoops
