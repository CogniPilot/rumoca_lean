import RumocaC.Body
import RumocaC.Statements

/-! Call/return extension of the memory-access machine. Ordinary calls execute
the selected tree body or the existing numerical statement machine, never a
function-name-specific result. Arguments are pure expressions; calls are
supported as entire assignment/declaration/return/discard operands. Function
pointers, nested effectful expressions, allocation and external calls remain
unsupported. This is an authored C fragment, not a native ABI/linker model. -/
noncomputable section
namespace Rumoca.CCalls
open CTree CMemory
variable [interface : CInterface]
set_option maxRecDepth 10000

inductive Definition where
  | tree (fn : CTree.Function)
  | kernel (fn : CStatements.Function)

structure Program where
  definitions : String → Option Definition
  kernel : CSyntax.Program

inductive Destination where
  | assign (target : Expr)
  | declare (type name : String)
  | discard
  | ret

inductive Continuation where
  | done
  | caller (destination : Destination) (rest : List Stmt)
      (locals : CBody.Locals) (resultType : String) (outer : Continuation)

inductive State where
  | body (state : CBody.State) (resultType : String) (stack : Continuation)
  | calling (name : String) (args : List Value) (heap : Heap) (stack : Continuation)
  | kernel (state : CStatements.State) (heap : Heap) (stack : Continuation)
  | returning (value : Value) (heap : Heap) (stack : Continuation)
  | halted (result : CBody.Result)

def returnCast (type : String) (value : Value) : Option Value :=
  if type = "void" then if value = .void then some .void else none
  else CBody.cast type value

/-- C11 N1570 §6.7.6.3 paragraph 7 adjusts an array parameter to a pointer.
The tree supports unsized `T name[]`, without qualifiers inside the brackets.
The adjusted spelling must still resolve in the explicit header dictionary. -/
def parameterType (p : Parameter) : String :=
  if p.array then p.type ++ " *" else p.type

/-- A fresh function scope. Arity, duplicate names and conversions to adjusted
parameter types are checked. Unknown types and unsupported conversions fail. -/
def parameters : List Parameter → List Value → Option CBody.Locals
  | [], [] => some (fun _ => none)
  | p :: ps, v :: vs => do
      let env ← parameters ps vs
      if (env p.name).isSome then none else do
        let value ← CBody.cast (parameterType p) v
        return CBody.bind env p.name value
  | _, _ => none

def arguments (env : CBody.Locals) (heap : Heap) : List Expr → Option (List Value)
  | [] => some []
  | e :: es => do return (← CBody.eval env heap e) :: (← arguments env heap es)

def finiteValue : Value → Option Binary64.Value
  | .float64 bits =>
    if h : bits.toNat % Binary64.signPlace < Binary64.magnitudeCount
    then some (Binary64.ofBits ⟨bits, h⟩) else none
  | _ => none

def counterValue : Value → Option CStatements.Counter
  | .integer n => if h : 0 ≤ n ∧ n < 2 ^ 64
    then some ⟨n.toNat, by omega⟩ else none
  | _ => none

omit interface in
@[simp] theorem finiteValue_finite (x : Binary64.Value) :
    finiteValue (.finite x) = some x := by
  simp [finiteValue, Value.finite, (Binary64.toBits x).property, Binary64.ofBits_toBits]

omit interface in
@[simp] theorem counterValue_counter (n : CStatements.Counter) :
    counterValue (.integer n.val) = some n := by
  simp [counterValue]

@[simp] theorem cast_counter (n : CStatements.Counter)
    (type : interface.types "uint64_t" = some .size) :
    CBody.cast "uint64_t" (.integer n.val) = some (.integer n.val) := by
  have hc : CBody.cast "uint64_t" = convert .size := by
    funext value
    simp only [CBody.cast, type, bind, Option.bind_some]
  rw [hc]
  simp only [convert]
  rw [if_pos ⟨Int.natCast_nonneg n.val, by exact_mod_cast n.isLt⟩]

def kernelEntry (fn : CStatements.Function) (args : List Value) : Option CStatements.State :=
  match fn, args with
  | .rhs, [] => some (.entry .rhs Binary64.positiveZero ⟨0, by decide⟩)
  | .step, [x] => do return .entry .step (← finiteValue x) ⟨0, by decide⟩
  | .sample, [x, n] => do return .entry .sample (← finiteValue x) (← counterValue n)
  | _, _ => none

def callOperand : Stmt → Option (Destination × String × List Expr)
  | .assign target (.call (.id name) args) => some (.assign target, name, args)
  | .declare type name (.call (.id fn) args) => some (.declare type name, fn, args)
  | .eval (.call (.id name) args) => some (.discard, name, args)
  | .ret (some (.call (.id name) args)) => some (.ret, name, args)
  | _ => none

def enterCall (s : CBody.State) (resultType : String) (stack : Continuation) : Option State :=
  match s with
  | .running [] _ heap =>
    if resultType = "void" then some (.returning .void heap stack) else none
  | .running (stmt :: rest) env heap => do
    let (destination, name, args) ← callOperand stmt
    -- A local binding shadows a global function; indirect calls are not in this fragment.
    if (env name).isSome || name = "isfinite" then none else do
      let values ← arguments env heap args
      return .calling name values heap (.caller destination rest env resultType stack)
  | .returned _ => none

def resume (value : Value) (heap : Heap) : Continuation → Option State
  | .done => some (.halted ⟨value, heap⟩)
  | .caller destination rest env resultType outer =>
    match destination with
    | .assign target => do
      let address ← CBody.lvalue env heap target
      let heap' ← store heap address value
      return .body (.running rest env heap') resultType outer
    | .declare type name => do
      if (env name).isSome then none else do
        let converted ← CBody.cast type value
        return .body (.running rest (CBody.bind env name converted) heap) resultType outer
    | .discard => some (.body (.running rest env heap) resultType outer)
    | .ret => do return .returning (← returnCast resultType value) heap outer

def next (p : Program) : State → Option State
  | .halted _ => none
  | .body (.returned r) resultType stack => do
    return .returning (← returnCast resultType r.value) r.heap stack
  | .body s resultType stack =>
    match CBody.next s with
    | some t => some (.body t resultType stack)
    | none => enterCall s resultType stack
  | .calling name args heap stack => do
    match ← p.definitions name with
    | .tree fn =>
      let env ← parameters fn.signature.parameters args
      return .body (.running fn.body env heap) fn.signature.result stack
    | .kernel fn => return .kernel (← kernelEntry fn args) heap stack
  | .kernel (.returned x) heap stack => some (.returning (.finite x) heap stack)
  | .kernel s heap stack => do return .kernel (← CStatements.next p.kernel s) heap stack
  | .returning value heap stack => resume value heap stack

def machine (p : Program) : Transition.Machine State CBody.Result where
  step s t := next p s = some t
  final | .halted result => some result | _ => none
  deterministic ha hb := Option.some.inj (ha.symm.trans hb)
  final_stuck := by
    intro s result hs t
    cases s <;> simp_all [next]

def run (p : Program) : Nat → State → Option State
  | 0, s => some s
  | n + 1, s => do run p n (← next p s)

theorem tree_entry (p : Program) (name args heap stack fn env)
    (hd : p.definitions name = some (.tree fn))
    (hp : parameters fn.signature.parameters args = some env) :
    next p (.calling name args heap stack) =
      some (.body (.running fn.body env heap) fn.signature.result stack) := by
  simp [next, hd, hp]

theorem run_reaches (h : run p n s = some t) : Transition.Reaches (machine p).step s t := by
  induction n generalizing s with
  | zero => cases Option.some.inj h; exact .refl _
  | succ n ih =>
    cases hn : next p s with
    | none => simp [run, hn] at h
    | some u =>
      simp only [run, hn] at h
      exact .next hn (ih h)

theorem behaviors_of_run (h : run p n s = some (.halted result)) (b) :
    (machine p).Behaves s b ↔ b = .terminates result :=
  (machine p).behavior_iff (run_reaches h) rfl

/-- Previously proved memory transitions retain exactly their old meaning. -/
theorem body_step (p : Program) (h : CBody.next s = some t) (type stack) :
    next p (.body s type stack) = some (.body t type stack) := by
  cases s with
  | returned => simp [CBody.next] at h
  | running => simp [next, h]

theorem body_reaches (p : Program)
    (h : Transition.Reaches CBody.machine.step s t) (type stack) :
    Transition.Reaches (machine p).step (.body s type stack) (.body t type stack) := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact .next (body_step p hs type stack) ih

theorem body_behaviors_of_reaches (p : Program)
    (h : Transition.Reaches CBody.machine.step s (.returned result))
    (hc : returnCast type result.value = some result.value) (b) :
    (machine p).Behaves (.body s type .done) b ↔ b = .terminates result := by
  have tailRun : Transition.Reaches (machine p).step
      (.body (.returned result) type .done) (.halted result) :=
    .next (t := .returning result.value result.heap .done)
      (by simp [machine, next, hc]) (.next (by rfl) (.refl _))
  exact (machine p).behavior_iff
    ((body_reaches p h type .done).trans tailRun) rfl

theorem body_behaviors (p : Program) (h : CBody.run n s = some (.returned result))
    (hc : returnCast type result.value = some result.value) (b) :
    (machine p).Behaves (.body s type .done) b ↔ b = .terminates result :=
  body_behaviors_of_reaches p (CBody.run_reaches h) hc b

theorem kernel_step (p : Program) (h : CStatements.next p.kernel s = some t) (heap stack) :
    next p (.kernel s heap stack) = some (.kernel t heap stack) := by
  cases s <;> simp_all [CStatements.next, next]

theorem kernel_reaches (p : Program) (h : CStatements.Reaches p.kernel s t) (heap stack) :
    Transition.Reaches (machine p).step (.kernel s heap stack) (.kernel t heap stack) := by
  induction h with
  | refl => exact .refl _
  | next hs _ ih => exact .next (kernel_step p hs heap stack) ih

/-- All numerical statements are executed, with their existing proof, while
the caller heap and continuation are carried unchanged. -/
theorem kernel_correct (p : Program) (m : Solve.Model source)
    (hp : p.kernel = Rumoca.CExecution.program m) (fn x n heap stack) :
    Transition.Reaches (machine p).step (.kernel (.entry fn x n) heap stack)
      (.returning (.finite (CStatements.result m fn x n)) heap stack) := by
  have h := CStatements.call_reaches m fn x n
  rw [← hp] at h
  exact (kernel_reaches p h heap stack).trans (.next (by rfl) (.refl _))

end Rumoca.CCalls
