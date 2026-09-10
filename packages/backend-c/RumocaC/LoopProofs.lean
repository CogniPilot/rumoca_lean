import RumocaC.Loops
import RumocaC.LoopCode

/-! Counted-loop execution against the actual C tree, including the mutable
counter, its declared unsigned type, loop condition and every body transition.
The body certificate is compositional and may update unrelated locals/cells. -/
noncomputable section
namespace Rumoca.CLoops
open CTree CMemory
variable [interface : CInterface]
set_option maxRecDepth 10000

def counterEnv (env : CBody.Locals) (counter : String) (i : Nat) : CBody.Locals :=
  CBody.bind env counter (.integer i)

omit interface in
theorem convert_size_nat (n : Nat) (bound : n < 2 ^ 64) :
    convert .size (.integer n) = some (.integer n) := by
  have h : (0 : Int) ≤ n ∧ (n : Int) < 2 ^ 64 := by constructor <;> omega
  simp only [convert, if_pos h]

theorem eval_increment (env : CBody.Locals) (types : Types) (heap : Heap)
    (counter : String) (i : Nat) (value : env counter = some (.integer i))
    (typed : types counter = some .size) (bound : i + 1 < 2 ^ 64) :
    eval env types heap (.bin .add (.id counter) (.nat 1)) = some (.integer (i + 1)) := by
  calc
    _ = (if types counter = some .size then (env counter).bind increment else none) :=
      eval.eq_1 env types heap counter
    _ = (env counter).bind increment := if_pos typed
    _ = (some (.integer i)).bind increment := congrArg (fun v => v.bind increment) value
    _ = increment (.integer i) := Option.bind_some _ _
    _ = _ := increment_exact i bound

theorem assign_local (env : CBody.Locals) (types : Types) (heap : Heap)
    (name : String) (expr : Expr) (rest : List Stmt) (old value converted : Value) (type : CType)
    (present : env name = some old) (typed : types name = some type)
    (evaluated : eval env types heap expr = some value) (cast : convert type value = some converted) :
    next (.running (.assign (.id name) expr :: rest) env types heap) =
      some (.running rest (CBody.bind env name converted) types heap) := by
  simp only [next, present, typed, evaluated, cast, bind, Option.bind_some, pure]

theorem counter_step (env : CBody.Locals) (types : Types) (heap : Heap) (counter : String)
    (i : Nat) (rest : List Stmt) (typed : types counter = some .size) (bound : i + 1 < 2 ^ 64) :
    next (.running (counterStep counter :: rest) (counterEnv env counter i) types heap) =
      some (.running rest (counterEnv env counter (i + 1)) types heap) := by
  have hconvert := convert_size_nat (i + 1) bound
  simp only [Nat.cast_add, Nat.cast_one] at hconvert
  have hvalue : counterEnv env counter i counter = some (.integer i) := by simp [counterEnv, CBody.bind]
  have hbind : CBody.bind (counterEnv env counter i) counter (.integer ((i : Int) + 1)) =
      counterEnv env counter (i + 1) := by
    funext key
    by_cases hk : key = counter <;> simp [counterEnv, CBody.bind, hk, Nat.cast_add, Nat.cast_one]
  have he := eval_increment (counterEnv env counter i) types heap counter i hvalue typed bound
  have hs := assign_local (counterEnv env counter i) types heap counter
    (.bin .add (.id counter) (.nat 1)) rest (.integer i) (.integer (i + 1)) (.integer (i + 1))
    .size hvalue typed he hconvert
  simpa only [counterStep, hbind] using hs

theorem loop_enter (env : CBody.Locals) (types : Types) (heap : Heap) (counter : String)
    (count : Expr) (body rest : List Stmt) (i n : Nat)
    (counter_value : env counter = some (.integer i))
    (count_value : CBody.eval env heap count = some (.integer n))
    (safe : body.all noDeclarations = true) (less : i < n) :
    next (.running (loop counter count body :: rest) env types heap) =
      some (.running (body ++ counterStep counter :: loop counter count body :: rest) env types heap) := by
  have hlt : (i : Int) < n := by exact_mod_cast less
  simp [loop, next, noDeclarations, counterStep, eval, safe, CBody.eval, CBody.resolve,
    counter_value, count_value, CBody.comparison, CBody.boolean, Value.truth, hlt, List.append_assoc]

theorem loop_stop (env : CBody.Locals) (types : Types) (heap : Heap) (counter : String)
    (count : Expr) (body rest : List Stmt) (n : Nat)
    (counter_value : env counter = some (.integer n))
    (count_value : CBody.eval env heap count = some (.integer n))
    (safe : body.all noDeclarations = true) :
    next (.running (loop counter count body :: rest) env types heap) = some (.running rest env types heap) := by
  simp [loop, next, noDeclarations, counterStep, eval, safe, CBody.eval, CBody.resolve,
    counter_value, count_value, CBody.comparison, CBody.boolean, Value.truth]

theorem counter_initialize (env : CBody.Locals) (types : Types) (heap : Heap) (counter : String)
    (rest : List Stmt) (fresh : env counter = none) (size_type : interface.types "size_t" = some .size) :
    next (.running (.declare "size_t" counter (.nat 0) :: rest) env types heap) =
      some (.running rest (counterEnv env counter 0) (bindType types counter .size) heap) := by
  have hc : convert .size (.integer 0) = some (.integer 0) := convert_size_nat 0 (by decide)
  simp [next, eval, CBody.eval, size_type, hc, fresh, counterEnv]

/-- Execute an arbitrary certified body for each counter value, then exit.
The unsigned increment cannot wrap because the bound itself fits `size_t`.
The body may evolve its other local bindings and its heap between iterations. -/
theorem loop_reaches (counter : String) (count : Expr) (body rest : List Stmt)
    (locals : Nat → CBody.Locals) (types : Types) (heaps : Nat → Heap) (n : Nat)
    (typed : types counter = some .size) (bounded : n < 2 ^ 64)
    (safe : body.all noDeclarations = true)
    (count_value : ∀ i ≤ n, CBody.eval (counterEnv (locals i) counter i) (heaps i) count = some (.integer n))
    (body_run : ∀ i < n, Transition.Reaches machine.step
      (.running (body ++ counterStep counter :: loop counter count body :: rest)
        (counterEnv (locals i) counter i) types (heaps i))
      (.running (counterStep counter :: loop counter count body :: rest)
        (counterEnv (locals (i + 1)) counter i) types (heaps (i + 1)))) :
    Transition.Reaches machine.step
      (.running (loop counter count body :: rest) (counterEnv (locals 0) counter 0) types (heaps 0))
      (.running rest (counterEnv (locals n) counter n) types (heaps n)) := by
  suffices ∀ remaining i, remaining + i = n → Transition.Reaches machine.step
      (.running (loop counter count body :: rest) (counterEnv (locals i) counter i) types (heaps i))
      (.running rest (counterEnv (locals n) counter n) types (heaps n)) from this n 0 (by omega)
  intro remaining
  induction remaining with
  | zero =>
    intro i hi
    have he : i = n := by omega
    subst i
    exact .next (loop_stop _ _ _ counter count body rest n
      (by simp [counterEnv, CBody.bind]) (count_value n (by omega)) safe) (.refl _)
  | succ remaining ih =>
    intro i hi
    have less : i < n := by omega
    refine .next (loop_enter _ _ _ counter count body rest i n
      (by simp [counterEnv, CBody.bind]) (count_value i (by omega)) safe less) ?_
    exact (body_run i less).trans (.next
      (counter_step _ types _ counter i _ typed (by omega)) (ih (i + 1) (by omega)))

end Rumoca.CLoops
