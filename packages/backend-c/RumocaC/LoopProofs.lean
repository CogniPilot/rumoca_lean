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

omit interface in
theorem sizeAdd_exact (a b : Nat) (bound : a + b < 2 ^ 64) :
    sizeAdd (.integer a) (.integer b) = some (.integer (a + b)) := by
  have ha := convert_size_nat a (by omega)
  have hb := convert_size_nat b (by omega)
  have sumLower : (0 : Int) ≤ (a : Int) + b := by omega
  have sumUpper : (a : Int) + b < 2 ^ 64 := by exact_mod_cast bound
  simp only [sizeAdd, ha, hb, bind, Option.bind_some, pure, Int.emod_eq_of_lt sumLower sumUpper]

theorem eval_sizeAdd (env : CBody.Locals) (types : Types) (heap : Heap)
    (left right : String) (a b : Nat)
    (hl : env left = some (.integer a)) (hr : env right = some (.integer b))
    (tl : types left = some .size) (tr : types right = some .size) (bound : a + b < 2 ^ 64) :
    eval env types heap (.bin .add (.id left) (.id right)) = some (.integer (a + b)) := by
  have both : types left = some .size ∧ types right = some .size := ⟨tl, tr⟩
  calc
    _ = (if types left = some .size ∧ types right = some .size then
      (env left).bind (fun x => (env right).bind (sizeAdd x))
      else (CBody.eval env heap (.id left)).bind (fun x =>
        (CBody.eval env heap (.id right)).bind (CArithmetic.floatAdd x))) := evalWith.eq_2 CBody.legacyExpressions env types heap left right
    _ = (env left).bind (fun x => (env right).bind (sizeAdd x)) := if_pos both
    _ = (some (.integer a)).bind (fun x => (env right).bind (sizeAdd x)) :=
      congrArg (fun v => v.bind (fun x => (env right).bind (sizeAdd x))) hl
    _ = (env right).bind (sizeAdd (.integer a)) := Option.bind_some _ _
    _ = (some (.integer b)).bind (sizeAdd (.integer a)) := congrArg (fun v => v.bind (sizeAdd (.integer a))) hr
    _ = sizeAdd (.integer a) (.integer b) := Option.bind_some _ _
    _ = _ := sizeAdd_exact a b bound

theorem declare_local (env : CBody.Locals) (types : Types) (heap : Heap)
    (type name : String) (expr : Expr) (rest : List Stmt) (declared : CType) (value converted : Value)
    (typed : interface.types type = some declared) (fresh : env name = none)
    (evaluated : eval env types heap expr = some value) (cast : convert declared value = some converted) :
    next (.running (.declare type name expr :: rest) env types heap) =
      some (.running rest (CBody.bind env name converted) (bindType types name declared) heap) := by
  simp only [next, nextWith, typed, evaluated, cast, fresh, Option.isSome_none, Bool.false_eq_true,
    ↓reduceIte, bind, Option.bind_some, pure]

theorem eval_increment (env : CBody.Locals) (types : Types) (heap : Heap)
    (counter : String) (i : Nat) (value : env counter = some (.integer i))
    (typed : types counter = some .size) (bound : i + 1 < 2 ^ 64) :
    eval env types heap (.bin .add (.id counter) (.nat 1)) = some (.integer (i + 1)) := by
  calc
    _ = (if types counter = some .size then (env counter).bind increment else none) :=
      evalWith.eq_1 CBody.legacyExpressions env types heap counter
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
  simp only [next, nextWith, present, typed, evaluated, cast, bind, Option.bind_some, pure]

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
  simp [loop, next, nextWith, noDeclarations, counterStep, evalWith, CBody.legacyExpressions, safe, CBody.eval, CBody.evalWith, CBody.resolve,
    counter_value, count_value, CBody.comparison, CBody.boolean, Value.truth, hlt, List.append_assoc]

theorem loop_stop (env : CBody.Locals) (types : Types) (heap : Heap) (counter : String)
    (count : Expr) (body rest : List Stmt) (n : Nat)
    (counter_value : env counter = some (.integer n))
    (count_value : CBody.eval env heap count = some (.integer n))
    (safe : body.all noDeclarations = true) :
    next (.running (loop counter count body :: rest) env types heap) = some (.running rest env types heap) := by
  simp [loop, next, nextWith, noDeclarations, counterStep, evalWith, CBody.legacyExpressions, safe, CBody.eval, CBody.evalWith, CBody.resolve,
    counter_value, count_value, CBody.comparison, CBody.boolean, Value.truth]

theorem counter_initialize (env : CBody.Locals) (types : Types) (heap : Heap) (counter : String)
    (rest : List Stmt) (fresh : env counter = none) (size_type : interface.types "size_t" = some .size) :
    next (.running (.declare "size_t" counter (.nat 0) :: rest) env types heap) =
      some (.running rest (counterEnv env counter 0) (bindType types counter .size) heap) := by
  have hc : convert .size (.integer 0) = some (.integer 0) := convert_size_nat 0 (by decide)
  simp [next, nextWith, evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, size_type, hc, fresh, counterEnv]

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
