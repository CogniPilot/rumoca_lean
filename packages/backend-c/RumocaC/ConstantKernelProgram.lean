import RumocaC.LoopCalls
import RumocaC.LoopProofs
import RumocaC.Arithmetic
import RumocaC.Execution
import RumocaCore.Constant.Semantics

/-! Executable numerical C for the G01 constant-rate profile. The three kernel
entries are `CTree.Function` definitions over the source rate list, universal in
the number of states and in the rates:

* `rumoca_constant_rhs(double *der)` writes the exactly rounded rate vector into
  the caller's derivative region, one declaration-order store per source rate;
* `rumoca_constant_step(double *x)` advances every state cell by the finite
  binary64 addition of its rate, one declaration-order update per source rate;
* `rumoca_constant_sample(double *x, size_t n)` iterates that whole-vector step a
  counted number of times.

Each body is executed by the loop-call machine over the caller-owned array; no
dynamic allocation is emitted. The rate literals enter as C floating constants
whose target binary64 value is the round-to-nearest-even of their exact base-ten
content (C11 6.4.4.2), specified by the body semantics `CBody.decimalValue`.
Listing the source rates is not tensor-coordinate enumeration: the rates are the
model's source data. -/
noncomputable section
namespace Rumoca.CConstant
open Rumoca.CTree Rumoca.CMemory Rumoca.ConstantProfile
set_option maxRecDepth 10000

/-! ### Rate literals and their rounded binary64 values -/

/-- The C floating constant for a source rate. Its exact base-ten magnitude is
`|sign| * mantissa * 10 ^ power`, negated when the sign is negative.
The body semantics assigns its nearest-even binary64 value; correspondence with
an external C translator's literal conversion is a separate trusted boundary. -/
def rateLit (d : Decimal) : Expr :=
  .decimal (decide (d.sign < 0)) (d.sign.natAbs * d.mantissa) d.power

/-- The exactly rounded binary64 rate of a source literal: the nearest-even
rounding of its exact base-ten content, as denoted by the C body semantics. -/
noncomputable def rateVal (d : Decimal) : Binary64.Value :=
  CBody.decimalValue (decide (d.sign < 0)) (d.sign.natAbs * d.mantissa) d.power

/-- The declaration-order rounded rate vector of the source list. -/
noncomputable def rateVals (rates : List Decimal) : List Binary64.Value := rates.map rateVal

/-- The whole-vector explicit Euler update of a state list by the rate list:
each state advances by the finite binary64 addition of its rate. -/
noncomputable def euler (rates : List Decimal) (xs : List Binary64.Value) : List Binary64.Value :=
  List.zipWith (fun x d => Binary64.roundedAdd x (rateVal d)) xs rates

/-- The state after `k` whole-vector steps from `xs0`. -/
noncomputable def stateAfter (rates : List Decimal) (xs0 : List Binary64.Value) : Nat → List Binary64.Value
  | 0 => xs0
  | k + 1 => euler rates (stateAfter rates xs0 k)

theorem euler_length (rates : List Decimal) (xs : List Binary64.Value) :
    (euler rates xs).length = min xs.length rates.length := by
  simp [euler]

theorem stateAfter_length (rates : List Decimal) (xs0 : List Binary64.Value)
    (len : xs0.length = rates.length) (k : Nat) : (stateAfter rates xs0 k).length = rates.length := by
  induction k with
  | zero => simpa using len
  | succ k ih => simp [stateAfter, euler_length, ih]

/-! ### A caller-owned finite-value writer over consecutive cells -/

theorem index_ne (base : Address) {a b : Nat} (h : a ≠ b) : base.index a ≠ base.index b := by
  intro he
  have := congrArg Address.offset he
  simp only [Address.index] at this
  omega

/-- The heap after storing finite values `vs` into consecutive writable
float64 cells from `base.index start`, one per element in order. -/
noncomputable def place (base : Address) (start : Nat) (heap : Heap) : List Binary64.Value → Heap
  | [] => heap
  | v :: vs => place base (start + 1) (replace heap (base.index start) ⟨.float64, true, some (.finite v)⟩) vs

/-- The consecutive float64 cells from `base.index start` hold the finite
values `vs`, and are writable. -/
def cells (heap : Heap) (base : Address) (start : Nat) : List Binary64.Value → Prop
  | [] => True
  | v :: vs => heap (base.index start) = some ⟨.float64, true, some (.finite v)⟩ ∧ cells heap base (start + 1) vs

/-- The consecutive cells from `base.index start` are writable float64 cells. -/
def writableN (heap : Heap) (base : Address) (start : Nat) : Nat → Prop
  | 0 => True
  | n + 1 => (∃ old, heap (base.index start) = some ⟨.float64, true, old⟩) ∧ writableN heap base (start + 1) n

theorem writableN_replace_below (base : Address) (start s : Nat) (heap : Heap) (c : Cell) (n : Nat)
    (below : start < s) (w : writableN heap base s n) :
    writableN (replace heap (base.index start) c) base s n := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih =>
    obtain ⟨⟨old, h0⟩, wt⟩ := w
    refine ⟨⟨old, ?_⟩, ih (s + 1) (by omega) wt⟩
    rw [replace_other _ _ _ _ (index_ne base (by omega))]
    exact h0

theorem cells_replace_below (base : Address) (start s : Nat) (heap : Heap) (c : Cell) (xs : List Binary64.Value)
    (below : start < s) (h : cells heap base s xs) :
    cells (replace heap (base.index start) c) base s xs := by
  induction xs generalizing s with
  | nil => trivial
  | cons x xs ih =>
    obtain ⟨h0, ht⟩ := h
    refine ⟨?_, ih (s + 1) (by omega) ht⟩
    rw [replace_other _ _ _ _ (index_ne base (by omega))]
    exact h0

theorem place_frame (base : Address) (start : Nat) (heap : Heap) (vs : List Binary64.Value) (q : Address)
    (outside : ∀ j < vs.length, q ≠ base.index (start + j)) :
    place base start heap vs q = heap q := by
  induction vs generalizing start heap with
  | nil => rfl
  | cons v vs ih =>
    rw [place, ih (start + 1)]
    · exact replace_other _ _ _ _ (by simpa using outside 0 (by simp))
    · intro j hj
      have := outside (j + 1) (by simpa using hj)
      have e : start + 1 + j = start + (j + 1) := by omega
      rw [e]; exact this

/-- The written cells hold exactly the placed values. -/
theorem place_cells (base : Address) (start : Nat) (heap : Heap) (vs : List Binary64.Value) :
    cells (place base start heap vs) base start vs := by
  induction vs generalizing start heap with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_, ?_⟩
    · rw [place, place_frame base (start + 1) _ vs (base.index start)]
      · simp [replace]
      · intro j hj; exact index_ne base (by omega)
    · rw [place]; exact ih (start + 1) _

/-- Placing values agrees with the base heap outside the written cells. -/
theorem place_outside (base : Address) (start : Nat) (heap : Heap) (vs : List Binary64.Value) (q : Address)
    (outside : ∀ j < vs.length, q ≠ base.index (start + j)) :
    place base start heap vs q = heap q := place_frame base start heap vs q outside

theorem load_finite (heap : Heap) (p : Address) (x : Binary64.Value)
    (hp : heap p = some ⟨.float64, true, some (.finite x)⟩) : load heap p = some (.finite x) := by
  simp [load, hp, Value.finite, convert]

theorem store_finite (heap : Heap) (p : Address) (old : Option Value) (x : Binary64.Value)
    (hp : heap p = some ⟨.float64, true, old⟩) :
    store heap p (.finite x) = some (replace heap p ⟨.float64, true, some (.finite x)⟩) := by
  simpa only [Value.finite] using store_float64 heap p old (Binary64.toBits x).val hp

/-! ### Evaluating the rate literal and the indexed lvalue -/

variable [interface : CInterface]

/-- The loop machine evaluates a rate literal to its rounded binary64 value,
independent of the environment, types and heap. -/
theorem eval_rateLit (env : CBody.Locals) (types : CLoops.Types) (heap : Heap) (d : Decimal) :
    CLoops.eval env types heap (rateLit d) = some (.finite (rateVal d)) := by
  rw [rateLit, rateVal]
  rfl

/-- Subscripting a caller pointer parameter with a literal index denotes the
addressed array cell. -/
theorem index_lvalue_nat (env : CBody.Locals) (heap : Heap) (name : String) (base : Address) (start : Nat)
    (ptr : env name = some (.pointer (some base))) :
    CBody.lvalue env heap (.index (.id name) (.nat start)) = some (base.index start) := by
  simp [CBody.lvalue, CBody.lvalueWith, CBody.evalWith, CBody.resolve, ptr, Value.address]

/-- Evaluating a subscripted caller pointer parameter loads the addressed cell. -/
theorem index_eval_nat (env : CBody.Locals) (heap : Heap) (name : String) (base : Address) (start : Nat)
    (ptr : env name = some (.pointer (some base))) :
    CBody.eval env heap (.index (.id name) (.nat start)) = load heap (base.index start) := by
  simp [CBody.eval, CBody.evalWith, CBody.resolve, ptr, Value.address]

/-! ### The kernel statement lists, universal in the source rates -/

/-- The declaration-order rate stores `der[start] = rate;`, one per source rate. -/
def rhsStmts (name : String) : Nat → List Decimal → List Stmt
  | _, [] => []
  | start, d :: ds => .assign (.index (.id name) (.nat start)) (rateLit d) :: rhsStmts name (start + 1) ds

/-- The declaration-order finite Euler updates `x[start] = (x[start] + rate);`,
one per source rate. -/
def stepStmts (name : String) : Nat → List Decimal → List Stmt
  | _, [] => []
  | start, d :: ds =>
      .assign (.index (.id name) (.nat start)) (.bin .add (.index (.id name) (.nat start)) (rateLit d))
        :: stepStmts name (start + 1) ds

omit interface in
theorem stepStmts_noDecl (name : String) (start : Nat) (ds : List Decimal) :
    (stepStmts name start ds).all CLoops.noDeclarations = true := by
  induction ds generalizing start with
  | nil => rfl
  | cons d ds ih => simpa [stepStmts, List.all_cons, CLoops.noDeclarations] using ih (start + 1)

/-! ### `rumoca_constant_rhs`: one rounded-rate store per source rate -/

/-- The per-state store `der[start] = rate;` writes the rounded rate into the
addressed cell and touches nothing else. -/
theorem rhs_next (name : String) (base : Address) (d : Decimal) (env : CBody.Locals)
    (types : CLoops.Types) (heap : Heap) (start : Nat) (rest : List Stmt) (old : Option Value)
    (ptr : env name = some (.pointer (some base)))
    (cell : heap (base.index start) = some ⟨.float64, true, old⟩) :
    CLoops.next (.running (.assign (.index (.id name) (.nat start)) (rateLit d) :: rest) env types heap)
      = some (.running rest env types
        (replace heap (base.index start) ⟨.float64, true, some (.finite (rateVal d))⟩)) := by
  have evaluated := eval_rateLit env types heap d
  simp only [CLoops.eval, CBody.legacyExpressions] at evaluated
  simp only [CLoops.next, CLoops.nextWith, evaluated, CBody.legacyExpressions,
    index_lvalue_nat env heap name base start ptr,
    store_finite heap (base.index start) old (rateVal d) cell, bind, Option.bind_some, pure]

/-- The declaration-order rate stores reach the heap that holds the rounded
rate vector, from any writable derivative region. -/
theorem rhs_reaches (name : String) (base : Address) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (rest : List Stmt) (start : Nat) (ds : List Decimal)
    (ptr : env name = some (.pointer (some base)))
    (writable : writableN heap base start ds.length) :
    Transition.Reaches CLoops.machine.step
      (.running (rhsStmts name start ds ++ rest) env types heap)
      (.running rest env types (place base start heap (ds.map rateVal))) := by
  induction ds generalizing start heap with
  | nil => exact .refl _
  | cons d ds ih =>
    obtain ⟨⟨old, cell⟩, wtail⟩ := writable
    refine .next (rhs_next name base d env types heap start (rhsStmts name (start + 1) ds ++ rest) old ptr cell) ?_
    have wtail' : writableN (replace heap (base.index start) ⟨.float64, true, some (.finite (rateVal d))⟩)
        base (start + 1) ds.length :=
      writableN_replace_below base start (start + 1) heap _ ds.length (by omega) wtail
    have := ih (start := start + 1)
      (heap := replace heap (base.index start) ⟨.float64, true, some (.finite (rateVal d))⟩) wtail'
    simpa only [place, List.map_cons] using this

/-! ### `rumoca_constant_step`: one finite Euler update per source rate -/

/-- The per-state update `x[start] = (x[start] + rate);` advances the addressed
cell by the finite binary64 addition of its rate and touches nothing else. -/
theorem step_next (name : String) (base : Address) (d : Decimal) (env : CBody.Locals)
    (types : CLoops.Types) (heap : Heap) (start : Nat) (rest : List Stmt) (x : Binary64.Value)
    (ptr : env name = some (.pointer (some base)))
    (cell : heap (base.index start) = some ⟨.float64, true, some (.finite x)⟩)
    (finite : CExecution.finiteRoundDomain (Binary64.units x + Binary64.units (rateVal d))) :
    CLoops.next (.running
        (.assign (.index (.id name) (.nat start)) (.bin .add (.index (.id name) (.nat start)) (rateLit d)) :: rest)
        env types heap)
      = some (.running rest env types
        (replace heap (base.index start) ⟨.float64, true, some (.finite (Binary64.roundedAdd x (rateVal d)))⟩)) := by
  have hload : CBody.eval env heap (.index (.id name) (.nat start)) = some (.finite x) := by
    rw [index_eval_nat env heap name base start ptr, load_finite heap (base.index start) x cell]
  have hlit : CBody.eval env heap (rateLit d) = some (.finite (rateVal d)) := by
    rw [rateLit, rateVal]; rfl
  have hadd : CLoops.eval env types heap
      (.bin .add (.index (.id name) (.nat start)) (rateLit d))
      = some (.finite (Binary64.roundedAdd x (rateVal d))) := by
    have hunfold : CLoops.eval env types heap (.bin .add (.index (.id name) (.nat start)) (rateLit d))
        = (CBody.eval env heap (.index (.id name) (.nat start))).bind
            (fun av => (CBody.eval env heap (rateLit d)).bind (fun bv => CArithmetic.floatAdd av bv)) := rfl
    rw [hunfold, hload, hlit]
    simp only [Option.bind_some]
    exact CArithmetic.floatAdd_finite x (rateVal d) finite
  simp only [CLoops.eval, CBody.legacyExpressions] at hadd
  simp only [CLoops.next, CLoops.nextWith, hadd, CBody.legacyExpressions,
    index_lvalue_nat env heap name base start ptr,
    store_finite heap (base.index start) (some (.finite x)) (Binary64.roundedAdd x (rateVal d)) cell,
    bind, Option.bind_some, pure]

/-- The declaration-order finite Euler updates reach the heap that holds the
whole-vector step, given the current values and per-cell finite-addition
premises. -/
theorem step_reaches (name : String) (base : Address) (env : CBody.Locals) (types : CLoops.Types)
    (heap : Heap) (rest : List Stmt) (start : Nat) (xs : List Binary64.Value) (ds : List Decimal)
    (ptr : env name = some (.pointer (some base))) (len : xs.length = ds.length)
    (cellsH : cells heap base start xs)
    (finite : ∀ i (hi : i < ds.length),
      CExecution.finiteRoundDomain (Binary64.units xs[i] + Binary64.units (rateVal ds[i]))) :
    Transition.Reaches CLoops.machine.step
      (.running (stepStmts name start ds ++ rest) env types heap)
      (.running rest env types (place base start heap (euler ds xs))) := by
  induction ds generalizing xs start heap with
  | nil =>
    simp only [stepStmts, List.nil_append, euler, List.zipWith_nil_right, place]
    exact .refl _
  | cons d ds ih =>
    obtain ⟨x, xs', rfl⟩ : ∃ x xs', xs = x :: xs' := by
      cases xs with
      | nil => simp at len
      | cons x xs' => exact ⟨x, xs', rfl⟩
    obtain ⟨cell, ctail⟩ := cellsH
    have hlen : xs'.length = ds.length := by simpa using len
    have hfin0 : CExecution.finiteRoundDomain (Binary64.units x + Binary64.units (rateVal d)) := by
      simpa using finite 0 (by simp)
    refine .next (step_next name base d env types heap start (stepStmts name (start + 1) ds ++ rest) x ptr cell hfin0) ?_
    have ctail' : cells (replace heap (base.index start)
        ⟨.float64, true, some (.finite (Binary64.roundedAdd x (rateVal d)))⟩) base (start + 1) xs' :=
      cells_replace_below base start (start + 1) heap _ xs' (by omega) ctail
    have finite' : ∀ i (hi : i < ds.length),
        CExecution.finiteRoundDomain (Binary64.units xs'[i] + Binary64.units (rateVal ds[i])) := by
      intro i hi
      simpa using finite (i + 1) (by simpa using hi)
    have := ih (xs := xs') (start := start + 1)
      (heap := replace heap (base.index start) ⟨.float64, true, some (.finite (Binary64.roundedAdd x (rateVal d)))⟩)
      (by simpa using len) ctail' finite'
    simpa only [stepStmts, euler, List.zipWith_cons_cons, place] using this

/-! ### The three kernel entries as `CTree.Function` definitions -/

/-- `void rumoca_constant_rhs(double *der)`: writes the rounded rate vector. -/
def rhsFunction (rates : List Decimal) : Function where
  signature := ⟨"void", "rumoca_constant_rhs", [⟨"double *", "der", false⟩]⟩
  body := rhsStmts "der" 0 rates ++ [.ret none]
  static := false

/-- `void rumoca_constant_step(double *x)`: one finite Euler step of the whole
state vector. -/
def stepFunction (rates : List Decimal) : Function where
  signature := ⟨"void", "rumoca_constant_step", [⟨"double *", "x", false⟩]⟩
  body := stepStmts "x" 0 rates ++ [.ret none]
  static := false

/-- `void rumoca_constant_sample(double *x, size_t n)`: iterates the whole-vector
Euler step `n` times. -/
def sampleFunction (rates : List Decimal) : Function where
  signature := ⟨"void", "rumoca_constant_sample", [⟨"double *", "x", false⟩, ⟨"size_t", "n", false⟩]⟩
  body := CLoops.counted "i" (.id "n") (stepStmts "x" 0 rates) ++ [.ret none]
  static := false

/-! ### Binding a single caller pointer parameter -/

theorem one_pointer_params (name : String) (base : Address) (ptrTy : interface.types "double *" = some .pointer) :
    CCalls.parameters [⟨"double *", name, false⟩] [.pointer (some base)]
      = some (CBody.bind (fun _ => none) name (.pointer (some base))) := by
  simp [CCalls.parameters, CCalls.parameterType, CBody.cast, ptrTy, convert]

theorem one_pointer_types (name : String) (ptrTy : interface.types "double *" = some .pointer) :
    CLoops.Calls.parameterTypes [⟨"double *", name, false⟩]
      = some (CLoops.bindType (fun _ => none) name .pointer) := by
  simp [CLoops.Calls.parameterTypes, CCalls.parameterType, ptrTy]

omit interface in
theorem bind_here (name : String) (v : Value) (env : CBody.Locals) : CBody.bind env name v name = some v := by
  simp [CBody.bind]

/-! ### `rumoca_constant_rhs` reaches its rounded rate vector -/

theorem rhs_behaves (definitions : CLoops.Calls.Definitions) (rates : List Decimal) (base : Address) (heap : Heap)
    (found : definitions "rumoca_constant_rhs" = some (rhsFunction rates))
    (ptrTy : interface.types "double *" = some .pointer)
    (writable : writableN heap base 0 rates.length) (behavior) :
    (CLoops.Calls.machine definitions).Behaves
      (.calling "rumoca_constant_rhs" [.pointer (some base)] heap .done) behavior ↔
      behavior = .terminates (place base 0 heap (rateVals rates)) := by
  have executed : Transition.Reaches CLoops.machine.step
      (.running (rhsFunction rates).body (CBody.bind (fun _ => none) "der" (.pointer (some base)))
        (CLoops.bindType (fun _ => none) "der" .pointer) heap)
      (.returned ⟨.void, place base 0 heap (rateVals rates)⟩) :=
    (rhs_reaches "der" base _ _ heap [.ret none] 0 rates (bind_here "der" _ _) writable).trans
      (.next rfl (.refl _))
  exact CLoops.Calls.call_behaviors definitions "rumoca_constant_rhs" [.pointer (some base)] heap
    (place base 0 heap (rateVals rates)) (rhsFunction rates) _ _ found rfl
    (one_pointer_params "der" base ptrTy) (one_pointer_types "der" ptrTy) executed behavior

/-! ### `rumoca_constant_step` reaches the finite whole-vector Euler step -/

theorem step_behaves (definitions : CLoops.Calls.Definitions) (rates : List Decimal) (base : Address) (heap : Heap)
    (xs : List Binary64.Value) (len : xs.length = rates.length)
    (found : definitions "rumoca_constant_step" = some (stepFunction rates))
    (ptrTy : interface.types "double *" = some .pointer)
    (cellsH : cells heap base 0 xs)
    (finite : ∀ i (hi : i < rates.length),
      CExecution.finiteRoundDomain (Binary64.units xs[i] + Binary64.units (rateVal rates[i]))) (behavior) :
    (CLoops.Calls.machine definitions).Behaves
      (.calling "rumoca_constant_step" [.pointer (some base)] heap .done) behavior ↔
      behavior = .terminates (place base 0 heap (euler rates xs)) := by
  have executed : Transition.Reaches CLoops.machine.step
      (.running (stepFunction rates).body (CBody.bind (fun _ => none) "x" (.pointer (some base)))
        (CLoops.bindType (fun _ => none) "x" .pointer) heap)
      (.returned ⟨.void, place base 0 heap (euler rates xs)⟩) :=
    (step_reaches "x" base _ _ heap [.ret none] 0 xs rates (bind_here "x" _ _) len cellsH finite).trans
      (.next rfl (.refl _))
  exact CLoops.Calls.call_behaviors definitions "rumoca_constant_step" [.pointer (some base)] heap
    (place base 0 heap (euler rates xs)) (stepFunction rates) _ _ found rfl
    (one_pointer_params "x" base ptrTy) (one_pointer_types "x" ptrTy) executed behavior

/-! ### `rumoca_constant_sample` iterates the whole-vector step -/

/-- The heap after `k` whole-vector Euler steps from the state `xs0`, each step
rewriting the `x` region with the next state. -/
noncomputable def runHeap (base : Address) (rates : List Decimal) (xs0 : List Binary64.Value)
    (heap : Heap) : Nat → Heap
  | 0 => heap
  | k + 1 => place base 0 (runHeap base rates xs0 heap k) (stateAfter rates xs0 (k + 1))

omit interface in
theorem runHeap_cells (base : Address) (rates : List Decimal) (xs0 : List Binary64.Value) (heap : Heap)
    (hc0 : cells heap base 0 xs0) :
    ∀ k, cells (runHeap base rates xs0 heap k) base 0 (stateAfter rates xs0 k)
  | 0 => hc0
  | k + 1 => place_cells base 0 (runHeap base rates xs0 heap k) (stateAfter rates xs0 (k + 1))

omit interface in
theorem runHeap_frame (base : Address) (rates : List Decimal) (xs0 : List Binary64.Value) (heap : Heap)
    (len0 : xs0.length = rates.length) (q : Address) (outside : ∀ j < rates.length, q ≠ base.index j) :
    ∀ k, runHeap base rates xs0 heap k q = heap q
  | 0 => rfl
  | k + 1 => by
      rw [runHeap, place_frame base 0 (runHeap base rates xs0 heap k) (stateAfter rates xs0 (k + 1)) q]
      · exact runHeap_frame base rates xs0 heap len0 q outside k
      · intro j hj
        rw [stateAfter_length rates xs0 len0 (k + 1)] at hj
        simpa using outside j hj

/-- Fresh parameter environment of the sample entry. -/
def sampleLocals (base : Address) (N : Nat) : CBody.Locals :=
  CBody.bind (CBody.bind (fun _ => none) "n" (.integer N)) "x" (.pointer (some base))

/-- Declared parameter types of the sample entry. -/
def sampleTypes : CLoops.Types :=
  CLoops.bindType (CLoops.bindType (fun _ => none) "n" .size) "x" .pointer

omit interface in
theorem sampleLocals_x (base : Address) (N : Nat) : sampleLocals base N "x" = some (.pointer (some base)) := by
  simp [sampleLocals, CBody.bind]

omit interface in
theorem sampleLocals_n (base : Address) (N : Nat) : sampleLocals base N "n" = some (.integer N) := by
  simp [sampleLocals, CBody.bind]

omit interface in
theorem sampleLocals_i (base : Address) (N : Nat) : sampleLocals base N "i" = none := by
  simp [sampleLocals, CBody.bind]

omit interface in
theorem counterEnv_x (base : Address) (N i : Nat) :
    (CLoops.counterEnv (sampleLocals base N) "i" i) "x" = some (.pointer (some base)) := by
  rw [CLoops.counterEnv, CBody.bind, if_neg (by decide), sampleLocals_x]

omit interface in
theorem counterEnv_n (base : Address) (N i : Nat) :
    (CLoops.counterEnv (sampleLocals base N) "i" i) "n" = some (.integer N) := by
  rw [CLoops.counterEnv, CBody.bind, if_neg (by decide), sampleLocals_n]

theorem sample_params (base : Address) (N : Nat) (ptrTy : interface.types "double *" = some .pointer)
    (sizeTy : interface.types "size_t" = some .size) (bnd : N < 2 ^ 64) :
    CCalls.parameters [⟨"double *", "x", false⟩, ⟨"size_t", "n", false⟩]
        [.pointer (some base), .integer N] = some (sampleLocals base N) := by
  have hs := CLoops.Calls.cast_of_type "size_t" .size (.integer N) (.integer N) sizeTy
    (CLoops.convert_size_nat N bnd)
  have hx := CLoops.Calls.cast_of_type "double *" .pointer (.pointer (some base)) (.pointer (some base)) ptrTy rfl
  have nBound := CLoops.Calls.bind_parameter ⟨"size_t", "n", false⟩ [] (.integer N) (.integer N) []
    (fun _ => none) rfl rfl rfl hs
  have xBound := CLoops.Calls.bind_parameter ⟨"double *", "x", false⟩ [⟨"size_t", "n", false⟩]
    (.pointer (some base)) (.pointer (some base)) [.integer N] (CBody.bind (fun _ => none) "n" (.integer N))
    rfl nBound (by simp [CBody.bind]) hx
  exact xBound

theorem sample_types (ptrTy : interface.types "double *" = some .pointer)
    (sizeTy : interface.types "size_t" = some .size) :
    CLoops.Calls.parameterTypes [⟨"double *", "x", false⟩, ⟨"size_t", "n", false⟩] = some sampleTypes := by
  simp [CLoops.Calls.parameterTypes, CCalls.parameterType, ptrTy, sizeTy, sampleTypes, CLoops.bindType]

theorem sample_body_reaches (rates : List Decimal)
    (base : Address) (xs0 : List Binary64.Value) (heap : Heap) (N : Nat)
    (len0 : xs0.length = rates.length) (bnd : N < 2 ^ 64) (sizeTy : interface.types "size_t" = some .size)
    (hc0 : cells heap base 0 xs0)
    (finite : ∀ i, i < N → ∀ k (hk : k < rates.length),
      CExecution.finiteRoundDomain (Binary64.units ((stateAfter rates xs0 i)[k]'(by rw [stateAfter_length rates xs0 len0 i]; exact hk)) + Binary64.units (rateVal rates[k]))) :
    Transition.Reaches CLoops.machine.step
      (.running (sampleFunction rates).body (sampleLocals base N) sampleTypes heap)
      (.returned ⟨.void, runHeap base rates xs0 heap N⟩) := by
  -- The counter declaration, then the counted loop, then the return.
  have started := CLoops.counter_initialize (sampleLocals base N) sampleTypes heap "i"
    [CLoops.loop "i" (.id "n") (stepStmts "x" 0 rates), .ret none]
    (sampleLocals_i base N) sizeTy
  have looped := CLoops.loop_reaches (interface := interface) "i" (.id "n") (stepStmts "x" 0 rates) [.ret none]
    (fun _ => sampleLocals base N) (CLoops.bindType sampleTypes "i" .size)
    (runHeap base rates xs0 heap) N
    (by simp [CLoops.bindType]) bnd (stepStmts_noDecl "x" 0 rates)
    (by
      intro i _
      rw [show CBody.eval (CLoops.counterEnv (sampleLocals base N) "i" i) (runHeap base rates xs0 heap i) (.id "n")
            = CBody.resolve (CLoops.counterEnv (sampleLocals base N) "i" i) "n" from rfl,
        CBody.resolve, counterEnv_n base N i]
      rfl)
    (by
      intro i hi
      have := step_reaches "x" base (CLoops.counterEnv (sampleLocals base N) "i" i)
        (CLoops.bindType sampleTypes "i" .size) (runHeap base rates xs0 heap i)
        (CLoops.counterStep "i" :: CLoops.loop "i" (.id "n") (stepStmts "x" 0 rates) :: [.ret none]) 0
        (stateAfter rates xs0 i) rates
        (counterEnv_x base N i)
        (stateAfter_length rates xs0 len0 i)
        (runHeap_cells base rates xs0 heap hc0 i)
        (fun k hk => finite i hi k hk)
      simpa only [runHeap, stateAfter] using this)
  refine .next started (looped.trans (.next rfl (.refl _)))

theorem sample_behaves (definitions : CLoops.Calls.Definitions) (rates : List Decimal) (base : Address)
    (xs0 : List Binary64.Value) (heap : Heap) (N : Nat) (len0 : xs0.length = rates.length) (bnd : N < 2 ^ 64)
    (found : definitions "rumoca_constant_sample" = some (sampleFunction rates))
    (ptrTy : interface.types "double *" = some .pointer) (sizeTy : interface.types "size_t" = some .size)
    (hc0 : cells heap base 0 xs0)
    (finite : ∀ i, i < N → ∀ k (hk : k < rates.length),
      CExecution.finiteRoundDomain (Binary64.units ((stateAfter rates xs0 i)[k]'(by rw [stateAfter_length rates xs0 len0 i]; exact hk)) + Binary64.units (rateVal rates[k]))) (behavior) :
    (CLoops.Calls.machine definitions).Behaves
      (.calling "rumoca_constant_sample" [.pointer (some base), .integer N] heap .done) behavior ↔
      behavior = .terminates (runHeap base rates xs0 heap N) := by
  exact CLoops.Calls.call_behaviors definitions "rumoca_constant_sample" [.pointer (some base), .integer N] heap
    (runHeap base rates xs0 heap N) (sampleFunction rates) _ _ found rfl
    (sample_params base N ptrTy sizeTy bnd) (sample_types ptrTy sizeTy)
    (sample_body_reaches rates base xs0 heap N len0 bnd sizeTy hc0 finite) behavior

/-! ### Exact rounding of each source rate -/

omit interface in
/-- Each stored rate is the nearest-even rounding of its literal's exact base-ten
content, derived from the body semantics' rounding certificate. -/
theorem rate_rounds (d : Decimal) :
    Binary64.Scaled.RoundsNearestEven (CBody.decimalScale d.power)
      (CBody.decimalNumerator (decide (d.sign < 0)) (d.sign.natAbs * d.mantissa) d.power) (rateVal d) :=
  CBody.decimalValue_rounds _ _ _

/-! ### The emitted numerical C: the three rendered functions -/

/-- The constant-rate translation unit's preamble. `<stddef.h>` scopes `size_t`
for the counted sample loop; the guard rejects a non-binary64 `double` target. -/
def preamble : String :=
  "/* Generated by lean_rumoca. Modelica Real: IEEE 754 binary64. */\n" ++
  "#include <stddef.h>\n#include <float.h>\n" ++
  "#if FLT_RADIX != 2 || DBL_MANT_DIG != 53 || DBL_MAX_EXP != 1024 || DBL_MIN_EXP != -1021 || FLT_EVAL_METHOD != 0\n" ++
  "#error \"Modelica Real backend requires IEEE 754 binary64 double\"\n#endif\n\n"

/-- The emitted numerical C for a rate list: the preamble and the three kernel
entries, each rendered through the shared structured printer. -/
def programText (rates : List Decimal) : String :=
  preamble ++ (rhsFunction rates).render ++ (stepFunction rates).render ++ (sampleFunction rates).render

/-! ### The executable-program conjuncts of the artifact contract -/

/-- `rumoca_constant_rhs` writes the rounded rate vector into the derivative
region, preserves every other cell, and its ordinary call terminates there. -/
def RhsExecutes (rates : List Decimal) : Prop :=
  ∀ (interface : CInterface) (definitions : CLoops.Calls.Definitions) (base : Address) (heap : Heap),
    definitions "rumoca_constant_rhs" = some (rhsFunction rates) →
    interface.types "double *" = some .pointer → writableN heap base 0 rates.length →
    cells (place base 0 heap (rateVals rates)) base 0 (rateVals rates) ∧
    (∀ q, (∀ j < rates.length, q ≠ base.index j) → place base 0 heap (rateVals rates) q = heap q) ∧
    ∀ behavior, (@CLoops.Calls.machine interface definitions).Behaves
      (.calling "rumoca_constant_rhs" [.pointer (some base)] heap .done) behavior ↔
      behavior = .terminates (place base 0 heap (rateVals rates))

/-- `rumoca_constant_step` advances every state cell by the finite binary64
addition of its rate, preserves every other cell, and terminates there. -/
def StepExecutes (rates : List Decimal) : Prop :=
  ∀ (interface : CInterface) (definitions : CLoops.Calls.Definitions) (base : Address) (heap : Heap)
    (xs : List Binary64.Value) (len : xs.length = rates.length),
    definitions "rumoca_constant_step" = some (stepFunction rates) →
    interface.types "double *" = some .pointer → cells heap base 0 xs →
    (∀ i (hi : i < rates.length),
      CExecution.finiteRoundDomain (Binary64.units xs[i] + Binary64.units (rateVal rates[i]))) →
    cells (place base 0 heap (euler rates xs)) base 0 (euler rates xs) ∧
    (∀ q, (∀ j < rates.length, q ≠ base.index j) → place base 0 heap (euler rates xs) q = heap q) ∧
    ∀ behavior, (@CLoops.Calls.machine interface definitions).Behaves
      (.calling "rumoca_constant_step" [.pointer (some base)] heap .done) behavior ↔
      behavior = .terminates (place base 0 heap (euler rates xs))

/-- `rumoca_constant_sample n` iterates the whole-vector step `n` times, so the
state region holds the `n`-fold Euler trajectory, preserves every other cell,
and terminates there. -/
def SampleExecutes (rates : List Decimal) : Prop :=
  ∀ (interface : CInterface) (definitions : CLoops.Calls.Definitions) (base : Address)
    (xs0 : List Binary64.Value) (heap : Heap) (N : Nat) (len0 : xs0.length = rates.length), N < 2 ^ 64 →
    definitions "rumoca_constant_sample" = some (sampleFunction rates) →
    interface.types "double *" = some .pointer → interface.types "size_t" = some .size →
    cells heap base 0 xs0 →
    (∀ i, i < N → ∀ k (hk : k < rates.length),
      CExecution.finiteRoundDomain (Binary64.units ((stateAfter rates xs0 i)[k]'(by
        rw [stateAfter_length rates xs0 len0 i]; exact hk)) + Binary64.units (rateVal rates[k]))) →
    cells (runHeap base rates xs0 heap N) base 0 (stateAfter rates xs0 N) ∧
    (∀ q, (∀ j < rates.length, q ≠ base.index j) → runHeap base rates xs0 heap N q = heap q) ∧
    ∀ behavior, (@CLoops.Calls.machine interface definitions).Behaves
      (.calling "rumoca_constant_sample" [.pointer (some base), .integer N] heap .done) behavior ↔
      behavior = .terminates (runHeap base rates xs0 heap N)

omit interface in
theorem rhs_executes (rates : List Decimal) : RhsExecutes rates := by
  intro interface definitions base heap found ptrTy writable
  refine ⟨place_cells base 0 heap (rateVals rates), ?_,
    rhs_behaves definitions rates base heap found ptrTy writable⟩
  intro q outside
  exact place_frame base 0 heap (rateVals rates) q
    (fun j hj => by rw [Nat.zero_add]; exact outside j (by simpa [rateVals] using hj))

omit interface in
theorem step_executes (rates : List Decimal) : StepExecutes rates := by
  intro interface definitions base heap xs len found ptrTy cellsH finite
  refine ⟨place_cells base 0 heap (euler rates xs), ?_,
    step_behaves definitions rates base heap xs len found ptrTy cellsH finite⟩
  intro q outside
  exact place_frame base 0 heap (euler rates xs) q (fun j hj => by
    rw [Nat.zero_add]; exact outside j (by rw [euler_length, len, Nat.min_self] at hj; exact hj))

omit interface in
theorem sample_executes (rates : List Decimal) : SampleExecutes rates := by
  intro interface definitions base xs0 heap N len0 bnd found ptrTy sizeTy hc0 finite
  refine ⟨runHeap_cells base rates xs0 heap hc0 N, ?_,
    sample_behaves definitions rates base xs0 heap N len0 bnd found ptrTy sizeTy hc0 finite⟩
  intro q outside
  exact runHeap_frame base rates xs0 heap len0 q outside N

/-! ### The actual-artifact contract over the executable program -/

/-- The target execution and rounding contract for the constant-rate kernel:
the emitted bytes are the three rendered kernel functions; every rate is the
round-to-nearest-even of its decimal literal's exact base-ten content; and the
three entries execute as the rounded-rate write, the finite whole-vector Euler
step, and its counted iteration. -/
structure Contract (rates : List Decimal) (emitted : String) : Prop where
  bytes : programText rates = emitted
  rates_rounded : ∀ d ∈ rates, Binary64.Scaled.RoundsNearestEven (CBody.decimalScale d.power)
    (CBody.decimalNumerator (decide (d.sign < 0)) (d.sign.natAbs * d.mantissa) d.power) (rateVal d)
  rhs_executes : RhsExecutes rates
  step_executes : StepExecutes rates
  sample_executes : SampleExecutes rates

omit interface in
/-- Every rate list satisfies the contract for its rendered numerical C.
Universal in the number of states and in the rates. -/
theorem contract_correct (rates : List Decimal) (emitted : String) (h : programText rates = emitted) :
    Contract rates emitted :=
  ⟨h, fun d _ => rate_rounds d, rhs_executes rates, step_executes rates, sample_executes rates⟩

end Rumoca.CConstant
