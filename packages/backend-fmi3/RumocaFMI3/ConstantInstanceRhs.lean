import RumocaFMI3.TensorInstanceStorage
import RumocaC.ConstantKernelProgram
import RumocaC.TypedEventsTransfer

/-! The executable constant-rate kernel entries bound to the static constant-rate
instance record.

The constant-rate profile (`G01`) deploys two numerical entries into the static
constant instance record of `TensorInstance`: `rumoca_constant_rhs(double *der)`
writes the exactly rounded rate vector into the derivative region, and
`rumoca_constant_step(double *x)` advances every state cell by the finite binary64
addition of its rate. Both are executed by the loop-call machine over the caller
array (`packages/backend-c/RumocaC/ConstantKernelProgram.lean`); here their proved
loop-call behaviors are bridged into the observable call machine through the
typed-to-observable transfer (`CCalls.Events.loop_call_reaches_events`), the
identical bridge the tensor derivative and Jacobian entries use.

The list-indexed kernel view (`CConstant.place`, `CConstant.cells`,
`CConstant.writableN` over the declaration-order rate list) is matched to the
dense tensor view of the instance record (`Reads`, `Writable`, `Values`) so the
adapter bodies consume the constant-rate rate vector and finite Euler step as
tensor values. Every theorem is universal in the state shape, the source rates
and the pool index: running the entry on an instance writes the rounded rate
vector or the finite Euler step into that instance's own region and preserves
every other cell, including every tensor cell of every other instance in the
pool. This is a package-checked product; it emits no production artifact, adds no
CLI or grammar case, and changes no existing contract or the scalar adapter.

The `resolves` premise (the constant analog of the tensor entries' resolution
premise) records that the direct call sites the loop-call run visits resolve to
their own names in the observable machine. The constant bodies contain only
assignments and a return with no nested calls, so no reachable loop-call state is
poised on an `eval`-call and the premise holds definitionally at every reachable
state; it is carried here to mirror the tensor entry theorems and keep the
adapter composition uniform. -/
noncomputable section
namespace Rumoca.FMI3.ConstantInstanceRhs
open CTree CMemory CMemory.TensorView Rumoca.Tensor
open Rumoca.ConstantProfile (Decimal)
open Rumoca.CConstant (rateVal rateVals euler)

/-! ### The constant kernel definitions table -/

/-- The constant-rate kernel program as a loop-call definitions table: the three
executable entries keyed by their emitted C names, universal in the source
rates. An adapter definitions table extends this. -/
def kernelDefinitions (rates : List Decimal) : CLoops.Calls.Definitions := fun name =>
  if name = "rumoca_constant_rhs" then some (Rumoca.CConstant.rhsFunction rates)
  else if name = "rumoca_constant_step" then some (Rumoca.CConstant.stepFunction rates)
  else if name = "rumoca_constant_sample" then some (Rumoca.CConstant.sampleFunction rates)
  else none

theorem kernelDefinitions_rhs (rates : List Decimal) :
    kernelDefinitions rates "rumoca_constant_rhs" = some (Rumoca.CConstant.rhsFunction rates) := rfl

theorem kernelDefinitions_step (rates : List Decimal) :
    kernelDefinitions rates "rumoca_constant_step" = some (Rumoca.CConstant.stepFunction rates) := by
  simp [kernelDefinitions]

theorem kernelDefinitions_sample (rates : List Decimal) :
    kernelDefinitions rates "rumoca_constant_sample" = some (Rumoca.CConstant.sampleFunction rates) := by
  simp [kernelDefinitions]

/-! ### Dense tensor views of the declaration-order rate list -/

/-- The declaration index of a state coordinate lies in the rate list. -/
theorem idxLt {rates : List Decimal} {shape : Shape} (len : rates.length = shape.volume)
    (i : Fin shape.volume) : i.val < rates.length := Nat.lt_of_lt_of_eq i.isLt len.symm

/-- A dense tensor value built from a coordinate function reads that function. -/
theorem valueGet {shape : Shape} (f : Fin shape.volume → Binary64.Value) (i : Fin shape.volume) :
    (⟨Vector.ofFn f⟩ : Values shape)[i] = f i := by
  change (Vector.ofFn f)[i.val] = f i
  rw [Vector.getElem_ofFn]

/-- The exactly rounded rate vector as a dense tensor value of the state shape. -/
def ratesVec (rates : List Decimal) (shape : Shape) (len : rates.length = shape.volume) :
    Values shape :=
  ⟨Vector.ofFn (fun i : Fin shape.volume => rateVal (rates[i.val]'(idxLt len i)))⟩

theorem ratesVec_get (rates : List Decimal) (shape : Shape) (len : rates.length = shape.volume)
    (i : Fin shape.volume) : (ratesVec rates shape len)[i] = rateVal (rates[i.val]'(idxLt len i)) :=
  valueGet _ i

/-- The declaration-order state list of a dense tensor value. -/
def stateList (state : Values shape) : List Binary64.Value :=
  List.ofFn (fun i : Fin shape.volume => state[i])

theorem stateList_length (state : Values shape) : (stateList state).length = shape.volume := by
  simp [stateList]

theorem stateList_get (state : Values shape) (i : Fin shape.volume) :
    (stateList state)[i.val]'(by rw [stateList_length]; exact i.isLt) = state[i] := by
  simp [stateList]

/-- The finite whole-vector Euler step of a dense tensor value by the rate list:
each state cell advances by the finite binary64 addition of its rate. -/
def eulerVec (rates : List Decimal) (state : Values shape) (len : rates.length = shape.volume) :
    Values shape :=
  ⟨Vector.ofFn (fun i : Fin shape.volume =>
    Binary64.roundedAdd state[i] (rateVal (rates[i.val]'(idxLt len i))))⟩

theorem eulerVec_get (rates : List Decimal) (state : Values shape) (len : rates.length = shape.volume)
    (i : Fin shape.volume) :
    (eulerVec rates state len)[i] = Binary64.roundedAdd state[i] (rateVal (rates[i.val]'(idxLt len i))) :=
  valueGet _ i

/-! ### Bridging the list-indexed kernel view and the dense tensor view -/

/-- A consecutive-cell run holds each declared value at its declaration index. -/
theorem cells_index (heap : Heap) (base : Address) : ∀ (start : Nat) (vs : List Binary64.Value),
    Rumoca.CConstant.cells heap base start vs → ∀ (j : Nat) (hj : j < vs.length),
    heap (base.index (start + j)) = some ⟨.float64, true, some (.finite (vs[j]'hj))⟩
  | _, [], _, j, hj => absurd hj (by simp)
  | start, v :: vs, h, 0, _ => by
      obtain ⟨h0, _⟩ := h
      simpa using h0
  | start, v :: vs, h, j + 1, hj => by
      obtain ⟨_, ht⟩ := h
      have recCell := cells_index heap base (start + 1) vs ht j (by simpa using hj)
      have e : start + (j + 1) = start + 1 + j := by omega
      rw [e]; simpa using recCell

/-- Consecutive cells that already hold the finite values `vs` read the matching
dense tensor value. -/
theorem cells_reads (heap : Heap) (base : Address) (vs : List Binary64.Value) (result : Values shape)
    (len : vs.length = shape.volume)
    (agree : ∀ (i : Fin shape.volume), result[i] = vs[i.val]'(Nat.lt_of_lt_of_eq i.isLt len.symm))
    (h : Rumoca.CConstant.cells heap base 0 vs) : Reads heap base result := by
  intro i
  have cell := cells_index heap base 0 vs h i.val (Nat.lt_of_lt_of_eq i.isLt len.symm)
  rw [Nat.zero_add] at cell
  rw [Rumoca.CConstant.load_finite heap (base.index i.val) _ cell, agree i]

/-- Consecutive cells hold the finite values `vs`, so the region is writable. -/
theorem cells_writable (heap : Heap) (base : Address) (vs : List Binary64.Value) (n : Nat)
    (len : n ≤ vs.length) (h : Rumoca.CConstant.cells heap base 0 vs) : Writable heap base n := by
  intro i hi
  have cell := cells_index heap base 0 vs h i (Nat.lt_of_lt_of_le hi len)
  rw [Nat.zero_add] at cell
  exact ⟨_, cell⟩

/-- The list-indexed `cells` view from per-cell finite contents. -/
theorem cells_of (heap : Heap) (base : Address) : ∀ (start : Nat) (vs : List Binary64.Value),
    (∀ (j : Nat) (hj : j < vs.length),
      heap (base.index (start + j)) = some ⟨.float64, true, some (.finite (vs[j]'hj))⟩) →
    Rumoca.CConstant.cells heap base start vs
  | _, [], _ => trivial
  | start, v :: vs, h => by
      refine ⟨by simpa using h 0 (by simp), cells_of heap base (start + 1) vs (fun j hj => ?_)⟩
      have hcell := h (j + 1) (by simpa using hj)
      have e : start + (j + 1) = start + 1 + j := by omega
      rw [e] at hcell; simpa using hcell

/-- A readable, writable float64 cell holds exactly the finite value it reads. -/
theorem reads_writable_cell (heap : Heap) (p : Address) (x : Binary64.Value)
    (r : load heap p = some (.finite x)) (w : ∃ old, heap p = some ⟨.float64, true, old⟩) :
    heap p = some ⟨.float64, true, some (.finite x)⟩ := by
  obtain ⟨old, hw⟩ := w
  have key : load heap p = Option.bind old (fun value =>
      Option.bind (convert .float64 value) fun checked => if checked = value then some value else none) := by
    simp [load, hw]
  rw [key] at r
  cases old with
  | none => simp at r
  | some value =>
    simp only [Option.bind_some] at r
    cases hc : convert .float64 value with
    | none => rw [hc] at r; simp at r
    | some checked =>
      rw [hc] at r
      simp only [Option.bind_some] at r
      by_cases he : checked = value
      · rw [if_pos he] at r
        rw [hw]; cases r; rfl
      · rw [if_neg he] at r; simp at r

/-- The dense tensor `Reads` view, together with region writability, recovers the
list-indexed `cells` view over the declaration-order state list. -/
theorem reads_writable_cells (heap : Heap) (base : Address) (state : Values shape)
    (reads : Reads heap base state) (writable : Writable heap base shape.volume) :
    Rumoca.CConstant.cells heap base 0 (stateList state) := by
  apply cells_of heap base 0 (stateList state)
  intro j hj
  have hj' : j < shape.volume := stateList_length state ▸ hj
  set i : Fin shape.volume := ⟨j, hj'⟩ with hi
  have hx : (stateList state)[j]'hj = state[i] := stateList_get state i
  rw [Nat.zero_add, hx]
  exact reads_writable_cell heap (base.index j) state[i]
    (by have := reads i; simpa [hi] using this) (writable j hj')

/-- The list-indexed `writableN` view from a dense-region writability. -/
theorem writableN_of (heap : Heap) (base : Address) (start : Nat) : ∀ (k : Nat),
    (∀ m, m < k → ∃ old, heap (base.index (start + m)) = some ⟨.float64, true, old⟩) →
    Rumoca.CConstant.writableN heap base start k
  | 0, _ => trivial
  | k + 1, h => by
      refine ⟨by simpa using h 0 (by omega), writableN_of heap base (start + 1) k (fun m hm => ?_)⟩
      have := h (m + 1) (by omega)
      have e : start + (m + 1) = start + 1 + m := by omega
      rw [e] at this; exact this

/-! ### The constant rate list read as a dense tensor value -/

theorem rateVals_length (rates : List Decimal) : (rateVals rates).length = rates.length := by
  simp [rateVals]

/-- The rounded rate vector as a dense tensor value agrees with the rate list. -/
theorem ratesVec_agree (rates : List Decimal) (shape : Shape) (len : rates.length = shape.volume)
    (i : Fin shape.volume) :
    (ratesVec rates shape len)[i] = (rateVals rates)[i.val]'(by rw [rateVals_length]; exact idxLt len i) := by
  rw [ratesVec_get]
  simp [rateVals, List.getElem_map]

variable [interface : CInterface]

open Rumoca.FMI3.TensorInstance (field record stateName derivativeName)

/-! ### `rumoca_constant_rhs` writes the rounded rate vector into the derivative region -/

/-- Running the constant-rate derivative entry `rumoca_constant_rhs` on instance
`i` writes the exactly rounded rate vector into that instance's derivative region
and preserves every other cell, including every tensor cell of every other
instance in the pool. Universal in the state shape, the source rates and the pool
index. The proved loop-call behavior (`CConstant.rhs_behaves`) is embedded into
the observable call machine through the typed-to-observable transfer. -/
theorem rhs_writes_events {shape : Shape} (rates : List Decimal) (len : rates.length = shape.volume)
    (definitions : CLoops.Calls.Definitions) {E : Type} (program : CCalls.Events.Program E)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (found : definitions "rumoca_constant_rhs" = some (Rumoca.CConstant.rhsFunction rates))
    (ptrTy : interface.types "double *" = some .pointer)
    (heap : Heap) (pool : Address) (i : Nat)
    (writable : Writable heap (field pool i derivativeName) shape.volume)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_rhs" [.pointer (some (field pool i derivativeName))] heap .done) v →
      CCalls.Events.Resolves program v)
    (stack : CCalls.Typed.Continuation) :
    ∃ finalHeap,
      Reads finalHeap (field pool i derivativeName) (ratesVec rates shape len) ∧
      Writable finalHeap (field pool i derivativeName) shape.volume ∧
      (∀ q, (∀ m, m < shape.volume → q ≠ (field pool i derivativeName).index m) → finalHeap q = heap q) ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((field pool j b).index k) = heap ((field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "rumoca_constant_rhs" [.pointer (some (field pool i derivativeName))] heap stack)
        (.returning .void finalHeap stack) := by
  set base := field pool i derivativeName with hbase
  have len2 : (rateVals rates).length = shape.volume := by rw [rateVals_length]; exact len
  have wN : Rumoca.CConstant.writableN heap base 0 rates.length :=
    writableN_of heap base 0 rates.length (fun m hm => by
      have := writable m (by rw [len] at hm; exact hm); simpa using this)
  have behaves := (Rumoca.CConstant.rhs_behaves definitions rates base heap found ptrTy wN _).mpr rfl
  refine ⟨Rumoca.CConstant.place base 0 heap (rateVals rates), ?_, ?_, ?_, ?_, ?_⟩
  · exact cells_reads _ base (rateVals rates) (ratesVec rates shape len) len2
      (fun k => (ratesVec_agree rates shape len k)) (Rumoca.CConstant.place_cells base 0 heap (rateVals rates))
  · exact cells_writable _ base (rateVals rates) shape.volume (le_of_eq len2.symm)
      (Rumoca.CConstant.place_cells base 0 heap (rateVals rates))
  · intro q outside
    exact Rumoca.CConstant.place_frame base 0 heap (rateVals rates) q
      (fun j hj => by rw [Nat.zero_add]; exact outside j (by rw [len2] at hj; exact hj))
  · intro j b k different
    exact Rumoca.CConstant.place_frame base 0 heap (rateVals rates) ((field pool j b).index k)
      (fun m _ => by
        rw [Nat.zero_add, hbase]
        exact Address.instances_separate pool j i different b derivativeName k m)
  · exact CCalls.Events.loop_call_reaches_events program definitions linked behaves resolves stack

/-! ### `rumoca_constant_step` advances every state cell by its rate -/

/-- Running the constant-rate state step entry `rumoca_constant_step` on instance
`i` advances every state cell by the finite binary64 addition of its rate, under
the explicit per-cell finite-addition premises, and preserves every other cell,
including every tensor cell of every other instance in the pool. Universal in the
state shape, the source rates and the pool index. -/
theorem step_writes_events {shape : Shape} (rates : List Decimal) (len : rates.length = shape.volume)
    (definitions : CLoops.Calls.Definitions) {E : Type} (program : CCalls.Events.Program E)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (found : definitions "rumoca_constant_step" = some (Rumoca.CConstant.stepFunction rates))
    (ptrTy : interface.types "double *" = some .pointer)
    (heap : Heap) (pool : Address) (i : Nat) (state : Values shape)
    (reads : Reads heap (field pool i stateName) state)
    (writable : Writable heap (field pool i stateName) shape.volume)
    (finite : ∀ (k : Fin shape.volume),
      CExecution.finiteRoundDomain (Binary64.units state[k] + Binary64.units (rateVal (rates[k.val]'(idxLt len k)))))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling "rumoca_constant_step" [.pointer (some (field pool i stateName))] heap .done) v →
      CCalls.Events.Resolves program v)
    (stack : CCalls.Typed.Continuation) :
    ∃ finalHeap,
      Reads finalHeap (field pool i stateName) (eulerVec rates state len) ∧
      Writable finalHeap (field pool i stateName) shape.volume ∧
      (∀ q, (∀ m, m < shape.volume → q ≠ (field pool i stateName).index m) → finalHeap q = heap q) ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((field pool j b).index k) = heap ((field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "rumoca_constant_step" [.pointer (some (field pool i stateName))] heap stack)
        (.returning .void finalHeap stack) := by
  set base := field pool i stateName with hbase
  have cellsH : Rumoca.CConstant.cells heap base 0 (stateList state) := reads_writable_cells heap base state reads writable
  have lenS : (stateList state).length = rates.length := by rw [stateList_length, len]
  have lenE : (euler rates (stateList state)).length = shape.volume := by
    rw [Rumoca.CConstant.euler_length, stateList_length, len, Nat.min_self]
  -- Recast the finite premises onto the declaration-order state list.
  have finiteList : ∀ (k : Nat) (hk : k < rates.length),
      CExecution.finiteRoundDomain (Binary64.units ((stateList state)[k]'(by rw [lenS]; exact hk))
        + Binary64.units (rateVal (rates[k]'hk))) := by
    intro k hk
    have hk' : k < shape.volume := by rw [len] at hk; exact hk
    have := finite ⟨k, hk'⟩
    rw [stateList_get state ⟨k, hk'⟩]
    simpa using this
  have behaves := (Rumoca.CConstant.step_behaves definitions rates base heap (stateList state) lenS found ptrTy
    cellsH finiteList _).mpr rfl
  refine ⟨Rumoca.CConstant.place base 0 heap (euler rates (stateList state)), ?_, ?_, ?_, ?_, ?_⟩
  · refine cells_reads _ base (euler rates (stateList state)) (eulerVec rates state len) lenE
      (fun k => ?_) (Rumoca.CConstant.place_cells base 0 heap (euler rates (stateList state)))
    rw [eulerVec_get]
    have hk : k.val < (stateList state).length := by rw [lenS]; exact idxLt len k
    have hr : k.val < rates.length := idxLt len k
    have hzip : (euler rates (stateList state))[k.val]'(by rw [lenE]; exact k.isLt)
        = Binary64.roundedAdd ((stateList state)[k.val]'hk) (rateVal (rates[k.val]'hr)) := by
      simp [euler, List.getElem_zipWith]
    rw [hzip, stateList_get state ⟨k.val, k.isLt⟩]
  · exact cells_writable _ base (euler rates (stateList state)) shape.volume (le_of_eq lenE.symm)
      (Rumoca.CConstant.place_cells base 0 heap (euler rates (stateList state)))
  · intro q outside
    exact Rumoca.CConstant.place_frame base 0 heap (euler rates (stateList state)) q
      (fun j hj => by rw [Nat.zero_add]; exact outside j (by rw [lenE] at hj; exact hj))
  · intro j b k different
    exact Rumoca.CConstant.place_frame base 0 heap (euler rates (stateList state)) ((field pool j b).index k)
      (fun m _ => by
        rw [Nat.zero_add, hbase]
        exact Address.instances_separate pool j i different b stateName k m)
  · exact CCalls.Events.loop_call_reaches_events program definitions linked behaves resolves stack

end Rumoca.FMI3.ConstantInstanceRhs
