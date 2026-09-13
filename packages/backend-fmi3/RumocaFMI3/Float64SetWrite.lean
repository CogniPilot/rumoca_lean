import RumocaFMI3.Float64SetValidation
import RumocaC.MemoryUpdates

noncomputable section
namespace Rumoca.FMI3.Float64Set
open CTree CMemory CBody CLoops Float64Calls

/-- The specification of the state after a prefix of ordered writes. Values
are a tensor-memory snapshot; no source/IR element is enumerated in lowering.
Only prefixes within the request's volume are used by the execution theorem. -/
def assigned (heap : Heap) (p : Address) (values : TensorView.Values shape) : Nat → Heap
  | 0 => heap
  | k + 1 => if h : k < shape.volume then
      StateProofs.written heap (StateProofs.stateAddress p) (Binary64.toBits values[k]).val
    else heap

theorem assigned_frame (heap : Heap) (p : Address) (values : TensorView.Values shape)
    (k : Nat) (q : Address) (outside : q ≠ StateProofs.stateAddress p) :
    assigned heap p values k q = heap q := by
  cases k with
  | zero => rfl
  | succ k =>
      rw [assigned]
      split
      · exact StateProofs.written_frame heap _ q _ outside
      · rfl

theorem assigned_writable (heap : Heap) (p : Address) (values : TensorView.Values shape)
    (k : Nat) (old : Option Value)
    (stored : heap (StateProofs.stateAddress p) = some ⟨.float64, true, old⟩) :
    ∃ current, assigned heap p values k (StateProofs.stateAddress p) = some ⟨.float64, true, current⟩ := by
  cases k with
  | zero => exact ⟨old, stored⟩
  | succ k =>
      rw [assigned]
      split
      · rename_i inside
        refine ⟨some (.float64 (Binary64.toBits values[k]).val), ?_⟩
        simp [StateProofs.written, replace]
      · exact ⟨old, stored⟩

theorem assigned_next (heap : Heap) (p : Address) (values : TensorView.Values shape)
    (k : Nat) (inside : k < shape.volume) :
    StateProofs.written (assigned heap p values k) (StateProofs.stateAddress p)
      (Binary64.toBits values[k]).val = assigned heap p values (k + 1) := by
  rw [assigned, dif_pos inside]
  cases k with
  | zero => rfl
  | succ k =>
      rw [assigned, dif_pos (by omega)]
      exact replace_overwrite heap _ _ _

theorem assigned_reads (heap : Heap) (p buffer : Address) (values : TensorView.Values shape)
    (k : Nat) (readable : TensorView.Reads heap buffer values)
    (separate : ∀ i < shape.volume, StateProofs.stateAddress p ≠ buffer.index i) :
    TensorView.Reads (assigned heap p values k) buffer values := by
  intro i
  have frame := assigned_frame heap p values k (buffer.index i.val) (Ne.symm (separate i.val i.isLt))
  simpa only [load, frame] using readable i

section
variable [interface : CInterface]

theorem write_step (env : Locals) (types : Types) (heap : Heap) (p : Address)
    (value : Binary64.Value) (old : Option Value) (rest : List Stmt)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (loaded : CBody.eval env heap output = some (.finite value))
    (stored : heap (StateProofs.stateAddress p) = some ⟨.float64, true, old⟩) :
    CLoops.next (.running (writeBody ++ rest) env types heap) =
      some (.running rest env types
        (StateProofs.written heap (StateProofs.stateAddress p) (Binary64.toBits value).val)) := by
  have address : CBody.lvalue env heap Runtime.x = some (StateProofs.stateAddress p) := by
    simp [Runtime.x, Runtime.field, Runtime.v, CBody.lvalue, CBody.eval, instanceBound,
      Value.address, StateProofs.stateAddress]
  have rhs : CLoops.eval env types heap output = some (.finite value) := by
    simpa [CLoops.eval] using loaded
  simp only [Runtime.x] at address
  simp [writeBody, Runtime.x, CLoops.next, address, rhs, Value.finite,
    store_float64 heap _ old _ stored, StateProofs.written]

theorem write_reaches (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (p buffer : Address) (values : TensorView.Values shape) (old : Option Value)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (bounded : shape.volume < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "nValueReferences" = some (.integer shape.volume))
    (valueBound : resolve env "values" = some (.pointer (some buffer)))
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (readable : TensorView.Reads heap buffer values)
    (stored : heap (StateProofs.stateAddress p) = some ⟨.float64, true, old⟩)
    (separate : ∀ i < shape.volume, StateProofs.stateAddress p ≠ buffer.index i) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "nValueReferences") writeBody :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running rest (counterEnv env "k" shape.volume) types
        (assigned heap p values shape.volume)) resultType stack) := by
  apply CCalls.Events.loop_reaches program "k" (Runtime.v "nValueReferences") writeBody rest
    (fun _ => env) types (assigned heap p values) shape.volume resultType stack typed bounded write_closed
  · intro i inside
    simpa [Runtime.v, CBody.eval, counterEnv, CBody.bind, resolve] using count
  · intro i inside
    obtain ⟨current, cell⟩ := assigned_writable heap p values i old stored
    have loaded := assigned_reads heap p buffer values i readable separate ⟨i, inside⟩
    have pointer : resolve (counterEnv env "k" i) "values" = some (.pointer (some buffer)) := by
      simpa [counterEnv, CBody.bind, resolve] using valueBound
    have counter : resolve (counterEnv env "k" i) "k" = some (.integer i) := by
      simp [counterEnv, CBody.bind, resolve]
    have rhs : CBody.eval (counterEnv env "k" i) (assigned heap p values i) output = some (.finite values[i]) := by
      simpa [output, Runtime.v, CBody.eval, pointer, counter, Value.address] using loaded
    have step := write_step (counterEnv env "k" i) types (assigned heap p values i) p values[i] current
      (counterStep "k" :: loop "k" (Runtime.v "nValueReferences") writeBody :: rest)
      (by simpa [counterEnv, CBody.bind, resolve] using instanceBound) rhs cell
    rw [assigned_next heap p values i inside] at step
    exact .next (CCalls.Events.body_step program step resultType stack) (.refl _)

end
end Rumoca.FMI3.Float64Set

noncomputable section
namespace Rumoca.FMI3.Float64Set
open CTree CMemory CBody CLoops Float64Calls

/-- Total bit snapshot used only in the proof's bounded input domain. -/
def bitsAt (values : TensorView.Values shape) (i : Nat) : BitVec 64 :=
  (Binary64.toBits (values.data.getD i Binary64.one)).val

theorem bitsAt_inside (values : TensorView.Values shape) (i : Nat) (inside : i < shape.volume) :
    bitsAt values i = (Binary64.toBits values[i]).val := by
  simp [bitsAt, Vector.getD, Array.getD_eq_getD_getElem?, inside]
  rfl

theorem snapshot_readable (heap : Heap) (buffer : Address) (values : TensorView.Values shape)
    (references : Nat → UInt32) (readable : TensorView.Reads heap buffer values) :
    ReadableValues heap (some buffer) shape.volume references (bitsAt values) := by
  intro i inside _
  refine ⟨buffer, rfl, ?_⟩
  rw [bitsAt_inside values i inside]
  exact readable ⟨i, inside⟩

theorem snapshot_valid (values : TensorView.Values shape) (references : Nat → UInt32)
    (valid : ∀ i < shape.volume, (references i).toNat = 1) :
    ∀ i < shape.volume, ValidEntry (references i) (bitsAt values i) := by
  intro i inside
  refine ⟨valid i inside, ?_⟩
  rw [bitsAt_inside values i inside]
  exact Value.isFinite_finite values[i]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

/-- Complete nonempty public setter entry, validation of every input before
any write, ordered state writes, and converted OK return. No intermediate
execution or loop invariant is supplied by the caller. -/
theorem set_reaches (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p input buffer : Address) (n : UInt64) (values : TensorView.Values shape)
    (references : Nat → UInt32) (kind : Kind) (mode : Mode) (old : Option Value)
    (stack : CCalls.Typed.Continuation) (volume : shape.volume = n.toNat) (nonempty : 0 < shape.volume)
    (defined : program.internal.definitions (signature true).name =
      some (.tree (Runtime.function model (signature true))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (readable : References heap (some input) shape.volume references)
    (valid : ∀ i < shape.volume, (references i).toNat = 1)
    (valuesReadable : TensorView.Reads heap buffer values)
    (stored : heap (StateProofs.stateAddress p) = some ⟨.float64, true, old⟩)
    (separate : ∀ i < shape.volume, StateProofs.stateAddress p ≠ buffer.index i) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling (signature true).name (arguments (some p) (some input) (some buffer) n n) heap stack)
      (.returning (.integer 0) (assigned heap p values shape.volume) stack) := by
  have bounded : shape.volume < 2 ^ 64 := volume ▸ n.toNat_lt_size
  have guarded := guard_run model heap p (some input) (some buffer) n n kind mode
    (Or.inl (by omega)) hk hm allowed
  rw [if_pos (by simp [ArrayAccess.Valid])] at guarded
  obtain ⟨types, entered⟩ := CCalls.Events.body_prefix_reaches program (Runtime.function model (signature true))
    (arguments (some p) (some input) (some buffer) n n) (parameters (some p) (some input) (some buffer) n n)
    (locals p (some input) (some buffer) n n) heap heap afterGuard stack 5
    defined (parameters_bound true _ _ _ _ _) (BodyEmbedding.body_closed model (signature true)) guarded
  let env := locals p (some input) (some buffer) n n
  let typed := bindType types "k" .size
  have ktype : typed "k" = some .size := by simp [typed, bindType]
  have count : resolve env "nValueReferences" = some (.integer shape.volume) := by
    simp [env, locals, parameters, CBody.bind, resolve, volume]
  have refBound : resolve env "valueReferences" = some (.pointer (some input)) := by
    simp [env, locals, parameters, CBody.bind, resolve]
  have valueBound : resolve env "values" = some (.pointer (some buffer)) := by
    simp [env, locals, parameters, CBody.bind, resolve]
  have initialized := counter_initialize env types heap "k"
    (loop "k" (Runtime.v "nValueReferences") [validation] :: afterValidation)
    (by simp [env, locals, parameters, CBody.bind]) (by rfl)
  refine entered.trans (.next (CCalls.Events.body_step program initialized "fmi3Status" stack) ?_)
  refine (validation_reaches program env typed heap (some input) (some buffer) shape.volume references
    (bitsAt values) afterValidation "fmi3Status" stack bounded ktype count refBound valueBound readable
    (snapshot_readable heap buffer values references valuesReadable) (snapshot_valid values references valid)).trans ?_
  refine .next (CCalls.Events.body_step program (counter_reset env typed heap "k" shape.volume
    (loop "k" (Runtime.v "nValueReferences") writeBody :: [Runtime.ok]) ktype) "fmi3Status" stack) ?_
  refine (write_reaches program env typed heap p buffer values old [Runtime.ok] "fmi3Status" stack
    bounded ktype count valueBound (by simp [env, locals, parameters, CBody.bind, resolve])
    valuesReadable stored separate).trans ?_
  exact DerivativeCalls.finish program _ (counterEnv env "k" shape.volume) typed stack
    (by simp [counterEnv, env, locals, parameters, CBody.bind])

theorem set_behaviors (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p input buffer : Address) (n : UInt64) (values : TensorView.Values shape)
    (references : Nat → UInt32) (kind : Kind) (mode : Mode) (old : Option Value)
    (volume : shape.volume = n.toNat) (nonempty : 0 < shape.volume)
    (defined : program.internal.definitions (signature true).name =
      some (.tree (Runtime.function model (signature true))))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (readable : References heap (some input) shape.volume references)
    (valid : ∀ i < shape.volume, (references i).toNat = 1)
    (valuesReadable : TensorView.Reads heap buffer values)
    (stored : heap (StateProofs.stateAddress p) = some ⟨.float64, true, old⟩)
    (separate : ∀ i < shape.volume, StateProofs.stateAddress p ≠ buffer.index i) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature true).name (arguments (some p) (some input) (some buffer) n n) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, assigned heap p values shape.volume⟩ :=
  (CCalls.Events.internal_prefix program (set_reaches model program heap p input buffer n values references
    kind mode old .done volume nonempty defined hk hm allowed readable valid valuesReadable stored separate)
    (CCalls.Events.return_forced program _ _)).behaviors behavior

end
end Rumoca.FMI3.Float64Set

noncomputable section
namespace Rumoca.FMI3.Float64Set
open CMemory Float64Calls

/-- Successful validation supplies a finite tensor snapshot of the original
host buffer, with exactly the accepted bits, including both signed zeroes. -/
theorem accepted_snapshot (heap : Heap) (buffer : Address) (shape : Tensor.Shape)
    (references : Nat → UInt32) (bits : Nat → BitVec 64)
    (valid : ∀ i < shape.volume, ValidEntry (references i) (bits i))
    (readable : ReadableValues heap (some buffer) shape.volume references bits) :
    ∃ values : TensorView.Values shape, TensorView.Reads heap buffer values ∧
      ∀ i < shape.volume, bitsAt values i = bits i := by
  have finite : ∀ i : Fin shape.volume, ∃ x : Binary64.Value, Value.float64 (bits i) = .finite x := by
    intro i
    exact (valid_entry_iff _ _).mp (valid i i.isLt) |>.2
  choose value same using finite
  let values : TensorView.Values shape := ⟨Vector.ofFn value⟩
  have selected (i : Fin shape.volume) : values[i] = value i := by
    change (Vector.ofFn value)[i] = value i
    simp
  refine ⟨values, ?_, ?_⟩
  · intro i
    obtain ⟨p, hp, loaded⟩ := readable i i.isLt (valid i i.isLt).1
    have equal := Option.some.inj hp
    subst p
    rw [same i] at loaded
    simpa only [selected] using loaded
  · intro i inside
    rw [bitsAt_inside values i inside]
    have item : values[i] = value ⟨i, inside⟩ := by
      change (Vector.ofFn value)[i] = value ⟨i, inside⟩
      simp
    rw [item]
    exact (Value.float64.inj (same ⟨i, inside⟩)).symm

/-- The complete ordered setter leaves the state selected by the final request.
This consequence refers to the semantic ME model state, not only a C cell. -/
theorem assigned_represents (heap : Heap) (p : Address) (values : TensorView.Values shape)
    (state : ModelExchange.State) (nonempty : 0 < shape.volume) :
    StateProofs.Represents (assigned heap p values shape.volume) p
      (ModelExchange.setContinuousState state values[shape.volume - 1]) := by
  have count : shape.volume = (shape.volume - 1) + 1 := by omega
  conv => arg 1; arg 4; rw [count]
  rw [assigned, dif_pos (by omega)]
  exact StateProofs.written_represents heap p state _

end Rumoca.FMI3.Float64Set
