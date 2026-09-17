import RumocaFMI3.TensorContinuousStates
import RumocaFMI3.TensorInstanceRhs
import RumocaC.AdditionResults

/-! Tensor Co-Simulation `fmi3DoStep` internal step over the static tensor
instance record, as a package-checked product.

The tensor Co-Simulation step mirrors the scalar unit-Euler policy: the
communication step must be a positive integer multiple of the internal unit step
and at most the scalar bound, otherwise `fmi3Discard` without advancing. Each
internal step evaluates the prepared tensor derivative entry `rumoca_rhs` into the
instance's `der(x)` region, advances the state `x` by `x + dx` elementwise with a
counted `size_t` loop over the symbolic state volume, and advances the independent
time base by one.

This module delivers the internal-step Euler kernel: the elementwise
`x[k] = x[k] + dx[k]` loop over the symbolic volume (`euler_reaches`), keeping the
finite-arithmetic outcome of each cell addition explicit as an `Adds` premise, in
the same style the tensor derivative getter keeps `Finite.Executes` explicit. The
loop bound is the symbolic state volume, so no tensor coordinate is enumerated in
Lean.

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. Every theorem is universal in the tensor shape,
the region addresses and the heap. -/
noncomputable section
namespace Rumoca.FMI3.TensorDoStep
open CTree CMemory CBody CLoops
open Rumoca.CMemory.TensorView
open Rumoca.FMI3.TensorFloat64 (dstCell srcCell dstCell_lvalue)
open Binary64 (toBits)

/-- The Euler update loop body: `x[k] = x[k] + dx[k];`, reading the state cell
`dst[k]` and the derivative cell `src[k]` and writing the elementwise sum back
into the state cell. -/
def eulerBody : List Stmt := [.assign dstCell (.bin .add dstCell srcCell)]

theorem eulerBody_closed : eulerBody.all CLoops.noDeclarations = true := by
  simp [eulerBody, dstCell, srcCell, CLoops.noDeclarations]

section
variable [interface : CInterface]

/-- One Euler iteration reads the state cell `dst[k]` and derivative cell `src[k]`
and writes their finite C sum back into the state cell. The finite-arithmetic
outcome of this cell is the explicit premise `adds`. -/
theorem eulerStep (env : Locals) (types : Types) (heap : Heap) (dstBase srcBase : Address)
    {shape : Tensor.Shape} (state deriv sum : Values shape) (i : Fin shape.volume)
    (old : Option Value) (rest : List Stmt)
    (dstBound : resolve env "dst" = some (.pointer (some dstBase)))
    (srcBound : resolve env "src" = some (.pointer (some srcBase)))
    (counter : resolve env "k" = some (.integer i.val))
    (dstRead : load heap (dstBase.index i.val) = some (.finite state[i]))
    (srcRead : load heap (srcBase.index i.val) = some (.finite deriv[i]))
    (dstStore : heap (dstBase.index i.val) = some ⟨.float64, true, old⟩)
    (adds : Binary64.Adds state[i] deriv[i] (.finite sum[i])) :
    CLoops.next (.running (eulerBody ++ rest) env types heap) =
      some (.running rest env types
        (StateProofs.written heap (dstBase.index i.val) (toBits sum[i]).val)) := by
  have address : CBody.lvalue env heap dstCell = some (dstBase.index i.val) :=
    dstCell_lvalue env heap dstBase i.val dstBound counter
  have dstEval : CBody.eval env heap dstCell = some (.finite state[i]) := by
    have raw : CBody.eval env heap dstCell = load heap (dstBase.index i.val) := by
      simp [dstCell, Runtime.v, CBody.eval, dstBound, counter, Value.address]
    exact raw.trans dstRead
  have srcEval : CBody.eval env heap srcCell = some (.finite deriv[i]) := by
    have raw : CBody.eval env heap srcCell = load heap (srcBase.index i.val) := by
      simp [srcCell, Runtime.v, CBody.eval, srcBound, counter, Value.address]
    exact raw.trans srcRead
  have rhs : CLoops.eval env types heap (.bin .add dstCell srcCell) =
      some (.float64 (Binary64.addResult state[i] deriv[i]).encode) := by
    have unfold : CLoops.eval env types heap (.bin .add dstCell srcCell) =
        (CBody.eval env heap dstCell).bind
          (fun x => (CBody.eval env heap srcCell).bind (fun y => CArithmetic.floatAdd x y)) := rfl
    rw [unfold, dstEval, srcEval]
    simp only [Option.bind_some]
    exact CArithmetic.add_result _ _
  have encoded : (Binary64.addResult state[i] deriv[i]).encode = (toBits sum[i]).val := by
    rw [(Binary64.addResult_correct state[i] deriv[i] (.finite sum[i])).mpr adds]
    rfl
  rw [encoded] at rhs
  simp only [dstCell, srcCell] at address rhs
  simp [eulerBody, dstCell, srcCell, CLoops.next, address, rhs, Option.bind_some,
    store_float64 heap _ old _ dstStore, StateProofs.written]

end

section
variable [interface : CInterface]

/-- The Euler update loop advances the whole state region by the elementwise finite
sum of the state and the derivative, cell by cell over the symbolic volume, in the
call scheduler. The state region is read in place while it is being written: cell
`k` is read before it is overwritten, and the derivative region is disjoint from
it. Each cell's finite-arithmetic outcome is the explicit premise `adds`. -/
theorem euler_reaches (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (dstBase srcBase : Address) {shape : Tensor.Shape}
    (state deriv sum : Values shape) (rest : List Stmt) (resultType : String)
    (stack : CCalls.Typed.Continuation)
    (bounded : shape.volume < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "expected" = some (.integer shape.volume))
    (dstBound : resolve env "dst" = some (.pointer (some dstBase)))
    (srcBound : resolve env "src" = some (.pointer (some srcBase)))
    (readableDst : Reads heap dstBase state)
    (readableSrc : Reads heap srcBase deriv)
    (writable : Writable heap dstBase shape.volume)
    (separate : ∀ i < shape.volume, ∀ j < shape.volume, dstBase.index i ≠ srcBase.index j)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds state[i] deriv[i] (.finite sum[i])) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "expected") eulerBody :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running rest (counterEnv env "k" shape.volume) types
        (written heap dstBase sum shape.volume)) resultType stack) := by
  apply CCalls.Events.loop_reaches program "k" (Runtime.v "expected") eulerBody rest
    (fun _ => env) types (written heap dstBase sum) shape.volume resultType stack typed bounded
    eulerBody_closed
  · intro i inside
    simpa [Runtime.v, CBody.eval, counterEnv, CBody.bind, resolve] using count
  · intro i inside
    obtain ⟨old, storage⟩ := Float64Calls.pending_output heap dstBase sum writable i inside
    have dstRead : load (written heap dstBase sum i) (dstBase.index i) =
        some (.finite state[(⟨i, inside⟩ : Fin shape.volume)]) := by
      have frame := written_at heap dstBase sum i (le_of_lt inside) ⟨i, inside⟩
      simp only [lt_self_iff_false, if_false] at frame
      have loaded := readableDst ⟨i, inside⟩
      simp only [load, frame] at loaded ⊢
      exact loaded
    have srcRead : load (written heap dstBase sum i) (srcBase.index i) =
        some (.finite deriv[(⟨i, inside⟩ : Fin shape.volume)]) := by
      have frame := written_frame heap dstBase sum i (srcBase.index i)
        (fun j hj => (separate j hj i inside).symm)
      have loaded := readableSrc ⟨i, inside⟩
      simp only [load, frame] at loaded ⊢
      exact loaded
    have counter : resolve (counterEnv env "k" i) "k" = some (.integer i) := by
      simp [counterEnv, CBody.bind, resolve]
    have step := eulerStep (counterEnv env "k" i) types (written heap dstBase sum i)
      dstBase srcBase state deriv sum ⟨i, inside⟩ old
      (counterStep "k" :: loop "k" (Runtime.v "expected") eulerBody :: rest)
      (by simpa [counterEnv, CBody.bind, resolve] using dstBound)
      (by simpa [counterEnv, CBody.bind, resolve] using srcBound)
      counter dstRead srcRead storage (adds ⟨i, inside⟩)
    have next : StateProofs.written (written heap dstBase sum i) (dstBase.index i)
        (toBits sum[(⟨i, inside⟩ : Fin shape.volume)]).val = written heap dstBase sum (i + 1) := by
      simp [written, dif_pos inside, StateProofs.written, Value.finite]
    rw [next] at step
    exact .next (CCalls.Events.body_step program step resultType stack) (.refl _)

end

/-! ### One internal step over the tensor instance record

The internal step advances the state by one unit Euler step: the derivative entry
has written `der(x) = result` into the instance's `dx` region (established by
`TensorInstanceRhs.derivative_writes_events`); the staged Euler tail then reads the
state region `x` and the derivative region `dx` and writes `x + dx` elementwise
back into `x`, over the symbolic state volume. This mirrors the scalar unit-Euler
solve while keeping the state tensor symbolic. -/

/-- The staged Euler tail: point `dst` at the state region `x`, `src` at the
derivative region `dx`, stage the element count, and run the elementwise update
loop. -/
def eulerTail (shape : Tensor.Shape) : List Stmt :=
  .declare "fmi3Float64 *" "dst" (.address (Runtime.field TensorInstance.stateName)) ::
  .declare "fmi3Float64 *" "src" (.address (Runtime.field TensorInstance.derivativeName)) ::
  .declare "size_t" "expected" (Runtime.n shape.volume) ::
  .declare "size_t" "k" (Runtime.n 0) ::
  [loop "k" (Runtime.v "expected") eulerBody]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
variable (program : CCalls.Events.Program E)

/-- The Euler tail over a heap whose derivative region already holds `result`
(the situation `TensorInstanceRhs.derivative_writes_events` establishes) and whose
state region holds `state`: it advances the state region to the elementwise finite
sum `state + result` and leaves any following statements to run on the updated
heap. Each cell's finite-arithmetic outcome is the explicit premise `adds`; the
state and derivative regions are disjoint members of the one instance record. -/
theorem euler_delivers (shape : Tensor.Shape) (H : Heap) (p : Address) (env : Locals) (types0 : Types)
    (state result sum : Values shape) (rest : List Stmt) (resultType : String)
    (stack : CCalls.Typed.Continuation) (bounded : shape.volume < 2 ^ 64)
    (mBound : env "m" = some (.pointer (some p)))
    (freshDst : env "dst" = none) (freshSrc : env "src" = none)
    (freshExpected : env "expected" = none) (freshK : env "k" = none)
    (readableX : Reads H (p.member TensorInstance.stateName) state)
    (readableDx : Reads H (p.member TensorInstance.derivativeName) result)
    (writableX : Writable H (p.member TensorInstance.stateName) shape.volume)
    (separate : ∀ i < shape.volume, ∀ j < shape.volume,
      (p.member TensorInstance.stateName).index i ≠ (p.member TensorInstance.derivativeName).index j)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds state[i] result[i] (.finite sum[i])) :
    ∃ envF typesF, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (eulerTail shape ++ rest) env types0 H) resultType stack)
      (.body (.running rest envF typesF
        (written H (p.member TensorInstance.stateName) sum shape.volume)) resultType stack) := by
  have s_dst : CLoops.next (.running (eulerTail shape ++ rest) env types0 H) =
      some (.running (.declare "fmi3Float64 *" "src" (.address (Runtime.field TensorInstance.derivativeName)) ::
        .declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") eulerBody :: rest)
        (bind env "dst" (.pointer (some (p.member TensorInstance.stateName))))
        (bindType types0 "dst" .pointer) H) := by
    apply TensorFloat64.declare_step_e env types0 H "fmi3Float64 *" "dst"
      (.address (Runtime.field TensorInstance.stateName)) .pointer
      (.pointer (some (p.member TensorInstance.stateName))) _ _ freshDst rfl _ rfl
    apply CBodyEmbedding.eval_refines
    simp [Runtime.field, Runtime.v, CBody.eval, CBody.lvalue, CBody.resolve, mBound, Value.address]
  set env1 := bind env "dst" (.pointer (some (p.member TensorInstance.stateName))) with henv1
  have s_src : CLoops.next (.running (.declare "fmi3Float64 *" "src"
        (.address (Runtime.field TensorInstance.derivativeName)) ::
        .declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") eulerBody :: rest)
        env1 (bindType types0 "dst" .pointer) H) =
      some (.running (.declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") eulerBody :: rest)
        (bind env1 "src" (.pointer (some (p.member TensorInstance.derivativeName))))
        (bindType (bindType types0 "dst" .pointer) "src" .pointer) H) := by
    apply TensorFloat64.declare_step_e env1 _ H "fmi3Float64 *" "src"
      (.address (Runtime.field TensorInstance.derivativeName)) .pointer
      (.pointer (some (p.member TensorInstance.derivativeName))) _ _
      (by simp [henv1, CBody.bind, freshSrc]) rfl _ rfl
    apply CBodyEmbedding.eval_refines
    have m1 : env1 "m" = some (.pointer (some p)) := by simp [henv1, CBody.bind, mBound]
    simp [Runtime.field, Runtime.v, CBody.eval, CBody.lvalue, CBody.resolve, m1, Value.address]
  set env2 := bind env1 "src" (.pointer (some (p.member TensorInstance.derivativeName))) with henv2
  have s_exp : CLoops.next (.running (.declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") eulerBody :: rest)
        env2 (bindType (bindType types0 "dst" .pointer) "src" .pointer) H) =
      some (.running (.declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") eulerBody :: rest)
        (bind env2 "expected" (.integer shape.volume))
        (CLoops.bindType (bindType (bindType types0 "dst" .pointer) "src" .pointer) "expected" .size) H) := by
    apply TensorFloat64.declare_step_e env2 _ H "size_t" "expected" (Runtime.n shape.volume) .size
      (.integer shape.volume) _ _ (by simp [henv2, henv1, CBody.bind, freshExpected]) rfl
      (by simp [Runtime.n, CLoops.eval, CBody.eval]) (CLoops.convert_size_nat _ bounded)
  set env3 := bind env2 "expected" (.integer shape.volume) with henv3
  set types3 := CLoops.bindType (bindType (bindType types0 "dst" .pointer) "src" .pointer) "expected" .size
    with htypes3
  have freshK3 : env3 "k" = none := by simp [henv3, henv2, henv1, CBody.bind, freshK]
  have s_k := CLoops.counter_initialize env3 types3 H "k"
    (loop "k" (Runtime.v "expected") eulerBody :: rest) freshK3 rfl
  have expBound : resolve env3 "expected" = some (.integer shape.volume) := by
    simp [henv3, CBody.bind, CBody.resolve]
  have dstBound : resolve env3 "dst" = some (.pointer (some (p.member TensorInstance.stateName))) := by
    simp [henv3, henv2, henv1, CBody.bind, CBody.resolve]
  have srcBound : resolve env3 "src" = some (.pointer (some (p.member TensorInstance.derivativeName))) := by
    simp [henv3, henv2, henv1, CBody.bind, CBody.resolve]
  refine ⟨counterEnv env3 "k" shape.volume, CLoops.bindType types3 "k" .size, ?_⟩
  refine .next (CCalls.Events.body_step program s_dst resultType stack)
    (.next (CCalls.Events.body_step program s_src resultType stack)
    (.next (CCalls.Events.body_step program s_exp resultType stack)
    (.next (CCalls.Events.body_step program s_k resultType stack) ?_)))
  exact euler_reaches program env3 (CLoops.bindType types3 "k" .size) H
    (p.member TensorInstance.stateName) (p.member TensorInstance.derivativeName) state result sum
    rest resultType stack bounded (by simp [CLoops.bindType]) expBound dstBound srcBound
    readableX readableDx writableX separate adds

end

/-! ### The full internal step: derivative evaluation composed with the Euler update

The internal-step body invokes the prepared tensor derivative entry `rumoca_rhs`
and then runs the staged Euler tail. Composing the derivative run (which writes
`der(x) = result` and preserves the state region and every other instance) with
the Euler tail (which advances the state region by `x + dx` elementwise over the
symbolic volume) yields one observable-machine execution that advances the state
by one unit Euler step. -/

/-- The internal-step body: evaluate the tensor derivative entry into `der(x)`,
then run the staged Euler update tail. -/
def internalBody (shape : Tensor.Shape) : List Stmt :=
  .eval (Runtime.call "rumoca_rhs" TensorContinuousStates.derivEntryArgs) :: eulerTail shape

/-- The state region of a tensor instance record is writable: it is placed with a
writable float64 array, and the input, derivative and output members are placed on
distinct members that preserve it. -/
theorem store_writable_state (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Tensor.Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (output : Option (Values oshape)) :
    Writable (TensorInstance.store backing pool i shape oshape time state input output)
      (TensorInstance.field pool i TensorInstance.stateName) shape.volume := by
  have core : Writable (TensorInstance.core backing pool i shape time state input)
      ((TensorInstance.record pool i).member TensorInstance.stateName) shape.volume := by
    unfold TensorInstance.core
    exact TensorInstance.writable_place_other (by decide +kernel)
      (TensorInstance.writable_place_other (by decide +kernel)
        (Rumoca.CMemory.TensorRegion.place_writable _ _ _ (some state)))
  cases output with
  | none => exact core
  | some J => exact TensorInstance.writable_place_other (by decide +kernel) core

section
variable [static : StaticLiterals]
private local instance stepInterface : CInterface := cInterface static.addresses
variable (program : CCalls.Events.Program E)

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile in
/-- One tensor Co-Simulation internal step over instance `i`, as one
observable-machine execution: invoke the prepared tensor derivative entry
`rumoca_rhs` (which writes `der(x) = result`), then advance the state region `x`
by `x + dx` elementwise over the symbolic volume. It reaches a heap whose state
region reads the elementwise finite Euler sum `state + result`, whose derivative
region still reads `result`, and every cell of every other instance preserved. The
finite tensor derivative is the explicit premise `executed`, each cell addition the
explicit premise `adds`, and `resolves` records that the nested tensor helper calls
resolve directly by name, exactly as the derivative getter records. -/
theorem internalStep_reaches (shape oshape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state input result sum : Values shape) (output : Option (Values oshape))
    (count : UInt64) (env : Locals) (types0 : Types) (resultType : String)
    (stack : CCalls.Typed.Continuation) (rest : List Stmt)
    (bounded : shape.volume < 2 ^ 64) (matched : count.toNat = shape.volume)
    (mBound : env "m" = some (.pointer (some (TensorInstance.record pool i))))
    (countBound : env "nContinuousStates" = some (.integer count.toNat))
    (freshDst : env "dst" = none) (freshSrc : env "src" = none)
    (freshExpected : env "expected" = none) (freshK : env "k" = none)
    (freshRhs : env "rumoca_rhs" = none)
    (executed : Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment state input) result)
    (adds : ∀ i : Fin shape.volume, Binary64.Adds state[i] result[i] (.finite sum[i]))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape))
        (TensorInstance.store backing pool i shape oshape time state input output) .done) v →
      CCalls.Events.Resolves program v) :
    ∃ derivHeap envF typesF,
      Reads derivHeap (TensorInstance.field pool i TensorInstance.derivativeName) result ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        derivHeap ((TensorInstance.field pool j b).index k) =
          backing ((TensorInstance.field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (internalBody shape ++ rest) env types0
          (TensorInstance.store backing pool i shape oshape time state input output)) resultType stack)
        (.body (.running rest envF typesF
          (written derivHeap (TensorInstance.field pool i TensorInstance.stateName) sum shape.volume))
          resultType stack) := by
  set H := TensorInstance.store backing pool i shape oshape time state input output with hH
  set m := TensorInstance.record pool i with hm'
  set cont := CCalls.Typed.Continuation.caller .discard (eulerTail shape ++ rest) env types0 resultType stack
    with hcont
  have enter : CCalls.Events.internalNext program
      (.body (.running (internalBody shape ++ rest) env types0 H) resultType stack) =
      some (.calling "rumoca_rhs"
        [.pointer (some (m.member TensorInstance.stateName)), .pointer (some (m.member TensorInstance.inputName)),
         .pointer (some (m.member TensorInstance.derivativeName)), .integer count.toNat] H cont) := by
    simp [internalBody, eulerTail, List.cons_append, CCalls.Events.internalNext, CCalls.Typed.nextWith,
      CLoops.next, CLoops.eval, TensorContinuousStates.derivEntryArgs, Runtime.call, Runtime.field,
      Runtime.v, CBody.eval, CBody.lvalue, CCalls.Events.enterCall, CCalls.Events.resolve,
      CCalls.Indirect.operand, CCalls.Indirect.resolve, CCalls.arguments, mBound, countBound,
      CBody.bind, CBody.resolve, CBody.constants, Value.address, hcont, freshRhs]
  have argsEq : [Value.pointer (some (m.member TensorInstance.stateName)),
      .pointer (some (m.member TensorInstance.inputName)),
      .pointer (some (m.member TensorInstance.derivativeName)), .integer count.toNat] =
      Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
        (TensorInstanceRhs.args pool i shape) := by
    rw [hm', matched]; rfl
  obtain ⟨derivHeap, reads, frameH, others, ran⟩ :=
    TensorInstanceRhs.derivative_writes_events (shape := shape) definitions program linked library found
      backing pool i oshape time state input result output bounded executed resolves cont
  have resume : CCalls.Events.internalNext program (.returning .void derivHeap cont) =
      some (.body (.running (eulerTail shape ++ rest) env types0 derivHeap) resultType stack) := by
    simp [hcont, CCalls.Events.internalNext, CCalls.Typed.nextWith, CCalls.Typed.resume]
  have outsideX : ∀ a : Fin shape.volume,
      Outside (TensorInstanceRhs.locations pool i) (TensorInstanceRhs.kernel shape).derivative
        (TensorModelRhs.derivativePlan (TensorInstanceRhs.kernel shape) (TensorInstanceRhs.plan shape))
        ((TensorInstance.field pool i TensorInstance.stateName).index a.val) :=
    fun a => ⟨fun a2 _ => TensorInstance.fields_separate pool i TensorInstance.stateName
      TensorInstance.derivativeName (by decide +kernel) a.val a2, True.intro⟩
  have readableX : Reads derivHeap (m.member TensorInstance.stateName) state := by
    intro a
    have frame := frameH ((TensorInstance.field pool i TensorInstance.stateName).index a.val) (outsideX a)
    have base := TensorInstance.reads_state backing pool i shape oshape time state input output a
    simp only [TensorInstance.field, hm'] at frame ⊢
    simp only [load, frame]
    simpa only [load, TensorInstance.field] using base
  have readableDx : Reads derivHeap (m.member TensorInstance.derivativeName) result := by
    intro a; simpa only [TensorInstance.field, hm'] using reads a
  have writableX : Writable derivHeap (m.member TensorInstance.stateName) shape.volume := by
    intro a ha
    have frame := frameH ((TensorInstance.field pool i TensorInstance.stateName).index a) (outsideX ⟨a, ha⟩)
    obtain ⟨old, ho⟩ := store_writable_state backing pool i shape oshape time state input output a ha
    refine ⟨old, ?_⟩
    simp only [TensorInstance.field, hm'] at frame ho ⊢
    rw [frame]; exact ho
  have separateXdx : ∀ a < shape.volume, ∀ b < shape.volume,
      (m.member TensorInstance.stateName).index a ≠ (m.member TensorInstance.derivativeName).index b := by
    intro a _ b _
    simpa only [TensorInstance.field, hm'] using
      TensorInstance.fields_separate pool i TensorInstance.stateName TensorInstance.derivativeName
        (by decide +kernel) a b
  obtain ⟨envF, typesF, eulerRun⟩ := euler_delivers program shape derivHeap m env types0 state result sum
    rest resultType stack bounded mBound freshDst freshSrc freshExpected freshK readableX readableDx
    writableX separateXdx adds
  refine ⟨derivHeap, envF, typesF, by simpa only [TensorInstance.field, hm'] using readableDx, others, ?_⟩
  exact .next (argsEq ▸ enter) (ran.trans (.next resume eulerRun))

end
end Rumoca.FMI3.TensorDoStep
