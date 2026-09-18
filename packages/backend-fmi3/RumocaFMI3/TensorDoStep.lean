import RumocaFMI3.TensorContinuousStates
import RumocaFMI3.TensorInstanceRhs
import RumocaFMI3.StepEntry
import RumocaFMI3.StepGuards
import RumocaFMI3.StepAdmission
import RumocaFMI3.StepDiscard
import RumocaC.AdditionResults
import RumocaC.TensorFillProofs

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

/-- Every cell of every instance record in a pool shares the pool block: the
record address is `pool.index i` and member/index only extend the member list and
offset, leaving the block field untouched. -/
theorem field_index_block (pool : Address) (i : Nat) (nm : String) (a : Nat) :
    ((TensorInstance.field pool i nm).index a).block = (TensorInstance.record pool i).block := rfl

/-- An address in a different block than an instance record cannot be any cell of
that record. Used to frame caller buffers, which lie outside the instance pool,
across the internal-step writes (which touch only instance-record cells). -/
theorem cell_block_ne (pool : Address) (i : Nat) (nm : String) (a : Nat) (q : Address)
    (hq : q.block ≠ (TensorInstance.record pool i).block) :
    q ≠ (TensorInstance.field pool i nm).index a :=
  fun same => hq ((congrArg Address.block same).trans (field_index_block pool i nm a))

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

/-! ### Interface-independent `fmi3OK` return

The final `return fmi3OK` statement resolves the status constant from the ambient
C interface's `fmi3OK` binding, so its reached-return holds under any interface
that binds `fmi3OK` to zero (the scalar `cInterface` table and the header-aware
floating-environment interface both do). -/
section
variable [interface : CInterface]

open CTree CMemory CBody in
/-- The trailing `return fmi3OK` reaches a `fmi3OK`-status return over the same
heap under any interface binding `fmi3OK` to zero. -/
theorem finishOK (program : CCalls.Events.Program E) (heap : Heap) (env : Locals)
    (types : CLoops.Types) (stack : CCalls.Typed.Continuation) (ok : env "fmi3OK" = none)
    (status : interface.types "fmi3Status" = some .int32)
    (okBound : interface.constants "fmi3OK" = some (.integer 0)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running [Runtime.ok] env types heap) "fmi3Status" stack)
      (.returning (.integer 0) heap stack) := by
  refine .next (t := .body (.returned ⟨.integer 0, heap⟩) "fmi3Status" stack) ?_ (.next ?_ (.refl _))
  · simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CLoops.next, CLoops.eval,
      Runtime.ok, Runtime.ret, Runtime.v, CBody.eval, CBody.resolve, CBody.constants, ok, okBound]
  · simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CCalls.returnCast, CBody.cast,
      status, convert]

end

/-! ### The header-aware tensor floating-environment interface

The tensor Co-Simulation step body reads the `FE_TONEAREST` rounding macro in its
guard prefix, so its proofs run in the floating-environment interface
`CFenv.Header.interface header (cInterface static.addresses)`: the pinned tensor C
interface extended with the header's round-to-nearest constant. Only that constant
is added; every type spelling and every other constant coincides with the pinned
`cInterface`, so the numerical tail's status and helper resolutions are unchanged. -/
/-- The pinned type spellings and helper/status constants the tensor Co-Simulation
step body resolves, stated once for any C interface. `cInterface` and the
header-aware floating-environment interface both satisfy it: the tensor numerical
tail carries this as a single premise instead of the individual bindings. -/
structure TensorFenv (interface : CInterface) : Prop where
  intType : interface.types "int" = some .int32
  doubleType : interface.types "double" = some .float64
  statusType : interface.types "fmi3Status" = some .int32
  floatPointerType : interface.types "fmi3Float64 *" = some .pointer
  sizeType : interface.types "size_t" = some .size
  fmi3OK : interface.constants "fmi3OK" = some (.integer 0)
  fegetround : interface.constants "fegetround" = none
  floorConstant : interface.constants "floor" = none
  rhs : interface.constants "rumoca_rhs" = none
  jacobian : interface.constants "rumoca_square_jacobian_diag" = none

section
variable [static : StaticLiterals]

/-- The floating-environment tensor interface: `cInterface` plus the header's
`FE_TONEAREST` rounding macro. -/
abbrev fenvInterface (header : CFenv.Header) : CInterface :=
  CFenv.Header.interface header (cInterface static.addresses)

@[simp] theorem fenvInterface_types (header : CFenv.Header) (name : String) :
    (fenvInterface (static := static) header).types name = cTypes name := rfl

@[simp] theorem fenvInterface_nearest (header : CFenv.Header) :
    (fenvInterface (static := static) header).constants "FE_TONEAREST" = some (.integer header.nearest) :=
  CFenv.Header.nearest_binding header _

theorem fenvInterface_constant (header : CFenv.Header) (name : String) (other : name ≠ "FE_TONEAREST") :
    (fenvInterface (static := static) header).constants name = cConstants name := by
  rw [CFenv.Header.other_binding header _ name other]; rfl

/-- The pinned tensor C interface supplies every pinned tensor type spelling and
helper/status constant (`FE_TONEAREST` is carried separately when the guard runs). -/
theorem cInterface_fenv : TensorFenv (cInterface static.addresses) where
  intType := rfl
  doubleType := rfl
  statusType := rfl
  floatPointerType := rfl
  sizeType := rfl
  fmi3OK := rfl
  fegetround := rfl
  floorConstant := rfl
  rhs := rfl
  jacobian := rfl

/-- The error context whose target is the pinned tensor C interface: reuses the
shared `StepDiscard`/error-callback machinery over the tensor instance record's
`logging`/`environment`/`logger` cells. -/
def cErrorContext : ErrorContext static.addresses where
  target := cInterface static.addresses
  types := rfl
  bytes := rfl
  helper := by
    simp [CLiteral.Interface.CodeAgrees, CLiteral.Interface.StmtAgrees, CLiteral.Interface.ExprAgrees,
      CLiteral.Interface.names, Runtime.helpers,
      Runtime.setMode, Runtime.put, Runtime.mode, Runtime.log, Runtime.branch,
      Runtime.ret, Runtime.v, Runtime.n, Runtime.field, Runtime.both]
  error := rfl
  ordinary := rfl

/-- The header-aware error context: the pinned tensor interface extended with the
round-to-nearest macro, so its target is `fenvInterface header`. -/
abbrev fenvErrorContext (header : CFenv.Header) : ErrorContext static.addresses :=
  (cErrorContext (static := static)).withRounding header

@[simp] theorem fenvErrorContext_target (header : CFenv.Header) :
    (fenvErrorContext (static := static) header).target = fenvInterface header := rfl

/-- The header-aware floating-environment interface supplies every pinned tensor
type spelling and helper/status constant. -/
theorem fenvInterface_fenv (header : CFenv.Header) :
    TensorFenv (fenvInterface (static := static) header) where
  intType := rfl
  doubleType := rfl
  statusType := rfl
  floatPointerType := rfl
  sizeType := rfl
  fmi3OK := fenvInterface_constant header "fmi3OK" (by decide)
  fegetround := fenvInterface_constant header "fegetround" (by decide)
  floorConstant := fenvInterface_constant header "floor" (by decide)
  rhs := fenvInterface_constant header "rumoca_rhs" (by decide)
  jacobian := fenvInterface_constant header "rumoca_square_jacobian_diag" (by decide)

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
  .declare "fmi3Float64 *" "dst" ((Runtime.region TensorInstance.stateName)) ::
  .declare "fmi3Float64 *" "src" ((Runtime.region TensorInstance.derivativeName)) ::
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
      some (.running (.declare "fmi3Float64 *" "src" ((Runtime.region TensorInstance.derivativeName)) ::
        .declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") eulerBody :: rest)
        (bind env "dst" (.pointer (some (p.member TensorInstance.stateName))))
        (bindType types0 "dst" .pointer) H) := by
    apply TensorFloat64.declare_step_e env types0 H "fmi3Float64 *" "dst"
      ((Runtime.region TensorInstance.stateName)) .pointer
      (.pointer (some (p.member TensorInstance.stateName))) _ _ freshDst rfl _ rfl
    apply CBodyEmbedding.eval_refines
    simp [Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.lvalue, CBody.resolve, mBound, Value.address]
  set env1 := bind env "dst" (.pointer (some (p.member TensorInstance.stateName))) with henv1
  have s_src : CLoops.next (.running (.declare "fmi3Float64 *" "src"
        ((Runtime.region TensorInstance.derivativeName)) ::
        .declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") eulerBody :: rest)
        env1 (bindType types0 "dst" .pointer) H) =
      some (.running (.declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") eulerBody :: rest)
        (bind env1 "src" (.pointer (some (p.member TensorInstance.derivativeName))))
        (bindType (bindType types0 "dst" .pointer) "src" .pointer) H) := by
    apply TensorFloat64.declare_step_e env1 _ H "fmi3Float64 *" "src"
      ((Runtime.region TensorInstance.derivativeName)) .pointer
      (.pointer (some (p.member TensorInstance.derivativeName))) _ _
      (by simp [henv1, CBody.bind, freshSrc]) rfl _ rfl
    apply CBodyEmbedding.eval_refines
    have m1 : env1 "m" = some (.pointer (some p)) := by simp [henv1, CBody.bind, mBound]
    simp [Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.lvalue, CBody.resolve, m1, Value.address]
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
      CLoops.next, CLoops.eval, TensorContinuousStates.derivEntryArgs, Runtime.call, Runtime.region, Runtime.field, Runtime.n,
      Runtime.v, CBody.eval, CBody.lvalue, CCalls.Events.enterCall, CCalls.Events.resolve,
      CCalls.Indirect.operand, CCalls.Indirect.resolve, CCalls.arguments, mBound, countBound,
      CBody.bind, CBody.resolve, CBody.constants, Value.address, hcont, freshRhs]
  have argsEq : [Value.pointer (some (m.member TensorInstance.stateName)),
      .pointer (some (m.member TensorInstance.inputName)),
      .pointer (some (m.member TensorInstance.derivativeName)), .integer count.toNat] =
      Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
        (TensorInstanceRhs.args pool i shape) := by
    rw [hm', matched]; rfl
  obtain ⟨derivHeap, reads, _writableDeriv, frameH, others, ran⟩ :=
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

/-! ### The prepared derivative run over an abstract well-formed instance heap

The internal-step composition above runs the derivative entry on the concrete
`TensorInstance.store` heap. The multi-step Co-Simulation loop reaches heaps that
are no longer literally `store`: after one internal step the `der(x)` region holds
the previous derivative rather than the uninitialized placement, so the transfer
lemma cannot be re-applied in `store` form. `derivative_run` states the same
derivative transfer over an arbitrary heap whose state and input regions read the
supplied values and whose derivative region is writable. The three heap premises
are exactly what `TensorModelRhs.events_reaches` needs; every other premise of the
prepared entry (argument validity, layout bounds, member separation) is structural
in the instance record and holds for any heap. -/
section
variable [interface : CInterface]
variable (program : CCalls.Events.Program E)

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile in
/-- Running the prepared tensor derivative entry `rumoca_rhs` on instance `i` over
an arbitrary heap `H` whose state region reads `state`, whose input region reads
`input`, and whose derivative region is writable: it writes the finite tensor
derivative `result` into the `der(x)` region and preserves every cell outside that
region (in particular the state, input and time regions, and every cell of every
other instance). Universal in the shape, instance index, heap and caller. -/
theorem derivative_run (shape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (H : Heap) (pool : Address) (i : Nat) (state input result : Values shape)
    (bounded : shape.volume < 2 ^ 64)
    (readsState : Reads H (TensorInstance.field pool i TensorInstance.stateName) state)
    (readsInput : Reads H (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableDx : Writable H (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume)
    (executed : Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment state input) result)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) H .done) v →
      CCalls.Events.Resolves program v)
    (stack : CCalls.Typed.Continuation) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i TensorInstance.derivativeName) result ∧
      Writable finalHeap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume ∧
      (∀ q, Outside (TensorInstanceRhs.locations pool i) (TensorInstanceRhs.kernel shape).derivative
          (TensorModelRhs.derivativePlan (TensorInstanceRhs.kernel shape) (TensorInstanceRhs.plan shape)) q →
        finalHeap q = H q) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling (TensorInstanceRhs.plan shape).derivative.function.name
          (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
            (TensorInstanceRhs.args pool i shape)) H stack)
        (.returning .void finalHeap stack) := by
  have arguments : Arguments.Valid (TensorInstanceRhs.plan shape).derivative.function.parameters
      (TensorInstanceRhs.args pool i shape) := by
    intro p member
    change p ∈ TensorInstanceRhs.derivativeParameters at member
    simp only [TensorInstanceRhs.derivativeParameters, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact .input _
    · exact .input _
    · exact .output _
    · exact .count _ bounded
  have bound : LayoutBound (Arguments.locals (TensorInstanceRhs.plan shape).derivative.function.parameters
      (TensorInstanceRhs.args pool i shape)) (TensorInstanceRhs.locations pool i)
      (TensorModelRhs.derivativeLayout (TensorInstanceRhs.kernel shape) (TensorInstanceRhs.plan shape)) := by
    intro s r
    cases r with
    | here =>
      exact TensorInstanceRhs.parameter_bound TensorInstanceRhs.derivativeParameters pool i shape
        TensorInstance.stateName (by decide +kernel) (by decide +kernel) (by decide +kernel)
    | there r => cases r with
      | here =>
        exact TensorInstanceRhs.parameter_bound TensorInstanceRhs.derivativeParameters pool i shape
          TensorInstance.inputName (by decide +kernel) (by decide +kernel) (by decide +kernel)
      | there r => nomatch r
  have represented : Represents (TensorInstanceRhs.locations pool i)
      (TensorModelRhs.derivativeLayout (TensorInstanceRhs.kernel shape) (TensorInstanceRhs.plan shape))
      H (ArrayProfile.environment state input) := by
    intro s r
    cases r with
    | here => exact readsState
    | there r => cases r with
      | here => exact readsInput
      | there r => nomatch r
  have ready : Ready (Arguments.locals (TensorInstanceRhs.plan shape).derivative.function.parameters
      (TensorInstanceRhs.args pool i shape)) (TensorInstanceRhs.locations pool i)
      (TensorInstanceRhs.kernel shape).derivative
      (TensorModelRhs.derivativePlan (TensorInstanceRhs.kernel shape) (TensorInstanceRhs.plan shape))
      (TensorModelRhs.derivativeLayout (TensorInstanceRhs.kernel shape) (TensorInstanceRhs.plan shape)) H := by
    refine ⟨writableDx, bounded,
      TensorInstanceRhs.parameter_bound TensorInstanceRhs.derivativeParameters pool i shape
        TensorInstance.derivativeName (by decide +kernel) (by decide +kernel) (by decide +kernel), ?_, True.intro⟩
    intro s r i' hi' j hj
    cases r with
    | here =>
      exact TensorInstance.fields_separate pool i TensorInstance.derivativeName TensorInstance.stateName
        (by decide +kernel) i' j
    | there r => cases r with
      | here =>
        exact TensorInstance.fields_separate pool i TensorInstance.derivativeName TensorInstance.inputName
          (by decide +kernel) i' j
      | there r => nomatch r
  obtain ⟨finalHeap, reads, frame, writableResult, ran⟩ :=
    TensorModelRhs.events_reaches (TensorInstanceRhs.kernel shape) (TensorInstanceRhs.plan shape)
      (TensorInstanceRhs.derivative_valid shape)
      definitions program linked library found (TensorInstanceRhs.args pool i shape) arguments
      (TensorInstanceRhs.locations pool i) (ArrayProfile.environment state input) result H
      bound represented ready executed resolves stack
  rw [TensorInstanceRhs.derivativeBuffer_eq] at writableResult
  exact ⟨finalHeap, by rwa [TensorInstanceRhs.derivativeBuffer_eq] at reads,
    writableResult writableDx, frame, ran⟩

end

/-! ### The declaration-free internal-step body

The Co-Simulation grid loop runs each internal step from one shared function-level
block: the pointers to `x` and `dx`, the element count, and both loop counters are
declared once at the top of `fmi3DoStep`, so every loop body is declaration-free
and `CBodyEmbedding.closedBlocks` holds for the whole function. `stepBody` is that
per-internal-step body: evaluate the prepared tensor derivative entry `rumoca_rhs`
into `der(x)`, reset the inner Euler counter `k`, and run the elementwise
`x[k] = x[k] + dx[k]` update loop over the symbolic state volume. Unlike
`internalBody`, it introduces no declarations, so it is a legal outer-loop body. -/
def stepBody : List Stmt :=
  .eval (Runtime.call "rumoca_rhs" TensorContinuousStates.derivEntryArgs) ::
  .assign (Runtime.v "k") (Runtime.n 0) ::
  [loop "k" (Runtime.v "expected") eulerBody]

theorem stepBody_closed : stepBody.all CBodyEmbedding.closedBlocks = true := by
  simp [stepBody, Runtime.call, Runtime.v, Runtime.n, eulerBody, dstCell, srcCell,
    CBodyEmbedding.closedBlocks, CLoops.noDeclarations, CLoops.loop, CLoops.counterStep]

theorem stepBody_noDecl : stepBody.all CLoops.noDeclarations = true := by
  simp [stepBody, Runtime.call, Runtime.v, Runtime.n, eulerBody, dstCell, srcCell,
    CLoops.noDeclarations, CLoops.loop, CLoops.counterStep]

section
variable [interface : CInterface]
variable (program : CCalls.Events.Program E)

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile in
/-- One tensor Co-Simulation internal step from the declaration-free body
`stepBody` over an arbitrary well-formed instance heap `H`: evaluate the prepared
derivative entry into `der(x)`, reset the inner counter, and advance the state
region `x` by `x + dx` elementwise over the symbolic volume. It reaches a heap
whose state region reads the finite Euler sum `state + result`, whose derivative
region reads `result`, and every cell of every other instance preserved. The three
heap premises `readsState`, `readsInput`, `writableState`/`writableDx` are exactly
those the prepared derivative entry and the Euler tail require; `executed`,
`adds` and `resolves` carry the finite tensor derivative, the per-cell finite
addition and the direct helper resolution, as in `internalStep_reaches`. -/
theorem internalStepPure_reaches (shape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (H : Heap) (pool : Address) (i : Nat)
    (state input result sum : Values shape) (count : UInt64) (v0 : Nat)
    (env : Locals) (types0 : Types) (resultType : String)
    (stack : CCalls.Typed.Continuation) (rest : List Stmt)
    (bounded : shape.volume < 2 ^ 64) (matched : count.toNat = shape.volume)
    (mBound : env "m" = some (.pointer (some (TensorInstance.record pool i))))
    (countBound : env "nContinuousStates" = some (.integer count.toNat))
    (kBound : env "k" = some (.integer v0)) (typedK : types0 "k" = some .size)
    (dstBound : resolve env "dst" =
      some (.pointer (some ((TensorInstance.record pool i).member TensorInstance.stateName))))
    (srcBound : resolve env "src" =
      some (.pointer (some ((TensorInstance.record pool i).member TensorInstance.derivativeName))))
    (expBound : resolve env "expected" = some (.integer shape.volume))
    (freshRhs : env "rumoca_rhs" = none)
    (readsState : Reads H (TensorInstance.field pool i TensorInstance.stateName) state)
    (readsInput : Reads H (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableState : Writable H (TensorInstance.field pool i TensorInstance.stateName) shape.volume)
    (writableDx : Writable H (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume)
    (executed : Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment state input) result)
    (adds : ∀ a : Fin shape.volume, Binary64.Adds state[a] result[a] (.finite sum[a]))
    (resolves : ∀ w, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) H .done) w →
      CCalls.Events.Resolves program w) (fenv : TensorFenv interface) :
    ∃ derivHeap,
      Reads derivHeap (TensorInstance.field pool i TensorInstance.derivativeName) result ∧
      Writable derivHeap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume ∧
      Reads derivHeap (TensorInstance.field pool i TensorInstance.inputName) input ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        derivHeap ((TensorInstance.field pool j b).index k) =
          H ((TensorInstance.field pool j b).index k)) ∧
      (∀ (b : String) (k : Nat), b ≠ TensorInstance.derivativeName →
        derivHeap ((TensorInstance.field pool i b).index k) =
          H ((TensorInstance.field pool i b).index k)) ∧
      (∀ q, q.block ≠ (TensorInstance.record pool i).block →
        written derivHeap (TensorInstance.field pool i TensorInstance.stateName) sum shape.volume q = H q) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (stepBody ++ rest) env types0 H) resultType stack)
        (.body (.running rest (counterEnv env "k" shape.volume) types0
          (written derivHeap (TensorInstance.field pool i TensorInstance.stateName) sum shape.volume))
          resultType stack) := by
  set m := TensorInstance.record pool i with hm'
  set tail := .assign (Runtime.v "k") (Runtime.n 0) :: loop "k" (Runtime.v "expected") eulerBody :: rest
    with htail
  set cont := CCalls.Typed.Continuation.caller .discard tail env types0 resultType stack with hcont
  have enter : CCalls.Events.internalNext program
      (.body (.running (stepBody ++ rest) env types0 H) resultType stack) =
      some (.calling "rumoca_rhs"
        [.pointer (some (m.member TensorInstance.stateName)), .pointer (some (m.member TensorInstance.inputName)),
         .pointer (some (m.member TensorInstance.derivativeName)), .integer count.toNat] H cont) := by
    simp [stepBody, htail, List.cons_append, CCalls.Events.internalNext, CCalls.Typed.nextWith,
      CLoops.next, CLoops.eval, TensorContinuousStates.derivEntryArgs, Runtime.call, Runtime.region, Runtime.field, Runtime.n,
      Runtime.v, CBody.eval, CBody.lvalue, CCalls.Events.enterCall, CCalls.Events.resolve,
      CCalls.Indirect.operand, CCalls.Indirect.resolve, CCalls.arguments, mBound, countBound,
      CBody.resolve, CBody.constants, Value.address, hcont, freshRhs, fenv.rhs]
  have argsEq : [Value.pointer (some (m.member TensorInstance.stateName)),
      .pointer (some (m.member TensorInstance.inputName)),
      .pointer (some (m.member TensorInstance.derivativeName)), .integer count.toNat] =
      Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
        (TensorInstanceRhs.args pool i shape) := by
    rw [hm', matched]; rfl
  obtain ⟨derivHeap, reads, writableDeriv, frameH, ran⟩ :=
    derivative_run program shape definitions linked library found H pool i state input result bounded
      readsState readsInput writableDx executed resolves cont
  have others : ∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
      derivHeap ((TensorInstance.field pool j b).index k) =
        H ((TensorInstance.field pool j b).index k) := by
    intro j b k different
    have outside : Outside (TensorInstanceRhs.locations pool i) (TensorInstanceRhs.kernel shape).derivative
        (TensorModelRhs.derivativePlan (TensorInstanceRhs.kernel shape) (TensorInstanceRhs.plan shape))
        ((TensorInstance.field pool j b).index k) :=
      ⟨fun i' _ => Address.instances_separate pool j i different b TensorInstance.derivativeName k i',
        True.intro⟩
    exact frameH _ outside
  have resume : CCalls.Events.internalNext program (.returning .void derivHeap cont) =
      some (.body (.running tail env types0 derivHeap) resultType stack) := by
    simp [hcont, CCalls.Events.internalNext, CCalls.Typed.nextWith, CCalls.Typed.resume]
  have reset : CLoops.next (.running tail env types0 derivHeap) =
      some (.running (loop "k" (Runtime.v "expected") eulerBody :: rest)
        (counterEnv env "k" 0) types0 derivHeap) := by
    have step := CLoops.assign_local env types0 derivHeap "k" (Runtime.n 0)
      (loop "k" (Runtime.v "expected") eulerBody :: rest) (.integer v0) (.integer 0) (.integer 0) .size
      kBound typedK (by simp [Runtime.n, CLoops.eval, CBody.eval]) (CLoops.convert_size_nat 0 (by decide +kernel))
    simpa only [htail, counterEnv] using step
  have outsideX : ∀ a : Fin shape.volume,
      Outside (TensorInstanceRhs.locations pool i) (TensorInstanceRhs.kernel shape).derivative
        (TensorModelRhs.derivativePlan (TensorInstanceRhs.kernel shape) (TensorInstanceRhs.plan shape))
        ((TensorInstance.field pool i TensorInstance.stateName).index a.val) :=
    fun a => ⟨fun a2 _ => TensorInstance.fields_separate pool i TensorInstance.stateName
      TensorInstance.derivativeName (by decide +kernel) a.val a2, True.intro⟩
  have readableX : Reads derivHeap (m.member TensorInstance.stateName) state := by
    intro a
    have frame := frameH ((TensorInstance.field pool i TensorInstance.stateName).index a.val) (outsideX a)
    have base := readsState a
    simp only [TensorInstance.field, hm'] at frame ⊢
    simp only [load, frame]
    simpa only [load, TensorInstance.field] using base
  have readableDx : Reads derivHeap (m.member TensorInstance.derivativeName) result := by
    intro a; simpa only [TensorInstance.field, hm'] using reads a
  have outsideInput : ∀ a : Fin shape.volume,
      Outside (TensorInstanceRhs.locations pool i) (TensorInstanceRhs.kernel shape).derivative
        (TensorModelRhs.derivativePlan (TensorInstanceRhs.kernel shape) (TensorInstanceRhs.plan shape))
        ((TensorInstance.field pool i TensorInstance.inputName).index a.val) :=
    fun a => ⟨fun a2 _ => TensorInstance.fields_separate pool i TensorInstance.inputName
      TensorInstance.derivativeName (by decide +kernel) a.val a2, True.intro⟩
  have readableInputDeriv : Reads derivHeap (TensorInstance.field pool i TensorInstance.inputName) input := by
    intro a
    have frame := frameH ((TensorInstance.field pool i TensorInstance.inputName).index a.val) (outsideInput a)
    simp only [load, frame]
    simpa only [load] using readsInput a
  have writableX : Writable derivHeap (m.member TensorInstance.stateName) shape.volume := by
    intro a ha
    have frame := frameH ((TensorInstance.field pool i TensorInstance.stateName).index a) (outsideX ⟨a, ha⟩)
    obtain ⟨old, ho⟩ := writableState a ha
    refine ⟨old, ?_⟩
    simp only [TensorInstance.field, hm'] at frame ho ⊢
    rw [frame]; exact ho
  have separateXdx : ∀ a < shape.volume, ∀ b < shape.volume,
      (m.member TensorInstance.stateName).index a ≠ (m.member TensorInstance.derivativeName).index b := by
    intro a _ b _
    simpa only [TensorInstance.field, hm'] using
      TensorInstance.fields_separate pool i TensorInstance.stateName TensorInstance.derivativeName
        (by decide +kernel) a b
  have eulerRun := euler_reaches program env types0 derivHeap
    (m.member TensorInstance.stateName) (m.member TensorInstance.derivativeName) state result sum
    rest resultType stack bounded typedK expBound
    (by simpa only [hm'] using dstBound) (by simpa only [hm'] using srcBound)
    readableX readableDx writableX separateXdx adds
  have memberFrame : ∀ (b : String) (k : Nat), b ≠ TensorInstance.derivativeName →
      derivHeap ((TensorInstance.field pool i b).index k) = H ((TensorInstance.field pool i b).index k) := by
    intro b k hb
    exact frameH _ ⟨fun a2 _ => TensorInstance.fields_separate pool i b TensorInstance.derivativeName hb k a2,
      True.intro⟩
  have genFrame : ∀ q, q.block ≠ (TensorInstance.record pool i).block →
      written derivHeap (TensorInstance.field pool i TensorInstance.stateName) sum shape.volume q = H q := by
    intro q hq
    have wf := written_frame derivHeap (TensorInstance.field pool i TensorInstance.stateName) sum shape.volume q
      (fun a _ => cell_block_ne pool i TensorInstance.stateName a q hq)
    have outq : Outside (TensorInstanceRhs.locations pool i) (TensorInstanceRhs.kernel shape).derivative
        (TensorModelRhs.derivativePlan (TensorInstanceRhs.kernel shape) (TensorInstanceRhs.plan shape)) q :=
      ⟨fun a2 _ => cell_block_ne pool i TensorInstance.derivativeName a2 q hq, True.intro⟩
    rw [wf, frameH q outq]
  refine ⟨derivHeap, readableDx, writableDeriv, readableInputDeriv, others, memberFrame, genFrame, ?_⟩
  refine .next (argsEq ▸ enter) (ran.trans (.next resume ?_))
  exact .next (CCalls.Events.body_step program reset resultType stack) eulerRun

end

/-! ### The N-fold Euler state iteration

The Co-Simulation grid loop advances the state region by one unit Euler step per
internal step. `eulerIterate` is that iteration as an explicit Lean function over
the step count and the per-step finite-sum sequence: the state after `n` internal
steps is `eulerIterate initial sums n`, where `sums k` is the elementwise finite C
sum of the state before step `k` and the derivative evaluated there. Each entry of
`sums` is supplied by the per-step `Binary64.Adds` premises, so no tensor
coordinate is enumerated. This keeps the multi-step state symbolic and matches the
single-step transition proved by `internalStepPure_reaches`, whose reached heap has
state region `written derivHeap x sum vol`, i.e. the next iterate. -/
def eulerIterate {shape : Tensor.Shape} (initial : Values shape) (sums : Nat → Values shape) :
    Nat → Values shape
  | 0 => initial
  | n + 1 => sums n

@[simp] theorem eulerIterate_zero {shape : Tensor.Shape} (initial : Values shape)
    (sums : Nat → Values shape) : eulerIterate initial sums 0 = initial := rfl

@[simp] theorem eulerIterate_succ {shape : Tensor.Shape} (initial : Values shape)
    (sums : Nat → Values shape) (n : Nat) : eulerIterate initial sums (n + 1) = sums n := rfl

/-! ### Outer grid-loop environment bookkeeping

The outer grid loop declares the state/derivative pointers, the element count and
both loop counters once at the top of the function; each internal step only resets
the inner counter `k` and writes the heap. `loopLocals` records the resulting
per-iteration local environment: it equals the entry environment except that the
inner counter `k` is left at the symbolic state volume after the first step. Every
other binding (the record pointer, the element count, the pointer/count locals and
the derivative-entry name) is preserved, so the prepared step premises hold at
every iteration. -/
def loopLocals (env0 : CBody.Locals) (vol : Nat) : Nat → CBody.Locals
  | 0 => env0
  | n + 1 => CBody.bind (loopLocals env0 vol n) "k" (.integer vol)

theorem loopLocals_other (env0 : CBody.Locals) (vol : Nat) (name : String) (h : name ≠ "k") :
    ∀ k, loopLocals env0 vol k name = env0 name
  | 0 => rfl
  | k + 1 => by simp only [loopLocals, CBody.bind, if_neg h]; exact loopLocals_other env0 vol name h k

theorem loopLocals_counter (env0 : CBody.Locals) (vol : Nat) (base : env0 "k" = some (.integer 0)) :
    ∀ k, ∃ v0 : Nat, loopLocals env0 vol k "k" = some (.integer (v0 : Int))
  | 0 => ⟨0, by simpa using base⟩
  | _ + 1 => ⟨vol, by simp [loopLocals, CBody.bind]⟩

/-- Reading a fixed local (any name other than the two loop counters) through the
outer-loop environment returns the entry binding. -/
theorem loopEnv_get (env0 : CBody.Locals) (vol k : Nat) (name : String)
    (hn : name ≠ "n") (hk : name ≠ "k") :
    counterEnv (loopLocals env0 vol k) "n" k name = env0 name := by
  simp only [counterEnv, CBody.bind, if_neg hn, loopLocals_other env0 vol name hk k]

/-- Resolving a fixed local through the outer-loop environment matches the entry
resolution, so pointer and count locals stay in scope at every iteration. -/
theorem resolve_loopEnv [interface : CInterface] (env0 : CBody.Locals) (vol k : Nat) (name : String)
    (hn : name ≠ "n") (hk : name ≠ "k") :
    CBody.resolve (counterEnv (loopLocals env0 vol k) "n" k) name = CBody.resolve env0 name := by
  simp only [CBody.resolve, loopEnv_get env0 vol k name hn hk]

/-- Evaluating a fixed local identifier through the outer-loop environment matches
the entry resolution; used to keep the loop-count operand in scope at every
iteration. -/
theorem eval_id_loopEnv [interface : CInterface] (env0 : CBody.Locals) (vol k : Nat) (heap : Heap)
    (name : String) (hn : name ≠ "n") (hk : name ≠ "k") :
    CBody.eval (counterEnv (loopLocals env0 vol k) "n" k) heap (Runtime.v name) = CBody.resolve env0 name :=
  resolve_loopEnv env0 vol k name hn hk

/-- Reading the inner counter through the outer-loop environment returns its
current (integer) binding, so the prepared step's inner-counter premise holds. -/
theorem loopEnv_inner (env0 : CBody.Locals) (vol k : Nat) {val : Value}
    (hk : loopLocals env0 vol k "k" = some val) :
    counterEnv (loopLocals env0 vol k) "n" k "k" = some val := by
  simp only [counterEnv, CBody.bind, if_neg (by decide : "k" ≠ "n")]; exact hk

/-- The inner counter reset re-associates the two counter bindings: the state
reached after one internal step (inner counter at the state volume, outer counter
still `k`) is the next iteration's entry environment before the outer increment. -/
theorem counterEnv_reset_comm (L : CBody.Locals) (k vol : Nat) :
    counterEnv (counterEnv L "n" k) "k" vol = counterEnv (CBody.bind L "k" (.integer vol)) "n" k := by
  funext key
  by_cases h1 : key = "k" <;> by_cases h2 : key = "n" <;> simp_all [counterEnv, CBody.bind]

/-! ### The N-step Co-Simulation grid loop

`stepLoop_reaches` iterates the declaration-free internal step `stepBody` `N` times
inside the outer counted loop `loop "n" steps stepBody`, by induction on the number
of completed steps. The state region advances by the `N`-fold finite Euler step
`eulerIterate initial sums`, the derivative region reads the last derivative result,
the input region and every cell of every other instance are preserved, and both the
state and derivative regions stay readable and writable throughout, so each step's
prepared-entry premises are re-established from the previous step. The finite tensor
derivative at each visited state is the per-step premise `executes`, each cell
addition the per-step premise `adds`, and `resolves` records the uniform
direct-resolution of the nested tensor helper calls, exactly as one internal step
requires. Universal in the tensor shape, the instance index, the heap and the step
count. -/
section
variable [interface : CInterface]
variable (program : CCalls.Events.Program E)

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile in
theorem stepLoop_reaches (shape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (H0 : Heap) (pool : Address) (i : Nat) (initial input : Values shape)
    (results sums : Nat → Values shape) (count : UInt64) (N : Nat)
    (env0 : Locals) (types0 : Types) (resultType : String)
    (stack : CCalls.Typed.Continuation) (rest : List Stmt)
    (bounded : shape.volume < 2 ^ 64) (matched : count.toNat = shape.volume) (nBound : N < 2 ^ 64)
    (mBound : env0 "m" = some (.pointer (some (TensorInstance.record pool i))))
    (countBound : env0 "nContinuousStates" = some (.integer count.toNat))
    (typedK : types0 "k" = some .size) (typedN : types0 "n" = some .size)
    (kInit : env0 "k" = some (.integer 0))
    (dstBound : CBody.resolve env0 "dst" =
      some (.pointer (some ((TensorInstance.record pool i).member TensorInstance.stateName))))
    (srcBound : CBody.resolve env0 "src" =
      some (.pointer (some ((TensorInstance.record pool i).member TensorInstance.derivativeName))))
    (expBound : CBody.resolve env0 "expected" = some (.integer shape.volume))
    (stepsBound : CBody.resolve env0 "steps" = some (.integer N))
    (freshRhs : env0 "rumoca_rhs" = none)
    (readsState0 : Reads H0 (TensorInstance.field pool i TensorInstance.stateName) initial)
    (readsInput0 : Reads H0 (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableState0 : Writable H0 (TensorInstance.field pool i TensorInstance.stateName) shape.volume)
    (writableDeriv0 : Writable H0 (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume)
    (executes : ∀ n < N, Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment (eulerIterate initial sums n) input) (results n))
    (adds : ∀ n < N, ∀ a : Fin shape.volume,
      Binary64.Adds (eulerIterate initial sums n)[a] (results n)[a] (.finite (sums n)[a]))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) Hn .done) w →
      CCalls.Events.Resolves program w) (fenv : TensorFenv interface) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName) (eulerIterate initial sums N) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.inputName) input ∧
      Writable finalHeap (TensorInstance.field pool i TensorInstance.stateName) shape.volume ∧
      Writable finalHeap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = H0 ((TensorInstance.field pool j b).index k)) ∧
      (∀ pos, N = pos + 1 → Reads finalHeap (TensorInstance.field pool i TensorInstance.derivativeName) (results pos)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (loop "n" (Runtime.v "steps") stepBody :: rest)
          (counterEnv env0 "n" 0) types0 H0) resultType stack)
        (.body (.running rest (counterEnv (loopLocals env0 shape.volume N) "n" N) types0 finalHeap)
          resultType stack) := by
  set sf := TensorInstance.field pool i TensorInstance.stateName with hsf
  set df := TensorInstance.field pool i TensorInstance.derivativeName with hdf
  set jf := TensorInstance.field pool i TensorInstance.inputName with hjf
  -- The loop invariant threaded up to `k` completed steps.
  suffices key : ∀ k, k ≤ N → ∃ Hk,
      Reads Hk sf (eulerIterate initial sums k) ∧
      Reads Hk jf input ∧
      Writable Hk sf shape.volume ∧ Writable Hk df shape.volume ∧
      (∀ (j : Nat) (b : String) (m : Nat), j ≠ i →
        Hk ((TensorInstance.field pool j b).index m) = H0 ((TensorInstance.field pool j b).index m)) ∧
      (∀ pos, k = pos + 1 → Reads Hk df (results pos)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (loop "n" (Runtime.v "steps") stepBody :: rest)
          (counterEnv env0 "n" 0) types0 H0) resultType stack)
        (.body (.running (loop "n" (Runtime.v "steps") stepBody :: rest)
          (counterEnv (loopLocals env0 shape.volume k) "n" k) types0 Hk) resultType stack) by
    obtain ⟨HN, stateN, inputN, wStateN, wDerivN, othersN, derivN, reachN⟩ := key N (le_refl N)
    have stop := CLoops.loop_stop (counterEnv (loopLocals env0 shape.volume N) "n" N) types0 HN "n"
      (Runtime.v "steps") stepBody rest N (by simp [counterEnv, CBody.bind])
      ((eval_id_loopEnv env0 shape.volume N HN "steps" (by decide) (by decide)).trans stepsBound)
      stepBody_noDecl
    exact ⟨HN, stateN, inputN, wStateN, wDerivN, othersN, derivN,
      reachN.trans (.next (CCalls.Events.body_step program stop resultType stack) (.refl _))⟩
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨H0, ?_, readsInput0, writableState0, writableDeriv0, fun _ _ _ _ => rfl, ?_, ?_⟩
    · exact readsState0
    · intro pos hpos; exact absurd hpos.symm (Nat.succ_ne_zero pos)
    · exact .refl _
  | succ k ih =>
    intro hk1
    have hk : k < N := Nat.lt_of_succ_le hk1
    obtain ⟨Hk, stateK, inputK, wStateK, wDerivK, othersK, _derivK, reachK⟩ := ih (le_of_lt hk)
    obtain ⟨v0, kv0⟩ := loopLocals_counter env0 shape.volume kInit k
    -- Enter the loop body for one internal step.
    have enter := CLoops.loop_enter (counterEnv (loopLocals env0 shape.volume k) "n" k) types0 Hk "n"
      (Runtime.v "steps") stepBody rest k N
      (by simp [counterEnv, CBody.bind])
      ((eval_id_loopEnv env0 shape.volume k Hk "steps" (by decide) (by decide)).trans stepsBound)
      stepBody_noDecl hk
    -- One internal step over the current heap.
    obtain ⟨Dk, readsDk, wDerivDk, inputDk, othersDk, _memberDk, _genDk, stepReach⟩ :=
      internalStepPure_reaches program shape definitions linked library found Hk pool i
        (eulerIterate initial sums k) input (results k) (sums k) count v0
        (counterEnv (loopLocals env0 shape.volume k) "n" k) types0 resultType stack
        (counterStep "n" :: loop "n" (Runtime.v "steps") stepBody :: rest)
        bounded matched
        ((loopEnv_get env0 shape.volume k "m" (by decide) (by decide)).trans mBound)
        ((loopEnv_get env0 shape.volume k "nContinuousStates" (by decide) (by decide)).trans countBound)
        (loopEnv_inner env0 shape.volume k kv0) typedK
        ((resolve_loopEnv env0 shape.volume k "dst" (by decide) (by decide)).trans dstBound)
        ((resolve_loopEnv env0 shape.volume k "src" (by decide) (by decide)).trans srcBound)
        ((resolve_loopEnv env0 shape.volume k "expected" (by decide) (by decide)).trans expBound)
        ((loopEnv_get env0 shape.volume k "rumoca_rhs" (by decide) (by decide)).trans freshRhs)
        stateK inputK wStateK wDerivK (executes k hk) (adds k hk) (resolves Hk) fenv
    -- Increment the outer counter.
    have commute : counterEnv (counterEnv (loopLocals env0 shape.volume k) "n" k) "k" shape.volume =
        counterEnv (loopLocals env0 shape.volume (k + 1)) "n" k :=
      counterEnv_reset_comm (loopLocals env0 shape.volume k) k shape.volume
    have increment := CLoops.counter_step (loopLocals env0 shape.volume (k + 1)) types0
      (written Dk sf (sums k) shape.volume) "n" k (loop "n" (Runtime.v "steps") stepBody :: rest) typedN
      (by omega)
    refine ⟨written Dk sf (sums k) shape.volume, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [eulerIterate_succ] using written_reads Dk sf (sums k)
    · exact reads_written Dk sf jf (sums k) input shape.volume
        (fun a _ b _ => TensorInstance.fields_separate pool i TensorInstance.stateName
          TensorInstance.inputName (by decide +kernel) a b) inputDk
    · exact written_writable Dk sf (sums k) shape.volume (le_refl _)
    · exact writable_written Dk df sf (sums k) shape.volume wDerivDk
        (fun a _ b _ => TensorInstance.fields_separate pool i TensorInstance.derivativeName
          TensorInstance.stateName (by decide +kernel) a b)
    · intro j b m different
      have hframe : written Dk sf (sums k) shape.volume ((TensorInstance.field pool j b).index m) =
          Dk ((TensorInstance.field pool j b).index m) :=
        written_frame Dk sf (sums k) shape.volume ((TensorInstance.field pool j b).index m)
          (fun a _ => Address.instances_separate pool j i different b TensorInstance.stateName m a)
      rw [hframe, othersDk j b m different]; exact othersK j b m different
    · intro pos hpos
      have hpk : pos = k := by omega
      rw [hpk]
      exact reads_written Dk sf df (sums k) (results k) shape.volume
        (fun a _ b _ => TensorInstance.fields_separate pool i TensorInstance.stateName
          TensorInstance.derivativeName (by decide +kernel) a b) readsDk
    · refine reachK.trans (.next (CCalls.Events.body_step program enter resultType stack) ?_)
      refine stepReach.trans ?_
      rw [commute]
      exact .next (CCalls.Events.body_step program increment resultType stack) (.refl _)

end

/-! ### Per-internal-step time advance

The scalar unit-Euler policy advances the instance's independent time base by one
unit per internal step. The tensor time base is the scalar (rank-0) member of the
instance record, so it is a single `double` cell that coincides with the scalar
`p.member "time"` cell (`Address.index_zero`). `timeAdvance` advances it in place:
`m->time = m->time + 1.0;`, reading and writing one cell, with the finite-arithmetic
outcome kept explicit as a `Binary64.Adds` premise, exactly as the elementwise state
update keeps each cell addition explicit. -/

/-- The `(double)1` unit-step literal, the shared C one renderer. -/
def oneExpr : Expr := CAlgorithm.literal .one

/-- The per-internal-step time advance `m->time = m->time + 1.0;`. -/
def timeAdvance : List Stmt := [Runtime.put "time" (.bin .add (Runtime.field "time") oneExpr)]

theorem timeAdvance_closed : timeAdvance.all CBodyEmbedding.closedBlocks = true := by
  simp [timeAdvance, Runtime.put, Runtime.field, Runtime.v, oneExpr, CAlgorithm.literal,
    CBodyEmbedding.closedBlocks, CLoops.noDeclarations]

theorem timeAdvance_noDecl : timeAdvance.all CLoops.noDeclarations = true := by
  simp [timeAdvance, Runtime.put, Runtime.field, Runtime.v, oneExpr, CAlgorithm.literal,
    CLoops.noDeclarations]

section
variable [interface : CInterface]

/-- One time-advance step reads the instance's scalar time cell holding `t` and
writes the finite C sum `t + 1` back into it. The finite-arithmetic outcome is the
explicit premise `adds : Binary64.Adds t 1 (.finite t')`. -/
theorem timeStep (env : Locals) (types : Types) (heap : Heap) (p : Address)
    (t t' : Binary64.Value) (old : Option Value) (rest : List Stmt)
    (double : interface.types "double" = some .float64)
    (mBound : env "m" = some (.pointer (some p)))
    (clock : load heap (p.member "time") = some (.finite t))
    (storage : heap (p.member "time") = some ⟨.float64, true, old⟩)
    (adds : Binary64.Adds t Binary64.one (.finite t')) :
    CLoops.next (.running (timeAdvance ++ rest) env types heap) =
      some (.running rest env types
        (StateProofs.written heap (p.member "time") (toBits t').val)) := by
  have leftEval : CBody.eval env heap (Runtime.field "time") = some (.finite t) := by
    have raw : CBody.eval env heap (Runtime.field "time") = load heap (p.member "time") := by
      simp [Runtime.field, Runtime.v, CBody.eval, CBody.resolve, mBound, Value.address]
    exact raw.trans clock
  have rightEval : CBody.eval env heap oneExpr = some (.finite Binary64.one) :=
    Rumoca.CTensor.Fill.literal_eval .one env heap double
  have rhs : CLoops.eval env types heap (.bin .add (Runtime.field "time") oneExpr) =
      some (.float64 (Binary64.addResult t Binary64.one).encode) :=
    CArithmetic.eval_member_add env types heap (Runtime.v "m") oneExpr "time" true t Binary64.one
      leftEval rightEval
  have encoded : (Binary64.addResult t Binary64.one).encode = (toBits t').val := by
    rw [(Binary64.addResult_correct t Binary64.one (.finite t')).mpr adds]; rfl
  rw [encoded] at rhs
  have address : CBody.lvalue env heap (Runtime.field "time") = some (p.member "time") := by
    simp [Runtime.field, Runtime.v, CBody.lvalue, CBody.eval, CBody.resolve, mBound, Value.address]
  simp only [Runtime.field, Runtime.v] at address rhs
  simp [timeAdvance, Runtime.put, Runtime.field, Runtime.v, CLoops.next, address, rhs,
    Option.bind_some, store_float64 heap _ old _ storage, StateProofs.written]

end

/-- The time-augmented per-internal-step body: advance the instance's time base by
one, then run the declaration-free state step (`stepBody`). Both fragments are
declaration-free, so it is a legal outer-loop body and the whole function stays
closed. -/
def stepBodyT : List Stmt := timeAdvance ++ stepBody

theorem stepBodyT_closed : stepBodyT.all CBodyEmbedding.closedBlocks = true := by
  simp only [stepBodyT, List.all_append, Bool.and_eq_true]
  exact ⟨timeAdvance_closed, stepBody_closed⟩

theorem stepBodyT_noDecl : stepBodyT.all CLoops.noDeclarations = true := by
  simp only [stepBodyT, List.all_append, Bool.and_eq_true]
  exact ⟨timeAdvance_noDecl, stepBody_noDecl⟩

section
variable [interface : CInterface]
variable (program : CCalls.Events.Program E)

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile in
/-- One tensor Co-Simulation internal step from the time-augmented declaration-free
body `stepBodyT` over an arbitrary well-formed instance heap `H`: advance the scalar
time base by one, evaluate the prepared derivative entry into `der(x)`, reset the
inner counter, and advance the state region `x` by `x + dx` elementwise over the
symbolic volume. The reached heap's state region reads the finite Euler sum
`state + result`, its derivative region reads `result`, its time cell reads the
finite sum `t + 1`, the input region and every other instance are preserved, and
the state, derivative and input regions stay readable/writable so the next step's
premises re-establish. `executed`, `adds`, `timeAdds` and `resolves` carry the
finite tensor derivative, the per-cell finite addition, the finite time addition
and the direct helper resolution. -/
theorem internalStepPureT_reaches (shape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (H : Heap) (pool : Address) (i : Nat)
    (state input result sum : Values shape) (t t' : Binary64.Value) (count : UInt64) (v0 : Nat)
    (env : Locals) (types0 : Types) (resultType : String)
    (stack : CCalls.Typed.Continuation) (rest : List Stmt)
    (bounded : shape.volume < 2 ^ 64) (matched : count.toNat = shape.volume)
    (mBound : env "m" = some (.pointer (some (TensorInstance.record pool i))))
    (countBound : env "nContinuousStates" = some (.integer count.toNat))
    (kBound : env "k" = some (.integer v0)) (typedK : types0 "k" = some .size)
    (dstBound : resolve env "dst" =
      some (.pointer (some ((TensorInstance.record pool i).member TensorInstance.stateName))))
    (srcBound : resolve env "src" =
      some (.pointer (some ((TensorInstance.record pool i).member TensorInstance.derivativeName))))
    (expBound : resolve env "expected" = some (.integer shape.volume))
    (freshRhs : env "rumoca_rhs" = none)
    (readsState : Reads H (TensorInstance.field pool i TensorInstance.stateName) state)
    (readsInput : Reads H (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableState : Writable H (TensorInstance.field pool i TensorInstance.stateName) shape.volume)
    (writableDx : Writable H (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume)
    (timeStored : H (TensorInstance.field pool i TensorInstance.timeName) =
      some ⟨.float64, true, some (.finite t)⟩)
    (executed : Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment state input) result)
    (adds : ∀ a : Fin shape.volume, Binary64.Adds state[a] result[a] (.finite sum[a]))
    (timeAdds : Binary64.Adds t Binary64.one (.finite t'))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) Hn .done) w →
      CCalls.Events.Resolves program w) (fenv : TensorFenv interface) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName) sum ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.derivativeName) result ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.inputName) input ∧
      Writable finalHeap (TensorInstance.field pool i TensorInstance.stateName) shape.volume ∧
      Writable finalHeap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume ∧
      finalHeap (TensorInstance.field pool i TensorInstance.timeName) =
        some ⟨.float64, true, some (.finite t')⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          H ((TensorInstance.field pool j b).index k)) ∧
      (∀ q, q.block ≠ (TensorInstance.record pool i).block → finalHeap q = H q) ∧
      (∀ (b : String) (k : Nat), b ≠ TensorInstance.derivativeName → b ≠ TensorInstance.stateName →
        b ≠ TensorInstance.timeName →
        finalHeap ((TensorInstance.field pool i b).index k) = H ((TensorInstance.field pool i b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (stepBodyT ++ rest) env types0 H) resultType stack)
        (.body (.running rest (counterEnv env "k" shape.volume) types0 finalHeap) resultType stack) := by
  have tfield : TensorInstance.field pool i TensorInstance.timeName =
      (TensorInstance.record pool i).member "time" := rfl
  set p := TensorInstance.record pool i with hp
  set H1 := StateProofs.written H (p.member "time") (toBits t').val with hH1
  have clockLoad : load H (p.member "time") = some (.finite t) := by
    rw [← tfield]; simp [load, timeStored, convert, Value.finite]
  have timeTrans : CLoops.next (.running (timeAdvance ++ (stepBody ++ rest)) env types0 H) =
      some (.running (stepBody ++ rest) env types0 H1) :=
    timeStep env types0 H p t t' (some (.finite t)) (stepBody ++ rest) fenv.doubleType
      mBound clockLoad (by rw [← tfield]; exact timeStored) timeAdds
  -- The time cell coincides with the scalar `p.member "time"` cell, separate from
  -- every other tensor member; framing carries the tensor reads/writability across
  -- the time write.
  have time_ne : ∀ (nm : String) (a : Nat), nm ≠ TensorInstance.timeName →
      (TensorInstance.field pool i nm).index a ≠ p.member "time" := by
    intro nm a hnm
    rw [← tfield, show TensorInstance.field pool i TensorInstance.timeName =
      (TensorInstance.field pool i TensorInstance.timeName).index 0 from (Address.index_zero _).symm]
    exact TensorInstance.fields_separate pool i nm TensorInstance.timeName hnm a 0
  have frameH1 : ∀ (nm : String) (a : Nat), nm ≠ TensorInstance.timeName →
      H1 ((TensorInstance.field pool i nm).index a) = H ((TensorInstance.field pool i nm).index a) :=
    fun nm a hnm => StateProofs.written_frame H (p.member "time") _ _ (time_ne nm a hnm)
  have readsStateH1 : Reads H1 (TensorInstance.field pool i TensorInstance.stateName) state := fun a => by
    simp only [load, frameH1 TensorInstance.stateName a.val (by decide)]; exact readsState a
  have readsInputH1 : Reads H1 (TensorInstance.field pool i TensorInstance.inputName) input := fun a => by
    simp only [load, frameH1 TensorInstance.inputName a.val (by decide)]; exact readsInput a
  have writableStateH1 : Writable H1 (TensorInstance.field pool i TensorInstance.stateName) shape.volume :=
    fun a ha => by
      obtain ⟨old, ho⟩ := writableState a ha
      exact ⟨old, by rw [frameH1 TensorInstance.stateName a (by decide)]; exact ho⟩
  have writableDxH1 : Writable H1 (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume :=
    fun a ha => by
      obtain ⟨old, ho⟩ := writableDx a ha
      exact ⟨old, by rw [frameH1 TensorInstance.derivativeName a (by decide)]; exact ho⟩
  -- One internal state step over the time-advanced heap.
  obtain ⟨D, readsD, wDerivD, inputD, othersD, memberD, genD, reachInner⟩ :=
    internalStepPure_reaches program shape definitions linked library found H1 pool i
      state input result sum count v0 env types0 resultType stack rest bounded matched
      mBound countBound kBound typedK dstBound srcBound expBound freshRhs
      readsStateH1 readsInputH1 writableStateH1 writableDxH1 executed adds (resolves H1) fenv
  refine ⟨written D (TensorInstance.field pool i TensorInstance.stateName) sum shape.volume,
    written_reads D _ sum, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact reads_written D _ _ sum result shape.volume
      (fun a _ b _ => TensorInstance.fields_separate pool i TensorInstance.stateName
        TensorInstance.derivativeName (by decide) a b) readsD
  · exact reads_written D _ _ sum input shape.volume
      (fun a _ b _ => TensorInstance.fields_separate pool i TensorInstance.stateName
        TensorInstance.inputName (by decide) a b) inputD
  · exact written_writable D _ sum shape.volume (le_refl _)
  · exact writable_written D _ _ sum shape.volume wDerivD
      (fun a _ b _ => TensorInstance.fields_separate pool i TensorInstance.derivativeName
        TensorInstance.stateName (by decide) a b)
  · -- time cell advanced to `t + 1`
    have frameTime : written D (TensorInstance.field pool i TensorInstance.stateName) sum shape.volume
        (p.member "time") = D (p.member "time") :=
      written_frame D _ sum shape.volume (p.member "time")
        (fun a _ => (time_ne TensorInstance.stateName a (by decide)).symm)
    have memberTime : D (p.member "time") = H1 (p.member "time") := by
      have h := memberD TensorInstance.timeName 0 (by decide)
      rw [Address.index_zero, tfield] at h; exact h
    have h1Time : H1 (p.member "time") = some ⟨.float64, true, some (.finite t')⟩ := by
      rw [hH1, StateProofs.written]; simp [replace, Value.finite]
    rw [tfield, frameTime, memberTime, h1Time]
  · -- other instances preserved
    intro j b k different
    have frameOther : written D (TensorInstance.field pool i TensorInstance.stateName) sum shape.volume
        ((TensorInstance.field pool j b).index k) = D ((TensorInstance.field pool j b).index k) :=
      written_frame D _ sum shape.volume ((TensorInstance.field pool j b).index k)
        (fun a _ => Address.instances_separate pool j i different b TensorInstance.stateName k a)
    have otherH1 : H1 ((TensorInstance.field pool j b).index k) =
        H ((TensorInstance.field pool j b).index k) := by
      apply StateProofs.written_frame
      rw [← tfield, show TensorInstance.field pool i TensorInstance.timeName =
        (TensorInstance.field pool i TensorInstance.timeName).index 0 from (Address.index_zero _).symm]
      exact Address.instances_separate pool j i different b TensorInstance.timeName k 0
    rw [frameOther, othersD j b k different, otherH1]
  · -- any cell outside the instance record is preserved (used to frame caller buffers)
    intro q hq
    have qneTime : q ≠ p.member "time" := by
      intro same
      have hb : (p.member "time").block = p.block := rfl
      exact hq ((congrArg Address.block same).trans hb)
    have h1frame : H1 q = H q := by
      rw [hH1]; exact StateProofs.written_frame H (p.member "time") q (toBits t').val qneTime
    exact (genD q hq).trans h1frame
  · -- an instance member other than der(x), the state or the time base is preserved
    -- (used to frame the output region across the internal step)
    intro b k hbd hbs hbt
    rw [written_frame D (TensorInstance.field pool i TensorInstance.stateName) sum shape.volume
        ((TensorInstance.field pool i b).index k)
        (fun a _ => TensorInstance.fields_separate pool i b TensorInstance.stateName hbs k a),
      memberD b k hbd, frameH1 b k hbt]
  · -- the observable-machine execution
    have assoc : stepBodyT ++ rest = timeAdvance ++ (stepBody ++ rest) := by
      simp [stepBodyT, List.append_assoc]
    rw [assoc]
    exact .next (CCalls.Events.body_step program timeTrans resultType stack) reachInner

end

/-! ### The N-step Co-Simulation grid loop with time advance

`stepLoopT_reaches` iterates the time-augmented internal step `stepBodyT` `N` times
inside the outer counted loop `loop "n" steps stepBodyT`, by induction on the number
of completed steps. Alongside the state region (which advances by the `N`-fold finite
Euler step `eulerIterate initial sums`), the instance's scalar time base advances by
one unit per step, so after `N` steps it reads the finite time sum `times N`, where
`times 0` is the initial time and each `times (n+1)` is the finite C sum of `times n`
and one (the explicit per-step premise `timeAdds`). The derivative region reads the
last result, the input region and every cell of every other instance are preserved,
and the state, derivative and time cells stay readable/writable throughout. -/
section
variable [interface : CInterface]
variable (program : CCalls.Events.Program E)

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile in
theorem stepLoopT_reaches (shape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (H0 : Heap) (pool : Address) (i : Nat) (initial input : Values shape)
    (results sums : Nat → Values shape) (times : Nat → Binary64.Value) (count : UInt64) (N : Nat)
    (env0 : Locals) (types0 : Types) (resultType : String)
    (stack : CCalls.Typed.Continuation) (rest : List Stmt)
    (bounded : shape.volume < 2 ^ 64) (matched : count.toNat = shape.volume) (nBound : N < 2 ^ 64)
    (mBound : env0 "m" = some (.pointer (some (TensorInstance.record pool i))))
    (countBound : env0 "nContinuousStates" = some (.integer count.toNat))
    (typedK : types0 "k" = some .size) (typedN : types0 "n" = some .size)
    (kInit : env0 "k" = some (.integer 0))
    (dstBound : CBody.resolve env0 "dst" =
      some (.pointer (some ((TensorInstance.record pool i).member TensorInstance.stateName))))
    (srcBound : CBody.resolve env0 "src" =
      some (.pointer (some ((TensorInstance.record pool i).member TensorInstance.derivativeName))))
    (expBound : CBody.resolve env0 "expected" = some (.integer shape.volume))
    (stepsBound : CBody.resolve env0 "steps" = some (.integer N))
    (freshRhs : env0 "rumoca_rhs" = none)
    (readsState0 : Reads H0 (TensorInstance.field pool i TensorInstance.stateName) initial)
    (readsInput0 : Reads H0 (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableState0 : Writable H0 (TensorInstance.field pool i TensorInstance.stateName) shape.volume)
    (writableDeriv0 : Writable H0 (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume)
    (timeInit0 : H0 (TensorInstance.field pool i TensorInstance.timeName) =
      some ⟨.float64, true, some (.finite (times 0))⟩)
    (executes : ∀ n < N, Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment (eulerIterate initial sums n) input) (results n))
    (adds : ∀ n < N, ∀ a : Fin shape.volume,
      Binary64.Adds (eulerIterate initial sums n)[a] (results n)[a] (.finite (sums n)[a]))
    (timeAdds : ∀ n < N, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1))))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) Hn .done) w →
      CCalls.Events.Resolves program w) (fenv : TensorFenv interface) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName) (eulerIterate initial sums N) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.inputName) input ∧
      Writable finalHeap (TensorInstance.field pool i TensorInstance.stateName) shape.volume ∧
      Writable finalHeap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume ∧
      finalHeap (TensorInstance.field pool i TensorInstance.timeName) =
        some ⟨.float64, true, some (.finite (times N))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = H0 ((TensorInstance.field pool j b).index k)) ∧
      (∀ pos, N = pos + 1 →
        Reads finalHeap (TensorInstance.field pool i TensorInstance.derivativeName) (results pos)) ∧
      (∀ q, q.block ≠ (TensorInstance.record pool i).block → finalHeap q = H0 q) ∧
      (∀ (b : String) (k : Nat), b ≠ TensorInstance.derivativeName → b ≠ TensorInstance.stateName →
        b ≠ TensorInstance.timeName →
        finalHeap ((TensorInstance.field pool i b).index k) = H0 ((TensorInstance.field pool i b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (loop "n" (Runtime.v "steps") stepBodyT :: rest)
          (counterEnv env0 "n" 0) types0 H0) resultType stack)
        (.body (.running rest (counterEnv (loopLocals env0 shape.volume N) "n" N) types0 finalHeap)
          resultType stack) := by
  set sf := TensorInstance.field pool i TensorInstance.stateName with hsf
  set df := TensorInstance.field pool i TensorInstance.derivativeName with hdf
  set jf := TensorInstance.field pool i TensorInstance.inputName with hjf
  set tf := TensorInstance.field pool i TensorInstance.timeName with htf
  suffices key : ∀ k, k ≤ N → ∃ Hk,
      Reads Hk sf (eulerIterate initial sums k) ∧
      Reads Hk jf input ∧
      Writable Hk sf shape.volume ∧ Writable Hk df shape.volume ∧
      Hk tf = some ⟨.float64, true, some (.finite (times k))⟩ ∧
      (∀ (j : Nat) (b : String) (m : Nat), j ≠ i →
        Hk ((TensorInstance.field pool j b).index m) = H0 ((TensorInstance.field pool j b).index m)) ∧
      (∀ pos, k = pos + 1 → Reads Hk df (results pos)) ∧
      (∀ q, q.block ≠ (TensorInstance.record pool i).block → Hk q = H0 q) ∧
      (∀ (b : String) (m : Nat), b ≠ TensorInstance.derivativeName → b ≠ TensorInstance.stateName →
        b ≠ TensorInstance.timeName →
        Hk ((TensorInstance.field pool i b).index m) = H0 ((TensorInstance.field pool i b).index m)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (loop "n" (Runtime.v "steps") stepBodyT :: rest)
          (counterEnv env0 "n" 0) types0 H0) resultType stack)
        (.body (.running (loop "n" (Runtime.v "steps") stepBodyT :: rest)
          (counterEnv (loopLocals env0 shape.volume k) "n" k) types0 Hk) resultType stack) by
    obtain ⟨HN, stateN, inputN, wStateN, wDerivN, timeN, othersN, derivN, genN, outputN, reachN⟩ :=
      key N (le_refl N)
    have stop := CLoops.loop_stop (counterEnv (loopLocals env0 shape.volume N) "n" N) types0 HN "n"
      (Runtime.v "steps") stepBodyT rest N (by simp [counterEnv, CBody.bind])
      ((eval_id_loopEnv env0 shape.volume N HN "steps" (by decide) (by decide)).trans stepsBound)
      stepBodyT_noDecl
    exact ⟨HN, stateN, inputN, wStateN, wDerivN, timeN, othersN, derivN, genN, outputN,
      reachN.trans (.next (CCalls.Events.body_step program stop resultType stack) (.refl _))⟩
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨H0, ?_, readsInput0, writableState0, writableDeriv0, timeInit0, fun _ _ _ _ => rfl, ?_,
      fun _ _ => rfl, fun _ _ _ _ _ => rfl, ?_⟩
    · exact readsState0
    · intro pos hpos; exact absurd hpos.symm (Nat.succ_ne_zero pos)
    · exact .refl _
  | succ k ih =>
    intro hk1
    have hk : k < N := Nat.lt_of_succ_le hk1
    obtain ⟨Hk, stateK, inputK, wStateK, wDerivK, timeK, othersK, _derivK, genK, outputK, reachK⟩ :=
      ih (le_of_lt hk)
    obtain ⟨v0, kv0⟩ := loopLocals_counter env0 shape.volume kInit k
    have enter := CLoops.loop_enter (counterEnv (loopLocals env0 shape.volume k) "n" k) types0 Hk "n"
      (Runtime.v "steps") stepBodyT rest k N
      (by simp [counterEnv, CBody.bind])
      ((eval_id_loopEnv env0 shape.volume k Hk "steps" (by decide) (by decide)).trans stepsBound)
      stepBodyT_noDecl hk
    obtain ⟨Dk, sumDk, derivDk, inputDk, wStateDk, wDerivDk, timeDk, othersDk, genDk, outputDk, stepReach⟩ :=
      internalStepPureT_reaches program shape definitions linked library found Hk pool i
        (eulerIterate initial sums k) input (results k) (sums k) (times k) (times (k + 1)) count v0
        (counterEnv (loopLocals env0 shape.volume k) "n" k) types0 resultType stack
        (counterStep "n" :: loop "n" (Runtime.v "steps") stepBodyT :: rest)
        bounded matched
        ((loopEnv_get env0 shape.volume k "m" (by decide) (by decide)).trans mBound)
        ((loopEnv_get env0 shape.volume k "nContinuousStates" (by decide) (by decide)).trans countBound)
        (loopEnv_inner env0 shape.volume k kv0) typedK
        ((resolve_loopEnv env0 shape.volume k "dst" (by decide) (by decide)).trans dstBound)
        ((resolve_loopEnv env0 shape.volume k "src" (by decide) (by decide)).trans srcBound)
        ((resolve_loopEnv env0 shape.volume k "expected" (by decide) (by decide)).trans expBound)
        ((loopEnv_get env0 shape.volume k "rumoca_rhs" (by decide) (by decide)).trans freshRhs)
        stateK inputK wStateK wDerivK timeK (executes k hk) (adds k hk) (timeAdds k hk) resolves fenv
    have commute : counterEnv (counterEnv (loopLocals env0 shape.volume k) "n" k) "k" shape.volume =
        counterEnv (loopLocals env0 shape.volume (k + 1)) "n" k :=
      counterEnv_reset_comm (loopLocals env0 shape.volume k) k shape.volume
    have increment := CLoops.counter_step (loopLocals env0 shape.volume (k + 1)) types0
      Dk "n" k (loop "n" (Runtime.v "steps") stepBodyT :: rest) typedN (by omega)
    refine ⟨Dk, ?_, inputDk, wStateDk, wDerivDk, timeDk, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [eulerIterate_succ] using sumDk
    · intro j b m different
      rw [othersDk j b m different]; exact othersK j b m different
    · intro pos hpos
      have hpk : pos = k := by omega
      rw [hpk]; exact derivDk
    · intro q hq
      exact (genDk q hq).trans (genK q hq)
    · intro b m hbd hbs hbt
      rw [outputDk b m hbd hbs hbt]; exact outputK b m hbd hbs hbt
    · refine reachK.trans (.next (CCalls.Events.body_step program enter resultType stack) ?_)
      refine stepReach.trans ?_
      rw [commute]
      exact .next (CCalls.Events.body_step program increment resultType stack) (.refl _)

end


/-! ### The guarded tensor `fmi3DoStep` body

The complete guarded function wraps the outer grid loop with the handle and
lifecycle guard, the scalar argument classification, and the rounding and
grid-policy checks. The guard prefix is the model-independent scalar prefix of
`Runtime.doStep` (handle/lifecycle guard, the output-pointer check and writes, the
invalid communication-point/step rejection, `stepRounding`, `stepClock`,
`stepGrid`), reused verbatim: the tensor instance record carries the scalar
metadata cells (`kind`, `mode`, `stopDefined`, `stop`) and its scalar time base
coincides with the `p.member "time"` cell those guards read, so those checks apply
unchanged. A communication step that is off the unit grid or over the bound reaches
`fmi3Discard` without advancing (the shared `Runtime.stepDiscard`). Only the final
numerical section is model dependent: instead of the scalar `model_advance` call it
declares the state/derivative pointers, the element count `expected`, the internal
step count `steps` and both loop counters once at function scope, runs the outer
grid loop `loop "n" steps stepBodyT` (each time-augmented internal step advances the
state elementwise and the time base by one), writes the advanced time base to
`lastSuccessfulTime`, and returns `fmi3OK`. Every loop body is declaration-free, so
`CBodyEmbedding.closedBlocks` holds for the whole function. -/

/-- The `fmi3DoStep` ABI signature (shared with the scalar adapter). -/
def signature : Signature := ⟨"fmi3Status", "fmi3DoStep",
  [⟨"fmi3Instance", "instance", false⟩,
   ⟨"fmi3Float64", "currentCommunicationPoint", false⟩,
   ⟨"fmi3Float64", "communicationStepSize", false⟩,
   ⟨"fmi3Boolean", "noSetFMUStatePriorToCurrentPoint", false⟩,
   ⟨"fmi3Boolean *", "eventHandlingNeeded", false⟩,
   ⟨"fmi3Boolean *", "terminateSimulation", false⟩,
   ⟨"fmi3Boolean *", "earlyReturn", false⟩,
   ⟨"fmi3Float64 *", "lastSuccessfulTime", false⟩]⟩

/-- The publish/return suffix of the numerical tail: publish the advanced time base
to `*lastSuccessfulTime` and return `fmi3OK`. Shared by both the output-free and the
output-aware tail. -/
def stepPublishTail : List Stmt :=
  Runtime.out "lastSuccessfulTime" (Runtime.field "time") ::
  [Runtime.ok]

/-- The tail after the outer grid loop. When the prepared problem exposes a dense
observation, the prepared square-Jacobian diagonal entry `rumoca_square_jacobian_diag`
runs once (writing `J = diag(2*u)` from the instance's current input region) before the
time publication; otherwise the publication runs directly. -/
def jacobianTail (shape : Tensor.Shape) : Bool → List Stmt
  | false => stepPublishTail
  | true => TensorContinuousStates.jacobianCall shape :: stepPublishTail

/-- The model-dependent numerical tail of the tensor `fmi3DoStep`: hoist the
state/derivative pointers, element count, step count and loop counters to function
scope, run the outer grid loop, (when the record carries the dense observation) run the
prepared square-Jacobian diagonal entry, publish the advanced time and return `fmi3OK`.
The output-free tail (`hasOutput = false`) is definitionally the loop followed by the
publish/return suffix. -/
def tensorStepSolve (shape : Tensor.Shape) (hasOutput : Bool) : List Stmt :=
  .declare "fmi3Float64 *" "dst" ((Runtime.region TensorInstance.stateName)) ::
  .declare "fmi3Float64 *" "src" ((Runtime.region TensorInstance.derivativeName)) ::
  .declare "size_t" "nContinuousStates" (Runtime.n shape.volume) ::
  .declare "size_t" "expected" (Runtime.n shape.volume) ::
  .declare "size_t" "steps" (.cast "size_t" (Runtime.v "communicationStepSize")) ::
  .declare "size_t" "k" (Runtime.n 0) ::
  .declare "size_t" "n" (Runtime.n 0) ::
  loop "n" (Runtime.v "steps") stepBodyT ::
  jacobianTail shape hasOutput

/-- The complete guarded tensor `fmi3DoStep` body: the model-independent scalar
guard prefix of `Runtime.doStep` followed by the tensor numerical tail. -/
def doStepBody (shape : Tensor.Shape) (hasOutput : Bool) : List Stmt :=
  Runtime.require .doStep ++
  [Runtime.pointerCheck ["eventHandlingNeeded", "terminateSimulation", "earlyReturn", "lastSuccessfulTime"],
   Runtime.out "eventHandlingNeeded" (Runtime.n 0), Runtime.out "terminateSimulation" (Runtime.n 0),
   Runtime.out "earlyReturn" (Runtime.n 0), Runtime.out "lastSuccessfulTime" (Runtime.field "time"),
   Runtime.reject (Runtime.any [Runtime.negate (Runtime.finite (Runtime.v "currentCommunicationPoint")),
     Runtime.negate (Runtime.finite (Runtime.v "communicationStepSize")),
     Runtime.nev (Runtime.v "currentCommunicationPoint") (Runtime.field "time"),
     Runtime.le (Runtime.v "communicationStepSize") (Runtime.n 0)])
     "Invalid communication point or step size"] ++
  Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape hasOutput

/-- The tensor `fmi3DoStep` function over the shared `fmi3DoStep` signature. -/
def function (shape : Tensor.Shape) (hasOutput : Bool) : CTree.Function :=
  ⟨signature, doStepBody shape hasOutput, false⟩

/-- The guard prefix of the tensor body is exactly the model-independent scalar
prefix of `Runtime.doStep` (the 16 statements up to and including `stepGrid`); only
the trailing numerical section differs. -/
theorem doStepBody_prefix (shape : Tensor.Shape) (hasOutput : Bool) :
    doStepBody shape hasOutput = Runtime.doStep.take 16 ++ tensorStepSolve shape hasOutput := rfl

/-- The outer grid-loop statement is a legal closed block: its body `stepBodyT`
(with the loop counter step) introduces no declarations. -/
theorem outerLoop_closed :
    CBodyEmbedding.closedBlocks (loop "n" (Runtime.v "steps") stepBodyT) = true := by
  simp only [CLoops.loop, CBodyEmbedding.closedBlocks, List.all_append, Bool.and_eq_true]
  exact ⟨stepBodyT_noDecl, by simp [CLoops.counterStep, CLoops.noDeclarations]⟩

theorem doStepBody_closed (shape : Tensor.Shape) (hasOutput : Bool) :
    (doStepBody shape hasOutput).all CBodyEmbedding.closedBlocks = true := by
  cases hasOutput <;>
    simp [doStepBody, tensorStepSolve, jacobianTail, stepPublishTail, TensorContinuousStates.jacobianCall,
      TensorContinuousStates.jacobianEntryArgs, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
      Runtime.reject, Runtime.branch, Runtime.pointerCheck, Runtime.out, Runtime.stepRounding,
      Runtime.stepClock, Runtime.stepGrid, Runtime.stepDiscard, Runtime.log, Runtime.fail, Runtime.ret,
      Runtime.ok, Runtime.call, Runtime.region, Runtime.field, Runtime.v, Runtime.n, Runtime.any, Runtime.negate,
      Runtime.finite, Runtime.nev, Runtime.le, Runtime.both, Runtime.either, Runtime.put,
      CBodyEmbedding.closedBlocks, CLoops.noDeclarations, CLoops.loop, CLoops.counterStep,
      List.all_append, stepBodyT_noDecl]

/-! ### The model-dependent numerical tail as one observable execution

`tensorSolve_reaches` runs the model-dependent tail `tensorStepSolve` from the
post-guard state: it declares the state/derivative pointers, the element count
`nContinuousStates`/`expected`, the internal step count `steps` (the `size_t` cast
of the admitted communication step, so it equals the admitted count), and both loop
counters; runs the outer grid loop `loop "n" steps stepBodyT` via `stepLoopT_reaches`
(advancing the state region by the N-fold finite Euler step and the time base to the
N-fold finite sum); writes the advanced time base to `*lastSuccessfulTime`; and
returns `fmi3OK`. The reached heap's state region reads `eulerIterate initial sums N`,
its time cell and the caller's `lastSuccessfulTime` both read `times N`, and every
cell of every other instance is preserved. Universal in the tensor shape, the
instance index, the heap and the saved caller. -/
section
variable [interface : CInterface]
variable (program : CCalls.Events.Program E)

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile in
theorem tensorSolve_reaches (shape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (H : Heap) (pool : Address) (i : Nat) (initial input : Values shape)
    (results sums : Nat → Values shape) (times : Nat → Binary64.Value)
    (count : UInt64) (duration : CStatements.Counter) (step : Binary64.Value)
    (env : Locals) (types0 : Types) (stack : CCalls.Typed.Continuation)
    (buffers : StepEntry.Buffers) (oldLast : Option Value)
    (bounded : shape.volume < 2 ^ 64) (matched : count.toNat = shape.volume)
    (mBound : env "m" = some (.pointer (some (TensorInstance.record pool i))))
    (stepValue : env "communicationStepSize" = some (.finite step))
    (stepCast : convert .size (.finite step) = some (.integer duration.val))
    (lastValue : env "lastSuccessfulTime" = some (.pointer (some buffers.last)))
    (freshDst : env "dst" = none) (freshSrc : env "src" = none)
    (freshCount : env "nContinuousStates" = none) (freshExpected : env "expected" = none)
    (freshSteps : env "steps" = none) (freshK : env "k" = none) (freshN : env "n" = none)
    (freshRhs : env "rumoca_rhs" = none) (freshOK : env "fmi3OK" = none)
    (readsState : Reads H (TensorInstance.field pool i TensorInstance.stateName) initial)
    (readsInput : Reads H (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableState : Writable H (TensorInstance.field pool i TensorInstance.stateName) shape.volume)
    (writableDeriv : Writable H (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume)
    (timeInit : H (TensorInstance.field pool i TensorInstance.timeName) =
      some ⟨.float64, true, some (.finite (times 0))⟩)
    (lastCell : H buffers.last = some ⟨.float64, true, oldLast⟩)
    (lastOutside : ∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block)
    (executes : ∀ n, Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment (eulerIterate initial sums n) input) (results n))
    (adds : ∀ n, ∀ a : Fin shape.volume,
      Binary64.Adds (eulerIterate initial sums n)[a] (results n)[a] (.finite (sums n)[a]))
    (timeAdds : ∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1))))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) Hn .done) w →
      CCalls.Events.Resolves program w) (fenv : TensorFenv interface) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName)
        (eulerIterate initial sums duration.val) ∧
      finalHeap (TensorInstance.field pool i TensorInstance.timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = H ((TensorInstance.field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (tensorStepSolve shape false) env types0 H) "fmi3Status" stack)
        (.returning (.integer 0) finalHeap stack) := by
  set p := TensorInstance.record pool i with hp
  set sf := TensorInstance.field pool i TensorInstance.stateName with hsf
  set df := TensorInstance.field pool i TensorInstance.derivativeName with hdf
  set tf := TensorInstance.field pool i TensorInstance.timeName with htf
  -- The hoisted-declaration environments and types, threaded through the seven
  -- function-scope declarations of `tensorStepSolve`.
  set env1 := bind env "dst" (.pointer (some (p.member TensorInstance.stateName))) with henv1
  set types1 := bindType types0 "dst" .pointer with htypes1
  have m1 : env1 "m" = some (.pointer (some p)) := by simp [henv1, CBody.bind, mBound]
  set env2 := bind env1 "src" (.pointer (some (p.member TensorInstance.derivativeName))) with henv2
  set types2 := bindType types1 "src" .pointer with htypes2
  set env3 := bind env2 "nContinuousStates" (.integer shape.volume) with henv3
  set types3 := bindType types2 "nContinuousStates" .size with htypes3
  set env4 := bind env3 "expected" (.integer shape.volume) with henv4
  set types4 := bindType types3 "expected" .size with htypes4
  have stepEval : CLoops.eval env4 types4 H (.cast "size_t" (Runtime.v "communicationStepSize")) =
      some (.integer duration.val) := by
    have base : CBody.resolve env4 "communicationStepSize" = some (.finite step) := by
      simp [CBody.resolve, henv4, henv3, henv2, henv1, CBody.bind, stepValue]
    simp [CLoops.eval, CBody.eval, base, CBody.expressionCast, Runtime.v, CBody.zeroLiteral,
      CBody.cast, stepCast, fenv.sizeType]
  set env5 := bind env4 "steps" (.integer duration.val) with henv5
  set types5 := bindType types4 "steps" .size with htypes5
  have freshK5 : env5 "k" = none := by simp [henv5, henv4, henv3, henv2, henv1, CBody.bind, freshK]
  set env6 := counterEnv env5 "k" 0 with henv6
  set types6 := bindType types5 "k" .size with htypes6
  have freshN6 : env6 "n" = none := by simp [henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, freshN]
  set types7 := bindType types6 "n" .size with htypes7
  -- The seven declaration steps as one observable-machine reach; each declaration's
  -- statement tail unifies with the shared function body.
  have declReach : Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (tensorStepSolve shape false) env types0 H) "fmi3Status" stack)
      (.body (.running (loop "n" (Runtime.v "steps") stepBodyT ::
        Runtime.out "lastSuccessfulTime" (Runtime.field "time") :: [Runtime.ok])
        (counterEnv env6 "n" 0) types7 H) "fmi3Status" stack) := by
    refine .next (CCalls.Events.body_step program
      (TensorFloat64.declare_step_e env types0 H "fmi3Float64 *" "dst"
        ((Runtime.region TensorInstance.stateName)) .pointer
        (.pointer (some (p.member TensorInstance.stateName))) _ _ freshDst fenv.floatPointerType
        (by apply CBodyEmbedding.eval_refines
            simp [Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.lvalue, CBody.resolve, mBound, Value.address]) rfl)
      "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (TensorFloat64.declare_step_e env1 types1 H "fmi3Float64 *" "src"
          ((Runtime.region TensorInstance.derivativeName)) .pointer
          (.pointer (some (p.member TensorInstance.derivativeName))) _ _
          (by simp [henv1, CBody.bind, freshSrc]) fenv.floatPointerType
          (by apply CBodyEmbedding.eval_refines
              simp [Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.lvalue, CBody.resolve, m1, Value.address]) rfl)
        "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (TensorFloat64.declare_step_e env2 types2 H "size_t" "nContinuousStates"
          (Runtime.n shape.volume) .size (.integer shape.volume) _ _
          (by simp [henv2, henv1, CBody.bind, freshCount]) fenv.sizeType
          (by simp [Runtime.n, CLoops.eval, CBody.eval]) (CLoops.convert_size_nat _ bounded))
        "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (TensorFloat64.declare_step_e env3 types3 H "size_t" "expected"
          (Runtime.n shape.volume) .size (.integer shape.volume) _ _
          (by simp [henv3, henv2, henv1, CBody.bind, freshExpected]) fenv.sizeType
          (by simp [Runtime.n, CLoops.eval, CBody.eval]) (CLoops.convert_size_nat _ bounded))
        "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (TensorFloat64.declare_step_e env4 types4 H "size_t" "steps"
          (.cast "size_t" (Runtime.v "communicationStepSize")) .size (.integer duration.val) _ _
          (by simp [henv4, henv3, henv2, henv1, CBody.bind, freshSteps]) fenv.sizeType stepEval
          (CLoops.convert_size_nat _ duration.isLt))
        "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (CLoops.counter_initialize env5 types5 H "k" _ freshK5 fenv.sizeType) "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (CLoops.counter_initialize env6 types6 H "n" _ freshN6 fenv.sizeType) "fmi3Status" stack)
        (.refl _)))))))
  -- The loop's entry environment `env6` carries every prepared binding.
  have kInit6 : env6 "k" = some (.integer 0) := by simp [henv6, counterEnv, CBody.bind]
  have mBound6 : env6 "m" = some (.pointer (some p)) := by
    simp [henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, mBound]
  have countBound6 : env6 "nContinuousStates" = some (.integer count.toNat) := by
    simp [henv6, henv5, henv4, henv3, counterEnv, CBody.bind, matched]
  have dstBound6 : CBody.resolve env6 "dst" =
      some (.pointer (some (p.member TensorInstance.stateName))) := by
    simp [henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, CBody.resolve]
  have srcBound6 : CBody.resolve env6 "src" =
      some (.pointer (some (p.member TensorInstance.derivativeName))) := by
    simp [henv6, henv5, henv4, henv3, henv2, counterEnv, CBody.bind, CBody.resolve]
  have expBound6 : CBody.resolve env6 "expected" = some (.integer shape.volume) := by
    simp [henv6, henv5, henv4, counterEnv, CBody.bind, CBody.resolve]
  have stepsBound6 : CBody.resolve env6 "steps" = some (.integer duration.val) := by
    simp [henv6, henv5, counterEnv, CBody.bind, CBody.resolve]
  have freshRhs6 : env6 "rumoca_rhs" = none := by
    simp [henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, freshRhs]
  have typedK7 : types7 "k" = some .size := by simp [htypes7, htypes6, CLoops.bindType]
  have typedN7 : types7 "n" = some .size := by simp [htypes7, CLoops.bindType]
  have nBoundD : duration.val < 2 ^ 64 := duration.isLt
  -- The outer grid loop.
  obtain ⟨loopHeap, stateN, inputN, wStateN, wDerivN, timeN, othersN, _derivN, genN, _outputN, loopReach⟩ :=
    stepLoopT_reaches program shape definitions linked library found H pool i initial input results sums times
      count duration.val env6 types7 "fmi3Status" stack
      (Runtime.out "lastSuccessfulTime" (Runtime.field "time") :: [Runtime.ok])
      bounded matched nBoundD mBound6 countBound6 typedK7 typedN7 kInit6 dstBound6 srcBound6 expBound6
      stepsBound6 freshRhs6 readsState readsInput writableState writableDeriv timeInit
      (fun n _ => executes n) (fun n _ => adds n) (fun n _ => timeAdds n) resolves fenv
  -- The environment at the `out`/`ok` tail.
  set tailEnv := counterEnv (loopLocals env6 shape.volume duration.val) "n" duration.val with htailEnv
  have mTail : tailEnv "m" = some (.pointer (some p)) := by
    simpa only [htailEnv] using (loopEnv_get env6 shape.volume duration.val "m" (by decide) (by decide)).trans mBound6
  have lastTail : CBody.resolve tailEnv "lastSuccessfulTime" = some (.pointer (some buffers.last)) := by
    have base : CBody.resolve env6 "lastSuccessfulTime" = some (.pointer (some buffers.last)) := by
      simp [CBody.resolve, henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, lastValue]
    simpa only [htailEnv] using
      (resolve_loopEnv env6 shape.volume duration.val "lastSuccessfulTime" (by decide) (by decide)).trans base
  have okTail : tailEnv "fmi3OK" = none := by
    have base : env6 "fmi3OK" = none := by
      simp [henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, freshOK]
    simpa only [htailEnv] using
      (loopEnv_get env6 shape.volume duration.val "fmi3OK" (by decide) (by decide)).trans base
  -- The instance's scalar time cell coincides with `p.member "time"`.
  have tfield : tf = p.member "time" := rfl
  have timeMember : loopHeap (p.member "time") = some ⟨.float64, true, some (.finite (times duration.val))⟩ := by
    rw [← tfield]; exact timeN
  have timeLoad : load loopHeap (p.member "time") = some (.finite (times duration.val)) := by
    simp [load, timeMember, convert, Value.finite]
  -- `buffers.last` lies outside the instance record and is preserved by the loop.
  have lastBlock : buffers.last.block ≠ (TensorInstance.record pool i).block := lastOutside i
  have lastNe : buffers.last ≠ p.member "time" := by
    intro same
    have hb : (p.member "time").block = p.block := rfl
    exact lastBlock ((congrArg Address.block same).trans hb)
  have lastLoop : loopHeap buffers.last = some ⟨.float64, true, oldLast⟩ := by
    rw [genN buffers.last lastBlock]; exact lastCell
  set finalHeap := StateProofs.written loopHeap buffers.last (toBits (times duration.val)).val with hfinal
  -- The `out lastSuccessfulTime` store step: publish the advanced time base.
  have outStep : CLoops.next (.running (Runtime.out "lastSuccessfulTime" (Runtime.field "time") :: [Runtime.ok])
      tailEnv types7 loopHeap) = some (.running [Runtime.ok] tailEnv types7 finalHeap) := by
    have leftEval : CLoops.eval tailEnv types7 loopHeap (Runtime.field "time") =
        some (.finite (times duration.val)) := by
      show CBody.eval tailEnv loopHeap (Runtime.field "time") = some (.finite (times duration.val))
      have raw : CBody.eval tailEnv loopHeap (Runtime.field "time") = load loopHeap (p.member "time") := by
        simp [Runtime.field, Runtime.v, CBody.eval, CBody.resolve, mTail, Value.address]
      rw [raw]; exact timeLoad
    have addr : CBody.lvalue tailEnv loopHeap (.deref (Runtime.v "lastSuccessfulTime")) = some buffers.last := by
      simp [CBody.lvalue, Runtime.v, CBody.eval, lastTail, Value.address]
    simp [Runtime.out, CLoops.next, leftEval, addr, Value.finite,
      store_float64 loopHeap buffers.last oldLast _ lastLoop, hfinal, StateProofs.written]
  have okReach := finishOK program finalHeap tailEnv types7 stack okTail fenv.statusType fenv.fmi3OK
  refine ⟨finalHeap, ?_, ?_, ?_, ?_, ?_⟩
  · -- state region reads the N-fold Euler iterate
    intro a
    have ne : sf.index a.val ≠ buffers.last :=
      (cell_block_ne pool i TensorInstance.stateName a.val buffers.last lastBlock).symm
    have frame : finalHeap (sf.index a.val) = loopHeap (sf.index a.val) := by
      rw [hfinal]; exact StateProofs.written_frame loopHeap buffers.last _ _ ne
    simp only [load, frame]; exact stateN a
  · -- the instance time cell advanced to `times N`
    have frame : finalHeap tf = loopHeap tf := by
      rw [hfinal]
      exact StateProofs.written_frame loopHeap buffers.last tf (toBits (times duration.val)).val
        (fun h => lastNe h.symm)
    rw [frame]; exact timeN
  · -- the caller's `lastSuccessfulTime` reads the advanced time base
    rw [hfinal, StateProofs.written]; simp [replace, Value.finite]
  · -- every other instance preserved
    intro j b k different
    have ne : (TensorInstance.field pool j b).index k ≠ buffers.last :=
      (cell_block_ne pool j b k buffers.last (lastOutside j)).symm
    have frame : finalHeap ((TensorInstance.field pool j b).index k) =
        loopHeap ((TensorInstance.field pool j b).index k) := by
      rw [hfinal]; exact StateProofs.written_frame loopHeap buffers.last _ _ ne
    rw [frame]; exact othersN j b k different
  · -- the observable-machine execution: declarations, loop, publish, return
    exact declReach.trans
      (loopReach.trans (.next (CCalls.Events.body_step program outStep "fmi3Status" stack) okReach))

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile Rumoca.CTensor in
/-- The model-dependent numerical tail of the output-aware tensor `fmi3DoStep`: the
seven function-scope declarations, the outer grid loop, then the prepared
square-Jacobian diagonal entry `rumoca_square_jacobian_diag` (writing `J = diag(2*u)`
from the instance's current input region), then the advanced-time publication and the
`fmi3OK` return. Alongside the output-free conclusion it delivers the dense Jacobian
`diag(2*u)` into the instance's `J` region. -/
theorem tensorSolveOutput_reaches (shape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (jacFound : definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function)
    (H : Heap) (pool : Address) (i : Nat) (initial input : Values shape)
    (results sums : Nat → Values shape) (times : Nat → Binary64.Value)
    (count : UInt64) (duration : CStatements.Counter) (step : Binary64.Value)
    (env : Locals) (types0 : Types) (stack : CCalls.Typed.Continuation)
    (buffers : StepEntry.Buffers) (oldLast : Option Value)
    (bounded : shape.volume < 2 ^ 64) (matched : count.toNat = shape.volume)
    (bounded2 : (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (mBound : env "m" = some (.pointer (some (TensorInstance.record pool i))))
    (stepValue : env "communicationStepSize" = some (.finite step))
    (stepCast : convert .size (.finite step) = some (.integer duration.val))
    (lastValue : env "lastSuccessfulTime" = some (.pointer (some buffers.last)))
    (freshDst : env "dst" = none) (freshSrc : env "src" = none)
    (freshCount : env "nContinuousStates" = none) (freshExpected : env "expected" = none)
    (freshSteps : env "steps" = none) (freshK : env "k" = none) (freshN : env "n" = none)
    (freshRhs : env "rumoca_rhs" = none) (freshOK : env "fmi3OK" = none)
    (freshJac : env "rumoca_square_jacobian_diag" = none)
    (readsState : Reads H (TensorInstance.field pool i TensorInstance.stateName) initial)
    (readsInput : Reads H (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableState : Writable H (TensorInstance.field pool i TensorInstance.stateName) shape.volume)
    (writableDeriv : Writable H (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume)
    (writableOutput : Writable H (TensorInstance.field pool i TensorInstance.outputName)
      (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume)
    (timeInit : H (TensorInstance.field pool i TensorInstance.timeName) =
      some ⟨.float64, true, some (.finite (times 0))⟩)
    (lastCell : H buffers.last = some ⟨.float64, true, oldLast⟩)
    (lastOutside : ∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block)
    (executes : ∀ n, Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment (eulerIterate initial sums n) input) (results n))
    (adds : ∀ n, ∀ a : Fin shape.volume,
      Binary64.Adds (eulerIterate initial sums n)[a] (results n)[a] (.finite (sums n)[a]))
    (timeAdds : ∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1))))
    (jacAdds : ∀ k : Fin shape.volume,
      Binary64.Adds input[k] input[k] (.finite (SquareDiagonal.doubled input)[k]))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) Hn .done) w →
      CCalls.Events.Resolves program w)
    (jacResolves : ∀ (H' : Heap) w, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling SquareDiagonal.function.signature.name
        (Diagonal.argumentValues (TensorInstance.field pool i TensorInstance.inputName)
          (TensorInstance.field pool i TensorInstance.outputName) shape) H' .done) w →
      CCalls.Events.Resolves program w) (fenv : TensorFenv interface) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName)
        (eulerIterate initial sums duration.val) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.outputName)
        (Diagonal.matrix (SquareDiagonal.doubled input)) ∧
      finalHeap (TensorInstance.field pool i TensorInstance.timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = H ((TensorInstance.field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (tensorStepSolve shape true) env types0 H) "fmi3Status" stack)
        (.returning (.integer 0) finalHeap stack) := by
  set p := TensorInstance.record pool i with hp
  set sf := TensorInstance.field pool i TensorInstance.stateName with hsf
  set df := TensorInstance.field pool i TensorInstance.derivativeName with hdf
  set tf := TensorInstance.field pool i TensorInstance.timeName with htf
  set jf := TensorInstance.field pool i TensorInstance.outputName with hjf
  set tail := TensorContinuousStates.jacobianCall shape ::
    Runtime.out "lastSuccessfulTime" (Runtime.field "time") :: [Runtime.ok] with htail
  -- The hoisted-declaration environments and types, threaded through the seven
  -- function-scope declarations of `tensorStepSolve`.
  set env1 := bind env "dst" (.pointer (some (p.member TensorInstance.stateName))) with henv1
  set types1 := bindType types0 "dst" .pointer with htypes1
  have m1 : env1 "m" = some (.pointer (some p)) := by simp [henv1, CBody.bind, mBound]
  set env2 := bind env1 "src" (.pointer (some (p.member TensorInstance.derivativeName))) with henv2
  set types2 := bindType types1 "src" .pointer with htypes2
  set env3 := bind env2 "nContinuousStates" (.integer shape.volume) with henv3
  set types3 := bindType types2 "nContinuousStates" .size with htypes3
  set env4 := bind env3 "expected" (.integer shape.volume) with henv4
  set types4 := bindType types3 "expected" .size with htypes4
  have stepEval : CLoops.eval env4 types4 H (.cast "size_t" (Runtime.v "communicationStepSize")) =
      some (.integer duration.val) := by
    have base : CBody.resolve env4 "communicationStepSize" = some (.finite step) := by
      simp [CBody.resolve, henv4, henv3, henv2, henv1, CBody.bind, stepValue]
    simp [CLoops.eval, CBody.eval, base, CBody.expressionCast, Runtime.v, CBody.zeroLiteral,
      CBody.cast, stepCast, fenv.sizeType]
  set env5 := bind env4 "steps" (.integer duration.val) with henv5
  set types5 := bindType types4 "steps" .size with htypes5
  have freshK5 : env5 "k" = none := by simp [henv5, henv4, henv3, henv2, henv1, CBody.bind, freshK]
  set env6 := counterEnv env5 "k" 0 with henv6
  set types6 := bindType types5 "k" .size with htypes6
  have freshN6 : env6 "n" = none := by simp [henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, freshN]
  set types7 := bindType types6 "n" .size with htypes7
  -- The seven declaration steps as one observable-machine reach.
  have declReach : Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (tensorStepSolve shape true) env types0 H) "fmi3Status" stack)
      (.body (.running (loop "n" (Runtime.v "steps") stepBodyT :: tail)
        (counterEnv env6 "n" 0) types7 H) "fmi3Status" stack) := by
    refine .next (CCalls.Events.body_step program
      (TensorFloat64.declare_step_e env types0 H "fmi3Float64 *" "dst"
        ((Runtime.region TensorInstance.stateName)) .pointer
        (.pointer (some (p.member TensorInstance.stateName))) _ _ freshDst fenv.floatPointerType
        (by apply CBodyEmbedding.eval_refines
            simp [Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.lvalue, CBody.resolve, mBound, Value.address]) rfl)
      "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (TensorFloat64.declare_step_e env1 types1 H "fmi3Float64 *" "src"
          ((Runtime.region TensorInstance.derivativeName)) .pointer
          (.pointer (some (p.member TensorInstance.derivativeName))) _ _
          (by simp [henv1, CBody.bind, freshSrc]) fenv.floatPointerType
          (by apply CBodyEmbedding.eval_refines
              simp [Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.lvalue, CBody.resolve, m1, Value.address]) rfl)
        "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (TensorFloat64.declare_step_e env2 types2 H "size_t" "nContinuousStates"
          (Runtime.n shape.volume) .size (.integer shape.volume) _ _
          (by simp [henv2, henv1, CBody.bind, freshCount]) fenv.sizeType
          (by simp [Runtime.n, CLoops.eval, CBody.eval]) (CLoops.convert_size_nat _ bounded))
        "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (TensorFloat64.declare_step_e env3 types3 H "size_t" "expected"
          (Runtime.n shape.volume) .size (.integer shape.volume) _ _
          (by simp [henv3, henv2, henv1, CBody.bind, freshExpected]) fenv.sizeType
          (by simp [Runtime.n, CLoops.eval, CBody.eval]) (CLoops.convert_size_nat _ bounded))
        "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (TensorFloat64.declare_step_e env4 types4 H "size_t" "steps"
          (.cast "size_t" (Runtime.v "communicationStepSize")) .size (.integer duration.val) _ _
          (by simp [henv4, henv3, henv2, henv1, CBody.bind, freshSteps]) fenv.sizeType stepEval
          (CLoops.convert_size_nat _ duration.isLt))
        "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (CLoops.counter_initialize env5 types5 H "k" _ freshK5 fenv.sizeType) "fmi3Status" stack)
      (.next (CCalls.Events.body_step program
        (CLoops.counter_initialize env6 types6 H "n" _ freshN6 fenv.sizeType) "fmi3Status" stack)
        (.refl _)))))))
  -- The loop's entry environment `env6` carries every prepared binding.
  have kInit6 : env6 "k" = some (.integer 0) := by simp [henv6, counterEnv, CBody.bind]
  have mBound6 : env6 "m" = some (.pointer (some p)) := by
    simp [henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, mBound]
  have countBound6 : env6 "nContinuousStates" = some (.integer count.toNat) := by
    simp [henv6, henv5, henv4, henv3, counterEnv, CBody.bind, matched]
  have dstBound6 : CBody.resolve env6 "dst" =
      some (.pointer (some (p.member TensorInstance.stateName))) := by
    simp [henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, CBody.resolve]
  have srcBound6 : CBody.resolve env6 "src" =
      some (.pointer (some (p.member TensorInstance.derivativeName))) := by
    simp [henv6, henv5, henv4, henv3, henv2, counterEnv, CBody.bind, CBody.resolve]
  have expBound6 : CBody.resolve env6 "expected" = some (.integer shape.volume) := by
    simp [henv6, henv5, henv4, counterEnv, CBody.bind, CBody.resolve]
  have stepsBound6 : CBody.resolve env6 "steps" = some (.integer duration.val) := by
    simp [henv6, henv5, counterEnv, CBody.bind, CBody.resolve]
  have freshRhs6 : env6 "rumoca_rhs" = none := by
    simp [henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, freshRhs]
  have typedK7 : types7 "k" = some .size := by simp [htypes7, htypes6, CLoops.bindType]
  have typedN7 : types7 "n" = some .size := by simp [htypes7, CLoops.bindType]
  have nBoundD : duration.val < 2 ^ 64 := duration.isLt
  -- The outer grid loop.
  obtain ⟨loopHeap, stateN, inputN, wStateN, wDerivN, timeN, othersN, _derivN, genN, outputN, loopReach⟩ :=
    stepLoopT_reaches program shape definitions linked library found H pool i initial input results sums times
      count duration.val env6 types7 "fmi3Status" stack tail
      bounded matched nBoundD mBound6 countBound6 typedK7 typedN7 kInit6 dstBound6 srcBound6 expBound6
      stepsBound6 freshRhs6 readsState readsInput writableState writableDeriv timeInit
      (fun n _ => executes n) (fun n _ => adds n) (fun n _ => timeAdds n) resolves fenv
  -- The environment at the tail (Jacobian call, publish, return).
  set tailEnv := counterEnv (loopLocals env6 shape.volume duration.val) "n" duration.val with htailEnv
  have mTail : tailEnv "m" = some (.pointer (some p)) := by
    simpa only [htailEnv] using (loopEnv_get env6 shape.volume duration.val "m" (by decide) (by decide)).trans mBound6
  have countTail : tailEnv "nContinuousStates" = some (.integer shape.volume) := by
    have base : env6 "nContinuousStates" = some (.integer shape.volume) := by
      simp [henv6, henv5, henv4, henv3, counterEnv, CBody.bind]
    simpa only [htailEnv] using
      (loopEnv_get env6 shape.volume duration.val "nContinuousStates" (by decide) (by decide)).trans base
  have freshJacTail : tailEnv "rumoca_square_jacobian_diag" = none := by
    have base : env6 "rumoca_square_jacobian_diag" = none := by
      simp [henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, freshJac]
    simpa only [htailEnv] using
      (loopEnv_get env6 shape.volume duration.val "rumoca_square_jacobian_diag" (by decide) (by decide)).trans base
  have lastTail : CBody.resolve tailEnv "lastSuccessfulTime" = some (.pointer (some buffers.last)) := by
    have base : CBody.resolve env6 "lastSuccessfulTime" = some (.pointer (some buffers.last)) := by
      simp [CBody.resolve, henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, lastValue]
    simpa only [htailEnv] using
      (resolve_loopEnv env6 shape.volume duration.val "lastSuccessfulTime" (by decide) (by decide)).trans base
  have okTail : tailEnv "fmi3OK" = none := by
    have base : env6 "fmi3OK" = none := by
      simp [henv6, henv5, henv4, henv3, henv2, henv1, counterEnv, CBody.bind, freshOK]
    simpa only [htailEnv] using
      (loopEnv_get env6 shape.volume duration.val "fmi3OK" (by decide) (by decide)).trans base
  -- The prepared square-Jacobian diagonal entry over the post-loop heap.
  set jacCont := CCalls.Typed.Continuation.caller .discard
    (Runtime.out "lastSuccessfulTime" (Runtime.field "time") :: [Runtime.ok]) tailEnv types7 "fmi3Status" stack
    with hjacCont
  have argsJac : [Value.pointer (some (p.member TensorInstance.inputName)),
      .pointer (some (p.member TensorInstance.outputName)),
      .integer shape.volume, .integer (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume] =
      Diagonal.argumentValues (TensorInstance.field pool i TensorInstance.inputName)
        (TensorInstance.field pool i TensorInstance.outputName) shape := rfl
  have jacEnter : CCalls.Events.internalNext program
      (.body (.running (TensorContinuousStates.jacobianCall shape ::
        Runtime.out "lastSuccessfulTime" (Runtime.field "time") :: [Runtime.ok]) tailEnv types7 loopHeap)
        "fmi3Status" stack) =
      some (.calling "rumoca_square_jacobian_diag"
        [.pointer (some (p.member TensorInstance.inputName)), .pointer (some (p.member TensorInstance.outputName)),
         .integer shape.volume, .integer (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume]
        loopHeap jacCont) := by
    simp [TensorContinuousStates.jacobianCall, hjacCont, CCalls.Events.internalNext, CCalls.Typed.nextWith,
      CLoops.next, CLoops.eval, TensorContinuousStates.jacobianEntryArgs, Runtime.call, Runtime.region,
      Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.lvalue, CCalls.Events.enterCall,
      CCalls.Events.resolve, CCalls.Indirect.operand, CCalls.Indirect.resolve, CCalls.arguments,
      CBody.bind, CBody.resolve, CBody.constants, Value.address, mTail, countTail, freshJacTail, fenv.jacobian]
  -- output writability survives the loop (the loop touches only x, dx and time).
  have writableOutputLoop : Writable loopHeap (TensorInstance.field pool i TensorInstance.outputName)
      (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume := by
    intro a ha
    obtain ⟨old, ho⟩ := writableOutput a ha
    exact ⟨old, by rw [outputN TensorInstance.outputName a (by decide) (by decide) (by decide)]; exact ho⟩
  obtain ⟨jacReads, jacFrame, jacRan⟩ :=
    TensorInstanceJacobian.jacobian_writes_events (shape := shape) definitions program linked library jacFound
      pool i input loopHeap bounded2 inputN writableOutputLoop jacAdds (jacResolves loopHeap) jacCont
  set jacHeap := Diagonal.resultHeap loopHeap (TensorInstance.field pool i TensorInstance.outputName)
    (SquareDiagonal.doubled input) with hjacHeap
  have resume : CCalls.Events.internalNext program (.returning .void jacHeap jacCont) =
      some (.body (.running (Runtime.out "lastSuccessfulTime" (Runtime.field "time") :: [Runtime.ok])
        tailEnv types7 jacHeap) "fmi3Status" stack) := by
    simp [hjacCont, CCalls.Events.internalNext, CCalls.Typed.nextWith, CCalls.Typed.resume]
  -- The instance's scalar time cell coincides with `p.member "time"`.
  have tfield : tf = p.member "time" := rfl
  have lastBlock : buffers.last.block ≠ (TensorInstance.record pool i).block := lastOutside i
  have lastNe : buffers.last ≠ p.member "time" := by
    intro same
    have hb : (p.member "time").block = p.block := rfl
    exact lastBlock ((congrArg Address.block same).trans hb)
  -- the time cell is preserved by the Jacobian write (time is a distinct member of J)
  have timeSep : ∀ a < (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume,
      p.member "time" ≠ (TensorInstance.field pool i TensorInstance.outputName).index a := by
    intro a _
    have coincide : p.member "time" = (TensorInstance.field pool i TensorInstance.timeName).index 0 :=
      (Address.index_zero (TensorInstance.field pool i TensorInstance.timeName)).symm
    rw [coincide]
    exact TensorInstance.fields_separate pool i TensorInstance.timeName TensorInstance.outputName
      (by decide +kernel) 0 a
  have timeJac : jacHeap (p.member "time") = loopHeap (p.member "time") := jacFrame (p.member "time") timeSep
  have timeMember : loopHeap (p.member "time") = some ⟨.float64, true, some (.finite (times duration.val))⟩ := by
    rw [← tfield]; exact timeN
  have timeLoadJac : load jacHeap (p.member "time") = some (.finite (times duration.val)) := by
    simp [load, timeJac, timeMember, convert, Value.finite]
  -- `buffers.last` lies outside the record, so both the loop and the Jacobian preserve it.
  have lastSep : ∀ a < (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume,
      buffers.last ≠ (TensorInstance.field pool i TensorInstance.outputName).index a :=
    fun a _ => cell_block_ne pool i TensorInstance.outputName a buffers.last lastBlock
  have lastLoop : loopHeap buffers.last = some ⟨.float64, true, oldLast⟩ := by
    rw [genN buffers.last lastBlock]; exact lastCell
  have lastLoopJac : jacHeap buffers.last = some ⟨.float64, true, oldLast⟩ :=
    (jacFrame buffers.last lastSep).trans lastLoop
  set finalHeap := StateProofs.written jacHeap buffers.last (toBits (times duration.val)).val with hfinal
  -- The `out lastSuccessfulTime` store step: publish the advanced time base.
  have outStep : CLoops.next (.running (Runtime.out "lastSuccessfulTime" (Runtime.field "time") :: [Runtime.ok])
      tailEnv types7 jacHeap) = some (.running [Runtime.ok] tailEnv types7 finalHeap) := by
    have leftEval : CLoops.eval tailEnv types7 jacHeap (Runtime.field "time") =
        some (.finite (times duration.val)) := by
      show CBody.eval tailEnv jacHeap (Runtime.field "time") = some (.finite (times duration.val))
      have raw : CBody.eval tailEnv jacHeap (Runtime.field "time") = load jacHeap (p.member "time") := by
        simp [Runtime.field, Runtime.v, CBody.eval, CBody.resolve, mTail, Value.address]
      rw [raw]; exact timeLoadJac
    have addr : CBody.lvalue tailEnv jacHeap (.deref (Runtime.v "lastSuccessfulTime")) = some buffers.last := by
      simp [CBody.lvalue, Runtime.v, CBody.eval, lastTail, Value.address]
    simp [Runtime.out, CLoops.next, leftEval, addr, Value.finite,
      store_float64 jacHeap buffers.last oldLast _ lastLoopJac, hfinal, StateProofs.written]
  have okReach := finishOK program finalHeap tailEnv types7 stack okTail fenv.statusType fenv.fmi3OK
  refine ⟨finalHeap, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- state region reads the N-fold Euler iterate
    intro a
    have neLast : sf.index a.val ≠ buffers.last :=
      (cell_block_ne pool i TensorInstance.stateName a.val buffers.last lastBlock).symm
    have frameLast : finalHeap (sf.index a.val) = jacHeap (sf.index a.val) := by
      rw [hfinal]; exact StateProofs.written_frame jacHeap buffers.last _ _ neLast
    have frameJac : jacHeap (sf.index a.val) = loopHeap (sf.index a.val) :=
      jacFrame (sf.index a.val)
        (fun b _ => TensorInstance.fields_separate pool i TensorInstance.stateName TensorInstance.outputName
          (by decide +kernel) a.val b)
    simp only [load, frameLast, frameJac]; exact stateN a
  · -- the J region reads the dense Jacobian `diag(2*u)`
    intro a
    have neLast : jf.index a.val ≠ buffers.last :=
      (cell_block_ne pool i TensorInstance.outputName a.val buffers.last lastBlock).symm
    have frameLast : finalHeap (jf.index a.val) = jacHeap (jf.index a.val) := by
      rw [hfinal]; exact StateProofs.written_frame jacHeap buffers.last _ _ neLast
    simp only [load, frameLast]; exact jacReads a
  · -- the instance time cell advanced to `times N`
    have frame : finalHeap tf = jacHeap tf := by
      rw [hfinal]
      exact StateProofs.written_frame jacHeap buffers.last tf (toBits (times duration.val)).val
        (fun h => lastNe h.symm)
    rw [frame, tfield, timeJac, ← tfield]; exact timeN
  · -- the caller's `lastSuccessfulTime` reads the advanced time base
    rw [hfinal, StateProofs.written]; simp [replace, Value.finite]
  · -- every other instance preserved
    intro j b k different
    have neLast : (TensorInstance.field pool j b).index k ≠ buffers.last :=
      (cell_block_ne pool j b k buffers.last (lastOutside j)).symm
    have frameLast : finalHeap ((TensorInstance.field pool j b).index k) =
        jacHeap ((TensorInstance.field pool j b).index k) := by
      rw [hfinal]; exact StateProofs.written_frame jacHeap buffers.last _ _ neLast
    have frameJac : jacHeap ((TensorInstance.field pool j b).index k) =
        loopHeap ((TensorInstance.field pool j b).index k) :=
      jacFrame ((TensorInstance.field pool j b).index k)
        (fun a _ => Address.instances_separate pool j i different b TensorInstance.outputName k a)
    rw [frameLast, frameJac]; exact othersN j b k different
  · -- the observable-machine execution: declarations, loop, Jacobian, publish, return
    exact declReach.trans (loopReach.trans (.next (argsJac ▸ jacEnter)
      (jacRan.trans (.next resume (.next (CCalls.Events.body_step program outStep "fmi3Status" stack) okReach)))))

end

/-! ### The reused model-independent guard prefix

`front_run` runs the first nine statements of the tensor `fmi3DoStep` body, which
are exactly the scalar prefix of `Runtime.doStep` (`doStepBody_prefix`): the
handle/lifecycle guard (`StepEntry.lifecycle_run`), the output-pointer check and the
zero/last-time output writes (`StepEntry.outputs_run`), and the invalid
communication-point/step rejection (`StepEntry.input_condition`). It reaches the
`stepRounding`/`stepClock`/`stepGrid` guard sections followed by the tensor numerical
tail, with the record pointer bound and the output cells initialized, over an
arbitrary saved caller. Because these guard statements are model-independent, the
scalar lemmas apply verbatim; only the trailing numerical section is tensor-specific. -/
section
variable [interface : CInterface]

theorem front_run (shape : Tensor.Shape) (hasOutput : Bool) (types : StepEntry.Types) (env : Locals) (heap : Heap)
    (p : Address) (buffers : StepEntry.Buffers) (point time step : Binary64.Value) (oldOutput : Option Value)
    (handle : env "instance" = some (.pointer (some p))) (fresh : env "m" = none)
    (kindValue : load heap (p.member "kind") = some (.integer 1))
    (modeValue : load heap (p.member "mode") = some (.integer 4))
    (pointValue : env "currentCommunicationPoint" = some (.finite point))
    (stepValue : env "communicationStepSize" = some (.finite step))
    (eventValue : env "eventHandlingNeeded" = some (.pointer (some buffers.event)))
    (terminateValue : env "terminateSimulation" = some (.pointer (some buffers.terminate)))
    (earlyValue : env "earlyReturn" = some (.pointer (some buffers.early)))
    (lastValue : env "lastSuccessfulTime" = some (.pointer (some buffers.last)))
    (clock : load heap (p.member "time") = some (.finite time))
    (same : Binary64.value point = Binary64.value time) (positive : 0 < Binary64.value step)
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, oldOutput⟩)
    (outsideEvent : buffers.event.block ≠ p.block) (outsideTerminate : buffers.terminate.block ≠ p.block)
    (outsideEarly : buffers.early.block ≠ p.block) (outsideLast : buffers.last.block ≠ p.block) :
    CBody.run 9 (.running (doStepBody shape hasOutput) env heap) =
      some (.running (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape hasOutput)
        (StepEntry.locals env p) (StepEntry.outputHeap heap buffers time)) := by
  set tail := Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape hasOutput with htail
  have entered := StepEntry.lifecycle_run types env heap p .cs .step
    (StepEntry.outputCode ++ StepEntry.inputGuard :: tail) handle fresh kindValue modeValue
  simp only [allowed, permittedModes] at entered
  have setup := StepEntry.outputs_run (StepEntry.locals env p) heap p buffers time oldOutput
    (StepEntry.inputGuard :: tail) (by simp [StepEntry.locals, CBody.bind])
    (by simpa [StepEntry.locals, CBody.bind] using eventValue)
    (by simpa [StepEntry.locals, CBody.bind] using terminateValue)
    (by simpa [StepEntry.locals, CBody.bind] using earlyValue)
    (by simpa [StepEntry.locals, CBody.bind] using lastValue) clock event terminate early last
    outsideEvent outsideTerminate outsideEarly
  have clockAfter : load (StepEntry.outputHeap heap buffers time) (p.member "time") = some (.finite time) := by
    simpa only [load, StepEntry.output_instance heap buffers time p (p.member "time")
      outsideEvent outsideTerminate outsideEarly outsideLast rfl] using clock
  have condition := StepEntry.input_condition (StepEntry.locals env p) (StepEntry.outputHeap heap buffers time) p
    point time step (by simp [StepEntry.locals, CBody.bind])
    (by simpa [StepEntry.locals, CBody.bind] using pointValue)
    (by simpa [StepEntry.locals, CBody.bind] using stepValue) clockAfter same positive
  have checked : CBody.run 1 (.running (StepEntry.inputGuard :: tail)
      (StepEntry.locals env p) (StepEntry.outputHeap heap buffers time)) =
      some (.running tail (StepEntry.locals env p) (StepEntry.outputHeap heap buffers time)) := by
    simp [CBody.run, CBody.next, StepEntry.inputGuard, Runtime.reject, Runtime.branch, condition,
      boolean, Value.truth]
  have decomp : doStepBody shape hasOutput = Runtime.require .doStep ++ StepEntry.outputCode ++
      StepEntry.inputGuard :: tail := rfl
  have remaining : CBody.run 6 (.running (StepEntry.outputCode ++ StepEntry.inputGuard :: tail)
      (StepEntry.locals env p) heap) =
      some (.running tail (StepEntry.locals env p) (StepEntry.outputHeap heap buffers time)) := by
    rw [show (6:Nat) = 5 + 1 from rfl, CBody.run_add, setup]; exact checked
  rw [decomp, List.append_assoc, show (9:Nat) = 3 + 6 from rfl, CBody.run_add, entered]
  exact remaining

end

/-! ### The accepted tensor `fmi3DoStep` call

`accepted_reaches`/`accepted_behaviors` compose the reused guard prefix
(`front_run`, then `StepGuards.rounding_path`/`clock_path`/`grid_path` under the
admitted-duration premises stated exactly as the scalar body exposes them) with the
tensor numerical tail (`tensorSolve_reaches`). For a request that passes the guard
prefix over the tensor instance record's metadata and time cells, the observable
machine's sole terminating behavior initializes the output cells, runs the outer
grid loop for the admitted step count, publishes the advanced time to
`*lastSuccessfulTime`, and returns `fmi3OK`; the state region equals the N-fold Euler
iterate, the instance time cell and the caller's `lastSuccessfulTime` read the
advanced time base, and every cell of every other instance is preserved. -/
section
open CTree.Printer StepGuards
open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile Rumoca.CTensor
variable [interface : CInterface]
variable (program : CCalls.Events.Program E)

set_option maxRecDepth 100000 in
theorem accepted_reaches (shape : Tensor.Shape) (types : StepEntry.Types) (header : CFenv.Header)
    (fenv : TensorFenv interface) (nearest : interface.constants "FE_TONEAREST" = some (.integer header.nearest))
    (definitions : CLoops.Calls.Definitions) (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (heap : Heap) (pool : Address) (i : Nat) (buffers : StepEntry.Buffers)
    (point step : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value) (oldOutput : Option Value)
    (initial input : Values shape) (results sums : Nat → Values shape) (times : Nat → Binary64.Value)
    (count : UInt64) (bounded : shape.volume < 2 ^ 64) (matched : count.toNat = shape.volume)
    (rounding : program.externals "fegetround" = some (CMathCalls.roundingExternal fenv.intType header.nearest
      ⟨by have positive := header.nonnegative; omega, header.bounded⟩))
    (floorBound : program.externals "floor" = some (CMathCalls.floorExternal fenv.doubleType))
    (defined : program.internal.definitions "fmi3DoStep" = some (.tree (function shape false)))
    (kindValue : load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1))
    (modeValue : load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4))
    (timeCell : heap ((TensorInstance.record pool i).member "time") =
      some ⟨.float64, true, some (.finite (times 0))⟩)
    (same : Binary64.value point = Binary64.value (times 0))
    (enabled : load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome))
    (limit : ∀ value, stop = some value →
      load heap ((TensorInstance.record pool i).member "stop") = some (.finite value))
    (admitted : StepAdmission.AdmittedDuration step)
    (progress : Binary64.value (times 0) < Binary64.value (Binary64.roundedAdd (times 0) step))
    (withinStop : ∀ value, stop = some value →
      Binary64.value (Binary64.roundedAdd (times 0) step) ≤ Binary64.value value)
    (readsState : Reads heap (TensorInstance.field pool i TensorInstance.stateName) initial)
    (readsInput : Reads heap (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableState : Writable heap (TensorInstance.field pool i TensorInstance.stateName) shape.volume)
    (writableDeriv : Writable heap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume)
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, oldOutput⟩)
    (outsideEvent : ∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block)
    (outsideTerminate : ∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block)
    (outsideEarly : ∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block)
    (outsideLast : ∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block)
    (executes : ∀ n, Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment (eulerIterate initial sums n) input) (results n))
    (adds : ∀ n, ∀ a : Fin shape.volume,
      Binary64.Adds (eulerIterate initial sums n)[a] (results n)[a] (.finite (sums n)[a]))
    (timeAdds : ∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1))))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) Hn .done) w →
      CCalls.Events.Resolves program w) :
    ∃ (duration : CStatements.Counter) (finalHeap : Heap),
      0 < duration.val ∧ duration.val ≤ 1000000 ∧ Binary64.value step = (duration.val : ℝ) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName)
        (eulerIterate initial sums duration.val) ∧
      finalHeap (TensorInstance.field pool i TensorInstance.timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = heap ((TensorInstance.field pool j b).index k)) ∧
      Transition.Events.Prefix (CCalls.Events.machine program)
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) []
        (.returning (.integer 0) finalHeap .done) := by
  set p := TensorInstance.record pool i with hp
  set params := StepEntry.parameters (some p) (Binary64.toBits point).val (Binary64.toBits step).val flag
    buffers.outputs with hparams
  set after := StepEntry.outputHeap heap buffers (times 0) with hafter
  obtain ⟨duration, dpos, dbound, ddur, dcast⟩ := StepAdmission.duration_count step admitted
  -- The reused guard prefix over the tensor instance heap.
  have front9 := front_run shape false types params heap p buffers point (times 0) step oldOutput
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]) kindValue modeValue
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [load, timeCell, convert, Value.finite]) same admitted.1 event terminate early last
    (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i)
  obtain ⟨localTypes, entered⟩ := CCalls.Events.body_prefix_reaches program (function shape false)
    (StepEntry.arguments (some p) (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs)
    params (StepEntry.locals params p) heap after
    (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape false) .done 9
    defined (StepEntry.parameters_bound types _ _ _ _ _) (doStepBody_closed shape false) front9
  -- The instance metadata cells survive the output-pointer writes.
  have loaded (name : String) : load after (p.member name) = load heap (p.member name) := by
    simp only [load, hafter, StepEntry.output_instance heap buffers (times 0) p (p.member name)
      (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl]
  set later := StepEntry.locals params p with hlater
  have instanceValue : later "m" = some (.pointer (some p)) := by simp [hlater, StepEntry.locals, CBody.bind]
  have stepBound : later "communicationStepSize" = some (.finite step) := by
    simp [hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite]
  have fresh (name) (member : name ∈ ["rounding", "next", "floored", "fegetround", "floor",
      "FE_TONEAREST", "model_advance", "fmi3OK"]) : later name = none := by
    fin_cases member <;>
      simp [hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  -- The three model-independent guard sections, reused verbatim.
  let rounded := Binary64.roundedAdd (times 0) step
  let roundingEnv := CBody.bind later "rounding" (.integer header.nearest)
  let roundingTypes := CLoops.bindType localTypes "rounding" .int32
  let clockEnv := CBody.bind roundingEnv "next" (.finite rounded)
  let clockTypes := CLoops.bindType roundingTypes "next" .float64
  let gridEnv := CBody.bind clockEnv "floored" (.finite (Binary64.floorValue step))
  let gridTypes := CLoops.bindType clockTypes "floored" .float64
  have first := StepGuards.rounding_path program header later localTypes after header.nearest
    ⟨by have positive := header.nonnegative; omega, header.bounded⟩
    (Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape false) "fmi3Status" .done
    fenv.intType (fresh _ (by simp)) (fresh _ (by simp)) (fresh _ (by simp)) fenv.fegetround nearest rounding
  simp only at first
  have second := StepGuards.clock_path program roundingEnv roundingTypes after p (times 0) step stop
    (Runtime.stepGrid ++ tensorStepSolve shape false) "fmi3Status" .done fenv.doubleType
    (by simpa [roundingEnv, CBody.bind] using fresh "next" (by simp))
    (by simpa [roundingEnv, CBody.bind] using instanceValue)
    (by simpa [roundingEnv, CBody.bind] using stepBound) ((loaded "time").trans
      (by simp [load, timeCell, convert, Value.finite]))
    ((loaded "stopDefined").trans enabled) (fun v c => (loaded "stop").trans (limit v c))
  have noStop : ¬ StepGuards.AboveStop (.finite rounded) stop := by
    cases stop with
    | none => simp [StepGuards.AboveStop]
    | some v => exact not_lt.mpr (withinStop v rfl)
  have second' : Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape false)
        roundingEnv roundingTypes after) "fmi3Status" .done) []
      (.body (.running (Runtime.stepGrid ++ tensorStepSolve shape false) clockEnv clockTypes after)
        "fmi3Status" .done) := by
    simpa [StepAdmission.duration_sum (times 0) step admitted, StepGuards.clockDestination, noStop,
      StepGuards.Progress, progress, rounded, clockEnv, clockTypes, Value.finite] using second
  have third := StepGuards.grid_path program clockEnv clockTypes after step (tensorStepSolve shape false)
    "fmi3Status" .done fenv.doubleType (by simpa [clockEnv, roundingEnv, CBody.bind] using fresh "floored" (by simp))
    (by simpa [clockEnv, roundingEnv, CBody.bind] using fresh "floor" (by simp)) fenv.floorConstant
    (by simpa [clockEnv, roundingEnv, CBody.bind] using stepBound) admitted.1 floorBound
  have third' : Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (Runtime.stepGrid ++ tensorStepSolve shape false) clockEnv clockTypes after) "fmi3Status" .done) []
      (.body (.running (tensorStepSolve shape false) gridEnv gridTypes after) "fmi3Status" .done) := by
    simpa [admitted, gridEnv, gridTypes] using third
  -- The instance regions and output cells over the initialized heap.
  have frameCell : ∀ (nm : String) (a : Nat), after ((TensorInstance.field pool i nm).index a) =
      heap ((TensorInstance.field pool i nm).index a) := fun nm a =>
    StepEntry.output_instance heap buffers (times 0) p ((TensorInstance.field pool i nm).index a)
      (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl
  have readsStateAfter : Reads after (TensorInstance.field pool i TensorInstance.stateName) initial := fun a => by
    simp only [load, frameCell TensorInstance.stateName a.val]; exact readsState a
  have readsInputAfter : Reads after (TensorInstance.field pool i TensorInstance.inputName) input := fun a => by
    simp only [load, frameCell TensorInstance.inputName a.val]; exact readsInput a
  have writableStateAfter : Writable after (TensorInstance.field pool i TensorInstance.stateName) shape.volume :=
    fun a ha => by
      obtain ⟨old, ho⟩ := writableState a ha
      exact ⟨old, by rw [frameCell TensorInstance.stateName a]; exact ho⟩
  have writableDerivAfter : Writable after (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume :=
    fun a ha => by
      obtain ⟨old, ho⟩ := writableDeriv a ha
      exact ⟨old, by rw [frameCell TensorInstance.derivativeName a]; exact ho⟩
  have timeAfter : after (TensorInstance.field pool i TensorInstance.timeName) =
      some ⟨.float64, true, some (.finite (times 0))⟩ := by
    rw [show TensorInstance.field pool i TensorInstance.timeName = p.member "time" from rfl, hafter,
      StepEntry.output_instance heap buffers (times 0) p (p.member "time")
        (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl]; exact timeCell
  obtain ⟨_e, _t, _ea, lastAfter⟩ := StepEntry.output_values heap buffers (times 0) oldOutput event terminate early last
  -- The tensor numerical tail from the post-guard state.
  obtain ⟨finalHeap, stateFinal, timeFinal, lastFinal, othersFinal, solveReach⟩ :=
    tensorSolve_reaches program shape definitions linked library found after pool i initial input results sums
      times count duration step gridEnv gridTypes .done buffers (some (.finite (times 0))) bounded matched
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, instanceValue, hp])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, stepBound]) dcast
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind]) (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals,
        hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]) (by simp [gridEnv, clockEnv, roundingEnv,
        CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind]) (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals,
        hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]) (by simp [gridEnv, clockEnv, roundingEnv,
        CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind]) readsStateAfter readsInputAfter writableStateAfter writableDerivAfter
      timeAfter lastAfter outsideLast executes adds timeAdds resolves fenv
  refine ⟨duration, finalHeap, dpos, dbound, ddur, stateFinal, timeFinal, lastFinal, ?_, ?_⟩
  · intro j b k different
    have frameAfter : after ((TensorInstance.field pool j b).index k) = heap ((TensorInstance.field pool j b).index k) :=
      StepEntry.output_instance heap buffers (times 0) p ((TensorInstance.field pool j b).index k)
        (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl
    rw [othersFinal j b k different, frameAfter]
  · refine (CCalls.Events.internal_path program entered).trans (first.trans (second'.trans (third'.trans ?_)))
    exact CCalls.Events.internal_path program solveReach

theorem accepted_behaviors (shape : Tensor.Shape) (types : StepEntry.Types) (header : CFenv.Header)
    (fenv : TensorFenv interface) (nearest : interface.constants "FE_TONEAREST" = some (.integer header.nearest))
    (definitions : CLoops.Calls.Definitions) (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (heap : Heap) (pool : Address) (i : Nat) (buffers : StepEntry.Buffers)
    (point step : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value) (oldOutput : Option Value)
    (initial input : Values shape) (results sums : Nat → Values shape) (times : Nat → Binary64.Value)
    (count : UInt64) (bounded : shape.volume < 2 ^ 64) (matched : count.toNat = shape.volume)
    (rounding : program.externals "fegetround" = some (CMathCalls.roundingExternal fenv.intType header.nearest
      ⟨by have positive := header.nonnegative; omega, header.bounded⟩))
    (floorBound : program.externals "floor" = some (CMathCalls.floorExternal fenv.doubleType))
    (defined : program.internal.definitions "fmi3DoStep" = some (.tree (function shape false)))
    (kindValue : load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1))
    (modeValue : load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4))
    (timeCell : heap ((TensorInstance.record pool i).member "time") =
      some ⟨.float64, true, some (.finite (times 0))⟩)
    (same : Binary64.value point = Binary64.value (times 0))
    (enabled : load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome))
    (limit : ∀ value, stop = some value →
      load heap ((TensorInstance.record pool i).member "stop") = some (.finite value))
    (admitted : StepAdmission.AdmittedDuration step)
    (progress : Binary64.value (times 0) < Binary64.value (Binary64.roundedAdd (times 0) step))
    (withinStop : ∀ value, stop = some value →
      Binary64.value (Binary64.roundedAdd (times 0) step) ≤ Binary64.value value)
    (readsState : Reads heap (TensorInstance.field pool i TensorInstance.stateName) initial)
    (readsInput : Reads heap (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableState : Writable heap (TensorInstance.field pool i TensorInstance.stateName) shape.volume)
    (writableDeriv : Writable heap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume)
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, oldOutput⟩)
    (outsideEvent : ∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block)
    (outsideTerminate : ∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block)
    (outsideEarly : ∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block)
    (outsideLast : ∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block)
    (executes : ∀ n, Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment (eulerIterate initial sums n) input) (results n))
    (adds : ∀ n, ∀ a : Fin shape.volume,
      Binary64.Adds (eulerIterate initial sums n)[a] (results n)[a] (.finite (sums n)[a]))
    (timeAdds : ∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1))))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) Hn .done) w →
      CCalls.Events.Resolves program w) :
    ∃ (duration : CStatements.Counter) (finalHeap : Heap),
      0 < duration.val ∧ duration.val ≤ 1000000 ∧ Binary64.value step = (duration.val : ℝ) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName)
        (eulerIterate initial sums duration.val) ∧
      finalHeap (TensorInstance.field pool i TensorInstance.timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = heap ((TensorInstance.field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, finalHeap⟩ := by
  obtain ⟨duration, finalHeap, dpos, dbound, ddur, stateFinal, timeFinal, lastFinal, othersFinal, reach⟩ :=
    accepted_reaches program shape types header fenv nearest definitions linked library found heap pool i buffers point step
      flag stop oldOutput initial input results sums times count bounded matched rounding floorBound
      defined kindValue modeValue timeCell same enabled limit admitted progress withinStop readsState
      readsInput writableState writableDeriv event terminate early last outsideEvent outsideTerminate
      outsideEarly outsideLast executes adds timeAdds resolves
  exact ⟨duration, finalHeap, dpos, dbound, ddur, stateFinal, timeFinal, lastFinal, othersFinal,
    fun behavior => (reach.forced (CCalls.Events.return_forced program (.integer 0) finalHeap)).behaviors behavior⟩

theorem accepted_output_reaches (shape : Tensor.Shape) (types : StepEntry.Types) (header : CFenv.Header)
    (fenv : TensorFenv interface) (nearest : interface.constants "FE_TONEAREST" = some (.integer header.nearest))
    (definitions : CLoops.Calls.Definitions) (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (jacFound : definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function)
    (heap : Heap) (pool : Address) (i : Nat) (buffers : StepEntry.Buffers)
    (point step : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value) (oldOutput : Option Value)
    (initial input : Values shape) (results sums : Nat → Values shape) (times : Nat → Binary64.Value)
    (count : UInt64) (bounded : shape.volume < 2 ^ 64) (matched : count.toNat = shape.volume)
    (bounded2 : (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (rounding : program.externals "fegetround" = some (CMathCalls.roundingExternal fenv.intType header.nearest
      ⟨by have positive := header.nonnegative; omega, header.bounded⟩))
    (floorBound : program.externals "floor" = some (CMathCalls.floorExternal fenv.doubleType))
    (defined : program.internal.definitions "fmi3DoStep" = some (.tree (function shape true)))
    (kindValue : load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1))
    (modeValue : load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4))
    (timeCell : heap ((TensorInstance.record pool i).member "time") =
      some ⟨.float64, true, some (.finite (times 0))⟩)
    (same : Binary64.value point = Binary64.value (times 0))
    (enabled : load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome))
    (limit : ∀ value, stop = some value →
      load heap ((TensorInstance.record pool i).member "stop") = some (.finite value))
    (admitted : StepAdmission.AdmittedDuration step)
    (progress : Binary64.value (times 0) < Binary64.value (Binary64.roundedAdd (times 0) step))
    (withinStop : ∀ value, stop = some value →
      Binary64.value (Binary64.roundedAdd (times 0) step) ≤ Binary64.value value)
    (readsState : Reads heap (TensorInstance.field pool i TensorInstance.stateName) initial)
    (readsInput : Reads heap (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableState : Writable heap (TensorInstance.field pool i TensorInstance.stateName) shape.volume)
    (writableDeriv : Writable heap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume)
    (writableOutput : Writable heap (TensorInstance.field pool i TensorInstance.outputName)
      (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume)
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, oldOutput⟩)
    (outsideEvent : ∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block)
    (outsideTerminate : ∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block)
    (outsideEarly : ∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block)
    (outsideLast : ∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block)
    (executes : ∀ n, Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment (eulerIterate initial sums n) input) (results n))
    (adds : ∀ n, ∀ a : Fin shape.volume,
      Binary64.Adds (eulerIterate initial sums n)[a] (results n)[a] (.finite (sums n)[a]))
    (timeAdds : ∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1))))
    (jacAdds : ∀ k : Fin shape.volume,
      Binary64.Adds input[k] input[k] (.finite (SquareDiagonal.doubled input)[k]))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) Hn .done) w →
      CCalls.Events.Resolves program w)
    (jacResolves : ∀ (H' : Heap) w, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling SquareDiagonal.function.signature.name
        (Diagonal.argumentValues (TensorInstance.field pool i TensorInstance.inputName)
          (TensorInstance.field pool i TensorInstance.outputName) shape) H' .done) w →
      CCalls.Events.Resolves program w) :
    ∃ (duration : CStatements.Counter) (finalHeap : Heap),
      0 < duration.val ∧ duration.val ≤ 1000000 ∧ Binary64.value step = (duration.val : ℝ) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName)
        (eulerIterate initial sums duration.val) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.outputName)
        (Diagonal.matrix (SquareDiagonal.doubled input)) ∧
      finalHeap (TensorInstance.field pool i TensorInstance.timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = heap ((TensorInstance.field pool j b).index k)) ∧
      Transition.Events.Prefix (CCalls.Events.machine program)
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) []
        (.returning (.integer 0) finalHeap .done) := by
  set p := TensorInstance.record pool i with hp
  set params := StepEntry.parameters (some p) (Binary64.toBits point).val (Binary64.toBits step).val flag
    buffers.outputs with hparams
  set after := StepEntry.outputHeap heap buffers (times 0) with hafter
  obtain ⟨duration, dpos, dbound, ddur, dcast⟩ := StepAdmission.duration_count step admitted
  -- The reused guard prefix over the tensor instance heap.
  have front9 := front_run shape true types params heap p buffers point (times 0) step oldOutput
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]) kindValue modeValue
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [load, timeCell, convert, Value.finite]) same admitted.1 event terminate early last
    (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i)
  obtain ⟨localTypes, entered⟩ := CCalls.Events.body_prefix_reaches program (function shape true)
    (StepEntry.arguments (some p) (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs)
    params (StepEntry.locals params p) heap after
    (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape true) .done 9
    defined (StepEntry.parameters_bound types _ _ _ _ _) (doStepBody_closed shape true) front9
  -- The instance metadata cells survive the output-pointer writes.
  have loaded (name : String) : load after (p.member name) = load heap (p.member name) := by
    simp only [load, hafter, StepEntry.output_instance heap buffers (times 0) p (p.member name)
      (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl]
  set later := StepEntry.locals params p with hlater
  have instanceValue : later "m" = some (.pointer (some p)) := by simp [hlater, StepEntry.locals, CBody.bind]
  have stepBound : later "communicationStepSize" = some (.finite step) := by
    simp [hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite]
  have fresh (name) (member : name ∈ ["rounding", "next", "floored", "fegetround", "floor",
      "FE_TONEAREST", "model_advance", "fmi3OK"]) : later name = none := by
    fin_cases member <;>
      simp [hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  -- The three model-independent guard sections, reused verbatim.
  let rounded := Binary64.roundedAdd (times 0) step
  let roundingEnv := CBody.bind later "rounding" (.integer header.nearest)
  let roundingTypes := CLoops.bindType localTypes "rounding" .int32
  let clockEnv := CBody.bind roundingEnv "next" (.finite rounded)
  let clockTypes := CLoops.bindType roundingTypes "next" .float64
  let gridEnv := CBody.bind clockEnv "floored" (.finite (Binary64.floorValue step))
  let gridTypes := CLoops.bindType clockTypes "floored" .float64
  have first := StepGuards.rounding_path program header later localTypes after header.nearest
    ⟨by have positive := header.nonnegative; omega, header.bounded⟩
    (Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape true) "fmi3Status" .done
    fenv.intType (fresh _ (by simp)) (fresh _ (by simp)) (fresh _ (by simp)) fenv.fegetround nearest rounding
  simp only at first
  have second := StepGuards.clock_path program roundingEnv roundingTypes after p (times 0) step stop
    (Runtime.stepGrid ++ tensorStepSolve shape true) "fmi3Status" .done fenv.doubleType
    (by simpa [roundingEnv, CBody.bind] using fresh "next" (by simp))
    (by simpa [roundingEnv, CBody.bind] using instanceValue)
    (by simpa [roundingEnv, CBody.bind] using stepBound) ((loaded "time").trans
      (by simp [load, timeCell, convert, Value.finite]))
    ((loaded "stopDefined").trans enabled) (fun v c => (loaded "stop").trans (limit v c))
  have noStop : ¬ StepGuards.AboveStop (.finite rounded) stop := by
    cases stop with
    | none => simp [StepGuards.AboveStop]
    | some v => exact not_lt.mpr (withinStop v rfl)
  have second' : Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape true)
        roundingEnv roundingTypes after) "fmi3Status" .done) []
      (.body (.running (Runtime.stepGrid ++ tensorStepSolve shape true) clockEnv clockTypes after)
        "fmi3Status" .done) := by
    simpa [StepAdmission.duration_sum (times 0) step admitted, StepGuards.clockDestination, noStop,
      StepGuards.Progress, progress, rounded, clockEnv, clockTypes, Value.finite] using second
  have third := StepGuards.grid_path program clockEnv clockTypes after step (tensorStepSolve shape true)
    "fmi3Status" .done fenv.doubleType (by simpa [clockEnv, roundingEnv, CBody.bind] using fresh "floored" (by simp))
    (by simpa [clockEnv, roundingEnv, CBody.bind] using fresh "floor" (by simp)) fenv.floorConstant
    (by simpa [clockEnv, roundingEnv, CBody.bind] using stepBound) admitted.1 floorBound
  have third' : Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (Runtime.stepGrid ++ tensorStepSolve shape true) clockEnv clockTypes after) "fmi3Status" .done) []
      (.body (.running (tensorStepSolve shape true) gridEnv gridTypes after) "fmi3Status" .done) := by
    simpa [admitted, gridEnv, gridTypes] using third
  -- The instance regions and output cells over the initialized heap.
  have frameCell : ∀ (nm : String) (a : Nat), after ((TensorInstance.field pool i nm).index a) =
      heap ((TensorInstance.field pool i nm).index a) := fun nm a =>
    StepEntry.output_instance heap buffers (times 0) p ((TensorInstance.field pool i nm).index a)
      (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl
  have readsStateAfter : Reads after (TensorInstance.field pool i TensorInstance.stateName) initial := fun a => by
    simp only [load, frameCell TensorInstance.stateName a.val]; exact readsState a
  have readsInputAfter : Reads after (TensorInstance.field pool i TensorInstance.inputName) input := fun a => by
    simp only [load, frameCell TensorInstance.inputName a.val]; exact readsInput a
  have writableStateAfter : Writable after (TensorInstance.field pool i TensorInstance.stateName) shape.volume :=
    fun a ha => by
      obtain ⟨old, ho⟩ := writableState a ha
      exact ⟨old, by rw [frameCell TensorInstance.stateName a]; exact ho⟩
  have writableDerivAfter : Writable after (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume :=
    fun a ha => by
      obtain ⟨old, ho⟩ := writableDeriv a ha
      exact ⟨old, by rw [frameCell TensorInstance.derivativeName a]; exact ho⟩
  have writableOutputAfter : Writable after (TensorInstance.field pool i TensorInstance.outputName)
      (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume :=
    fun a ha => by
      obtain ⟨old, ho⟩ := writableOutput a ha
      exact ⟨old, by rw [frameCell TensorInstance.outputName a]; exact ho⟩
  have timeAfter : after (TensorInstance.field pool i TensorInstance.timeName) =
      some ⟨.float64, true, some (.finite (times 0))⟩ := by
    rw [show TensorInstance.field pool i TensorInstance.timeName = p.member "time" from rfl, hafter,
      StepEntry.output_instance heap buffers (times 0) p (p.member "time")
        (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl]; exact timeCell
  obtain ⟨_e, _t, _ea, lastAfter⟩ := StepEntry.output_values heap buffers (times 0) oldOutput event terminate early last
  -- The tensor numerical tail from the post-guard state.
  obtain ⟨finalHeap, stateFinal, jFinal, timeFinal, lastFinal, othersFinal, solveReach⟩ :=
    tensorSolveOutput_reaches program shape definitions linked library found jacFound after pool i initial input results sums
      times count duration step gridEnv gridTypes .done buffers (some (.finite (times 0))) bounded matched bounded2
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, instanceValue, hp])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, stepBound]) dcast
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind]) (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals,
        hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]) (by simp [gridEnv, clockEnv, roundingEnv,
        CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind]) (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals,
        hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]) (by simp [gridEnv, clockEnv, roundingEnv,
        CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind])
      (by simp [gridEnv, clockEnv, roundingEnv, CBody.bind, hlater, StepEntry.locals, hparams, StepEntry.parameters,
        StepEntry.bindings, CBody.bind]) readsStateAfter readsInputAfter writableStateAfter writableDerivAfter writableOutputAfter
      timeAfter lastAfter outsideLast executes adds timeAdds jacAdds resolves jacResolves fenv
  refine ⟨duration, finalHeap, dpos, dbound, ddur, stateFinal, jFinal, timeFinal, lastFinal, ?_, ?_⟩
  · intro j b k different
    have frameAfter : after ((TensorInstance.field pool j b).index k) = heap ((TensorInstance.field pool j b).index k) :=
      StepEntry.output_instance heap buffers (times 0) p ((TensorInstance.field pool j b).index k)
        (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl
    rw [othersFinal j b k different, frameAfter]
  · refine (CCalls.Events.internal_path program entered).trans (first.trans (second'.trans (third'.trans ?_)))
    exact CCalls.Events.internal_path program solveReach

theorem accepted_output_behaviors (shape : Tensor.Shape) (types : StepEntry.Types) (header : CFenv.Header)
    (fenv : TensorFenv interface) (nearest : interface.constants "FE_TONEAREST" = some (.integer header.nearest))
    (definitions : CLoops.Calls.Definitions) (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (jacFound : definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function)
    (heap : Heap) (pool : Address) (i : Nat) (buffers : StepEntry.Buffers)
    (point step : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value) (oldOutput : Option Value)
    (initial input : Values shape) (results sums : Nat → Values shape) (times : Nat → Binary64.Value)
    (count : UInt64) (bounded : shape.volume < 2 ^ 64) (matched : count.toNat = shape.volume)
    (bounded2 : (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (rounding : program.externals "fegetround" = some (CMathCalls.roundingExternal fenv.intType header.nearest
      ⟨by have positive := header.nonnegative; omega, header.bounded⟩))
    (floorBound : program.externals "floor" = some (CMathCalls.floorExternal fenv.doubleType))
    (defined : program.internal.definitions "fmi3DoStep" = some (.tree (function shape true)))
    (kindValue : load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1))
    (modeValue : load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4))
    (timeCell : heap ((TensorInstance.record pool i).member "time") =
      some ⟨.float64, true, some (.finite (times 0))⟩)
    (same : Binary64.value point = Binary64.value (times 0))
    (enabled : load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome))
    (limit : ∀ value, stop = some value →
      load heap ((TensorInstance.record pool i).member "stop") = some (.finite value))
    (admitted : StepAdmission.AdmittedDuration step)
    (progress : Binary64.value (times 0) < Binary64.value (Binary64.roundedAdd (times 0) step))
    (withinStop : ∀ value, stop = some value →
      Binary64.value (Binary64.roundedAdd (times 0) step) ≤ Binary64.value value)
    (readsState : Reads heap (TensorInstance.field pool i TensorInstance.stateName) initial)
    (readsInput : Reads heap (TensorInstance.field pool i TensorInstance.inputName) input)
    (writableState : Writable heap (TensorInstance.field pool i TensorInstance.stateName) shape.volume)
    (writableDeriv : Writable heap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume)
    (writableOutput : Writable heap (TensorInstance.field pool i TensorInstance.outputName)
      (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume)
    (event : HistoryBodies.BoolWritable heap buffers.event)
    (terminate : HistoryBodies.BoolWritable heap buffers.terminate)
    (early : HistoryBodies.BoolWritable heap buffers.early)
    (last : heap buffers.last = some ⟨.float64, true, oldOutput⟩)
    (outsideEvent : ∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block)
    (outsideTerminate : ∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block)
    (outsideEarly : ∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block)
    (outsideLast : ∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block)
    (executes : ∀ n, Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment (eulerIterate initial sums n) input) (results n))
    (adds : ∀ n, ∀ a : Fin shape.volume,
      Binary64.Adds (eulerIterate initial sums n)[a] (results n)[a] (.finite (sums n)[a]))
    (timeAdds : ∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1))))
    (jacAdds : ∀ k : Fin shape.volume,
      Binary64.Adds input[k] input[k] (.finite (SquareDiagonal.doubled input)[k]))
    (resolves : ∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) Hn .done) w →
      CCalls.Events.Resolves program w)
    (jacResolves : ∀ (H' : Heap) w, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling SquareDiagonal.function.signature.name
        (Diagonal.argumentValues (TensorInstance.field pool i TensorInstance.inputName)
          (TensorInstance.field pool i TensorInstance.outputName) shape) H' .done) w →
      CCalls.Events.Resolves program w) :
    ∃ (duration : CStatements.Counter) (finalHeap : Heap),
      0 < duration.val ∧ duration.val ≤ 1000000 ∧ Binary64.value step = (duration.val : ℝ) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName)
        (eulerIterate initial sums duration.val) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.outputName)
        (Diagonal.matrix (SquareDiagonal.doubled input)) ∧
      finalHeap (TensorInstance.field pool i TensorInstance.timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = heap ((TensorInstance.field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, finalHeap⟩ := by
  obtain ⟨duration, finalHeap, dpos, dbound, ddur, stateFinal, jFinal, timeFinal, lastFinal, othersFinal, reach⟩ :=
    accepted_output_reaches program shape types header fenv nearest definitions linked library found jacFound heap pool i buffers point step
      flag stop oldOutput initial input results sums times count bounded matched bounded2 rounding floorBound
      defined kindValue modeValue timeCell same enabled limit admitted progress withinStop readsState
      readsInput writableState writableDeriv writableOutput event terminate early last outsideEvent outsideTerminate
      outsideEarly outsideLast executes adds timeAdds jacAdds resolves jacResolves
  exact ⟨duration, finalHeap, dpos, dbound, ddur, stateFinal, jFinal, timeFinal, lastFinal, othersFinal,
    fun behavior => (reach.forced (CCalls.Events.return_forced program (.integer 0) finalHeap)).behaviors behavior⟩

end

/-! ### The pre-guard rejections

The handle and lifecycle guards are the model-independent scalar prefix, so a null
handle and a lifecycle-mismatched call are rejected exactly as the scalar body
rejects them: a null handle returns `fmi3Error` leaving the heap unchanged; a call
in a disallowed FMI state returns `fmi3Error` after writing the terminated mode and,
with logging suppressed, changing nothing else. Both are reached before any tensor
declaration, and reuse the shared `GuardedCalls` rejection lemmas over the tensor
`fmi3DoStep` body. These stay in the pinned `cInterface`; the pre-guard fmi3Error
return does not read the floating-environment header. -/
section
variable [static : StaticLiterals]
private local instance rejectionInterface : CInterface := cInterface static.addresses
variable (program : CCalls.Events.Program E)

/-- A null instance handle is rejected with `fmi3Error`, changing nothing. -/
theorem null_behaviors (shape : Tensor.Shape) (hasOutput : Bool) (types : StepEntry.Types) (heap : Heap)
    (point step : BitVec 64) (flag : Bool) (outputs : StepEntry.Outputs)
    (defined : program.internal.definitions "fmi3DoStep" = some (.tree (function shape hasOutput))) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3DoStep" (StepEntry.arguments none point step flag outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (function shape hasOutput)
    (Runtime.modeGuard .doStep :: (StepEntry.outputCode ++ StepEntry.inputGuard ::
      (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape hasOutput)))
    (StepEntry.arguments none point step flag outputs) (StepEntry.parameters none point step flag outputs)
    heap defined (StepEntry.parameters_bound types none point step flag outputs)
    (by simp [function, doStepBody, Runtime.require, StepEntry.outputCode, StepEntry.inputGuard, StepEntry.inputCondition, List.append_assoc]) rfl (doStepBody_closed shape hasOutput)
  all_goals simp [StepEntry.parameters, StepEntry.bindings, CBody.bind]

/-- A `fmi3DoStep` call in a disallowed FMI state is rejected with `fmi3Error`,
writing the terminated mode and (logging suppressed) changing nothing else. -/
theorem lifecycle_behaviors (shape : Tensor.Shape) (hasOutput : Bool) (types : StepEntry.Types) (heap : Heap)
    (p message : Address) (logger : Option Address) (kind : Kind) (mode : Mode)
    (point step : BitVec 64) (flag : Bool) (outputs : StepEntry.Outputs)
    (defined : program.internal.definitions "fmi3DoStep" = some (.tree (function shape hasOutput)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses ErrorCalls.rejectionMessage = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0))
    (rejected : ¬ Reference.Allowed .doStep kind mode) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3DoStep" (StepEntry.arguments (some p) point step flag outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  apply GuardedCalls.rejected_silent_behaviors program (function shape hasOutput) .doStep
    (StepEntry.outputCode ++ StepEntry.inputGuard ::
      (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape hasOutput))
    (StepEntry.arguments (some p) point step flag outputs) (StepEntry.parameters (some p) point step flag outputs)
    heap p message logger kind mode defined (StepEntry.parameters_bound types (some p) point step flag outputs)
    (by simp [function, doStepBody, Runtime.require, StepEntry.outputCode, StepEntry.inputGuard, StepEntry.inputCondition, List.append_assoc]) rfl (doStepBody_closed shape hasOutput)
    helper (by simp [StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [StepEntry.parameters, StepEntry.bindings, CBody.bind]) messageBound hk hm hl hg rejected

end

/-! ### The off-grid / over-bound `fmi3Discard` rejection

An admitted-rounding call whose communication step does not lie on the unit internal
time grid (off-grid) or exceeds the internal-step bound (over-bound) but still makes
clock progress inside any stop window reaches the shared `Runtime.stepDiscard` block
before any tensor declaration, via the reused `StepGuards.rounding_path`/`clock_path`
guard sections and the rejected `grid_path` branch. The whole call then returns
`fmi3Discard` with the heap unchanged apart from the output-cell initialization the
scalar prefix documents, reusing the scalar `StepDiscard` logging-callback composition
over the tensor instance record's `logging`/`environment`/`logger` cells: the reached
prefix is silent, so the suppressed outcome terminates with `fmi3Discard`, and the
enabled outcome mirrors every represented logger callback result. -/
section
open CTree.Printer StepGuards
open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile Rumoca.CTensor
variable [static : StaticLiterals]

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 100000 in
/-- The reused guard prefix over the tensor instance heap reaches the shared
`Runtime.stepDiscard` block for an off-grid or over-bound admitted step. -/
theorem discard_prefix (shape : Tensor.Shape) (hasOutput : Bool)
    (header : CFenv.Header) :
    letI : CInterface := fenvInterface (static := static) header
    ∀ {E} (program : CCalls.Events.Program E) (types : StepEntry.Types) (heap : Heap) (pool : Address) (i : Nat)
      (buffers : StepEntry.Buffers) (point step time : Binary64.Value) (flag : Bool)
      (stop : Option Binary64.Value) (oldOutput : Option Value),
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      program.internal.definitions "fmi3DoStep" = some (.tree (function shape hasOutput)) →
      load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1) →
      load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4) →
      heap ((TensorInstance.record pool i).member "time") = some ⟨.float64, true, some (.finite time)⟩ →
      Binary64.value point = Binary64.value time →
      load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value →
        load heap ((TensorInstance.record pool i).member "stop") = some (.finite value)) →
      HistoryBodies.BoolWritable heap buffers.event → HistoryBodies.BoolWritable heap buffers.terminate →
      HistoryBodies.BoolWritable heap buffers.early → heap buffers.last = some ⟨.float64, true, oldOutput⟩ →
      (∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block) →
      0 < Binary64.value step →
      StepGuards.Progress time (Binary64.addResult time step) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
      ¬ StepAdmission.AdmittedDuration step →
      StepDiscard.Path program
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done)
        (StepEntry.outputHeap heap buffers time) (TensorInstance.record pool i) := by
  letI : CInterface := fenvInterface header
  have fenv : TensorFenv (fenvInterface header) := fenvInterface_fenv header
  have nearest : (fenvInterface (static := static) header).constants "FE_TONEAREST" =
    some (.integer header.nearest) := fenvInterface_nearest header
  intro E program types heap pool i buffers point step time flag stop oldOutput rounding floorBound defined
    kindValue modeValue timeCell same enabled limit event terminate early last outsideEvent outsideTerminate
    outsideEarly outsideLast positive progress noStop offGrid
  set p := TensorInstance.record pool i with hp
  set params := StepEntry.parameters (some p) (Binary64.toBits point).val (Binary64.toBits step).val flag
    buffers.outputs with hparams
  set after := StepEntry.outputHeap heap buffers time with hafter
  have front9 := front_run shape hasOutput types params heap p buffers point time step oldOutput
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]) kindValue modeValue
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, StepEntry.Buffers.outputs])
    (by simp [load, timeCell, convert, Value.finite]) same positive event terminate early last
    (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i)
  obtain ⟨localTypes, entered⟩ := CCalls.Events.body_prefix_reaches program (function shape hasOutput)
    (StepEntry.arguments (some p) (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs)
    params (StepEntry.locals params p) heap after
    (Runtime.stepRounding ++ Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape hasOutput) .done 9
    defined (StepEntry.parameters_bound types _ _ _ _ _) (doStepBody_closed shape hasOutput) front9
  have loaded (name : String) : load after (p.member name) = load heap (p.member name) := by
    simp only [load, hafter, StepEntry.output_instance heap buffers time p (p.member name)
      (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl]
  set later := StepEntry.locals params p with hlater
  have instanceValue : later "m" = some (.pointer (some p)) := by simp [hlater, StepEntry.locals, CBody.bind]
  have stepBound : later "communicationStepSize" = some (.finite step) := by
    simp [hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind, Value.finite]
  have fresh (name) (member : name ∈ ["rounding", "next", "floored", "fegetround", "floor",
      "FE_TONEAREST", "model_advance", "fmi3OK"]) : later name = none := by
    fin_cases member <;>
      simp [hlater, StepEntry.locals, hparams, StepEntry.parameters, StepEntry.bindings, CBody.bind]
  let candidate := Binary64.addResult time step
  let roundingEnv := CBody.bind later "rounding" (.integer header.nearest)
  let roundingTypes := CLoops.bindType localTypes "rounding" .int32
  let clockEnv := CBody.bind roundingEnv "next" (.float64 candidate.encode)
  let clockTypes := CLoops.bindType roundingTypes "next" .float64
  let gridEnv := CBody.bind clockEnv "floored" (.finite (Binary64.floorValue step))
  let gridTypes := CLoops.bindType clockTypes "floored" .float64
  have first := StepGuards.rounding_path program header later localTypes after header.nearest
    ⟨by have positive := header.nonnegative; omega, header.bounded⟩
    (Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape hasOutput) "fmi3Status" .done
    fenv.intType (fresh _ (by simp)) (fresh _ (by simp)) (fresh _ (by simp)) fenv.fegetround nearest rounding
  simp only at first
  have second := StepGuards.clock_path program roundingEnv roundingTypes after p time step stop
    (Runtime.stepGrid ++ tensorStepSolve shape hasOutput) "fmi3Status" .done fenv.doubleType
    (by simpa [roundingEnv, CBody.bind] using fresh "next" (by simp))
    (by simpa [roundingEnv, CBody.bind] using instanceValue)
    (by simpa [roundingEnv, CBody.bind] using stepBound) ((loaded "time").trans
      (by simp [load, timeCell, convert, Value.finite]))
    ((loaded "stopDefined").trans enabled) (fun v c => (loaded "stop").trans (limit v c))
  have second' : Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (Runtime.stepClock ++ Runtime.stepGrid ++ tensorStepSolve shape hasOutput)
        roundingEnv roundingTypes after) "fmi3Status" .done) []
      (.body (.running (Runtime.stepGrid ++ tensorStepSolve shape hasOutput) clockEnv clockTypes after)
        "fmi3Status" .done) := by
    simpa only [StepGuards.clockDestination, noStop, progress, ↓reduceIte, List.nil_append,
      clockEnv, clockTypes, candidate] using second
  have third := StepGuards.grid_path program clockEnv clockTypes after step (tensorStepSolve shape hasOutput)
    "fmi3Status" .done fenv.doubleType (by simpa [clockEnv, roundingEnv, CBody.bind] using fresh "floored" (by simp))
    (by simpa [clockEnv, roundingEnv, CBody.bind] using fresh "floor" (by simp)) fenv.floorConstant
    (by simpa [clockEnv, roundingEnv, CBody.bind] using stepBound) positive floorBound
  have third' : Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running (Runtime.stepGrid ++ tensorStepSolve shape hasOutput) clockEnv clockTypes after) "fmi3Status" .done) []
      (.body (.running (Runtime.stepDiscard ++ tensorStepSolve shape hasOutput) gridEnv gridTypes after) "fmi3Status" .done) := by
    simpa [offGrid, gridEnv, gridTypes] using third
  refine ⟨gridEnv, gridTypes, tensorStepSolve shape hasOutput,
    (CCalls.Events.internal_path program entered).trans (first.trans (second'.trans third')), ?_, ?_⟩
  · simp [gridEnv, clockEnv, roundingEnv, CBody.bind, CBody.resolve, hlater, StepEntry.locals, hparams,
      StepEntry.parameters, StepEntry.bindings, hp]
  · simp [gridEnv, clockEnv, roundingEnv, CBody.bind, CBody.resolve, hlater, StepEntry.locals, hparams,
      StepEntry.parameters, StepEntry.bindings, CBody.constants,
      fenvInterface_constant header "fmi3Discard" (by decide)]

/-- With logging suppressed, an off-grid or over-bound admitted step returns
`fmi3Discard`, leaving the heap unchanged apart from the scalar output-cell
initialization. -/
def DiscardSuppressed (shape : Tensor.Shape) (hasOutput : Bool) (header : CFenv.Header) : Prop :=
    letI : CInterface := fenvInterface (static := static) header
    ∀ {E} (program : CCalls.Events.Program E) (types : StepEntry.Types) (heap : Heap) (pool : Address) (i : Nat)
      (buffers : StepEntry.Buffers) (point step time : Binary64.Value) (flag : Bool)
      (stop : Option Binary64.Value) (oldOutput : Option Value) (logger : Option Address) (logging : Bool),
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      program.internal.definitions "fmi3DoStep" = some (.tree (function shape hasOutput)) →
      load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1) →
      load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4) →
      heap ((TensorInstance.record pool i).member "time") = some ⟨.float64, true, some (.finite time)⟩ →
      Binary64.value point = Binary64.value time →
      load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value →
        load heap ((TensorInstance.record pool i).member "stop") = some (.finite value)) →
      HistoryBodies.BoolWritable heap buffers.event → HistoryBodies.BoolWritable heap buffers.terminate →
      HistoryBodies.BoolWritable heap buffers.early → heap buffers.last = some ⟨.float64, true, oldOutput⟩ →
      (∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block) →
      0 < Binary64.value step →
      StepGuards.Progress time (Binary64.addResult time step) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
      ¬ StepAdmission.AdmittedDuration step →
      load heap ((TensorInstance.record pool i).member "logger") = some (.pointer logger) →
      load heap ((TensorInstance.record pool i).member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 2, StepEntry.outputHeap heap buffers time⟩

set_option maxRecDepth 100000 in
theorem discard_suppressed_behaviors (shape : Tensor.Shape) (hasOutput : Bool) (header : CFenv.Header) :
    DiscardSuppressed shape hasOutput header := by
  letI : CInterface := fenvInterface (static := static) header
  intro E program types heap pool i buffers point step time flag stop oldOutput logger logging rounding floorBound
    defined kindValue modeValue timeCell same enabled limit event terminate early last outsideEvent outsideTerminate
    outsideEarly outsideLast positive progress noStop offGrid loggerValue loggingValue suppressed behavior
  set p := TensorInstance.record pool i with hp
  have loaded (name : String) :
      load (StepEntry.outputHeap heap buffers time) (p.member name) = load heap (p.member name) := by
    simp only [load, StepEntry.output_instance heap buffers time p (p.member name)
      (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl]
  obtain ⟨env, gtypes, rest, reached, instanceValue, statusValue⟩ :=
    discard_prefix shape hasOutput header program types heap pool i buffers point step time flag stop oldOutput
      rounding floorBound defined kindValue modeValue timeCell same enabled limit event terminate early last
      outsideEvent outsideTerminate outsideEarly outsideLast positive progress noStop offGrid
  have result := StepDiscard.suppressed_behaviors (fenvErrorContext header) program env gtypes rest
    (StepEntry.outputHeap heap buffers time) p logger logging instanceValue statusValue
    ((loaded "logger").trans loggerValue) ((loaded "logging").trans loggingValue) suppressed
  exact (reached.silent_finite_behaviors (by intro history divergent; have impossible := (result (.diverges history)).mp divergent; simp at impossible) behavior).trans (result behavior)

/-- With logging enabled, an off-grid or over-bound admitted step returns
`fmi3Discard` after invoking the logging callback, mirroring every represented
callback outcome; the heap is unchanged apart from the scalar output-cell
initialization and the callback's own writes. -/
def DiscardLogged (shape : Tensor.Shape) (hasOutput : Bool) (header : CFenv.Header) : Prop :=
    letI : CInterface := fenvInterface (static := static) header
    ∀ {E} (program : CCalls.Events.Program E) (types : StepEntry.Types) (heap : Heap) (pool : Address) (i : Nat)
      (buffers : StepEntry.Buffers) (point step time : Binary64.Value) (flag : Bool)
      (stop : Option Binary64.Value) (oldOutput : Option Value)
      (text category logger : Address) (environment : Option Address) (name : String)
      (foreign : CCalls.Events.External E),
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest
        ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      program.internal.definitions "fmi3DoStep" = some (.tree (function shape hasOutput)) →
      static.addresses "logStatus" = some category → static.addresses StepDiscard.message = some text →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1) →
      load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4) →
      heap ((TensorInstance.record pool i).member "time") = some ⟨.float64, true, some (.finite time)⟩ →
      Binary64.value point = Binary64.value time →
      load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome) →
      (∀ value, stop = some value →
        load heap ((TensorInstance.record pool i).member "stop") = some (.finite value)) →
      HistoryBodies.BoolWritable heap buffers.event → HistoryBodies.BoolWritable heap buffers.terminate →
      HistoryBodies.BoolWritable heap buffers.early → heap buffers.last = some ⟨.float64, true, oldOutput⟩ →
      (∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block) →
      (∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block) →
      0 < Binary64.value step →
      StepGuards.Progress time (Binary64.addResult time step) →
      ¬ StepGuards.AboveStop (Binary64.addResult time step) stop →
      ¬ StepAdmission.AdmittedDuration step →
      load heap ((TensorInstance.record pool i).member "logger") = some (.pointer (some logger)) →
      load heap ((TensorInstance.record pool i).member "logging") = some (.integer 1) →
      load heap ((TensorInstance.record pool i).member "environment") = some (.pointer environment) → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
      (∃ events value after, foreign.execute (StepDiscard.arguments environment category text)
        (StepEntry.outputHeap heap buffers time) events value after ∧
        behavior = .terminates events ⟨.integer 2, after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (StepDiscard.arguments environment category text)
        (StepEntry.outputHeap heap buffers time) events value after) ∧ behavior = .wrong [])

set_option maxRecDepth 100000 in
theorem discard_logged_behaviors (shape : Tensor.Shape) (hasOutput : Bool) (header : CFenv.Header) :
    DiscardLogged shape hasOutput header := by
  letI : CInterface := fenvInterface (static := static) header
  intro E program types heap pool i buffers point step time flag stop oldOutput text category logger environment name
    foreign rounding floorBound defined categoryBound textBound address external prototype kindValue modeValue timeCell
    same enabled limit event terminate early last outsideEvent outsideTerminate outsideEarly outsideLast positive
    progress noStop offGrid loggerValue loggingValue environmentValue behavior
  set p := TensorInstance.record pool i with hp
  have loaded (name : String) :
      load (StepEntry.outputHeap heap buffers time) (p.member name) = load heap (p.member name) := by
    simp only [load, StepEntry.output_instance heap buffers time p (p.member name)
      (outsideEvent i) (outsideTerminate i) (outsideEarly i) (outsideLast i) rfl]
  obtain ⟨env, gtypes, rest, reached, instanceValue, statusValue⟩ :=
    discard_prefix shape hasOutput header program types heap pool i buffers point step time flag stop oldOutput
      rounding floorBound defined kindValue modeValue timeCell same enabled limit event terminate early last
      outsideEvent outsideTerminate outsideEarly outsideLast positive progress noStop offGrid
  have result := StepDiscard.all_behaviors (fenvErrorContext header) program env gtypes rest
    (StepEntry.outputHeap heap buffers time) p text category logger environment name foreign instanceValue statusValue
    ((loaded "logger").trans loggerValue) ((loaded "logging").trans loggingValue)
    ((loaded "environment").trans environmentValue) address categoryBound textBound external prototype
  exact (reached.silent_finite_behaviors (by intro history divergent; have impossible := (result (.diverges history)).mp divergent; simp at impossible) behavior).trans (result behavior)

end

/-! ### Printed-text denotation of the guarded body -/
section
open CTree.Printer CTree.Syntax

theorem signature_printable : SignaturePrintable RuntimePrinter.typedefs signature := by
  refine ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel, ?_⟩
  intro param member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  · exact ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  · exact ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  · exact ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩
  · exact ⟨.pointer (text := "fmi3Boolean") (.named (.typedefName (by decide +kernel) (by decide +kernel))),
      by decide +kernel⟩
  · exact ⟨.pointer (text := "fmi3Boolean") (.named (.typedefName (by decide +kernel) (by decide +kernel))),
      by decide +kernel⟩
  · exact ⟨.pointer (text := "fmi3Boolean") (.named (.typedefName (by decide +kernel) (by decide +kernel))),
      by decide +kernel⟩
  · exact ⟨.pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel))),
      by decide +kernel⟩

set_option maxHeartbeats 8000000 in
theorem body_printable (shape : Tensor.Shape) (hasOutput : Bool) :
    ∀ stmt ∈ (function shape hasOutput).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  have intType : TypeSpelling RuntimePrinter.typedefs "int" := .named (.primitive (by decide +kernel))
  have doubleType : TypeSpelling RuntimePrinter.typedefs "double" := .named (.primitive (by decide +kernel))
  cases hasOutput <;>
  simp only [function, doStepBody, tensorStepSolve, jacobianTail, stepPublishTail,
      TensorContinuousStates.jacobianCall, TensorContinuousStates.jacobianEntryArgs,
      stepBodyT, stepBody, eulerBody, timeAdvance, oneExpr,
      dstCell, srcCell, TensorContinuousStates.derivEntryArgs, Runtime.region, Runtime.require,
      Runtime.instancePrefix,
      Runtime.modeGuard, Runtime.allowedExpression, permittedModes, Runtime.mode, Runtime.reject, Runtime.branch,
      Runtime.pointerCheck, Runtime.out, Runtime.put, Runtime.ok, Runtime.ret, Runtime.fail, Runtime.stepRounding,
      Runtime.stepClock, Runtime.stepGrid, Runtime.stepDiscard, Runtime.log, Runtime.field, Runtime.v, Runtime.n, Runtime.call, Runtime.any,
      Runtime.negate, Runtime.finite, Runtime.nev, Runtime.eqv, Runtime.le, Runtime.lt, Runtime.gt, Runtime.both,
      Runtime.either, CAlgorithm.literal, CLoops.loop, CLoops.counterStep, List.foldr_cons, List.foldr_nil,
      List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
      List.cons_append, List.nil_append, forall_eq] <;>
    repeat first
      | exact CNull.literal_printable _
      | exact iType
      | exact fType
      | exact sType
      | exact intType
      | exact doubleType
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
      | apply ItemPrintable.eval
      | apply ItemPrintable.branch
      | apply ItemPrintable.whileLoop
      | apply ItemPrintable.returnValue
      | apply Printable.cast
      | apply Printable.binary
      | apply Printable.not
      | apply Printable.dereference
      | apply Printable.address
      | apply Printable.call
      | apply Printable.field
      | apply Printable.index
      | exact Printable.natural
      | exact Printable.string
      | apply Printable.identifier
      | solve | intro stmt impossible; cases impossible
      | decide +kernel
      | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          Postfix, FieldBase]

/-- The rendered tensor `fmi3DoStep` denotes its function under the shared C printer. -/
theorem function_denotes (shape : Tensor.Shape) (hasOutput : Bool) :
    FunctionDenotes RuntimePrinter.typedefs (function shape hasOutput).render (function shape hasOutput) :=
  CTree.Printer.function_denotes ⟨signature_printable, body_printable shape hasOutput⟩

end

/-! ### The consumable tensor `fmi3DoStep` contract

This mirrors the tensor-native contract shape of `TensorReset.Contract`,
`TensorContinuousStates.DerivContract` and `TensorNominals.Contract`: the printed
function text, its declaration closedness, its printed-text denotation under the
shared C printer, the null-handle rejection, and the accepted end-to-end execution
over the tensor instance record. The lifecycle rejection (`lifecycle_behaviors`) and,
under the same C floating-environment guard premises, the `fmi3Discard` off-grid path
are companion theorems. -/
section
open CTree.Printer
open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile Rumoca.CTensor
variable [static : StaticLiterals]

/-- The accepted end-to-end behavior of the output-free tensor `fmi3DoStep`.
It advances the state by the admitted number of unit Euler steps and publishes the
advanced time, preserving every other instance. The C floating-environment
interface is the header-aware tensor interface, so the round-to-nearest guard and
`fmi3OK` return resolve; the only remaining external premise is the modeled
`fegetround`/`floor` platform returns. -/
def ExecutionFree (shape : Tensor.Shape) (header : CFenv.Header) : Prop :=
    letI : CInterface := fenvInterface header
    ∀ {E} (program : CCalls.Events.Program E) (ptypes : StepEntry.Types)
    (definitions : CLoops.Calls.Definitions) (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (heap : Heap) (pool : Address) (i : Nat) (buffers : StepEntry.Buffers)
    (point step : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value) (oldOutput : Option Value)
    (initial input : Values shape) (results sums : Nat → Values shape) (times : Nat → Binary64.Value)
    (count : UInt64), shape.volume < 2 ^ 64 → count.toNat = shape.volume →
    program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest
      ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    program.internal.definitions "fmi3DoStep" = some (.tree (function shape false)) →
    load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1) →
    load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4) →
    heap ((TensorInstance.record pool i).member "time") =
      some ⟨.float64, true, some (.finite (times 0))⟩ →
    Binary64.value point = Binary64.value (times 0) →
    load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value →
      load heap ((TensorInstance.record pool i).member "stop") = some (.finite value)) →
    StepAdmission.AdmittedDuration step →
    Binary64.value (times 0) < Binary64.value (Binary64.roundedAdd (times 0) step) →
    (∀ value, stop = some value →
      Binary64.value (Binary64.roundedAdd (times 0) step) ≤ Binary64.value value) →
    Reads heap (TensorInstance.field pool i TensorInstance.stateName) initial →
    Reads heap (TensorInstance.field pool i TensorInstance.inputName) input →
    Writable heap (TensorInstance.field pool i TensorInstance.stateName) shape.volume →
    Writable heap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume →
    HistoryBodies.BoolWritable heap buffers.event → HistoryBodies.BoolWritable heap buffers.terminate →
    HistoryBodies.BoolWritable heap buffers.early → heap buffers.last = some ⟨.float64, true, oldOutput⟩ →
    (∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block) →
    (∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block) →
    (∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block) →
    (∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block) →
    (∀ n, Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment (eulerIterate initial sums n) input) (results n)) →
    (∀ n, ∀ a : Fin shape.volume,
      Binary64.Adds (eulerIterate initial sums n)[a] (results n)[a] (.finite (sums n)[a])) →
    (∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1)))) →
    (∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) Hn .done) w →
      CCalls.Events.Resolves program w) →
    ∃ (duration : CStatements.Counter) (finalHeap : Heap),
      0 < duration.val ∧ duration.val ≤ 1000000 ∧ Binary64.value step = (duration.val : ℝ) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName)
        (eulerIterate initial sums duration.val) ∧
      finalHeap (TensorInstance.field pool i TensorInstance.timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = heap ((TensorInstance.field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, finalHeap⟩

/-- The accepted end-to-end behavior of the output-aware tensor `fmi3DoStep`.
Alongside the output-free behavior it writes the dense Jacobian `diag(2*u)` into the
instance's `J` region on every accepted step, preserving every other instance. -/
def ExecutionOutput (shape : Tensor.Shape) (header : CFenv.Header) : Prop :=
    letI : CInterface := fenvInterface header
    ∀ {E} (program : CCalls.Events.Program E) (ptypes : StepEntry.Types)
    (definitions : CLoops.Calls.Definitions) (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (jacFound : definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function)
    (heap : Heap) (pool : Address) (i : Nat) (buffers : StepEntry.Buffers)
    (point step : Binary64.Value) (flag : Bool) (stop : Option Binary64.Value) (oldOutput : Option Value)
    (initial input : Values shape) (results sums : Nat → Values shape) (times : Nat → Binary64.Value)
    (count : UInt64), shape.volume < 2 ^ 64 → count.toNat = shape.volume →
    (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume < 2 ^ 64 →
    program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest
      ⟨by have positive := header.nonnegative; omega, header.bounded⟩) →
    program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    program.internal.definitions "fmi3DoStep" = some (.tree (function shape true)) →
    load heap ((TensorInstance.record pool i).member "kind") = some (.integer 1) →
    load heap ((TensorInstance.record pool i).member "mode") = some (.integer 4) →
    heap ((TensorInstance.record pool i).member "time") =
      some ⟨.float64, true, some (.finite (times 0))⟩ →
    Binary64.value point = Binary64.value (times 0) →
    load heap ((TensorInstance.record pool i).member "stopDefined") = some (boolean stop.isSome) →
    (∀ value, stop = some value →
      load heap ((TensorInstance.record pool i).member "stop") = some (.finite value)) →
    StepAdmission.AdmittedDuration step →
    Binary64.value (times 0) < Binary64.value (Binary64.roundedAdd (times 0) step) →
    (∀ value, stop = some value →
      Binary64.value (Binary64.roundedAdd (times 0) step) ≤ Binary64.value value) →
    Reads heap (TensorInstance.field pool i TensorInstance.stateName) initial →
    Reads heap (TensorInstance.field pool i TensorInstance.inputName) input →
    Writable heap (TensorInstance.field pool i TensorInstance.stateName) shape.volume →
    Writable heap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume →
    Writable heap (TensorInstance.field pool i TensorInstance.outputName)
      (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume →
    HistoryBodies.BoolWritable heap buffers.event → HistoryBodies.BoolWritable heap buffers.terminate →
    HistoryBodies.BoolWritable heap buffers.early → heap buffers.last = some ⟨.float64, true, oldOutput⟩ →
    (∀ j : Nat, buffers.event.block ≠ (TensorInstance.record pool j).block) →
    (∀ j : Nat, buffers.terminate.block ≠ (TensorInstance.record pool j).block) →
    (∀ j : Nat, buffers.early.block ≠ (TensorInstance.record pool j).block) →
    (∀ j : Nat, buffers.last.block ≠ (TensorInstance.record pool j).block) →
    (∀ n, Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment (eulerIterate initial sums n) input) (results n)) →
    (∀ n, ∀ a : Fin shape.volume,
      Binary64.Adds (eulerIterate initial sums n)[a] (results n)[a] (.finite (sums n)[a])) →
    (∀ n, Binary64.Adds (times n) Binary64.one (.finite (times (n + 1)))) →
    (∀ k : Fin shape.volume, Binary64.Adds input[k] input[k] (.finite (SquareDiagonal.doubled input)[k])) →
    (∀ (Hn : Heap) (w), Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) Hn .done) w →
      CCalls.Events.Resolves program w) →
    (∀ (H' : Heap) w, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling SquareDiagonal.function.signature.name
        (Diagonal.argumentValues (TensorInstance.field pool i TensorInstance.inputName)
          (TensorInstance.field pool i TensorInstance.outputName) shape) H' .done) w →
      CCalls.Events.Resolves program w) →
    ∃ (duration : CStatements.Counter) (finalHeap : Heap),
      0 < duration.val ∧ duration.val ≤ 1000000 ∧ Binary64.value step = (duration.val : ℝ) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.stateName)
        (eulerIterate initial sums duration.val) ∧
      Reads finalHeap (TensorInstance.field pool i TensorInstance.outputName)
        (Diagonal.matrix (SquareDiagonal.doubled input)) ∧
      finalHeap (TensorInstance.field pool i TensorInstance.timeName) =
        some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      finalHeap buffers.last = some ⟨.float64, true, some (.finite (times duration.val))⟩ ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = heap ((TensorInstance.field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3DoStep" (StepEntry.arguments (some (TensorInstance.record pool i))
          (Binary64.toBits point).val (Binary64.toBits step).val flag buffers.outputs) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, finalHeap⟩

/-- The tensor `fmi3DoStep` function contract, parameterized on whether the record
carries the dense observation. The accepted execution carries the extra Jacobian
conjunct exactly in the output case. -/
structure Contract (shape : Tensor.Shape) (hasOutput : Bool) (header : CFenv.Header) (text : String) : Prop where
  printed : text = (function shape hasOutput).render
  closed : (function shape hasOutput).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (function shape hasOutput)
  rejected : letI : CInterface := cInterface static.addresses
    ∀ {E} (program : CCalls.Events.Program E) (types : StepEntry.Types) (heap : Heap)
    (point step : BitVec 64) (flag : Bool) (outputs : StepEntry.Outputs),
    program.internal.definitions "fmi3DoStep" = some (.tree (function shape hasOutput)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3DoStep" (StepEntry.arguments none point step flag outputs) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩
  execution : cond hasOutput (ExecutionOutput shape header) (ExecutionFree shape header)
  discarded : DiscardSuppressed shape hasOutput header ∧ DiscardLogged shape hasOutput header

theorem execution_free (shape : Tensor.Shape) (header : CFenv.Header) : ExecutionFree shape header := by
  letI : CInterface := fenvInterface header
  intro E program ptypes definitions linked library found heap pool i buffers point step flag stop
      oldOutput initial input results sums times count bounded matched rounding floorBound
      defined kindValue modeValue timeCell same enabled limit admitted progress withinStop readsState readsInput
      writableState writableDeriv event terminate early last outsideEvent outsideTerminate outsideEarly outsideLast
      executes adds timeAdds resolves
  exact accepted_behaviors program shape ptypes header (fenvInterface_fenv header) (fenvInterface_nearest header)
      definitions linked library found heap pool i buffers point step
      flag stop oldOutput initial input results sums times count bounded matched rounding floorBound
      defined kindValue modeValue timeCell same enabled limit admitted progress withinStop readsState
      readsInput writableState writableDeriv event terminate early last outsideEvent outsideTerminate outsideEarly
      outsideLast executes adds timeAdds resolves

theorem execution_output (shape : Tensor.Shape) (header : CFenv.Header) : ExecutionOutput shape header := by
  letI : CInterface := fenvInterface header
  intro E program ptypes definitions linked library found jacFound heap pool i buffers point step flag stop
      oldOutput initial input results sums times count bounded matched bounded2 rounding floorBound
      defined kindValue modeValue timeCell same enabled limit admitted progress withinStop readsState readsInput
      writableState writableDeriv writableOutput event terminate early last outsideEvent outsideTerminate outsideEarly
      outsideLast executes adds timeAdds jacAdds resolves jacResolves
  exact accepted_output_behaviors program shape ptypes header (fenvInterface_fenv header) (fenvInterface_nearest header)
      definitions linked library found jacFound heap pool i buffers
      point step flag stop oldOutput initial input results sums times count bounded matched bounded2 rounding floorBound
      defined kindValue modeValue timeCell same enabled limit admitted progress withinStop readsState
      readsInput writableState writableDeriv writableOutput event terminate early last outsideEvent outsideTerminate
      outsideEarly outsideLast executes adds timeAdds jacAdds resolves jacResolves

theorem contract (shape : Tensor.Shape) (hasOutput : Bool) (header : CFenv.Header) :
    Contract shape hasOutput header (function shape hasOutput).render where
  printed := rfl
  closed := doStepBody_closed shape hasOutput
  denotes := function_denotes shape hasOutput
  rejected := by
    letI : CInterface := cInterface static.addresses
    intro E program types heap point step flag outputs defined
    exact null_behaviors program shape hasOutput types heap point step flag outputs defined
  execution := by
    cases hasOutput
    · exact execution_free shape header
    · exact execution_output shape header
  discarded := ⟨discard_suppressed_behaviors shape hasOutput header,
    discard_logged_behaviors shape hasOutput header⟩

end

end Rumoca.FMI3.TensorDoStep
