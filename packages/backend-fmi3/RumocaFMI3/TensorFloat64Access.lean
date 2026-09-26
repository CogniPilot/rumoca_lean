import RumocaFMI3.TensorFloat64Copy
import RumocaFMI3.TensorEntryCalls
import RumocaFMI3.TensorInstanceRhs
import RumocaFMI3.TensorInstanceJacobian
import RumocaFMI3.Float64Get
import RumocaFMI3.DerivativeCalls
import RumocaFMI3.Float64Dispatch
import RumocaFMI3.Float64Table
import RumocaC.PointerConditions

/-! `fmi3GetFloat64` / `fmi3SetFloat64` bodies over a static instance record, for
every profile with a declared interface, as package-checked products.

Each accessor uses the same authored C subset as the scalar runtime. The
instance handle and lifecycle guard are validated exactly as the scalar bodies
do (through `Runtime.require`). One array value reference then denotes a whole
declared variable under the FMI 3.0.2 array-access rule: the dispatch arms are
the declared value-reference table (`Float64Table.getArms`, `setArms`), each
staging the variable's record region (member, element offset and element
count). A calculated variable (a state derivative or an algebraic output) is
evaluated first by the profile's prepared kernel entry (`Float64Table.Reads`),
so the value returned is the one the prepared model calculates from the current
inputs and states, never one left in the region by an earlier call. The getter copies the referenced region into the caller's Float64
buffer; the setter copies the caller's values into a writable region (an input
or a state) after checking finiteness. The caller's `nValues` must equal the
referenced variable's element count; the copy uses one counted `size_t` loop
whose bound is that symbolic count, so no tensor coordinate is enumerated. A
request must name exactly one value reference (`nValueReferences = 1`); a
multi-reference aggregate is rejected, not mishandled. Return status is
`fmi3OK` on success and the scalar code's status on rejection.

The tensor and constant-rate adapters consume these bodies and proofs. This
module alone does not establish source acceptance or certify an actual
artifact; those obligations belong to the composed adapter/compiler contracts.
Every theorem is universal in the declared interface, the instance index of the
static pool, the request lengths and the heap. -/
noncomputable section
namespace Rumoca.FMI3.TensorFloat64
open CTree CMemory CBody CLoops Float64Calls
open Rumoca.CMemory.TensorView Rumoca.CMemory.TensorRegion Rumoca.FMI3.TensorInstance
open Rumoca.FMI3.Float64Table (Region getArm setArm pointer)

/-- The reference `valueReferences[0]`. -/
def vr0 : Expr := .index (Runtime.v "valueReferences") (Runtime.n 0)

/-! ### Small machine steps -/

section
variable [interface : CInterface]

/-- One rejected-condition-false check consumes its statement without effect. -/
theorem reject_false (env : Locals) (heap : Heap) (c : Expr) (msg : String) (rest : List Stmt)
    (hc : CBody.eval env heap c = some (boolean false)) :
    CBody.next (.running (Runtime.reject c msg :: rest) env heap) = some (.running rest env heap) := by
  simp [Runtime.reject, Runtime.branch, CBody.next, CBody.nextWith, CBody.legacyExpressions, hc, boolean, Value.truth]

/-- A branch whose condition is false takes the else block. -/
theorem branch_false (env : Locals) (heap : Heap) (c : Expr) (yes no rest : List Stmt)
    (hc : CBody.eval env heap c = some (boolean false)) :
    CBody.next (.running (.branch c yes no :: rest) env heap) = some (.running (no ++ rest) env heap) := by
  simp [CBody.next, CBody.nextWith, CBody.legacyExpressions, hc, boolean, Value.truth]

/-- A branch whose condition is true takes the then block. -/
theorem branch_true (env : Locals) (heap : Heap) (c : Expr) (yes no rest : List Stmt)
    (hc : CBody.eval env heap c = some (boolean true)) :
    CBody.next (.running (.branch c yes no :: rest) env heap) = some (.running (yes ++ rest) env heap) := by
  simp [CBody.next, CBody.nextWith, CBody.legacyExpressions, hc, boolean, Value.truth]

/-- One declaration binds its evaluated, cast value into a fresh local. -/
theorem declare_next (env : Locals) (heap : Heap) (type name : String) (expr : Expr)
    (v0 value : Value) (rest : List Stmt) (fresh : env name = none)
    (ev : CBody.eval env heap expr = some v0) (cst : CBody.cast type v0 = some value) :
    CBody.next (.running (.declare type name expr :: rest) env heap) =
      some (.running rest (CBody.bind env name value) heap) := by
  simp [CBody.next, CBody.nextWith, CBody.legacyExpressions, ev, cst, fresh]

/-- Compose two counted runs. -/
theorem run_append {a b : Nat} {s t u : CBody.State} (h1 : CBody.run a s = some t)
    (h2 : CBody.run b t = some u) : CBody.run (a + b) s = some u := by
  rw [CBody.run_add, h1, Option.bind_some, h2]

/-- One machine step is a run of length one. -/
theorem run_one {s t : CBody.State} (h : CBody.next s = some t) : CBody.run 1 s = some t := by
  simp [CBody.run, h]

/-- `valueReferences[0]` compared with a literal, when the stored reference is `r`. -/
theorem vr0_cmp (env : Locals) (heap : Heap) (refs : Address) (r j : Nat)
    (rBound : resolve env "valueReferences" = some (.pointer (some refs)))
    (refRead : load heap (refs.index 0) = some (.integer r)) :
    CBody.eval env heap (Runtime.eqv vr0 (Runtime.n j)) = some (boolean (decide ((r : Int) = j))) := by
  have refRead' : load heap refs = some (.integer r) := refRead
  simp [vr0, Runtime.eqv, Runtime.n, Runtime.v, CBody.eval, CBody.evalWith, rBound, refRead', Value.address,
    CBody.comparison, boolean]

/-- `valueReferences[0]` differs from a literal, in the memory machine. -/
theorem vr0_bne (env : Locals) (heap : Heap) (refs : Address) (r j : Nat)
    (rBound : resolve env "valueReferences" = some (.pointer (some refs)))
    (refRead : load heap (refs.index 0) = some (.integer r)) (hne : r ≠ j) :
    CBody.eval env heap (Runtime.eqv vr0 (Runtime.n j)) = some (boolean false) := by
  rw [vr0_cmp env heap refs r j rBound refRead]; simp [Nat.cast_inj, hne]

end

/-! ### Typed-machine steps for the dispatch -/

section
variable [interface : CInterface]

/-- One declaration in the typed call machine, exposing the declared type. -/
theorem declare_step_e (env : Locals) (types : Types) (heap : Heap) (type name : String) (expr : Expr)
    (declared : CType) (raw value : Value) (rest : List Stmt) (fresh : env name = none)
    (spelling : interface.types type = some declared)
    (ev : CLoops.eval env types heap expr = some raw) (cst : convert declared raw = some value) :
    CLoops.next (.running (.declare type name expr :: rest) env types heap) =
      some (.running rest (CBody.bind env name value) (CLoops.bindType types name declared) heap) := by
  simp only [CLoops.eval, CBody.legacyExpressions] at ev
  simp [CLoops.next, CLoops.nextWith, CBody.legacyExpressions, spelling, ev, cst, fresh]

/-- A typed-machine branch whose condition is false takes the else block. -/
theorem cbranch_false (env : Locals) (types : Types) (heap : Heap) (c : Expr) (yes no rest : List Stmt)
    (safe : (yes.all CLoops.noDeclarations && no.all CLoops.noDeclarations) = true)
    (hc : CLoops.eval env types heap c = some (boolean false)) :
    CLoops.next (.running (.branch c yes no :: rest) env types heap) =
      some (.running (no ++ rest) env types heap) := by
  simp only [CLoops.eval, CBody.legacyExpressions] at hc
  simp only [CLoops.next, CLoops.nextWith, CBody.legacyExpressions]; rw [safe]; simp [hc, boolean, Value.truth]

/-- A typed-machine branch whose condition is true takes the then block. -/
theorem cbranch_true (env : Locals) (types : Types) (heap : Heap) (c : Expr) (yes no rest : List Stmt)
    (safe : (yes.all CLoops.noDeclarations && no.all CLoops.noDeclarations) = true)
    (hc : CLoops.eval env types heap c = some (boolean true)) :
    CLoops.next (.running (.branch c yes no :: rest) env types heap) =
      some (.running (yes ++ rest) env types heap) := by
  simp only [CLoops.eval, CBody.legacyExpressions] at hc
  simp only [CLoops.next, CLoops.nextWith, CBody.legacyExpressions]; rw [safe]; simp [hc, boolean, Value.truth]

end

/-! ### The dispatch -/

/-- The dispatch statement over a list of arms: the first arm whose reference
equals `valueReferences[0]` runs; otherwise the fallback runs. -/
def dispatch (arms : List (Nat × List Stmt)) (fallback : Stmt) : Stmt :=
  match arms with
  | [] => fallback
  | (j, arm) :: rest =>
    Runtime.branch (Runtime.eqv vr0 (Runtime.n j)) arm
      (Float64Dispatch.dispatchChain vr0 rest [fallback])

theorem dispatch_chain (arms : List (Nat × List Stmt)) (fallback : Stmt) :
    Float64Dispatch.dispatchChain vr0 arms [fallback] = [dispatch arms fallback] := by
  cases arms <;> rfl

theorem dispatchChain_noDecl (arms : List (Nat × List Stmt)) (fallback : List Stmt)
    (hfallback : fallback.all CLoops.noDeclarations = true)
    (harms : ∀ a ∈ arms, a.2.all CLoops.noDeclarations = true) :
    (Float64Dispatch.dispatchChain vr0 arms fallback).all CLoops.noDeclarations = true := by
  induction arms with
  | nil => exact hfallback
  | cons a rest ih =>
    obtain ⟨j, arm⟩ := a
    rw [Float64Dispatch.dispatchChain_cons]
    have harm := harms (j, arm) (List.mem_cons_self ..)
    have hrest := ih (fun b hb => harms b (List.mem_cons_of_mem _ hb))
    simp only [List.all_eq_true] at harm hrest
    simp only [Runtime.branch, List.all_cons, List.all_nil, Bool.and_true]
    rw [CLoops.noDeclarations]
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_attach, forall_const, Subtype.forall]
    exact ⟨harm, hrest⟩

theorem dispatch_noDecl (arms : List (Nat × List Stmt)) (fallback : Stmt)
    (hfallback : CLoops.noDeclarations fallback = true)
    (harms : ∀ a ∈ arms, a.2.all CLoops.noDeclarations = true) :
    CLoops.noDeclarations (dispatch arms fallback) = true := by
  have h := dispatchChain_noDecl arms [fallback] (by simp [hfallback]) harms
  rw [dispatch_chain] at h
  simpa using h

theorem dispatch_closed (arms : List (Nat × List Stmt)) (fallback : Stmt)
    (hfallback : CLoops.noDeclarations fallback = true)
    (harms : ∀ a ∈ arms, a.2.all CLoops.noDeclarations = true) :
    CBodyEmbedding.closedBlocks (dispatch arms fallback) = true :=
  CBodyEmbedding.noDeclarations_closed _ (dispatch_noDecl arms fallback hfallback harms)

theorem fail_noDecl (message : String) : CLoops.noDeclarations (Runtime.fail message) = true := by
  simp [Runtime.fail, Runtime.ret, CLoops.noDeclarations]

/-! ### The getter body -/

/-- The remaining copy-loop suffix, shared by every value reference. -/
def getLoopSuffix : List Stmt :=
  [.declare "size_t" "k" (Runtime.n 0), CLoops.loop "k" (Runtime.v "expected") getCopyBody, Runtime.ok]

/-- The initial request check: a single value reference and non-null arrays. -/
def basicReject : Stmt :=
  Runtime.reject (Runtime.any [Runtime.nev (Runtime.v "nValueReferences") (Runtime.n 1),
    Runtime.eqv (Runtime.v "valueReferences") Expr.nullPointer,
    Runtime.eqv (Runtime.v "values") Expr.nullPointer])
    "Invalid Float64 array lengths or pointers"

/-- Explicit pointer leaves preserve the complete condition result, including
failure, without assumptions on the count expression or pointed-to storage. -/
theorem basic_condition_eq [interface : CInterface] (env : Locals) (heap : Heap)
    (refs buffer : Option Address) (nullType : interface.types "void *" = some .pointer)
    (refsBound : resolve env "valueReferences" = some (.pointer refs))
    (valuesBound : resolve env "values" = some (.pointer buffer)) :
    eval env heap (Runtime.any [Runtime.nev (Runtime.v "nValueReferences") (Runtime.n 1),
      Runtime.eqv (Runtime.v "valueReferences") Expr.nullPointer,
      Runtime.eqv (Runtime.v "values") Expr.nullPointer]) =
    eval env heap (Runtime.any [Runtime.nev (Runtime.v "nValueReferences") (Runtime.n 1),
      Runtime.negate (Runtime.v "valueReferences"), Runtime.negate (Runtime.v "values")]) := by
  let addresses : String → Option Address := fun name =>
    if name = "valueReferences" then refs else buffer
  have bound : ∀ name ∈ ["valueReferences", "values"],
      resolve env name = some (.pointer (addresses name)) := by
    intro name member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [addresses, refsBound, valuesBound]
  have tail := CPointerConditions.explicit_missing_eq env heap
    ["valueReferences", "values"] addresses bound nullType
  change eval env heap (Runtime.any [
    Runtime.eqv (Runtime.v "valueReferences") Expr.nullPointer,
    Runtime.eqv (Runtime.v "values") Expr.nullPointer]) =
    eval env heap (Runtime.any [
      Runtime.negate (Runtime.v "valueReferences"), Runtime.negate (Runtime.v "values")]) at tail
  change ((eval env heap (Runtime.nev (Runtime.v "nValueReferences") (Runtime.n 1))).bind
    fun a => a.truth.bind fun b => if b then some (boolean true) else
      (eval env heap (Runtime.any [
        Runtime.eqv (Runtime.v "valueReferences") Expr.nullPointer,
        Runtime.eqv (Runtime.v "values") Expr.nullPointer])).bind
        fun c => c.truth.bind fun d => some (boolean d)) = _
  rw [tail]
  rfl

/-- The count check between the dispatch and the copy loop. -/
def countReject : Stmt :=
  Runtime.reject (Runtime.nev (Runtime.v "nValues") (Runtime.v "expected")) "Invalid Float64 value count"


/-- Dispatch one value reference to its declared region, staging its pointer and
count; every other reference fails. -/
def getDispatch (reads : Float64Table.Reads) (i : Solve.Interface) : Stmt :=
  dispatch (Float64Table.getArms reads i) (Runtime.fail "Unknown value reference")

/-- The statements after the guard, run in the typed machine. -/
def getRest (reads : Float64Table.Reads) (i : Solve.Interface) : List Stmt :=
  [.declare "fmi3Float64 *" "src" Expr.nullPointer, .declare "size_t" "expected" (Runtime.n 0),
    getDispatch reads i, countReject] ++ getLoopSuffix

def getBody (reads : Float64Table.Reads) (i : Solve.Interface) : List Stmt :=
  Runtime.require .get ++ (basicReject :: getRest reads i)

def getFunction (reads : Float64Table.Reads) (i : Solve.Interface) : CTree.Function :=
  ⟨Float64Calls.signature false, getBody reads i, false⟩

/-- The getter body around an abstract value-reference dispatch statement: only
the dispatch depends on the declared interface. -/
def getBodyFor (dispatch : Stmt) : List Stmt :=
  Runtime.require .get ++ (basicReject ::
    [.declare "fmi3Float64 *" "src" Expr.nullPointer, .declare "size_t" "expected" (Runtime.n 0),
      dispatch, countReject] ++ getLoopSuffix)

theorem getDispatch_noDecl (reads : Float64Table.Reads) (i : Solve.Interface)
    (closedReads : (reads.derivative ++ reads.output).all CLoops.noDeclarations = true) :
    CLoops.noDeclarations (getDispatch reads i) = true :=
  dispatch_noDecl _ _ (fail_noDecl _) (Float64Table.getArms_noDecl reads i closedReads)

theorem getBody_closed (reads : Float64Table.Reads) (i : Solve.Interface)
    (closedReads : (reads.derivative ++ reads.output).all CLoops.noDeclarations = true) :
    (getFunction reads i).body.all CBodyEmbedding.closedBlocks = true := by
  have closed := CBodyEmbedding.noDeclarations_closed _ (getDispatch_noDecl reads i closedReads)
  simp only [CBodyEmbedding.closedBlocks] at closed
  simp [getFunction, getBody, getRest, closed, basicReject, countReject, getLoopSuffix, Runtime.require,
    Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject, Runtime.branch, Runtime.fail,
    Runtime.ret, Runtime.ok, getCopyBody, CBodyEmbedding.closedBlocks, CLoops.noDeclarations,
    CLoops.loop, CLoops.counterStep]

/-- The tensor profile evaluates `der(x)` through `rumoca_rhs` and the dense
Jacobian through `rumoca_square_jacobian_diag`, both over the record's state
volume. -/
def tensorReads (shape : Tensor.Shape) : Float64Table.Reads :=
  ⟨[TensorEntry.rhsCall (Runtime.n shape.volume)], [TensorEntry.jacobianCall (Runtime.n shape.volume) shape]⟩

theorem tensorReads_noDecl (shape : Tensor.Shape) :
    ((tensorReads shape).derivative ++ (tensorReads shape).output).all CLoops.noDeclarations = true := by
  simp [tensorReads, TensorEntry.rhsCall, TensorEntry.jacobianCall, CLoops.noDeclarations]


/-- Local bindings after the handle/lifecycle guard: the instance pointer. -/
def guardEnv (p refs buffer : Address) (n m : UInt64) : Locals :=
  CBody.bind (parameters (some p) (some refs) (some buffer) n m) "m" (.pointer (some p))

/-- Local bindings after the two staging declarations. -/
def declaredEnv (env0 : Locals) : Locals :=
  CBody.bind (CBody.bind env0 "src" (.pointer none)) "expected" (.integer 0)

/-- Local bindings after the dispatch has staged the region pointer and count. -/
def stagedEnv (env0 : Locals) (regionBase : Address) (count : Nat) : Locals :=
  CBody.bind (CBody.bind (declaredEnv env0) "src" (.pointer (some regionBase))) "expected" (.integer count)

/-- Types after the two staging declarations. -/
def declaredTypes (types0 : Types) : Types :=
  CLoops.bindType (CLoops.bindType types0 "src" .pointer) "expected" .size

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

/-- Fixed FMI typing discharges null comparison locally for the shared guard. -/
theorem basic_explicit_pass (heap : Heap) (p refs buffer : Address) (n m : UInt64)
    (nref : n.toNat = 1) :
    CBody.eval (guardEnv p refs buffer n m) heap
      (Runtime.any [Runtime.nev (Runtime.v "nValueReferences") (Runtime.n 1),
        Runtime.eqv (Runtime.v "valueReferences") Expr.nullPointer,
        Runtime.eqv (Runtime.v "values") Expr.nullPointer]) = some (boolean false) := by
  rw [basic_condition_eq _ _ (some refs) (some buffer) rfl
    (by simp [guardEnv, parameters, CBody.bind, resolve])
    (by simp [guardEnv, parameters, CBody.bind, resolve])]
  simp [Runtime.any, Runtime.negate, Runtime.nev, Runtime.v, Runtime.n,
    CBody.eval, CBody.evalWith, guardEnv, parameters, CBody.bind, CBody.resolve,
    CBody.comparison, boolean, Value.truth, nref]

/-- The getter function around an abstract dispatch statement. -/
def getFunctionFor (dispatch : Stmt) : CTree.Function :=
  ⟨Float64Calls.signature false, getBodyFor dispatch, false⟩

/-- The guard of every profile's getter, executed in memory, reaches the typed
statements after it. -/
theorem guard_reaches_for (dispatch : Stmt)
    (closed : (getFunctionFor dispatch).body.all CBodyEmbedding.closedBlocks = true)
    (program : CCalls.Events.Program E) (heap : Heap) (p refs buffer : Address) (n m : UInt64)
    (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunctionFor dispatch)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (nref : n.toNat = 1) (stack : CCalls.Typed.Continuation) :
    ∃ types0, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap stack)
      (.body (.running ([.declare "fmi3Float64 *" "src" Expr.nullPointer, .declare "size_t" "expected" (Runtime.n 0),
          dispatch, countReject] ++ getLoopSuffix) (guardEnv p refs buffer n m) types0 heap)
        "fmi3Status" stack) := by
  let rest : List Stmt := [.declare "fmi3Float64 *" "src" Expr.nullPointer,
    .declare "size_t" "expected" (Runtime.n 0), dispatch, countReject] ++ getLoopSuffix
  have accepted := LifecycleGuard.accept (parameters (some p) (some refs) (some buffer) n m) heap p
    .get kind mode (basicReject :: rest)
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  have hc := basic_explicit_pass heap p refs buffer n m nref
  have prefix_run : CBody.run 4 (.running (getBodyFor dispatch)
      (parameters (some p) (some refs) (some buffer) n m) heap) =
      some (.running rest (guardEnv p refs buffer n m) heap) := by
    rw [show getBodyFor dispatch = Runtime.require .get ++ basicReject :: rest from rfl,
      show (4 : Nat) = 3 + 1 from rfl, CBody.run_add, accepted, Option.bind_some]
    exact run_one (reject_false (guardEnv p refs buffer n m) heap _
      "Invalid Float64 array lengths or pointers" rest hc)
  exact CCalls.Events.body_prefix_reaches program (getFunctionFor dispatch)
    (arguments (some p) (some refs) (some buffer) n m) (parameters (some p) (some refs) (some buffer) n m)
    (guardEnv p refs buffer n m) heap heap rest stack 4 defined
    (parameters_bound false _ _ _ _ _) closed prefix_run

/-- The guard of the table-driven getter, executed in memory, reaches the typed
statements after it. -/
theorem guard_reaches (reads : Float64Table.Reads) (iface : Solve.Interface)
    (closedReads : (reads.derivative ++ reads.output).all CLoops.noDeclarations = true)
    (program : CCalls.Events.Program E) (heap : Heap) (p refs buffer : Address) (n m : UInt64)
    (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction reads iface)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (nref : n.toNat = 1) (stack : CCalls.Typed.Continuation) :
    ∃ types0, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap stack)
      (.body (.running (getRest reads iface) (guardEnv p refs buffer n m) types0 heap)
        "fmi3Status" stack) :=
  guard_reaches_for (getDispatch reads iface) (getBody_closed reads iface closedReads) program heap p refs
    buffer n m kind mode defined hk hm allowed nref stack

/-- The two staging declarations of every profile's getter, executed in the typed machine. -/
theorem declares_reaches_for (program : CCalls.Events.Program E) (dispatch : Stmt)
    (env0 : Locals) (types0 : Types) (heap : Heap)
    (stack : CCalls.Typed.Continuation) (fresh_src : env0 "src" = none) (fresh_exp : env0 "expected" = none) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running ([.declare "fmi3Float64 *" "src" Expr.nullPointer, .declare "size_t" "expected" (Runtime.n 0),
          dispatch, countReject] ++ getLoopSuffix) env0 types0 heap) "fmi3Status" stack)
      (.body (.running (dispatch :: countReject :: getLoopSuffix)
        (declaredEnv env0) (declaredTypes types0) heap) "fmi3Status" stack) := by
  have s1 : CLoops.next (.running ([.declare "fmi3Float64 *" "src" Expr.nullPointer, .declare "size_t" "expected" (Runtime.n 0),
          dispatch, countReject] ++ getLoopSuffix) env0 types0 heap) =
      some (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        dispatch :: countReject :: getLoopSuffix)
        (CBody.bind env0 "src" (.pointer none)) (CLoops.bindType types0 "src" .pointer) heap) :=
    declare_step_e env0 types0 heap "fmi3Float64 *" "src" Expr.nullPointer .pointer (.pointer none)
      (.pointer none) _ fresh_src rfl
      (by simp [Expr.nullPointer, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.expressionCast, CBody.zeroLiteral]) rfl
  have s2 : CLoops.next (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        dispatch :: countReject :: getLoopSuffix)
        (CBody.bind env0 "src" (.pointer none)) (CLoops.bindType types0 "src" .pointer) heap) =
      some (.running (dispatch :: countReject :: getLoopSuffix)
        (declaredEnv env0) (declaredTypes types0) heap) :=
    declare_step_e (CBody.bind env0 "src" (.pointer none)) (CLoops.bindType types0 "src" .pointer) heap
      "size_t" "expected" (Runtime.n 0) .size (.integer 0) (.integer 0) _
      (by simp [CBody.bind, fresh_exp]) rfl (by simp [Runtime.n, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith]) rfl
  exact .next (CCalls.Events.body_step program s1 "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s2 "fmi3Status" stack) (.refl _))

/-- The two staging declarations of the table-driven getter. -/
theorem declares_reaches (program : CCalls.Events.Program E) (reads : Float64Table.Reads)
    (iface : Solve.Interface) (env0 : Locals) (types0 : Types) (heap : Heap)
    (stack : CCalls.Typed.Continuation) (fresh_src : env0 "src" = none) (fresh_exp : env0 "expected" = none) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (getRest reads iface) env0 types0 heap) "fmi3Status" stack)
      (.body (.running (getDispatch reads iface :: countReject :: getLoopSuffix)
        (declaredEnv env0) (declaredTypes types0) heap) "fmi3Status" stack) :=
  declares_reaches_for program (getDispatch reads iface) env0 types0 heap stack fresh_src fresh_exp

/-- The count check and copy loop, run in the typed machine after the dispatch
has staged the region pointer and count. Region-agnostic. -/
theorem get_tail_reaches (program : CCalls.Events.Program E) (env0 : Locals) (types0 : Types)
    (heap : Heap) (regionBase buffer : Address) (rshape : Tensor.Shape) (regionValues : Values rshape)
    (m : UInt64) (stack : CCalls.Typed.Continuation) (bounded : rshape.volume < 2 ^ 64)
    (matched : m.toNat = rshape.volume)
    (srcBound : resolve (stagedEnv env0 regionBase rshape.volume) "src" = some (.pointer (some regionBase)))
    (expBound : resolve (stagedEnv env0 regionBase rshape.volume) "expected" = some (.integer rshape.volume))
    (valuesBound : resolve (stagedEnv env0 regionBase rshape.volume) "values" = some (.pointer (some buffer)))
    (nvalBound : resolve (stagedEnv env0 regionBase rshape.volume) "nValues" = some (.integer m.toNat))
    (fmiok : (stagedEnv env0 regionBase rshape.volume) "fmi3OK" = none)
    (fresh_k : (stagedEnv env0 regionBase rshape.volume) "k" = none)
    (readable : Reads heap regionBase regionValues)
    (writable : Writable heap buffer rshape.volume)
    (separate : ∀ a < rshape.volume, ∀ b < rshape.volume, regionBase.index a ≠ buffer.index b) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (countReject :: getLoopSuffix) (stagedEnv env0 regionBase rshape.volume) types0 heap)
        "fmi3Status" stack)
      (.returning (.integer 0) (written heap buffer regionValues rshape.volume) stack) := by
  set env := stagedEnv env0 regionBase rshape.volume with henv
  have hcount : CLoops.eval env types0 heap (Runtime.nev (Runtime.v "nValues") (Runtime.v "expected")) =
      some (boolean false) := by
    simp [Runtime.nev, Runtime.v, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, nvalBound, expBound, matched,
      CBody.comparison, boolean]
  have s1 : CLoops.next (.running (countReject :: getLoopSuffix) env types0 heap) =
      some (.running getLoopSuffix env types0 heap) := by
    have := cbranch_false env types0 heap _ [Runtime.fail "Invalid Float64 value count"] [] getLoopSuffix
      (by simp [Runtime.fail, Runtime.ret, CLoops.noDeclarations]) hcount
    simpa [countReject, Runtime.reject, Runtime.branch] using this
  refine .next (CCalls.Events.body_step program s1 "fmi3Status" stack) ?_
  refine .next (CCalls.Events.body_step program
    (CLoops.counter_initialize env types0 heap "k"
      (CLoops.loop "k" (Runtime.v "expected") getCopyBody :: [Runtime.ok]) fresh_k rfl) _ stack) ?_
  refine (getCopy_reaches program env (CLoops.bindType types0 "k" .size) heap regionBase buffer
    regionValues [Runtime.ok] _ stack bounded (by simp [CLoops.bindType]) expBound srcBound valuesBound
    readable writable separate).trans ?_
  exact DerivativeCalls.finish program _ (counterEnv env "k" rshape.volume) (CLoops.bindType types0 "k" .size)
    stack (by simp [counterEnv, CBody.bind, fmiok])

end

/-! ### Dispatch staging -/

section
variable [interface : CInterface]

/-- `valueReferences[0] == j` in the typed machine, when the stored reference is `r`. -/
theorem cvr0_cmp (env : Locals) (types : Types) (heap : Heap) (refs : Address) (r j : Nat)
    (rBound : resolve env "valueReferences" = some (.pointer (some refs)))
    (refRead : load heap (refs.index 0) = some (.integer r)) :
    CLoops.eval env types heap (Runtime.eqv vr0 (Runtime.n j)) = some (boolean (decide ((r : Int) = j))) :=
  CBodyEmbedding.eval_refines env types heap _ _ (vr0_cmp env heap refs r j rBound refRead)

/-- `valueReferences[0]` equals a different literal than the stored reference. -/
theorem cvr0_ne (env : Locals) (types : Types) (heap : Heap) (refs : Address) (r j : Nat)
    (rBound : resolve env "valueReferences" = some (.pointer (some refs)))
    (refRead : load heap (refs.index 0) = some (.integer r)) (hne : r ≠ j) :
    CLoops.eval env types heap (Runtime.eqv vr0 (Runtime.n j)) = some (boolean false) := by
  rw [cvr0_cmp env types heap refs r j rBound refRead]
  simp [Nat.cast_inj, hne]

/-- `valueReferences[0]` equals the stored reference. -/
theorem cvr0_eq (env : Locals) (types : Types) (heap : Heap) (refs : Address) (r : Nat)
    (rBound : resolve env "valueReferences" = some (.pointer (some refs)))
    (refRead : load heap (refs.index 0) = some (.integer r)) :
    CLoops.eval env types heap (Runtime.eqv vr0 (Runtime.n r)) = some (boolean true) := by
  rw [cvr0_cmp env types heap refs r r rBound refRead]; simp

/-- The first cell a region addresses in the record at `p`. -/
def regionBase (p : Address) (r : Region) : Address := (p.member r.member).index r.offset

theorem regionBase_zero (p : Address) (member : String) (count : Nat) :
    regionBase p ⟨member, 0, count⟩ = p.member member := Address.index_zero _

/-- A region of the scalar time base starts at offset `0`. -/
def Addressable (r : Region) : Prop := r.member = timeName → r.offset = 0

/-- The staged pointer evaluates to the region's first cell, heap-independently:
the scalar time base is `&(m->time)`, every other region `&(m->member)[offset]`. -/
theorem eval_pointer (env : Locals) (heap : Heap) (p : Address) (r : Region)
    (mResolves : CBody.resolve env "m" = some (.pointer (some p))) (addressable : Addressable r) :
    CBody.eval env heap (pointer r.member r.offset) = some (.pointer (some (regionBase p r))) := by
  unfold pointer regionBase
  split
  · rename_i time
    rw [addressable time, Address.index_zero]
    simp [Runtime.field, Runtime.v, CBody.eval, CBody.evalWith, CBody.lvalueWith, mResolves, Value.address]
  · have nonnegative : ¬ ((r.offset : Int) < 0) := by omega
    simp [Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.evalWith, CBody.lvalueWith, mResolves,
      Value.address, nonnegative]

/-- The dispatch reaches the arm whose reference is the stored one. -/
theorem dispatch_reaches (program : CCalls.Events.Program E) (env : Locals) (types : Types) (heap : Heap)
    (refs : Address) (r : Nat) (resultType : String) (stack : CCalls.Typed.Continuation)
    (rBound : resolve env "valueReferences" = some (.pointer (some refs)))
    (refRead : load heap (refs.index 0) = some (.integer r))
    (fallback : Stmt) (hfallback : CLoops.noDeclarations fallback = true)
    (arms : List (Nat × List Stmt)) (harms : ∀ a ∈ arms, a.2.all CLoops.noDeclarations = true)
    (arm : List Stmt) (found : arms.lookup r = some arm) (rest : List Stmt) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (dispatch arms fallback :: rest) env types heap) resultType stack)
      (.body (.running (arm ++ rest) env types heap) resultType stack) := by
  induction arms with
  | nil => cases found
  | cons a tl ih =>
    obtain ⟨j, yes⟩ := a
    have safe : (yes.all CLoops.noDeclarations &&
        [dispatch tl fallback].all CLoops.noDeclarations) = true := by
      have hyes := harms (j, yes) (List.mem_cons_self ..)
      simp [hyes, dispatch_noDecl tl fallback hfallback (fun b hb => harms b (List.mem_cons_of_mem _ hb))]
    have shape : dispatch ((j, yes) :: tl) fallback =
        .branch (Runtime.eqv vr0 (Runtime.n j)) yes [dispatch tl fallback] := by
      show Runtime.branch _ yes (Float64Dispatch.dispatchChain vr0 tl [fallback]) = _
      rw [dispatch_chain]; rfl
    rw [shape]
    by_cases same : r = j
    · subst same
      have : yes = arm := by simpa [List.lookup] using found
      subst this
      exact .next (CCalls.Events.body_step program
        (cbranch_true env types heap _ _ _ rest safe (cvr0_eq env types heap refs r rBound refRead))
        resultType stack) (.refl _)
    · have hb : (r == j) = false := by simpa using same
      have next : tl.lookup r = some arm := by
        simpa [List.lookup, hb] using found
      refine .next (CCalls.Events.body_step program
        (cbranch_false env types heap _ _ _ rest safe (cvr0_ne env types heap refs r j rBound refRead same))
        resultType stack) ?_
      exact ih (fun b hb => harms b (List.mem_cons_of_mem _ hb)) next

/-- The two dispatch assignments stage the region pointer and count. -/
theorem stage_reaches (program : CCalls.Events.Program E) (env0 : Locals) (types0 : Types) (heap : Heap)
    (p : Address) (r : Region) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (bounded : r.count < 2 ^ 64)
    (mBound : env0 "m" = some (.pointer (some p))) (addressable : Addressable r) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (getArm r ++ rest) (declaredEnv env0) (declaredTypes types0) heap)
        "fmi3Status" stack)
      (.body (.running rest (stagedEnv env0 (regionBase p r) r.count) (declaredTypes types0) heap)
        "fmi3Status" stack) := by
  have addr : CLoops.eval (declaredEnv env0) (declaredTypes types0) heap (pointer r.member r.offset) =
      some (.pointer (some (regionBase p r))) := by
    apply CBodyEmbedding.eval_refines
    exact eval_pointer (declaredEnv env0) heap p r
      (by simp [declaredEnv, CBody.bind, CBody.resolve, mBound]) addressable
  have s1 : CLoops.next (.running (getArm r ++ rest) (declaredEnv env0) (declaredTypes types0) heap) =
      some (.running (.assign (Runtime.v "expected") (Runtime.n r.count) :: rest)
        (CBody.bind (declaredEnv env0) "src" (.pointer (some (regionBase p r)))) (declaredTypes types0) heap) := by
    have := CLoops.assign_local (declaredEnv env0) (declaredTypes types0) heap "src"
      (pointer r.member r.offset) (.assign (Runtime.v "expected") (Runtime.n r.count) :: rest)
      (.pointer none) (.pointer (some (regionBase p r))) (.pointer (some (regionBase p r))) .pointer
      (by simp [declaredEnv, CBody.bind]) (by simp [declaredTypes, CLoops.bindType]) addr rfl
    simpa [getArm, Runtime.v] using this
  have s2 : CLoops.next (.running (.assign (Runtime.v "expected") (Runtime.n r.count) :: rest)
        (CBody.bind (declaredEnv env0) "src" (.pointer (some (regionBase p r)))) (declaredTypes types0) heap) =
      some (.running rest (stagedEnv env0 (regionBase p r) r.count) (declaredTypes types0) heap) := by
    have := CLoops.assign_local (CBody.bind (declaredEnv env0) "src" (.pointer (some (regionBase p r))))
      (declaredTypes types0) heap "expected" (Runtime.n r.count) rest (.integer 0) (.integer r.count)
      (.integer r.count) .size (by simp [declaredEnv, CBody.bind]) (by simp [declaredTypes, CLoops.bindType])
      (by simp [Runtime.n, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith])
      (CLoops.convert_size_nat r.count bounded)
    simpa [Runtime.v, stagedEnv] using this
  exact .next (CCalls.Events.body_step program s1 "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s2 "fmi3Status" stack) (.refl _))

end

/-! ### The complete getter for a declared value reference -/

section
variable [static : StaticLiterals]
private local instance getInterface : CInterface := cInterface static.addresses

/-- The complete getter for one value reference whose table arm stages the region
`⟨member, offset, rshape.volume⟩`: it writes exactly the region's values into
the caller buffer and changes no other cell. -/
theorem get_reaches (reads : Float64Table.Reads) (iface : Solve.Interface)
    (closedReads : (reads.derivative ++ reads.output).all CLoops.noDeclarations = true) (program : CCalls.Events.Program E) (heap : Heap)
    (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (reference : Nat)
    (member : String) (offset : Nat) (rshape : Tensor.Shape) (regionValues : Values rshape)
    (stack : CCalls.Typed.Continuation)
    (found : (Float64Table.getArms reads iface).lookup reference = some (getArm ⟨member, offset, rshape.volume⟩))
    (addressable : Addressable ⟨member, offset, rshape.volume⟩)
    (nref : n.toNat = 1) (matched : m.toNat = rshape.volume) (bounded : rshape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction reads iface)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load heap (refs.index 0) = some (.integer reference))
    (readable : Reads heap ((p.member member).index offset) regionValues)
    (writable : Writable heap buffer rshape.volume)
    (separate : ∀ a < rshape.volume, ∀ b < rshape.volume,
      ((p.member member).index offset).index a ≠ buffer.index b) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap stack)
      (.returning (.integer 0) (written heap buffer regionValues rshape.volume) stack) := by
  obtain ⟨types0, entered⟩ := guard_reaches reads iface closedReads program heap p refs buffer n m kind mode
    defined hk hm allowed nref stack
  refine entered.trans ((declares_reaches program reads iface (guardEnv p refs buffer n m) types0
    heap stack (by simp [guardEnv, parameters, CBody.bind]) (by simp [guardEnv, parameters, CBody.bind])).trans ?_)
  refine (dispatch_reaches program _ _ heap refs reference "fmi3Status" stack
    (by simp [declaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve]) refRead _ (fail_noDecl _)
    _ (Float64Table.getArms_noDecl reads iface closedReads) _ found _).trans ?_
  refine (stage_reaches program (guardEnv p refs buffer n m) types0 heap p ⟨member, offset, rshape.volume⟩
    (countReject :: getLoopSuffix) stack bounded (by simp [guardEnv, CBody.bind]) addressable).trans ?_
  exact get_tail_reaches program (guardEnv p refs buffer n m) (declaredTypes types0) heap
    ((p.member member).index offset) buffer rshape regionValues m stack bounded matched
    (by simp [stagedEnv, regionBase, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind]) readable writable separate

/-- The getter's whole behavior for one declared value reference. -/
theorem get_behaviors (reads : Float64Table.Reads) (iface : Solve.Interface)
    (closedReads : (reads.derivative ++ reads.output).all CLoops.noDeclarations = true) (program : CCalls.Events.Program E) (heap : Heap)
    (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (reference : Nat)
    (member : String) (offset : Nat) (rshape : Tensor.Shape) (regionValues : Values rshape)
    (found : (Float64Table.getArms reads iface).lookup reference = some (getArm ⟨member, offset, rshape.volume⟩))
    (addressable : Addressable ⟨member, offset, rshape.volume⟩)
    (nref : n.toNat = 1) (matched : m.toNat = rshape.volume)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction reads iface)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load heap (refs.index 0) = some (.integer reference))
    (readable : Reads heap ((p.member member).index offset) regionValues)
    (writable : Writable heap buffer rshape.volume)
    (separate : ∀ a < rshape.volume, ∀ b < rshape.volume,
      ((p.member member).index offset).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap buffer regionValues rshape.volume⟩ :=
  (CCalls.Events.internal_prefix program (get_reaches reads iface closedReads program heap p refs buffer n m kind mode
    reference member offset rshape regionValues .done found addressable nref matched
    (matched ▸ m.toNat_lt_size) defined hk hm allowed refRead readable writable separate)
    (CCalls.Events.return_forced program _ _)).behaviors behavior

end

/-! ### Instance-record readability and writability -/

theorem core_reads_time (backing : Heap) (pool : Address) (i : Nat) (shape : Tensor.Shape)
    (time : Values Tensor.scalar) (state input : Values shape) :
    Reads (TensorInstance.core backing pool i shape time state input) (TensorInstance.field pool i timeName) time := by
  unfold TensorInstance.core TensorInstance.field
  exact reads_place_other (by decide +kernel) (reads_place_other (by decide +kernel)
    (reads_place_other (by decide +kernel) (place_reads _ _ _ _)))

theorem reads_time (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Tensor.Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (output : Option (Values oshape)) :
    Reads (TensorInstance.store backing pool i shape oshape time state input output)
      (TensorInstance.field pool i timeName) time := by
  cases output with
  | none => exact core_reads_time backing pool i shape time state input
  | some J => exact reads_place_other (by decide +kernel) (core_reads_time backing pool i shape time state input)

theorem reads_output (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Tensor.Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (J : Values oshape) :
    Reads (TensorInstance.store backing pool i shape oshape time state input (some J))
      (TensorInstance.field pool i outputName) J := by
  show Reads (place (TensorInstance.core backing pool i shape time state input)
    ((TensorInstance.record pool i).member outputName) oshape true (some J))
    (TensorInstance.field pool i outputName) J
  unfold TensorInstance.field
  exact place_reads _ _ _ _

theorem core_writable_state (backing : Heap) (pool : Address) (i : Nat) (shape : Tensor.Shape)
    (time : Values Tensor.scalar) (state input : Values shape) :
    Writable (TensorInstance.core backing pool i shape time state input)
      (TensorInstance.field pool i stateName) shape.volume := by
  unfold TensorInstance.core TensorInstance.field
  exact writable_place_other (by decide +kernel)
    (writable_place_other (by decide +kernel) (place_writable _ _ _ (some state)))

theorem writable_state (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Tensor.Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (output : Option (Values oshape)) :
    Writable (TensorInstance.store backing pool i shape oshape time state input output)
      (TensorInstance.field pool i stateName) shape.volume := by
  cases output with
  | none => exact core_writable_state backing pool i shape time state input
  | some J =>
    show Writable (place (TensorInstance.core backing pool i shape time state input)
      ((TensorInstance.record pool i).member outputName) oshape true (some J))
      (TensorInstance.field pool i stateName) shape.volume
    exact writable_place_other (show TensorInstance.stateName ≠ TensorInstance.outputName by decide +kernel)
      (core_writable_state backing pool i shape time state input)

/-! ### The getter bound to the static tensor instance record -/

section
variable [static : StaticLiterals]
private local instance instGetInterface : CInterface := cInterface static.addresses
variable (program : CCalls.Events.Program E) (backing : Heap) (pool : Address) (i : Nat)
  (shape oshape : Tensor.Shape) (time : Values Tensor.scalar) (state input : Values shape)
  (output : Option (Values oshape)) (refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode)
  (iface : Solve.Interface) (reference : Nat) (reads : Float64Table.Reads)
  (closedReads : (reads.derivative ++ reads.output).all CLoops.noDeclarations = true)
include closedReads

/-- The getter reading the state region of instance `i`: it writes exactly
the state into the caller buffer and changes no instance cell. -/
theorem get_instance_behaviors_state (found : (Float64Table.getArms reads iface).lookup reference =
      some (getArm ⟨stateName, 0, shape.volume⟩))
    (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction reads iface)))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load (TensorInstance.store backing pool i shape oshape time state input output)
      (refs.index 0) = some (.integer reference))
    (writable : Writable (TensorInstance.store backing pool i shape oshape time state input output)
      buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i stateName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
        (TensorInstance.store backing pool i shape oshape time state input output) .done) behavior ↔
      behavior = .terminates []
        ⟨.integer 0, written (TensorInstance.store backing pool i shape oshape time state input output)
          buffer state shape.volume⟩ :=
  get_behaviors reads iface closedReads program _ (TensorInstance.record pool i) refs buffer n m kind mode reference stateName 0
    shape state found (fun _ => rfl) nref nval defined hk hm allowed refRead
    (by rw [Address.index_zero]; exact TensorInstance.reads_state backing pool i shape oshape time state input output)
    writable (by simpa only [Address.index_zero] using separate) behavior

/-- The getter reading the input region of instance `i`. -/
theorem get_instance_behaviors_input (found : (Float64Table.getArms reads iface).lookup reference =
      some (getArm ⟨inputName, 0, shape.volume⟩))
    (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction reads iface)))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load (TensorInstance.store backing pool i shape oshape time state input output)
      (refs.index 0) = some (.integer reference))
    (writable : Writable (TensorInstance.store backing pool i shape oshape time state input output)
      buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i inputName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
        (TensorInstance.store backing pool i shape oshape time state input output) .done) behavior ↔
      behavior = .terminates []
        ⟨.integer 0, written (TensorInstance.store backing pool i shape oshape time state input output)
          buffer input shape.volume⟩ :=
  get_behaviors reads iface closedReads program _ (TensorInstance.record pool i) refs buffer n m kind mode reference inputName 0
    shape input found (fun _ => rfl) nref nval defined hk hm allowed refRead
    (by rw [Address.index_zero]; exact TensorInstance.reads_input backing pool i shape oshape time state input output)
    writable (by simpa only [Address.index_zero] using separate) behavior

/-- The getter reading the time base of instance `i`. -/
theorem get_instance_behaviors_time (found : (Float64Table.getArms reads iface).lookup reference =
      some (getArm ⟨timeName, 0, Tensor.scalar.volume⟩))
    (nref : n.toNat = 1) (nval : m.toNat = 1)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction reads iface)))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load (TensorInstance.store backing pool i shape oshape time state input output)
      (refs.index 0) = some (.integer reference))
    (writable : Writable (TensorInstance.store backing pool i shape oshape time state input output) buffer 1)
    (separate : ∀ a < 1, ∀ b < 1, (TensorInstance.field pool i timeName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
        (TensorInstance.store backing pool i shape oshape time state input output) .done) behavior ↔
      behavior = .terminates []
        ⟨.integer 0, written (TensorInstance.store backing pool i shape oshape time state input output)
          buffer time 1⟩ :=
  get_behaviors reads iface closedReads program _ (TensorInstance.record pool i) refs buffer n m kind mode reference timeName 0
    Tensor.scalar time found (fun _ => rfl) nref nval defined hk hm allowed refRead
    (by rw [Address.index_zero]; exact reads_time backing pool i shape oshape time state input output)
    writable (by simpa only [Address.index_zero] using separate) behavior

end

/-! ### Calculated variables are evaluated when they are read

The arms of the calculated variables (`Float64Table.Reads`) call the prepared
kernel entries before staging the region, so the value returned is the one the prepared model
calculates from the current input and state, never a value left in the region
by an earlier call. -/

section
variable [static : StaticLiterals]
private local instance computedInterface : CInterface := cInterface static.addresses
variable (program : CCalls.Events.Program E)

/-- The derivative evaluation enters `rumoca_rhs` over the instance regions with
the record's state volume, from any locals that bind `m` and do not shadow the
entry name. -/
theorem rhs_read_enter (shape : Tensor.Shape) (env : Locals) (prior : Types) (heap : Heap) (p : Address)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (instanceValue : env "m" = some (.pointer (some p))) (unbound : env "rumoca_rhs" = none) :
    CCalls.Events.internalNext program
      (.body (.running (TensorEntry.rhsCall (Runtime.n shape.volume) :: rest) env prior heap) resultType stack) =
      some (.calling "rumoca_rhs"
        [.pointer (some (p.member stateName)), .pointer (some (p.member inputName)),
         .pointer (some (p.member derivativeName)), .integer shape.volume] heap
        (.caller .discard rest env prior resultType stack)) := by
  simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions,
    CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, TensorEntry.rhsCall, TensorEntry.rhsArgs,
    Runtime.call, Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.evalWith,
    CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, CBody.lvalueWith,
    CCalls.Events.enterCallWith, CCalls.Events.resolveWith, CCalls.Indirect.operand,
    CCalls.Indirect.resolveWith, CCalls.argumentsWith, CBody.resolve, CBody.constants,
    Value.address, instanceValue, unbound]

/-- The Jacobian evaluation enters `rumoca_square_jacobian_diag` over the instance
regions with the record's state volume and matrix cell count. -/
theorem jacobian_read_enter (shape : Tensor.Shape) (env : Locals) (prior : Types) (heap : Heap)
    (p : Address) (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (instanceValue : env "m" = some (.pointer (some p)))
    (unbound : env "rumoca_square_jacobian_diag" = none) :
    CCalls.Events.internalNext program
      (.body (.running (TensorEntry.jacobianCall (Runtime.n shape.volume) shape :: rest) env prior heap)
        resultType stack) =
      some (.calling "rumoca_square_jacobian_diag"
        [.pointer (some (p.member inputName)), .pointer (some (p.member outputName)),
         .integer shape.volume, .integer (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume] heap
        (.caller .discard rest env prior resultType stack)) := by
  simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions,
    CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, TensorEntry.jacobianCall,
    TensorEntry.jacobianArgs, Runtime.call, Runtime.region, Runtime.field, Runtime.v, Runtime.n,
    CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt,
    CDeclaredMembers.fieldAt, CBody.lvalueWith, CCalls.Events.enterCallWith, CCalls.Events.resolveWith,
    CCalls.Indirect.operand, CCalls.Indirect.resolveWith, CCalls.argumentsWith, CBody.resolve,
    CBody.constants, Value.address, instanceValue, unbound]

/-- A call returning to a discarding caller resumes the caller's statements. -/
theorem resume_discard (heap : Heap) (rest : List Stmt) (env : Locals) (prior : Types)
    (resultType : String) (stack : CCalls.Typed.Continuation) :
    CCalls.Events.internalNext program
      (.returning .void heap (.caller .discard rest env prior resultType stack)) =
      some (.body (.running rest env prior heap) resultType stack) := by
  simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions,
    CCalls.Typed.resumeWith]

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile in
/-- Reading `der(x)` of instance `i`: the getter evaluates the prepared derivative
from the instance's state and input, returns it in the caller buffer with
`fmi3OK`, leaves it in the `der(x)` region and preserves every other instance.
This holds whatever the `der(x)` region held before the call. -/
theorem get_deriv_reaches (shape oshape : Tensor.Shape) (iface : Solve.Interface) (reference : Nat)
    (arm : (Float64Table.getArms (tensorReads shape) iface).lookup reference =
      some (TensorEntry.rhsCall (Runtime.n shape.volume) :: getArm ⟨derivativeName, 0, shape.volume⟩)) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state input result : Values shape) (output : Option (Values oshape))
    (refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (nref : n.toNat = 1) (nval : m.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction (tensorReads shape) iface)))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load (TensorInstance.store backing pool i shape oshape time state input output)
      (refs.index 0) = some (.integer reference))
    (executed : Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment state input) result)
    (writable : Writable (TensorInstance.store backing pool i shape oshape time state input output)
      buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape))
        (TensorInstance.store backing pool i shape oshape time state input output) .done) v →
      CCalls.Events.Resolves program v) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName) result ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          backing ((TensorInstance.field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
          (TensorInstance.store backing pool i shape oshape time state input output) stack)
        (.returning (.integer 0) (written finalHeap buffer result shape.volume) stack) := by
  set H := TensorInstance.store backing pool i shape oshape time state input output with hH
  set p := TensorInstance.record pool i with hp
  obtain ⟨types0, entered⟩ := guard_reaches (tensorReads shape) iface (tensorReads_noDecl shape) program H p
    refs buffer n m kind mode defined hk hm allowed nref stack
  have declared := declares_reaches program (tensorReads shape) iface (guardEnv p refs buffer n m)
    types0 H stack (by simp [guardEnv, parameters, CBody.bind]) (by simp [guardEnv, parameters, CBody.bind])
  set env := declaredEnv (guardEnv p refs buffer n m) with henv
  set rest := countReject :: getLoopSuffix with hrest
  have nav := dispatch_reaches program env (declaredTypes types0) H refs reference "fmi3Status" stack
    (by simp [henv, declaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve]) refRead (Runtime.fail "Unknown value reference") (fail_noDecl _)
    _ (Float64Table.getArms_noDecl (tensorReads shape) iface (tensorReads_noDecl shape)) _ arm rest
  have enterStep := rhs_read_enter program shape env (declaredTypes types0) H p
    (getArm ⟨derivativeName, 0, shape.volume⟩ ++ rest) "fmi3Status" stack
    (by simp [henv, declaredEnv, guardEnv, CBody.bind])
    (by simp [henv, declaredEnv, guardEnv, parameters, CBody.bind])
  have argsEq : [Value.pointer (some (p.member stateName)), .pointer (some (p.member inputName)),
      .pointer (some (p.member derivativeName)), .integer shape.volume] =
      Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
        (TensorInstanceRhs.args pool i shape) := by
    rw [hp]; rfl
  rw [argsEq] at enterStep
  obtain ⟨finalHeap, reads, _writableDeriv, frameH, others, ran⟩ :=
    TensorInstanceRhs.derivative_writes_events (shape := shape) definitions program linked library found
      backing pool i oshape time state input result output bounded executed resolves
      (.caller .discard (getArm ⟨derivativeName, 0, shape.volume⟩ ++ rest) env (declaredTypes types0) "fmi3Status" stack)
  have writableFinal : Writable finalHeap buffer shape.volume := by
    intro b hb
    obtain ⟨old, ho⟩ := writable b hb
    exact ⟨old, (frameH (buffer.index b)
      (TensorInstanceRhs.buffer_outside pool i buffer b hb separate)).trans ho⟩
  have staged := stage_reaches program (guardEnv p refs buffer n m) types0 finalHeap p
    ⟨derivativeName, 0, shape.volume⟩ rest stack bounded (by simp [guardEnv, CBody.bind]) (fun _ => rfl)
  rw [regionBase_zero] at staged
  have tail := get_tail_reaches program (guardEnv p refs buffer n m) (declaredTypes types0) finalHeap
    (p.member derivativeName) buffer shape result m stack bounded nval
    (by simp [stagedEnv, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind]) reads writableFinal separate
  refine ⟨finalHeap, reads, others, entered.trans (declared.trans (nav.trans ?_))⟩
  exact .next enterStep (ran.trans (.next (resume_discard program _ _ _ _ _ _) (staged.trans tail)))

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile in
/-- Reading the dense Jacobian `J` of instance `i`: the getter evaluates the
prepared square-Jacobian diagonal from the instance's input, returns
`diag(2*u)` in the caller buffer with `fmi3OK`, leaves it in the `J` region and
preserves every other cell outside that region. This holds whatever the `J`
region held before the call. -/
theorem get_output_reaches (shape : Tensor.Shape) (iface : Solve.Interface) (reference : Nat)
    (arm : (Float64Table.getArms (tensorReads shape) iface).lookup reference =
      some (TensorEntry.jacobianCall (Runtime.n shape.volume) shape ::
        getArm ⟨outputName, 0, (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume⟩)) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (jacFound : definitions Rumoca.CTensor.SquareDiagonal.function.signature.name = some Rumoca.CTensor.SquareDiagonal.function)
    (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state input : Values shape)
    (J : Values (Rumoca.Tensor.matrixShape shape.volume shape.volume))
    (refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (nref : n.toNat = 1) (nval : m.toNat = (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume)
    (bounded2 : (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction (tensorReads shape) iface)))
    (hk : load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load (TensorInstance.store backing pool i shape
      (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input (some J))
      (refs.index 0) = some (.integer reference))
    (writable : Writable (TensorInstance.store backing pool i shape
      (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input (some J))
      buffer (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume)
    (separate : ∀ a < (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume,
      ∀ b < (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume,
      (TensorInstance.field pool i outputName).index a ≠ buffer.index b)
    (adds : ∀ k : Fin shape.volume,
      Binary64.Adds input[k] input[k] (.finite (Rumoca.CTensor.SquareDiagonal.doubled input)[k]))
    (jacResolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling Rumoca.CTensor.SquareDiagonal.function.signature.name
        (Rumoca.CTensor.Diagonal.argumentValues (TensorInstance.field pool i inputName)
          (TensorInstance.field pool i outputName) shape)
        (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
          time state input (some J)) .done) v →
      CCalls.Events.Resolves program v) :
    Reads (Rumoca.CTensor.Diagonal.resultHeap (TensorInstance.store backing pool i shape
        (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input (some J))
        (TensorInstance.field pool i outputName) (Rumoca.CTensor.SquareDiagonal.doubled input))
      (TensorInstance.field pool i outputName) (Rumoca.CTensor.Diagonal.matrix (Rumoca.CTensor.SquareDiagonal.doubled input)) ∧
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
        (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
          time state input (some J)) stack)
      (.returning (.integer 0)
        (written (Rumoca.CTensor.Diagonal.resultHeap (TensorInstance.store backing pool i shape
            (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input (some J))
            (TensorInstance.field pool i outputName) (Rumoca.CTensor.SquareDiagonal.doubled input))
          buffer (Rumoca.CTensor.Diagonal.matrix (Rumoca.CTensor.SquareDiagonal.doubled input))
          (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume) stack) := by
  let os := Rumoca.Tensor.matrixShape shape.volume shape.volume
  let H := TensorInstance.store backing pool i shape os time state input (some J)
  let p := TensorInstance.record pool i
  obtain ⟨types0, entered⟩ := guard_reaches (tensorReads shape) iface (tensorReads_noDecl shape) program H p
    refs buffer n m kind mode defined hk hm allowed nref stack
  have declared := declares_reaches program (tensorReads shape) iface (guardEnv p refs buffer n m)
    types0 H stack (by simp [guardEnv, parameters, CBody.bind]) (by simp [guardEnv, parameters, CBody.bind])
  let env := declaredEnv (guardEnv p refs buffer n m)
  let rest := countReject :: getLoopSuffix
  have nav := dispatch_reaches program env (declaredTypes types0) H refs reference "fmi3Status" stack
    (by simp [env, declaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve]) refRead (Runtime.fail "Unknown value reference") (fail_noDecl _)
    _ (Float64Table.getArms_noDecl (tensorReads shape) iface (tensorReads_noDecl shape)) _ arm rest
  have enterStep := jacobian_read_enter program shape (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) H p
    (getArm ⟨outputName, 0, os.volume⟩ ++ rest) "fmi3Status" stack
    (by simp [declaredEnv, guardEnv, CBody.bind])
    (by simp [declaredEnv, guardEnv, parameters, CBody.bind])
  have argsEq : [Value.pointer (some (p.member inputName)), .pointer (some (p.member outputName)),
      .integer shape.volume, .integer os.volume] =
      Rumoca.CTensor.Diagonal.argumentValues (TensorInstance.field pool i inputName)
        (TensorInstance.field pool i outputName) shape := by
    rfl
  rw [argsEq] at enterStep
  have readsInput : Reads H (TensorInstance.field pool i inputName) input :=
    TensorInstance.reads_input backing pool i shape os time state input (some J)
  have writableOutput : Writable H (TensorInstance.field pool i outputName) os.volume :=
    TensorInstance.writable_output backing pool i shape os time state input J
  obtain ⟨jacReads, jacFrame, jacRan⟩ :=
    TensorInstanceJacobian.jacobian_writes_events (shape := shape) definitions program linked library jacFound
      pool i input H bounded2 readsInput writableOutput adds jacResolves
      (.caller .discard (getArm ⟨outputName, 0, os.volume⟩ ++ rest) env (declaredTypes types0) "fmi3Status" stack)
  let F := Rumoca.CTensor.Diagonal.resultHeap H (TensorInstance.field pool i outputName) (Rumoca.CTensor.SquareDiagonal.doubled input)
  have writableFinal : Writable F buffer os.volume := by
    intro b hb
    obtain ⟨old, ho⟩ := writable b hb
    exact ⟨old, (jacFrame (buffer.index b) (fun a ha => (separate a ha b hb).symm)).trans ho⟩
  have staged := stage_reaches program (guardEnv p refs buffer n m) types0 F p
    ⟨outputName, 0, os.volume⟩ rest stack bounded2 (by simp [guardEnv, CBody.bind]) (fun _ => rfl)
  rw [regionBase_zero] at staged
  have tail := get_tail_reaches program (guardEnv p refs buffer n m) (declaredTypes types0) F
    (p.member outputName) buffer os (Rumoca.CTensor.Diagonal.matrix (Rumoca.CTensor.SquareDiagonal.doubled input)) m stack bounded2 nval
    (by simp [stagedEnv, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind]) jacReads writableFinal separate
  refine ⟨jacReads, entered.trans (declared.trans (nav.trans ?_))⟩
  exact .next enterStep (jacRan.trans (.next (resume_discard program _ _ _ _ _ _) (staged.trans tail)))

end



/-- The setter finiteness check applied to each caller value before any write. -/
def validateBody : List Stmt :=
  [Runtime.reject (Expr.nonfinite output) "Only finite Float64 values may be set"]

theorem validateBody_closed : validateBody.all CLoops.noDeclarations = true := by
  simp [validateBody, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, CLoops.noDeclarations]

/-- The setter loop suffix: validate finiteness, then copy the caller values. -/
def setLoopSuffix : List Stmt :=
  [.declare "size_t" "k" (Runtime.n 0), CLoops.loop "k" (Runtime.v "expected") validateBody,
    .assign (Runtime.v "k") (Runtime.n 0), CLoops.loop "k" (Runtime.v "expected") setCopyBody, Runtime.ok]

/-- Dispatch one value reference to its writable declared region; the time base,
derivatives and calculated outputs are read-only, and every other reference
fails. -/
def setDispatch (i : Solve.Interface) : Stmt :=
  dispatch (Float64Table.setArms i) (Runtime.fail "Unknown or read-only value reference")

def setRest (i : Solve.Interface) : List Stmt :=
  [.declare "fmi3Float64 *" "dst" Expr.nullPointer, .declare "size_t" "expected" (Runtime.n 0),
    setDispatch i, countReject] ++ setLoopSuffix

def setBody (i : Solve.Interface) : List Stmt :=
  Runtime.require .setStart ++ (basicReject :: setRest i)

def setFunction (i : Solve.Interface) : CTree.Function :=
  ⟨Float64Calls.signature true, setBody i, false⟩

/-- The setter body around an abstract value-reference dispatch statement: only
the writable-region dispatch depends on the declared interface. -/
def setBodyFor (dispatch : Stmt) : List Stmt :=
  Runtime.require .setStart ++ (basicReject ::
    [.declare "fmi3Float64 *" "dst" Expr.nullPointer, .declare "size_t" "expected" (Runtime.n 0),
      dispatch, countReject] ++ setLoopSuffix)

theorem setDispatch_noDecl (i : Solve.Interface) : CLoops.noDeclarations (setDispatch i) = true :=
  dispatch_noDecl _ _ (fail_noDecl _) (Float64Table.setArms_noDecl i)

theorem setBody_closed (i : Solve.Interface) :
    (setFunction i).body.all CBodyEmbedding.closedBlocks = true := by
  have closed := CBodyEmbedding.noDeclarations_closed _ (setDispatch_noDecl i)
  simp only [CBodyEmbedding.closedBlocks] at closed
  simp [setFunction, setBody, setRest, closed, basicReject, countReject, setLoopSuffix,
    validateBody, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject,
    Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, setCopyBody, CBodyEmbedding.closedBlocks,
    CLoops.noDeclarations, CLoops.loop, CLoops.counterStep]

/-- Local bindings after the setter's two staging declarations. -/
def setDeclaredEnv (env0 : Locals) : Locals :=
  CBody.bind (CBody.bind env0 "dst" (.pointer none)) "expected" (.integer 0)

/-- Types after the setter's two staging declarations. -/
def setDeclaredTypes (types0 : Types) : Types :=
  CLoops.bindType (CLoops.bindType types0 "dst" .pointer) "expected" .size

/-- Local bindings after the setter's staged region pointer and count. -/
def stagedSetEnv (env0 : Locals) (regionBase : Address) (count : Nat) : Locals :=
  CBody.bind (CBody.bind (setDeclaredEnv env0) "dst" (.pointer (some regionBase))) "expected" (.integer count)

section
variable [interface : CInterface]

/-- One validation iteration accepts a finite caller value. -/
theorem validate_step (env : Locals) (types : Types) (heap : Heap) (buffer : Address)
    (values : Values shape) (i : Fin shape.volume) (rest : List Stmt)
    (valuesBound : resolve env "values" = some (.pointer (some buffer)))
    (counter : resolve env "k" = some (.integer i.val))
    (read : load heap (buffer.index i.val) = some (.finite values[i])) :
    CLoops.next (.running (validateBody ++ rest) env types heap) = some (.running rest env types heap) := by
  have valueLoaded : CBody.eval env heap output = some (.finite values[i]) := by
    simp [output, Runtime.v, CBody.eval, CBody.evalWith, valuesBound, counter, Value.address, read]
  simp [validateBody, Runtime.reject, Runtime.branch, Runtime.call,
    Runtime.v, CLoops.next, CLoops.nextWith, CBody.legacyExpressions, CLoops.noDeclarations, Runtime.fail, Runtime.ret, CBody.eval,
    valueLoaded, boolean, Value.truth, Value.isFinite_finite]

/-- The validation loop accepts every finite caller value, heap fixed. -/
theorem validate_reaches (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (buffer : Address) (values : Values shape) (rest : List Stmt) (resultType : String)
    (stack : CCalls.Typed.Continuation) (bounded : shape.volume < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "expected" = some (.integer shape.volume))
    (valuesBound : resolve env "values" = some (.pointer (some buffer)))
    (readable : Reads heap buffer values) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (CLoops.loop "k" (Runtime.v "expected") validateBody :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running rest (counterEnv env "k" shape.volume) types heap) resultType stack) := by
  apply CCalls.Events.loop_reaches program "k" (Runtime.v "expected") validateBody rest
    (fun _ => env) types (fun _ => heap) shape.volume resultType stack typed bounded validateBody_closed
  · intro i inside
    simpa [Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, counterEnv, CBody.bind, resolve] using count
  · intro i inside
    have step := validate_step (counterEnv env "k" i) types heap buffer values ⟨i, inside⟩
      (counterStep "k" :: CLoops.loop "k" (Runtime.v "expected") validateBody :: rest)
      (by simpa [counterEnv, CBody.bind, resolve] using valuesBound)
      (by simp [counterEnv, CBody.bind, resolve]) (readable ⟨i, inside⟩)
    exact .next (CCalls.Events.body_step program step resultType stack) (.refl _)

end

section
variable [static : StaticLiterals]
private local instance setInterface : CInterface := cInterface static.addresses

/-- The setter guard reaches the typed statements after it. -/
theorem set_guard_reaches (iface : Solve.Interface) (program : CCalls.Events.Program E) (heap : Heap)
    (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction iface)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode) (nref : n.toNat = 1)
    (stack : CCalls.Typed.Continuation) :
    ∃ types0, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3SetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap stack)
      (.body (.running (setRest iface) (guardEnv p refs buffer n m) types0 heap) "fmi3Status" stack) := by
  have accepted := LifecycleGuard.accept (parameters (some p) (some refs) (some buffer) n m) heap p
    .setStart kind mode (basicReject :: setRest iface)
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  have hc := basic_explicit_pass heap p refs buffer n m nref
  have prefix_run : CBody.run 4 (.running (setBody iface)
      (parameters (some p) (some refs) (some buffer) n m) heap) =
      some (.running (setRest iface) (guardEnv p refs buffer n m) heap) := by
    rw [setBody, show (4 : Nat) = 3 + 1 from rfl, CBody.run_add, accepted, Option.bind_some]
    exact run_one (reject_false (guardEnv p refs buffer n m) heap _
      "Invalid Float64 array lengths or pointers" (setRest iface) hc)
  exact CCalls.Events.body_prefix_reaches program (setFunction iface)
    (arguments (some p) (some refs) (some buffer) n m) (parameters (some p) (some refs) (some buffer) n m)
    (guardEnv p refs buffer n m) heap heap (setRest iface) stack 4 defined
    (parameters_bound true _ _ _ _ _) (setBody_closed iface) prefix_run

/-- The setter's two staging declarations. -/
theorem set_declares_reaches (program : CCalls.Events.Program E) (iface : Solve.Interface) (env0 : Locals)
    (types0 : Types) (heap : Heap) (stack : CCalls.Typed.Continuation)
    (fresh_dst : env0 "dst" = none) (fresh_exp : env0 "expected" = none) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (setRest iface) env0 types0 heap) "fmi3Status" stack)
      (.body (.running (setDispatch iface :: countReject :: setLoopSuffix)
        (setDeclaredEnv env0) (setDeclaredTypes types0) heap) "fmi3Status" stack) := by
  have s1 : CLoops.next (.running (setRest iface) env0 types0 heap) =
      some (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        setDispatch iface :: countReject :: setLoopSuffix)
        (CBody.bind env0 "dst" (.pointer none)) (CLoops.bindType types0 "dst" .pointer) heap) :=
    declare_step_e env0 types0 heap "fmi3Float64 *" "dst" Expr.nullPointer .pointer (.pointer none)
      (.pointer none) _ fresh_dst rfl
      (by simp [Expr.nullPointer, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.expressionCast, CBody.zeroLiteral]) rfl
  have s2 : CLoops.next (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        setDispatch iface :: countReject :: setLoopSuffix)
        (CBody.bind env0 "dst" (.pointer none)) (CLoops.bindType types0 "dst" .pointer) heap) =
      some (.running (setDispatch iface :: countReject :: setLoopSuffix)
        (setDeclaredEnv env0) (setDeclaredTypes types0) heap) := by
    have := declare_step_e (CBody.bind env0 "dst" (.pointer none)) (CLoops.bindType types0 "dst" .pointer)
      heap "size_t" "expected" (Runtime.n 0) .size (.integer 0) (.integer 0)
      (setDispatch iface :: countReject :: setLoopSuffix)
      (by simp [CBody.bind, fresh_exp]) rfl (by simp [Runtime.n, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith]) rfl
    simpa [setDeclaredEnv, setDeclaredTypes] using this
  exact .next (CCalls.Events.body_step program s1 "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s2 "fmi3Status" stack) (.refl _))

/-- The setter's two dispatch assignments stage the writable region pointer and count. -/
theorem set_stage_reaches (program : CCalls.Events.Program E) (env0 : Locals) (types0 : Types) (heap : Heap)
    (p : Address) (r : Region) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (bounded : r.count < 2 ^ 64)
    (mBound : env0 "m" = some (.pointer (some p))) (addressable : Addressable r) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (setArm r ++ rest) (setDeclaredEnv env0) (setDeclaredTypes types0) heap)
        "fmi3Status" stack)
      (.body (.running rest (stagedSetEnv env0 (regionBase p r) r.count) (setDeclaredTypes types0) heap)
        "fmi3Status" stack) := by
  have addr : CLoops.eval (setDeclaredEnv env0) (setDeclaredTypes types0) heap (pointer r.member r.offset) =
      some (.pointer (some (regionBase p r))) := by
    apply CBodyEmbedding.eval_refines
    exact eval_pointer (setDeclaredEnv env0) heap p r
      (by simp [setDeclaredEnv, CBody.bind, CBody.resolve, mBound]) addressable
  have s1 : CLoops.next (.running (setArm r ++ rest) (setDeclaredEnv env0) (setDeclaredTypes types0) heap) =
      some (.running (.assign (Runtime.v "expected") (Runtime.n r.count) :: rest)
        (CBody.bind (setDeclaredEnv env0) "dst" (.pointer (some (regionBase p r)))) (setDeclaredTypes types0)
        heap) := by
    have := CLoops.assign_local (setDeclaredEnv env0) (setDeclaredTypes types0) heap "dst"
      (pointer r.member r.offset) (.assign (Runtime.v "expected") (Runtime.n r.count) :: rest)
      (.pointer none) (.pointer (some (regionBase p r))) (.pointer (some (regionBase p r))) .pointer
      (by simp [setDeclaredEnv, CBody.bind]) (by simp [setDeclaredTypes, CLoops.bindType]) addr rfl
    simpa [setArm, Runtime.v] using this
  have s2 : CLoops.next (.running (.assign (Runtime.v "expected") (Runtime.n r.count) :: rest)
        (CBody.bind (setDeclaredEnv env0) "dst" (.pointer (some (regionBase p r)))) (setDeclaredTypes types0)
        heap) =
      some (.running rest (stagedSetEnv env0 (regionBase p r) r.count) (setDeclaredTypes types0) heap) := by
    have := CLoops.assign_local (CBody.bind (setDeclaredEnv env0) "dst" (.pointer (some (regionBase p r))))
      (setDeclaredTypes types0) heap "expected" (Runtime.n r.count) rest (.integer 0) (.integer r.count)
      (.integer r.count) .size (by simp [setDeclaredEnv, CBody.bind]) (by simp [setDeclaredTypes, CLoops.bindType])
      (by simp [Runtime.n, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith])
      (CLoops.convert_size_nat r.count bounded)
    simpa [Runtime.v, stagedSetEnv] using this
  exact .next (CCalls.Events.body_step program s1 "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s2 "fmi3Status" stack) (.refl _))

/-- The count check, finiteness validation and copy loop after the dispatch. -/
theorem set_tail_reaches (program : CCalls.Events.Program E) (env0 : Locals) (types0 : Types) (heap : Heap)
    (regionBase buffer : Address) (rshape : Tensor.Shape) (values : Values rshape) (m : UInt64)
    (stack : CCalls.Typed.Continuation) (bounded : rshape.volume < 2 ^ 64) (matched : m.toNat = rshape.volume)
    (dstBound : resolve (stagedSetEnv env0 regionBase rshape.volume) "dst" = some (.pointer (some regionBase)))
    (expBound : resolve (stagedSetEnv env0 regionBase rshape.volume) "expected" = some (.integer rshape.volume))
    (valuesBound : resolve (stagedSetEnv env0 regionBase rshape.volume) "values" = some (.pointer (some buffer)))
    (nvalBound : resolve (stagedSetEnv env0 regionBase rshape.volume) "nValues" = some (.integer m.toNat))
    (fmiok : (stagedSetEnv env0 regionBase rshape.volume) "fmi3OK" = none)
    (fresh_k : (stagedSetEnv env0 regionBase rshape.volume) "k" = none)
    (readable : Reads heap buffer values)
    (writable : Writable heap regionBase rshape.volume)
    (separate : ∀ a < rshape.volume, ∀ b < rshape.volume, regionBase.index a ≠ buffer.index b) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (countReject :: setLoopSuffix) (stagedSetEnv env0 regionBase rshape.volume) types0 heap)
        "fmi3Status" stack)
      (.returning (.integer 0) (written heap regionBase values rshape.volume) stack) := by
  set env := stagedSetEnv env0 regionBase rshape.volume with henv
  have hcount : CLoops.eval env types0 heap (Runtime.nev (Runtime.v "nValues") (Runtime.v "expected")) =
      some (boolean false) := by
    simp [Runtime.nev, Runtime.v, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, nvalBound, expBound, matched,
      CBody.comparison, boolean]
  have s1 : CLoops.next (.running (countReject :: setLoopSuffix) env types0 heap) =
      some (.running setLoopSuffix env types0 heap) := by
    have := cbranch_false env types0 heap _ [Runtime.fail "Invalid Float64 value count"] [] setLoopSuffix
      (by simp [Runtime.fail, Runtime.ret, CLoops.noDeclarations]) hcount
    simpa [countReject, Runtime.reject, Runtime.branch] using this
  refine .next (CCalls.Events.body_step program s1 "fmi3Status" stack) ?_
  -- declare counter, validate, reset counter, copy
  refine .next (CCalls.Events.body_step program
    (CLoops.counter_initialize env types0 heap "k"
      (CLoops.loop "k" (Runtime.v "expected") validateBody :: .assign (Runtime.v "k") (Runtime.n 0) ::
        CLoops.loop "k" (Runtime.v "expected") setCopyBody :: [Runtime.ok]) fresh_k rfl) _ stack) ?_
  refine (validate_reaches program env (CLoops.bindType types0 "k" .size) heap buffer values
    (.assign (Runtime.v "k") (Runtime.n 0) :: CLoops.loop "k" (Runtime.v "expected") setCopyBody ::
      [Runtime.ok]) _ stack bounded (by simp [CLoops.bindType]) expBound valuesBound readable).trans ?_
  refine .next (CCalls.Events.body_step program
    (CLoops.counter_reset env (CLoops.bindType types0 "k" .size) heap "k" rshape.volume
      (CLoops.loop "k" (Runtime.v "expected") setCopyBody :: [Runtime.ok]) (by simp [CLoops.bindType]))
    _ stack) ?_
  refine (setCopy_reaches program env (CLoops.bindType types0 "k" .size) heap regionBase buffer values
    [Runtime.ok] _ stack bounded (by simp [CLoops.bindType]) expBound dstBound valuesBound readable
    writable separate).trans ?_
  exact DerivativeCalls.finish program _ (counterEnv env "k" rshape.volume) (CLoops.bindType types0 "k" .size)
    stack (by simp [counterEnv, CBody.bind, fmiok])

end


/-! ### The complete setter for a writable declared value reference -/

section
variable [static : StaticLiterals]
private local instance setBehaviorInterface : CInterface := cInterface static.addresses

/-- The complete setter for one writable value reference whose table arm stages
the region `⟨member, offset, rshape.volume⟩`: it replaces exactly that region
with the caller's finite values. -/
theorem set_reaches (iface : Solve.Interface) (program : CCalls.Events.Program E) (heap : Heap)
    (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (reference : Nat)
    (member : String) (offset : Nat) (rshape : Tensor.Shape) (values : Values rshape)
    (stack : CCalls.Typed.Continuation)
    (found : (Float64Table.setArms iface).lookup reference = some (setArm ⟨member, offset, rshape.volume⟩))
    (addressable : Addressable ⟨member, offset, rshape.volume⟩)
    (nref : n.toNat = 1) (matched : m.toNat = rshape.volume) (bounded : rshape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction iface)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (refRead : load heap (refs.index 0) = some (.integer reference))
    (readable : Reads heap buffer values)
    (writable : Writable heap ((p.member member).index offset) rshape.volume)
    (separate : ∀ a < rshape.volume, ∀ b < rshape.volume,
      ((p.member member).index offset).index a ≠ buffer.index b) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3SetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap stack)
      (.returning (.integer 0) (written heap ((p.member member).index offset) values rshape.volume) stack) := by
  obtain ⟨types0, entered⟩ := set_guard_reaches iface program heap p refs buffer n m kind mode defined
    hk hm allowed nref stack
  refine entered.trans ((set_declares_reaches program iface (guardEnv p refs buffer n m) types0 heap stack
    (by simp [guardEnv, parameters, CBody.bind]) (by simp [guardEnv, parameters, CBody.bind])).trans ?_)
  refine (dispatch_reaches program _ _ heap refs reference "fmi3Status" stack
    (by simp [setDeclaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve]) refRead _ (fail_noDecl _)
    _ (Float64Table.setArms_noDecl iface) _ found _).trans ?_
  refine (set_stage_reaches program (guardEnv p refs buffer n m) types0 heap p ⟨member, offset, rshape.volume⟩
    (countReject :: setLoopSuffix) stack bounded (by simp [guardEnv, CBody.bind]) addressable).trans ?_
  exact set_tail_reaches program (guardEnv p refs buffer n m) (setDeclaredTypes types0) heap
    ((p.member member).index offset) buffer rshape values m stack bounded matched
    (by simp [stagedSetEnv, regionBase, CBody.bind, CBody.resolve])
    (by simp [stagedSetEnv, CBody.bind, CBody.resolve])
    (by simp [stagedSetEnv, setDeclaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve])
    (by simp [stagedSetEnv, setDeclaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve])
    (by simp [stagedSetEnv, setDeclaredEnv, guardEnv, parameters, CBody.bind])
    (by simp [stagedSetEnv, setDeclaredEnv, guardEnv, parameters, CBody.bind]) readable writable separate

/-- The setter's whole behavior for one writable declared value reference. -/
theorem set_behaviors (iface : Solve.Interface) (program : CCalls.Events.Program E) (heap : Heap)
    (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (reference : Nat)
    (member : String) (offset : Nat) (rshape : Tensor.Shape) (values : Values rshape)
    (found : (Float64Table.setArms iface).lookup reference = some (setArm ⟨member, offset, rshape.volume⟩))
    (addressable : Addressable ⟨member, offset, rshape.volume⟩)
    (nref : n.toNat = 1) (matched : m.toNat = rshape.volume)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction iface)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (refRead : load heap (refs.index 0) = some (.integer reference))
    (readable : Reads heap buffer values)
    (writable : Writable heap ((p.member member).index offset) rshape.volume)
    (separate : ∀ a < rshape.volume, ∀ b < rshape.volume,
      ((p.member member).index offset).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap ((p.member member).index offset) values rshape.volume⟩ :=
  (CCalls.Events.internal_prefix program (set_reaches iface program heap p refs buffer n m kind mode reference
    member offset rshape values .done found addressable nref matched (matched ▸ m.toNat_lt_size) defined hk hm
    allowed refRead readable writable separate) (CCalls.Events.return_forced program _ _)).behaviors behavior

end

/-! ### Printed-text denotation -/

section
open CTree.Printer CTree.Syntax

/-- The `Runtime.fail` rejection statement prints its intended C token grammar,
independent of the diagnostic message. Every dispatch fallback is one of these. -/
theorem fail_printable (msg : String) : ItemPrintable RuntimePrinter.typedefs (Runtime.fail msg) := by
  simp only [Runtime.fail, Runtime.ret, Runtime.call, Runtime.v]
  refine ItemPrintable.returnValue (Printable.call (Printable.identifier (by decide +kernel)) ?_ ?_)
  · simp [Postfix]
  · intro arg harg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at harg
    rcases harg with rfl | rfl
    · exact Printable.identifier (by decide +kernel)
    · exact Printable.string

/-- The compared reference expression `valueReferences[0]` prints its intended C
token grammar; every dispatch guard compares it with a literal. -/
theorem vr0_printable : Printable RuntimePrinter.typedefs vr0 := by
  simp only [vr0, Runtime.v, Runtime.n]
  exact Printable.index (Printable.identifier (by decide +kernel)) (by simp [Postfix]) Printable.natural


set_option maxHeartbeats 4000000 in
/-- Every statement of the getter body around an abstract dispatch prints its
intended C token grammar, once the dispatch statement does. This is the shared
printability proof: every profile's `getBody` is definitionally `getBodyFor` of
its own dispatch, so the two per-profile getters cite this by instantiation. -/
theorem getBodyFor_printable (dispatch : Stmt)
    (hd : ItemPrintable RuntimePrinter.typedefs dispatch) :
    ∀ stmt ∈ getBodyFor dispatch, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  simp only [getBodyFor, getLoopSuffix, basicReject, countReject, Runtime.require,
      Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression, Runtime.kindModes, permittedModes,
      Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, Runtime.field, Runtime.v,
      Runtime.n, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.negate, Runtime.any, Expr.disjunction,
      Runtime.mode, Runtime.call, getCopyBody, srcCell, output, CLoops.loop,
      CLoops.counterStep, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
      List.cons_append, List.nil_append, forall_eq] <;>
    repeat first
      | exact hd
      | exact CNull.literal_printable _
      | exact iType
      | exact fType
      | exact sType
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
      | apply ItemPrintable.branch
      | apply ItemPrintable.whileLoop
      | apply ItemPrintable.returnValue
      | apply Printable.cast
      | apply Printable.binary
      | apply Printable.not
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

set_option maxHeartbeats 4000000 in
/-- Every statement of the setter body around an abstract dispatch prints its
intended C token grammar, once the dispatch statement does. Shared by every
profile's setter through `setBodyFor`. -/
theorem setBodyFor_printable (dispatch : Stmt)
    (hd : ItemPrintable RuntimePrinter.typedefs dispatch) :
    ∀ stmt ∈ setBodyFor dispatch, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  simp only [setBodyFor, setLoopSuffix, validateBody, basicReject, countReject, Runtime.require,
      Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression, Runtime.kindModes, permittedModes,
      Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, Runtime.field, Runtime.v,
      Runtime.n, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.negate, Runtime.any, Expr.disjunction,
      Runtime.mode, Runtime.call, Expr.nonfinite, setCopyBody, dstCell, output, CLoops.loop,
      CLoops.counterStep, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
      List.cons_append, List.nil_append, forall_eq] <;>
    repeat first
      | exact hd
      | exact CNull.literal_printable _
      | exact iType
      | exact fType
      | exact sType
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
      | apply ItemPrintable.branch
      | apply ItemPrintable.whileLoop
      | apply ItemPrintable.returnValue
      | apply Printable.cast
      | apply Printable.binary
      | apply Printable.not
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

/-- The derivative evaluation over `count` elements prints its intended C token grammar. -/
theorem rhsCall_printable (count : Nat) :
    ItemPrintable RuntimePrinter.typedefs (TensorEntry.rhsCall (Runtime.n count)) := by
  simp only [TensorEntry.rhsCall, TensorEntry.rhsArgs, Runtime.call, Runtime.region, Runtime.field,
    Runtime.v, Runtime.n, stateName, inputName, derivativeName]
  repeat first
    | apply And.intro
    | apply ItemPrintable.eval
    | apply Printable.address
    | apply Printable.call
    | apply Printable.field
    | apply Printable.index
    | exact Printable.natural
    | apply Printable.identifier
    | decide +kernel
    | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Postfix, FieldBase]

/-- The Jacobian evaluation prints its intended C token grammar. -/
theorem jacobianCall_printable (shape : Tensor.Shape) :
    ItemPrintable RuntimePrinter.typedefs (TensorEntry.jacobianCall (Runtime.n shape.volume) shape) := by
  simp only [TensorEntry.jacobianCall, TensorEntry.jacobianArgs, Runtime.call, Runtime.region, Runtime.field,
    Runtime.v, Runtime.n, inputName, outputName]
  repeat first
    | apply And.intro
    | apply ItemPrintable.eval
    | apply Printable.address
    | apply Printable.call
    | apply Printable.field
    | apply Printable.index
    | exact Printable.natural
    | apply Printable.identifier
    | decide +kernel
    | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, Postfix, FieldBase]

theorem tensorReads_printable (shape : Tensor.Shape) :
    ∀ stmt ∈ (tensorReads shape).derivative ++ (tensorReads shape).output,
      ItemPrintable RuntimePrinter.typedefs stmt := by
  intro stmt member
  simp only [tensorReads, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact rhsCall_printable shape.volume
  · exact jacobianCall_printable shape

/-- Every statement of a dispatch prints its intended C token grammar, given its
arms and fallback do. -/
theorem dispatch_printable (arms : List (Nat × List Stmt)) (fallback : Stmt)
    (hfallback : ItemPrintable RuntimePrinter.typedefs fallback)
    (harms : ∀ a ∈ arms, ∀ stmt ∈ a.2, ItemPrintable RuntimePrinter.typedefs stmt) :
    ItemPrintable RuntimePrinter.typedefs (dispatch arms fallback) := by
  have h := Float64Dispatch.dispatchChain_printable RuntimePrinter.typedefs vr0 arms
    [fallback] vr0_printable (fun stmt hs => by
      simp only [List.mem_singleton] at hs; subst hs; exact hfallback) harms
  exact h _ (by rw [dispatch_chain]; simp)

/-- The getter dispatch prints its intended C token grammar. -/
theorem getDispatch_printable (reads : Float64Table.Reads) (i : Solve.Interface)
    (printableReads : ∀ stmt ∈ reads.derivative ++ reads.output, ItemPrintable RuntimePrinter.typedefs stmt) :
    ItemPrintable RuntimePrinter.typedefs (getDispatch reads i) :=
  dispatch_printable _ _ (fail_printable _) (Float64Table.getArms_printable reads i printableReads)

/-- The setter dispatch prints its intended C token grammar. -/
theorem setDispatch_printable (i : Solve.Interface) :
    ItemPrintable RuntimePrinter.typedefs (setDispatch i) :=
  dispatch_printable _ _ (fail_printable _) (Float64Table.setArms_printable i)

/-- Every statement of the getter body prints its intended C token grammar. -/
theorem getBody_printable (reads : Float64Table.Reads) (i : Solve.Interface)
    (printableReads : ∀ stmt ∈ reads.derivative ++ reads.output, ItemPrintable RuntimePrinter.typedefs stmt) :
    ∀ stmt ∈ (getFunction reads i).body, ItemPrintable RuntimePrinter.typedefs stmt :=
  getBodyFor_printable (getDispatch reads i) (getDispatch_printable reads i printableReads)

/-- Every statement of the setter body prints its intended C token grammar. -/
theorem setBody_printable (i : Solve.Interface) :
    ∀ stmt ∈ (setFunction i).body, ItemPrintable RuntimePrinter.typedefs stmt :=
  setBodyFor_printable (setDispatch i) (setDispatch_printable i)

/-- The accessor signature prints its intended C token grammar. -/
theorem signature_printable (write : Bool) :
    SignaturePrintable RuntimePrinter.typedefs (Float64Calls.signature write) := by
  cases write <;>
    (refine ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel, ?_⟩
     intro param member
     simp only [Float64Calls.signature, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
        List.not_mem_nil, or_false] at member
     rcases member with rfl | rfl | rfl | rfl | rfl <;>
       refine ⟨?_, by decide +kernel⟩ <;>
       first
         | exact .named (.typedefName (by decide +kernel) (by decide +kernel))
         | exact .const (show TypeSpelling RuntimePrinter.typedefs "fmi3ValueReference" from
             .named (.typedefName (by decide +kernel) (by decide +kernel)))
         | exact .const (show TypeSpelling RuntimePrinter.typedefs "fmi3Float64" from
             .named (.typedefName (by decide +kernel) (by decide +kernel))))

/-- The rendered getter denotes its function under the shared C printer. -/
theorem getFunction_denotes (reads : Float64Table.Reads) (i : Solve.Interface)
    (printableReads : ∀ stmt ∈ reads.derivative ++ reads.output, ItemPrintable RuntimePrinter.typedefs stmt) :
    FunctionDenotes RuntimePrinter.typedefs (getFunction reads i).render (getFunction reads i) :=
  CTree.Printer.function_denotes ⟨signature_printable false, getBody_printable reads i printableReads⟩

/-- The rendered setter denotes its function under the shared C printer. -/
theorem setFunction_denotes (i : Solve.Interface) :
    FunctionDenotes RuntimePrinter.typedefs (setFunction i).render (setFunction i) :=
  CTree.Printer.function_denotes ⟨signature_printable true, setBody_printable i⟩

end

/-! ### Calls -/

section
open CCallPolicy

/-- A dispatch calls only what its arms and its fallback call. -/
theorem dispatch_admits (p : Expr → Prop) (arms : List (Nat × List Stmt)) (fallback : Stmt)
    (hfallback : StatementAdmits p fallback)
    (harms : ∀ a ∈ arms, ∀ stmt ∈ a.2, StatementAdmits p stmt) :
    StatementAdmits p (dispatch arms fallback) := by
  suffices h : ∀ stmt ∈ Float64Dispatch.dispatchChain vr0 arms [fallback], StatementAdmits p stmt by
    rw [dispatch_chain] at h
    exact h _ (List.mem_singleton_self _)
  induction arms with
  | nil => intro stmt hs; rw [List.mem_singleton.mp hs]; exact hfallback
  | cons a rest ih =>
    obtain ⟨j, arm⟩ := a
    intro stmt hs
    rw [Float64Dispatch.dispatchChain_cons, List.mem_singleton] at hs
    subst hs
    simp only [Runtime.branch, StatementAdmits]
    refine ⟨by simp [ExpressionAdmits, Runtime.eqv, vr0, Runtime.v, Runtime.n], ?_, ?_⟩
    · exact harms (j, arm) (List.mem_cons_self ..)
    · exact ih (fun b hb => harms b (List.mem_cons_of_mem _ hb))

/-- The Float64 dispatches stage pointers and counts and call only the `fail`
diagnostic of their fallback. -/
theorem getDispatch_admits (p : Expr → Prop) (reads : Float64Table.Reads) (i : Solve.Interface)
    (fallback : StatementAdmits p (Runtime.fail "Unknown value reference"))
    (evaluations : ∀ stmt ∈ reads.derivative ++ reads.output, StatementAdmits p stmt) :
    StatementAdmits p (getDispatch reads i) :=
  dispatch_admits _ _ _ fallback (Float64Table.getArms_admits _ reads i evaluations)

theorem setDispatch_admits (p : Expr → Prop) (i : Solve.Interface)
    (fallback : StatementAdmits p (Runtime.fail "Unknown or read-only value reference")) :
    StatementAdmits p (setDispatch i) :=
  dispatch_admits _ _ _ fallback (Float64Table.setArms_admits _ i)

end

/-! ### Null-handle rejections -/

section
variable [static : StaticLiterals]
private local instance rejectInterface : CInterface := cInterface static.addresses

/-- A null instance handle is rejected with `fmi3Error`, changing nothing. -/
theorem null_get_behaviors (reads : Float64Table.Reads) (iface : Solve.Interface)
    (closedReads : (reads.derivative ++ reads.output).all CLoops.noDeclarations = true)
    (program : CCalls.Events.Program E) (heap : Heap) (refs buffer : Option Address) (n m : UInt64)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction reads iface)))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (getFunction reads iface)
    (Runtime.modeGuard .get :: basicReject :: getRest reads iface)
    (arguments none refs buffer n m) (parameters none refs buffer n m) heap defined
    (parameters_bound false _ _ _ _ _) (by simp [getFunction, getBody, Runtime.require, List.append_assoc])
    rfl (getBody_closed reads iface closedReads)
  all_goals simp [parameters, CBody.bind]

/-- A null instance handle is rejected with `fmi3Error`, changing nothing. -/
theorem null_set_behaviors (iface : Solve.Interface) (program : CCalls.Events.Program E) (heap : Heap)
    (refs buffer : Option Address) (n m : UInt64)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction iface))) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (setFunction iface)
    (Runtime.modeGuard .setStart :: basicReject :: setRest iface)
    (arguments none refs buffer n m) (parameters none refs buffer n m) heap defined
    (parameters_bound true _ _ _ _ _) (by simp [setFunction, setBody, Runtime.require, List.append_assoc])
    rfl (setBody_closed iface)
  all_goals simp [parameters, CBody.bind]

end
/-! ### Unknown or read-only value-reference failure paths

The Float64 dispatch reaches the scalar `fail` statement before the copy loop for
a value reference that names no declared variable (getter) or no writable one
(setter). The memory-machine execution witness leaves the heap unchanged up to
that statement; `GuardedCalls.FailurePrefix.silent_behaviors` then returns
`fmi3Error`. -/

section
variable [interface : CInterface]

/-- A reference with no arm runs through every guard to the fallback. -/
theorem dispatch_fails (env : Locals) (heap : Heap) (refs : Address) (r : Nat)
    (rBound : resolve env "valueReferences" = some (.pointer (some refs)))
    (refRead : load heap (refs.index 0) = some (.integer r)) (fallback : Stmt)
    (arms : List (Nat × List Stmt)) (absent : arms.lookup r = none) (rest : List Stmt) :
    CBody.run arms.length (.running (dispatch arms fallback :: rest) env heap) =
      some (.running (fallback :: rest) env heap) := by
  induction arms with
  | nil => rfl
  | cons a tl ih =>
    obtain ⟨j, yes⟩ := a
    have different : r ≠ j := by
      intro same; subst same; simp [List.lookup] at absent
    have hb : (r == j) = false := by simpa using different
    have next : tl.lookup r = none := by simpa [List.lookup, hb] using absent
    have shape : dispatch ((j, yes) :: tl) fallback =
        .branch (Runtime.eqv vr0 (Runtime.n j)) yes [dispatch tl fallback] := by
      show Runtime.branch _ yes (Float64Dispatch.dispatchChain vr0 tl [fallback]) = _
      rw [dispatch_chain]; rfl
    rw [shape, List.length_cons, Nat.add_comm]
    exact run_append (run_one (branch_false env heap _ yes [dispatch tl fallback] rest
      (vr0_bne env heap refs r j rBound refRead different))) (ih next)

end

section
variable [static : StaticLiterals]
private local instance failPathInterface : CInterface := cInterface static.addresses

/-- The getter's memory-machine execution reaches its `fail` statement before the
copy loop, leaving the heap unchanged, for a reference that names no declared
variable. -/
theorem get_fail_prefix (reads : Float64Table.Reads) (iface : Solve.Interface)
    (closedReads : (reads.derivative ++ reads.output).all CLoops.noDeclarations = true)
    (heap : Heap) (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (r : Nat)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode) (nref : n.toNat = 1)
    (refRead : load heap (refs.index 0) = some (.integer r))
    (absent : (Float64Table.getArms reads iface).lookup r = none) :
    GuardedCalls.FailurePrefix (getFunction reads iface)
      (arguments (some p) (some refs) (some buffer) n m) heap p "Unknown value reference" heap := by
  set env0 := parameters (some p) (some refs) (some buffer) n m with henv0
  set g := guardEnv p refs buffer n m with hg
  set d := declaredEnv g with hd
  have rv : resolve d "valueReferences" = some (.pointer (some refs)) := by
    simp [hd, declaredEnv, hg, guardEnv, parameters, CBody.bind, CBody.resolve]
  have s_accept : CBody.run 3 (.running (getBody reads iface) env0 heap) =
      some (.running (basicReject :: getRest reads iface) g heap) :=
    LifecycleGuard.accept env0 heap p .get kind mode (basicReject :: getRest reads iface)
      (by simp [henv0, parameters, CBody.bind]) (by simp [henv0, parameters, CBody.bind]) hk hm allowed
  have s_reject : CBody.run 1 (.running (basicReject :: getRest reads iface) g heap) =
      some (.running (getRest reads iface) g heap) :=
    run_one (reject_false g heap _ "Invalid Float64 array lengths or pointers" (getRest reads iface)
      (basic_explicit_pass heap p refs buffer n m nref))
  have s_src : CBody.run 1 (.running (getRest reads iface) g heap) =
      some (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        getDispatch reads iface :: countReject :: getLoopSuffix)
        (CBody.bind g "src" (.pointer none)) heap) :=
    run_one (declare_next g heap "fmi3Float64 *" "src" Expr.nullPointer (.pointer none) (.pointer none) _
      (by simp [hg, guardEnv, parameters, CBody.bind])
      (by simp [Expr.nullPointer, CBody.eval, CBody.evalWith, CBody.expressionCast, CBody.zeroLiteral])
      (by simp [CBody.cast, convert]))
  have s_exp : CBody.run 1 (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        getDispatch reads iface :: countReject :: getLoopSuffix)
        (CBody.bind g "src" (.pointer none)) heap) =
      some (.running (getDispatch reads iface :: countReject :: getLoopSuffix) d heap) :=
    run_one (declare_next (CBody.bind g "src" (.pointer none)) heap "size_t" "expected" (Runtime.n 0)
      (.integer 0) (.integer 0) _ (by simp [hg, guardEnv, parameters, CBody.bind])
      (by simp [Runtime.n, CBody.eval, CBody.evalWith]) (by simp [CBody.cast, convert]))
  have s_dispatch := dispatch_fails d heap refs r rv refRead (Runtime.fail "Unknown value reference")
    (Float64Table.getArms reads iface) absent (countReject :: getLoopSuffix)
  have chain := run_append s_accept (run_append s_reject (run_append s_src (run_append s_exp s_dispatch)))
  refine ⟨rfl, getBody_closed reads iface closedReads, env0, d, countReject :: getLoopSuffix, _,
    parameters_bound false _ _ _ _ _, chain, ?_, ?_⟩
  · simp [hd, declaredEnv, hg, guardEnv, parameters, CBody.bind]
  · simp [hd, declaredEnv, hg, guardEnv, parameters, CBody.bind, CBody.resolve]

/-- The setter's memory-machine execution reaches its `fail` statement before the
copy loop for a reference that names no writable declared variable. -/
theorem set_fail_prefix (iface : Solve.Interface)
    (heap : Heap) (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (r : Nat)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode) (nref : n.toNat = 1)
    (refRead : load heap (refs.index 0) = some (.integer r))
    (absent : (Float64Table.setArms iface).lookup r = none) :
    GuardedCalls.FailurePrefix (setFunction iface)
      (arguments (some p) (some refs) (some buffer) n m) heap p "Unknown or read-only value reference" heap := by
  set env0 := parameters (some p) (some refs) (some buffer) n m with henv0
  set g := guardEnv p refs buffer n m with hg
  set d := setDeclaredEnv g with hd
  have rv : resolve d "valueReferences" = some (.pointer (some refs)) := by
    simp [hd, setDeclaredEnv, hg, guardEnv, parameters, CBody.bind, CBody.resolve]
  have s_accept : CBody.run 3 (.running (setBody iface) env0 heap) =
      some (.running (basicReject :: setRest iface) g heap) :=
    LifecycleGuard.accept env0 heap p .setStart kind mode (basicReject :: setRest iface)
      (by simp [henv0, parameters, CBody.bind]) (by simp [henv0, parameters, CBody.bind]) hk hm allowed
  have s_reject : CBody.run 1 (.running (basicReject :: setRest iface) g heap) =
      some (.running (setRest iface) g heap) :=
    run_one (reject_false g heap _ "Invalid Float64 array lengths or pointers" (setRest iface)
      (basic_explicit_pass heap p refs buffer n m nref))
  have s_dst : CBody.run 1 (.running (setRest iface) g heap) =
      some (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        setDispatch iface :: countReject :: setLoopSuffix)
        (CBody.bind g "dst" (.pointer none)) heap) :=
    run_one (declare_next g heap "fmi3Float64 *" "dst" Expr.nullPointer (.pointer none) (.pointer none) _
      (by simp [hg, guardEnv, parameters, CBody.bind])
      (by simp [Expr.nullPointer, CBody.eval, CBody.evalWith, CBody.expressionCast, CBody.zeroLiteral])
      (by simp [CBody.cast, convert]))
  have s_exp : CBody.run 1 (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        setDispatch iface :: countReject :: setLoopSuffix)
        (CBody.bind g "dst" (.pointer none)) heap) =
      some (.running (setDispatch iface :: countReject :: setLoopSuffix) d heap) :=
    run_one (declare_next (CBody.bind g "dst" (.pointer none)) heap "size_t" "expected" (Runtime.n 0)
      (.integer 0) (.integer 0) _ (by simp [hg, guardEnv, parameters, CBody.bind])
      (by simp [Runtime.n, CBody.eval, CBody.evalWith]) (by simp [CBody.cast, convert]))
  have s_dispatch := dispatch_fails d heap refs r rv refRead
    (Runtime.fail "Unknown or read-only value reference") (Float64Table.setArms iface) absent
    (countReject :: setLoopSuffix)
  have chain := run_append s_accept (run_append s_reject (run_append s_dst (run_append s_exp s_dispatch)))
  refine ⟨rfl, setBody_closed iface, env0, d, countReject :: setLoopSuffix, _,
    parameters_bound true _ _ _ _ _, chain, ?_, ?_⟩
  · simp [hd, setDeclaredEnv, hg, guardEnv, parameters, CBody.bind]
  · simp [hd, setDeclaredEnv, hg, guardEnv, parameters, CBody.bind, CBody.resolve]

/-- The getter's whole behavior on a reference that names no declared variable, with
logging disabled: it reaches `fail` before the copy loop and returns `fmi3Error`,
its only heap change the terminated lifecycle mode. -/
theorem get_fail_behaviors (reads : Float64Table.Reads) (iface : Solve.Interface)
    (closedReads : (reads.derivative ++ reads.output).all CLoops.noDeclarations = true)
    (program : CCalls.Events.Program E) (heap : Heap) (p refs buffer message : Address)
    (n m : UInt64) (kind : Kind) (mode : Mode) (r : Nat) (logger : Option Address)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction reads iface)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses "Unknown value reference" = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hmode : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (allowed : Reference.Allowed .get kind mode) (nref : n.toNat = 1)
    (refRead : load heap (refs.index 0) = some (.integer r))
    (absent : (Float64Table.getArms reads iface).lookup r = none)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  have hmodeLoad : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hmode, convert, Mode.code]
  exact GuardedCalls.FailurePrefix.silent_behaviors program (getFunction reads iface)
    (arguments (some p) (some refs) (some buffer) n m) heap heap p message "Unknown value reference"
    (some (.integer mode.code)) logger
    (get_fail_prefix reads iface closedReads heap p refs buffer n m kind mode r hk hmodeLoad allowed nref refRead absent) defined helper messageBound hmode hl hg behavior

/-- The setter's whole behavior on a reference that names no writable region
with logging disabled: it reaches `fail` before the copy loop and returns
`fmi3Error`, its only heap change the terminated lifecycle mode. -/
theorem set_fail_behaviors (iface : Solve.Interface)
    (program : CCalls.Events.Program E) (heap : Heap) (p refs buffer message : Address)
    (n m : UInt64) (kind : Kind) (mode : Mode) (r : Nat) (logger : Option Address)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction iface)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses "Unknown or read-only value reference" = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hmode : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (allowed : Reference.Allowed .setStart kind mode) (nref : n.toNat = 1)
    (refRead : load heap (refs.index 0) = some (.integer r))
    (absent : (Float64Table.setArms iface).lookup r = none)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  have hmodeLoad : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hmode, convert, Mode.code]
  exact GuardedCalls.FailurePrefix.silent_behaviors program (setFunction iface)
    (arguments (some p) (some refs) (some buffer) n m) heap heap p message "Unknown or read-only value reference"
    (some (.integer mode.code)) logger
    (set_fail_prefix iface heap p refs buffer n m kind mode r hk hmodeLoad allowed nref refRead absent)
    defined helper messageBound hmode hl hg behavior

end

/-! ### The setter bound to the static tensor instance record -/

/-- The instance record with its input region made writable, modeling an
instance ready to receive input/start values. -/
def inputWritableStore (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Tensor.Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (output : Option (Values oshape)) : Heap :=
  place (TensorInstance.store backing pool i shape oshape time state input output)
    ((TensorInstance.record pool i).member inputName) shape true (some input)

theorem inputWritableStore_writable (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Tensor.Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (output : Option (Values oshape)) :
    Writable (inputWritableStore backing pool i shape oshape time state input output)
      (TensorInstance.field pool i inputName) shape.volume := by
  unfold inputWritableStore TensorInstance.field
  exact place_writable _ _ _ (some input)

section
variable [static : StaticLiterals]
private local instance instSetInterface : CInterface := cInterface static.addresses
variable (program : CCalls.Events.Program E) (backing : Heap) (pool : Address) (i : Nat)
  (shape oshape : Tensor.Shape) (time : Values Tensor.scalar) (state input : Values shape)
  (output : Option (Values oshape)) (refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode)
  (iface : Solve.Interface) (reference : Nat)

/-- The setter writing the state region of instance `i` replaces exactly
that region with the caller's finite values. -/
theorem set_instance_behaviors_state (found : (Float64Table.setArms iface).lookup reference =
      some (setArm ⟨stateName, 0, shape.volume⟩))
    (newValues : Values shape) (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction iface)))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (refRead : load (TensorInstance.store backing pool i shape oshape time state input output)
      (refs.index 0) = some (.integer reference))
    (readable : Reads (TensorInstance.store backing pool i shape oshape time state input output) buffer newValues)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i stateName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
        (TensorInstance.store backing pool i shape oshape time state input output) .done) behavior ↔
      behavior = .terminates []
        ⟨.integer 0, written (TensorInstance.store backing pool i shape oshape time state input output)
          (TensorInstance.field pool i stateName) newValues shape.volume⟩ := by
  have result := set_behaviors iface program _ (TensorInstance.record pool i) refs buffer n m kind mode reference
    stateName 0 shape newValues found (fun _ => rfl) nref nval defined hk hm allowed refRead readable
    (by rw [Address.index_zero]; exact writable_state backing pool i shape oshape time state input output)
    (by simpa only [Address.index_zero] using separate) behavior
  simpa only [Address.index_zero] using result

/-- The setter writing the input region of instance `i` (writable input). -/
theorem set_instance_behaviors_input (found : (Float64Table.setArms iface).lookup reference =
      some (setArm ⟨inputName, 0, shape.volume⟩))
    (newValues : Values shape) (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction iface)))
    (hk : load (inputWritableStore backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (inputWritableStore backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (refRead : load (inputWritableStore backing pool i shape oshape time state input output)
      (refs.index 0) = some (.integer reference))
    (readable : Reads (inputWritableStore backing pool i shape oshape time state input output) buffer newValues)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i inputName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
        (inputWritableStore backing pool i shape oshape time state input output) .done) behavior ↔
      behavior = .terminates []
        ⟨.integer 0, written (inputWritableStore backing pool i shape oshape time state input output)
          (TensorInstance.field pool i inputName) newValues shape.volume⟩ := by
  have result := set_behaviors iface program _ (TensorInstance.record pool i) refs buffer n m kind mode reference
    inputName 0 shape newValues found (fun _ => rfl) nref nval defined hk hm allowed refRead readable
    (by rw [Address.index_zero]; exact inputWritableStore_writable backing pool i shape oshape time state input output)
    (by simpa only [Address.index_zero] using separate) behavior
  simpa only [Address.index_zero] using result

/-- The successful setter's result heap preserves every tensor cell of every
other instance in the static pool. -/
theorem set_preserves_other_instances (H : Heap) (member : String) (newValues : Values shape)
    (j : Nat) (b : String) (k : Nat) (different : j ≠ i) :
    written H (TensorInstance.field pool i member) newValues shape.volume
        ((TensorInstance.field pool j b).index k) = H ((TensorInstance.field pool j b).index k) :=
  written_frame H (TensorInstance.field pool i member) newValues shape.volume
    ((TensorInstance.field pool j b).index k)
    (fun j' _ => Address.instances_separate pool j i different b member k j')

end

/-! ### Consumable function contracts

These mirror the scalar `Float64Calls.FunctionContract`: the printed function
text, its declaration closedness, its printed-text denotation under the shared C
printer, and a rejection guarantee for a null handle. The tensor getter contract
also states that reading a calculated variable evaluates it. -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The tensor `fmi3GetFloat64` function contract. -/
structure GetContract (shape : Tensor.Shape) (iface : Solve.Interface) (text : String) : Prop where
  printed : text = (getFunction (tensorReads shape) iface).render
  closed : (getFunction (tensorReads shape) iface).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (getFunction (tensorReads shape) iface)
  rejected : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (refs buffer : Option Address)
    (n m : UInt64),
    program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction (tensorReads shape) iface)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩
  /-- Reading `der(x)` evaluates the prepared derivative from the current state and
  input and returns it; the region's earlier contents do not matter. -/
  derivativeRead : ∀ {E} (program : CCalls.Events.Program E) (definitions : CLoops.Calls.Definitions)
    (reference : Nat)
    (oshape : Tensor.Shape) (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state input result : Values shape) (output : Option (Values oshape))
    (refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode),
    CCalls.Typed.Extends definitions program.internal →
    Rumoca.CTensor.Lowering.Library definitions →
    definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree →
    (Float64Table.getArms (tensorReads shape) iface).lookup reference =
      some (TensorEntry.rhsCall (Runtime.n shape.volume) :: getArm ⟨derivativeName, 0, shape.volume⟩) →
    n.toNat = 1 → m.toNat = shape.volume → shape.volume < 2 ^ 64 →
    program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction (tensorReads shape) iface)) →
    load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code) →
    load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code) →
    Reference.Allowed .get kind mode →
    load (TensorInstance.store backing pool i shape oshape time state input output)
      (refs.index 0) = some (.integer reference) →
    Rumoca.Solve.Tensor.Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment state input) result →
    Writable (TensorInstance.store backing pool i shape oshape time state input output) buffer shape.volume →
    (∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b) →
    (∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Rumoca.CTensor.Lowering.Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape))
        (TensorInstance.store backing pool i shape oshape time state input output) .done) v →
      CCalls.Events.Resolves program v) →
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName) result ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          backing ((TensorInstance.field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
          (TensorInstance.store backing pool i shape oshape time state input output) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, written finalHeap buffer result shape.volume⟩
  /-- Reading `J` evaluates the prepared dense Jacobian `diag(2*u)` from the current
  input and returns it; the region's earlier contents do not matter. -/
  outputRead : ∀ {E} (program : CCalls.Events.Program E) (definitions : CLoops.Calls.Definitions)
    (reference : Nat)
    (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state input : Values shape)
    (J : Values (Rumoca.Tensor.matrixShape shape.volume shape.volume))
    (refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode),
    CCalls.Typed.Extends definitions program.internal →
    Rumoca.CTensor.Lowering.Library definitions →
    definitions Rumoca.CTensor.SquareDiagonal.function.signature.name =
      some Rumoca.CTensor.SquareDiagonal.function →
    (Float64Table.getArms (tensorReads shape) iface).lookup reference =
      some (TensorEntry.jacobianCall (Runtime.n shape.volume) shape ::
        getArm ⟨outputName, 0, (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume⟩) →
    n.toNat = 1 → m.toNat = (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume →
    (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume < 2 ^ 64 →
    program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction (tensorReads shape) iface)) →
    load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) ((TensorInstance.record pool i).member "kind") = some (.integer kind.code) →
    load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) ((TensorInstance.record pool i).member "mode") = some (.integer mode.code) →
    Reference.Allowed .get kind mode →
    load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) (refs.index 0) = some (.integer reference) →
    Writable (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) buffer (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume →
    (∀ a < (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume,
      ∀ b < (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume,
      (TensorInstance.field pool i outputName).index a ≠ buffer.index b) →
    (∀ k : Fin shape.volume,
      Binary64.Adds input[k] input[k] (.finite (Rumoca.CTensor.SquareDiagonal.doubled input)[k])) →
    (∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling Rumoca.CTensor.SquareDiagonal.function.signature.name
        (Rumoca.CTensor.Diagonal.argumentValues (TensorInstance.field pool i inputName)
          (TensorInstance.field pool i outputName) shape)
        (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
          time state input (some J)) .done) v →
      CCalls.Events.Resolves program v) →
    Reads (Rumoca.CTensor.Diagonal.resultHeap (TensorInstance.store backing pool i shape
        (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input (some J))
        (TensorInstance.field pool i outputName) (Rumoca.CTensor.SquareDiagonal.doubled input))
      (TensorInstance.field pool i outputName)
      (Rumoca.CTensor.Diagonal.matrix (Rumoca.CTensor.SquareDiagonal.doubled input)) ∧
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
        (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
          time state input (some J)) .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0,
        written (Rumoca.CTensor.Diagonal.resultHeap (TensorInstance.store backing pool i shape
            (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input (some J))
            (TensorInstance.field pool i outputName) (Rumoca.CTensor.SquareDiagonal.doubled input))
          buffer (Rumoca.CTensor.Diagonal.matrix (Rumoca.CTensor.SquareDiagonal.doubled input))
          (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume⟩
/-- The `fmi3SetFloat64` function contract. -/
structure SetContract (iface : Solve.Interface) (text : String) : Prop where
  printed : text = (setFunction iface).render
  closed : (setFunction iface).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (setFunction iface)
  rejected : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (refs buffer : Option Address)
    (n m : UInt64),
    program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction iface)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem get_contract (shape : Tensor.Shape) (iface : Solve.Interface) :
    GetContract shape iface (getFunction (tensorReads shape) iface).render where
  printed := rfl
  closed := getBody_closed (tensorReads shape) iface (tensorReads_noDecl shape)
  denotes := getFunction_denotes (tensorReads shape) iface (tensorReads_printable shape)
  rejected program heap refs buffer n m defined :=
    null_get_behaviors (tensorReads shape) iface (tensorReads_noDecl shape) program heap refs buffer n m defined
  derivativeRead program definitions reference oshape backing pool i time state input result output refs buffer n
      m kind mode linked library found arm nref nval bounded defined hk hm allowed refRead executed writable
      separate resolves := by
    obtain ⟨finalHeap, reads, others, ran⟩ := get_deriv_reaches program shape oshape iface reference arm
      definitions linked library found backing pool i time state input result output refs buffer n m kind mode
      .done nref nval bounded defined hk hm allowed refRead executed writable separate resolves
    exact ⟨finalHeap, reads, others, fun behavior =>
      (CCalls.Events.internal_prefix program ran (CCalls.Events.return_forced program _ _)).behaviors behavior⟩
  outputRead program definitions reference backing pool i time state input J refs buffer n m kind mode linked
      library jacFound arm nref nval bounded2 defined hk hm allowed refRead writable separate adds jacResolves := by
    obtain ⟨reads, ran⟩ := get_output_reaches program shape iface reference arm definitions linked library
      jacFound backing pool i time state input J refs buffer n m kind mode .done nref nval bounded2 defined hk hm
      allowed refRead writable separate adds jacResolves
    exact ⟨reads, fun behavior =>
      (CCalls.Events.internal_prefix program ran (CCalls.Events.return_forced program _ _)).behaviors behavior⟩

theorem set_contract (iface : Solve.Interface) : SetContract iface (setFunction iface).render where
  printed := rfl
  closed := setBody_closed iface
  denotes := setFunction_denotes iface
  rejected program heap refs buffer n m defined :=
    null_set_behaviors iface program heap refs buffer n m defined

end
end Rumoca.FMI3.TensorFloat64
