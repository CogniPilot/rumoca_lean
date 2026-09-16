import RumocaFMI3.TensorFloat64Copy
import RumocaFMI3.Float64Get
import RumocaFMI3.DerivativeCalls

/-! Tensor `fmi3GetFloat64` / `fmi3SetFloat64` bodies over a static tensor
instance record, as package-checked products.

Each accessor uses the same authored C subset as the scalar runtime. The
instance handle and lifecycle guard are validated exactly as the scalar bodies
do (through `Runtime.require`). One array value reference then denotes a whole
instance region under the FMI 3.0.2 array-access rule: reference `0` denotes the
independent time base (element count 1), `1` the input tensor `u`, `2` the state
tensor `x`, `3` the state derivative `der(x)` (each element count `shape.volume`),
and `4` the dense output tensor `J` (element count `oshape.volume`, present only
when the instance record carries the output). The getter copies the referenced
region into the caller's Float64 buffer; the setter copies the caller's values
into the writable region (`u` or `x`) after checking finiteness. The caller's
`nValues` must equal the referenced variable's element count; the copy uses one
counted `size_t` loop whose bound is that symbolic count, so no tensor
coordinate is enumerated. A request must name exactly one value reference
(`nValueReferences = 1`); a multi-reference aggregate is rejected, not
mishandled. Return status is `fmi3OK` on success and the scalar code's status on
rejection.

This is a package-checked product only: no production artifact is emitted, no
CLI or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. Every theorem is universal in the tensor shape,
the instance index of the static pool, the request lengths and the heap. -/
noncomputable section
namespace Rumoca.FMI3.TensorFloat64
open CTree CMemory CBody CLoops Float64Calls
open Rumoca.CMemory.TensorView Rumoca.CMemory.TensorRegion Rumoca.FMI3.TensorInstance

/-- The reference `valueReferences[0]`. -/
def vr0 : Expr := .index (Runtime.v "valueReferences") (Runtime.n 0)

/-! ### Small machine steps -/

section
variable [interface : CInterface]

/-- One rejected-condition-false check consumes its statement without effect. -/
theorem reject_false (env : Locals) (heap : Heap) (c : Expr) (msg : String) (rest : List Stmt)
    (hc : CBody.eval env heap c = some (boolean false)) :
    CBody.next (.running (Runtime.reject c msg :: rest) env heap) = some (.running rest env heap) := by
  simp [Runtime.reject, Runtime.branch, CBody.next, hc, boolean, Value.truth]

/-- A branch whose condition is false takes the else block. -/
theorem branch_false (env : Locals) (heap : Heap) (c : Expr) (yes no rest : List Stmt)
    (hc : CBody.eval env heap c = some (boolean false)) :
    CBody.next (.running (.branch c yes no :: rest) env heap) = some (.running (no ++ rest) env heap) := by
  simp [CBody.next, hc, boolean, Value.truth]

/-- A branch whose condition is true takes the then block. -/
theorem branch_true (env : Locals) (heap : Heap) (c : Expr) (yes no rest : List Stmt)
    (hc : CBody.eval env heap c = some (boolean true)) :
    CBody.next (.running (.branch c yes no :: rest) env heap) = some (.running (yes ++ rest) env heap) := by
  simp [CBody.next, hc, boolean, Value.truth]

/-- One declaration binds its evaluated, cast value into a fresh local. -/
theorem declare_next (env : Locals) (heap : Heap) (type name : String) (expr : Expr)
    (v0 value : Value) (rest : List Stmt) (fresh : env name = none)
    (ev : CBody.eval env heap expr = some v0) (cst : CBody.cast type v0 = some value) :
    CBody.next (.running (.declare type name expr :: rest) env heap) =
      some (.running rest (CBody.bind env name value) heap) := by
  simp [CBody.next, ev, cst, fresh]

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
  simp [vr0, Runtime.eqv, Runtime.n, Runtime.v, CBody.eval, rBound, refRead', Value.address,
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
  simp [CLoops.next, spelling, ev, cst, fresh, CLoops.bindType]

/-- A typed-machine branch whose condition is false takes the else block. -/
theorem cbranch_false (env : Locals) (types : Types) (heap : Heap) (c : Expr) (yes no rest : List Stmt)
    (safe : (yes.all CLoops.noDeclarations && no.all CLoops.noDeclarations) = true)
    (hc : CLoops.eval env types heap c = some (boolean false)) :
    CLoops.next (.running (.branch c yes no :: rest) env types heap) =
      some (.running (no ++ rest) env types heap) := by
  simp only [CLoops.next]; rw [safe]; simp [hc, boolean, Value.truth]

/-- A typed-machine branch whose condition is true takes the then block. -/
theorem cbranch_true (env : Locals) (types : Types) (heap : Heap) (c : Expr) (yes no rest : List Stmt)
    (safe : (yes.all CLoops.noDeclarations && no.all CLoops.noDeclarations) = true)
    (hc : CLoops.eval env types heap c = some (boolean true)) :
    CLoops.next (.running (.branch c yes no :: rest) env types heap) =
      some (.running (yes ++ rest) env types heap) := by
  simp only [CLoops.next]; rw [safe]; simp [hc, boolean, Value.truth]

end

/-! ### The getter body -/

/-- The remaining copy-loop suffix, shared by every value reference. -/
def getLoopSuffix : List Stmt :=
  [.declare "size_t" "k" (Runtime.n 0), CLoops.loop "k" (Runtime.v "expected") getCopyBody, Runtime.ok]

/-- One dispatch arm stages the region pointer and its element count. -/
def getArm (member : String) (count : Nat) : List Stmt :=
  [.assign (Runtime.v "src") (.address (Runtime.field member)), .assign (Runtime.v "expected") (Runtime.n count)]

/-- The `J` arm is present only when the instance record carries the output. -/
def getOutputArm (outputShape : Option Tensor.Shape) : List Stmt :=
  match outputShape with
  | some os => getArm outputName os.volume
  | none => [Runtime.fail "Unknown value reference"]

/-- Dispatch tail for reference 4 (the output). -/
def getDispatch4 (outputShape : Option Tensor.Shape) : List Stmt :=
  [Runtime.branch (Runtime.eqv vr0 (Runtime.n 4)) (getOutputArm outputShape)
    [Runtime.fail "Unknown value reference"]]

/-- Dispatch tail for references 3 and above. -/
def getDispatch3 (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) : List Stmt :=
  [Runtime.branch (Runtime.eqv vr0 (Runtime.n 3)) (getArm derivativeName shape.volume)
    (getDispatch4 outputShape)]

/-- Dispatch tail for references 2 and above. -/
def getDispatch2 (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) : List Stmt :=
  [Runtime.branch (Runtime.eqv vr0 (Runtime.n 2)) (getArm stateName shape.volume)
    (getDispatch3 shape outputShape)]

/-- Dispatch tail for references 1 and above. -/
def getDispatch1 (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) : List Stmt :=
  [Runtime.branch (Runtime.eqv vr0 (Runtime.n 1)) (getArm inputName shape.volume)
    (getDispatch2 shape outputShape)]

/-- Dispatch one value reference to its region, staging its pointer and count. -/
def getDispatch (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) : Stmt :=
  Runtime.branch (Runtime.eqv vr0 (Runtime.n 0)) (getArm timeName 1) (getDispatch1 shape outputShape)

theorem getArm_noDecl (member : String) (count : Nat) :
    (getArm member count).all CLoops.noDeclarations = true := by
  simp [getArm, CLoops.noDeclarations]

theorem outputArm_noDecl (outputShape : Option Tensor.Shape) :
    (getOutputArm outputShape).all CLoops.noDeclarations = true := by
  cases outputShape <;> simp [getOutputArm, getArm, Runtime.fail, Runtime.ret, CLoops.noDeclarations]

theorem d4_noDecl (outputShape : Option Tensor.Shape) :
    (getDispatch4 outputShape).all CLoops.noDeclarations = true := by
  cases outputShape <;>
    simp [getDispatch4, getOutputArm, getArm, Runtime.branch, Runtime.eqv, Runtime.fail, Runtime.ret,
      Runtime.v, CLoops.noDeclarations]

theorem d3_noDecl (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) :
    (getDispatch3 shape outputShape).all CLoops.noDeclarations = true := by
  cases outputShape <;>
    simp [getDispatch3, getDispatch4, getOutputArm, getArm, Runtime.branch, Runtime.eqv, Runtime.fail,
      Runtime.ret, Runtime.v, CLoops.noDeclarations]

theorem d2_noDecl (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) :
    (getDispatch2 shape outputShape).all CLoops.noDeclarations = true := by
  cases outputShape <;>
    simp [getDispatch2, getDispatch3, getDispatch4, getOutputArm, getArm, Runtime.branch, Runtime.eqv,
      Runtime.fail, Runtime.ret, Runtime.v, CLoops.noDeclarations]

theorem d1_noDecl (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) :
    (getDispatch1 shape outputShape).all CLoops.noDeclarations = true := by
  cases outputShape <;>
    simp [getDispatch1, getDispatch2, getDispatch3, getDispatch4, getOutputArm, getArm, Runtime.branch,
      Runtime.eqv, Runtime.fail, Runtime.ret, Runtime.v, CLoops.noDeclarations]

/-- The initial request check: a single value reference and non-null arrays. -/
def basicReject : Stmt :=
  Runtime.reject (Runtime.any [Runtime.nev (Runtime.v "nValueReferences") (Runtime.n 1),
    Runtime.negate (Runtime.v "valueReferences"), Runtime.negate (Runtime.v "values")])
    "Invalid Float64 array lengths or pointers"

/-- The count check between the dispatch and the copy loop. -/
def countReject : Stmt :=
  Runtime.reject (Runtime.nev (Runtime.v "nValues") (Runtime.v "expected")) "Invalid Float64 value count"

/-- The statements after the guard, run in the typed machine. -/
def getRest (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) : List Stmt :=
  [.declare "fmi3Float64 *" "src" Expr.nullPointer, .declare "size_t" "expected" (Runtime.n 0),
    getDispatch shape outputShape, countReject] ++ getLoopSuffix

def getBody (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) : List Stmt :=
  Runtime.require .get ++ (basicReject :: getRest shape outputShape)

def getFunction (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) : CTree.Function :=
  ⟨Float64Calls.signature false, getBody shape outputShape, false⟩

theorem getBody_closed (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) :
    (getFunction shape outputShape).body.all CBodyEmbedding.closedBlocks = true := by
  cases outputShape <;>
    simp [getFunction, getBody, getRest, getDispatch, getDispatch1, getDispatch2, getDispatch3,
      getDispatch4, basicReject, countReject, getLoopSuffix, getArm, getOutputArm, Runtime.require,
      Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject, Runtime.branch, Runtime.fail,
      Runtime.ret, Runtime.ok, getCopyBody, CBodyEmbedding.closedBlocks, CLoops.noDeclarations,
      CLoops.loop, CLoops.counterStep]

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

/-- The guard, executed in memory, reaches the typed statements after it. -/
theorem guard_reaches (shape : Tensor.Shape) (outputShape : Option Tensor.Shape)
    (program : CCalls.Events.Program E) (heap : Heap) (p refs buffer : Address) (n m : UInt64)
    (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape outputShape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (nref : n.toNat = 1) (refs_present : True) (values_present : True) (stack : CCalls.Typed.Continuation) :
    ∃ types0, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap stack)
      (.body (.running (getRest shape outputShape) (guardEnv p refs buffer n m) types0 heap)
        "fmi3Status" stack) := by
  have accepted := LifecycleGuard.accept (parameters (some p) (some refs) (some buffer) n m) heap p
    .get kind mode (basicReject :: getRest shape outputShape)
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  have hc : CBody.eval (guardEnv p refs buffer n m) heap
      (Runtime.any [Runtime.nev (Runtime.v "nValueReferences") (Runtime.n 1),
        Runtime.negate (Runtime.v "valueReferences"), Runtime.negate (Runtime.v "values")]) =
      some (boolean false) := by
    simp [Runtime.any, Runtime.either, Runtime.negate, Runtime.nev, Runtime.v, Runtime.n, CBody.eval,
      guardEnv, parameters, CBody.bind, CBody.resolve, CBody.comparison, boolean, Value.truth, nref]
  have prefix_run : CBody.run 4 (.running (getBody shape outputShape)
      (parameters (some p) (some refs) (some buffer) n m) heap) =
      some (.running (getRest shape outputShape) (guardEnv p refs buffer n m) heap) := by
    rw [getBody, show (4 : Nat) = 3 + 1 from rfl, CBody.run_add, accepted, Option.bind_some]
    exact run_one (reject_false (guardEnv p refs buffer n m) heap _
      "Invalid Float64 array lengths or pointers" (getRest shape outputShape) hc)
  exact CCalls.Events.body_prefix_reaches program (getFunction shape outputShape)
    (arguments (some p) (some refs) (some buffer) n m) (parameters (some p) (some refs) (some buffer) n m)
    (guardEnv p refs buffer n m) heap heap (getRest shape outputShape) stack 4 defined
    (parameters_bound false _ _ _ _ _) (getBody_closed shape outputShape) prefix_run

/-- The two staging declarations, executed in the typed machine. -/
theorem declares_reaches (program : CCalls.Events.Program E) (shape : Tensor.Shape)
    (outputShape : Option Tensor.Shape) (env0 : Locals) (types0 : Types) (heap : Heap)
    (stack : CCalls.Typed.Continuation) (fresh_src : env0 "src" = none) (fresh_exp : env0 "expected" = none) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (getRest shape outputShape) env0 types0 heap) "fmi3Status" stack)
      (.body (.running (getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (declaredEnv env0) (declaredTypes types0) heap) "fmi3Status" stack) := by
  have s1 : CLoops.next (.running (getRest shape outputShape) env0 types0 heap) =
      some (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (CBody.bind env0 "src" (.pointer none)) (CLoops.bindType types0 "src" .pointer) heap) :=
    declare_step_e env0 types0 heap "fmi3Float64 *" "src" Expr.nullPointer .pointer (.pointer none)
      (.pointer none) _ fresh_src rfl
      (by simp [Expr.nullPointer, CLoops.eval, CBody.eval, CBody.expressionCast, CBody.zeroLiteral]) rfl
  have s2 : CLoops.next (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (CBody.bind env0 "src" (.pointer none)) (CLoops.bindType types0 "src" .pointer) heap) =
      some (.running (getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (declaredEnv env0) (declaredTypes types0) heap) :=
    declare_step_e (CBody.bind env0 "src" (.pointer none)) (CLoops.bindType types0 "src" .pointer) heap
      "size_t" "expected" (Runtime.n 0) .size (.integer 0) (.integer 0) _
      (by simp [CBody.bind, fresh_exp]) rfl (by simp [Runtime.n, CLoops.eval, CBody.eval]) rfl
  exact .next (CCalls.Events.body_step program s1 "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s2 "fmi3Status" stack) (.refl _))

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
    simp [Runtime.nev, Runtime.v, CLoops.eval, CBody.eval, nvalBound, expBound, matched,
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

/-- The two dispatch assignments stage the region pointer and count. -/
theorem stage_reaches (program : CCalls.Events.Program E) (env0 : Locals) (types0 : Types) (heap : Heap)
    (p regionBase : Address) (member : String) (count : Nat) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (bounded : count < 2 ^ 64)
    (mBound : env0 "m" = some (.pointer (some p))) (regionEq : p.member member = regionBase) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (getArm member count ++ rest) (declaredEnv env0) (declaredTypes types0) heap)
        "fmi3Status" stack)
      (.body (.running rest (stagedEnv env0 regionBase count) (declaredTypes types0) heap)
        "fmi3Status" stack) := by
  have addr : CLoops.eval (declaredEnv env0) (declaredTypes types0) heap (.address (Runtime.field member)) =
      some (.pointer (some regionBase)) := by
    apply CBodyEmbedding.eval_refines
    simp [Runtime.field, Runtime.v, CBody.eval, CBody.lvalue, declaredEnv, CBody.bind, CBody.resolve,
      mBound, Value.address, regionEq]
  have s1 : CLoops.next (.running (getArm member count ++ rest) (declaredEnv env0) (declaredTypes types0) heap) =
      some (.running (.assign (Runtime.v "expected") (Runtime.n count) :: rest)
        (CBody.bind (declaredEnv env0) "src" (.pointer (some regionBase))) (declaredTypes types0) heap) := by
    have := CLoops.assign_local (declaredEnv env0) (declaredTypes types0) heap "src"
      (.address (Runtime.field member)) (.assign (Runtime.v "expected") (Runtime.n count) :: rest)
      (.pointer none) (.pointer (some regionBase)) (.pointer (some regionBase)) .pointer
      (by simp [declaredEnv, CBody.bind]) (by simp [declaredTypes, CLoops.bindType]) addr rfl
    simpa [getArm, Runtime.v] using this
  have s2 : CLoops.next (.running (.assign (Runtime.v "expected") (Runtime.n count) :: rest)
        (CBody.bind (declaredEnv env0) "src" (.pointer (some regionBase))) (declaredTypes types0) heap) =
      some (.running rest (stagedEnv env0 regionBase count) (declaredTypes types0) heap) := by
    have := CLoops.assign_local (CBody.bind (declaredEnv env0) "src" (.pointer (some regionBase)))
      (declaredTypes types0) heap "expected" (Runtime.n count) rest (.integer 0) (.integer count)
      (.integer count) .size (by simp [declaredEnv, CBody.bind]) (by simp [declaredTypes, CLoops.bindType])
      (by simp [Runtime.n, CLoops.eval, CBody.eval]) (CLoops.convert_size_nat count bounded)
    simpa [Runtime.v, stagedEnv] using this
  exact .next (CCalls.Events.body_step program s1 "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s2 "fmi3Status" stack) (.refl _))

end

/-! ### Complete getter, per value reference -/

section
variable [static : StaticLiterals]
private local instance getInterface : CInterface := cInterface static.addresses

/-- The complete getter for one value reference, given the navigation that
selects the region. Region-agnostic apart from that navigation. -/
theorem get_reaches_of (shape : Tensor.Shape) (outputShape : Option Tensor.Shape)
    (program : CCalls.Events.Program E) (heap : Heap) (p refs buffer : Address) (n m : UInt64)
    (kind : Kind) (mode : Mode) (member : String) (rshape : Tensor.Shape) (regionValues : Values rshape)
    (stack : CCalls.Typed.Continuation)
    (nref : n.toNat = 1) (matched : m.toNat = rshape.volume) (bounded : rshape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape outputShape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (readable : Reads heap (p.member member) regionValues)
    (writable : Writable heap buffer rshape.volume)
    (separate : ∀ a < rshape.volume, ∀ b < rshape.volume, (p.member member).index a ≠ buffer.index b)
    (nav : ∀ types0, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" stack)
      (.body (.running (getArm member rshape.volume ++ (countReject :: getLoopSuffix))
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" stack)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap stack)
      (.returning (.integer 0) (written heap buffer regionValues rshape.volume) stack) := by
  obtain ⟨types0, entered⟩ := guard_reaches shape outputShape program heap p refs buffer n m kind mode
    defined hk hm allowed nref trivial trivial stack
  refine entered.trans ((declares_reaches program shape outputShape (guardEnv p refs buffer n m) types0
    heap stack (by simp [guardEnv, parameters, CBody.bind]) (by simp [guardEnv, parameters, CBody.bind])).trans ?_)
  refine (nav types0).trans ?_
  refine (stage_reaches program (guardEnv p refs buffer n m) types0 heap p (p.member member) member
    rshape.volume (countReject :: getLoopSuffix) stack bounded (by simp [guardEnv, parameters, CBody.bind])
    rfl).trans ?_
  exact get_tail_reaches program (guardEnv p refs buffer n m) (declaredTypes types0) heap (p.member member)
    buffer rshape regionValues m stack bounded matched
    (by simp [stagedEnv, declaredEnv, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind])
    (by simp [stagedEnv, declaredEnv, guardEnv, parameters, CBody.bind]) readable writable separate

theorem get_behaviors_of (shape : Tensor.Shape) (outputShape : Option Tensor.Shape)
    (program : CCalls.Events.Program E) (heap : Heap) (p refs buffer : Address) (n m : UInt64)
    (kind : Kind) (mode : Mode) (member : String) (rshape : Tensor.Shape) (regionValues : Values rshape)
    (nref : n.toNat = 1) (matched : m.toNat = rshape.volume) (bounded : rshape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape outputShape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (readable : Reads heap (p.member member) regionValues)
    (writable : Writable heap buffer rshape.volume)
    (separate : ∀ a < rshape.volume, ∀ b < rshape.volume, (p.member member).index a ≠ buffer.index b)
    (nav : ∀ types0, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" .done)
      (.body (.running (getArm member rshape.volume ++ (countReject :: getLoopSuffix))
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" .done))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap buffer regionValues rshape.volume⟩ :=
  (CCalls.Events.internal_prefix program (get_reaches_of shape outputShape program heap p refs buffer n m
    kind mode member rshape regionValues .done nref matched bounded defined hk hm allowed readable writable
    separate nav) (CCalls.Events.return_forced program _ _)).behaviors behavior

end

/-! ### Per-reference navigation -/

section
variable [interface : CInterface]

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

variable (program : CCalls.Events.Program E) (shape : Tensor.Shape) (outputShape : Option Tensor.Shape)
  (p refs buffer : Address) (n m : UInt64) (types0 : Types) (heap : Heap)
  (stack : CCalls.Typed.Continuation)

/-- Env after the guard and staging declarations, over which the dispatch runs. -/
private def navEnv : Locals := declaredEnv (guardEnv p refs buffer n m)
private def navTypes : Types := declaredTypes types0

private theorem navRefs (refs buffer : Address) :
    resolve (navEnv p refs buffer n m) "valueReferences" = some (.pointer (some refs)) := by
  simp [navEnv, declaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve]

/-- Navigate the dispatch to reference 2 (the state `x`). -/
theorem get_nav_state (refRead : load heap (refs.index 0) = some (.integer 2)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" stack)
      (.body (.running (getArm stateName shape.volume ++ (countReject :: getLoopSuffix))
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" stack) := by
  refine .next (CCalls.Events.body_step program (cbranch_false _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d1_noDecl]) (cvr0_ne _ _ heap refs 2 0 (navRefs p n m refs buffer) refRead (by decide)))
    "fmi3Status" stack) ?_
  refine .next (CCalls.Events.body_step program (cbranch_false _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d2_noDecl]) (cvr0_ne _ _ heap refs 2 1 (navRefs p n m refs buffer) refRead (by decide)))
    "fmi3Status" stack) ?_
  refine .next (CCalls.Events.body_step program (cbranch_true _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d3_noDecl]) (cvr0_eq _ _ heap refs 2 (navRefs p n m refs buffer) refRead))
    "fmi3Status" stack) (.refl _)

/-- Navigate the dispatch to reference 0 (the time base). -/
theorem get_nav_time (refRead : load heap (refs.index 0) = some (.integer 0)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" stack)
      (.body (.running (getArm timeName Tensor.scalar.volume ++ (countReject :: getLoopSuffix))
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" stack) :=
  .next (CCalls.Events.body_step program (cbranch_true _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d1_noDecl]) (cvr0_eq _ _ heap refs 0 (navRefs p n m refs buffer) refRead))
    "fmi3Status" stack) (.refl _)

/-- Navigate the dispatch to reference 1 (the input `u`). -/
theorem get_nav_input (refRead : load heap (refs.index 0) = some (.integer 1)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" stack)
      (.body (.running (getArm inputName shape.volume ++ (countReject :: getLoopSuffix))
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" stack) := by
  refine .next (CCalls.Events.body_step program (cbranch_false _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d1_noDecl]) (cvr0_ne _ _ heap refs 1 0 (navRefs p n m refs buffer) refRead (by decide)))
    "fmi3Status" stack) ?_
  exact .next (CCalls.Events.body_step program (cbranch_true _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d2_noDecl]) (cvr0_eq _ _ heap refs 1 (navRefs p n m refs buffer) refRead))
    "fmi3Status" stack) (.refl _)

/-- Navigate the dispatch to reference 3 (the derivative `der(x)`). -/
theorem get_nav_deriv (refRead : load heap (refs.index 0) = some (.integer 3)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" stack)
      (.body (.running (getArm derivativeName shape.volume ++ (countReject :: getLoopSuffix))
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" stack) := by
  refine .next (CCalls.Events.body_step program (cbranch_false _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d1_noDecl]) (cvr0_ne _ _ heap refs 3 0 (navRefs p n m refs buffer) refRead (by decide)))
    "fmi3Status" stack) ?_
  refine .next (CCalls.Events.body_step program (cbranch_false _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d2_noDecl]) (cvr0_ne _ _ heap refs 3 1 (navRefs p n m refs buffer) refRead (by decide)))
    "fmi3Status" stack) ?_
  refine .next (CCalls.Events.body_step program (cbranch_false _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d3_noDecl]) (cvr0_ne _ _ heap refs 3 2 (navRefs p n m refs buffer) refRead (by decide)))
    "fmi3Status" stack) ?_
  exact .next (CCalls.Events.body_step program (cbranch_true _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d4_noDecl]) (cvr0_eq _ _ heap refs 3 (navRefs p n m refs buffer) refRead))
    "fmi3Status" stack) (.refl _)

/-- Navigate the dispatch to reference 4 (the output `J`), present in the record. -/
theorem get_nav_output (os : Tensor.Shape) (present : outputShape = some os)
    (refRead : load heap (refs.index 0) = some (.integer 4)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" stack)
      (.body (.running (getArm outputName os.volume ++ (countReject :: getLoopSuffix))
        (declaredEnv (guardEnv p refs buffer n m)) (declaredTypes types0) heap) "fmi3Status" stack) := by
  subst present
  refine .next (CCalls.Events.body_step program (cbranch_false _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d1_noDecl]) (cvr0_ne _ _ heap refs 4 0 (navRefs p n m refs buffer) refRead (by decide)))
    "fmi3Status" stack) ?_
  refine .next (CCalls.Events.body_step program (cbranch_false _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d2_noDecl]) (cvr0_ne _ _ heap refs 4 1 (navRefs p n m refs buffer) refRead (by decide)))
    "fmi3Status" stack) ?_
  refine .next (CCalls.Events.body_step program (cbranch_false _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d3_noDecl]) (cvr0_ne _ _ heap refs 4 2 (navRefs p n m refs buffer) refRead (by decide)))
    "fmi3Status" stack) ?_
  refine .next (CCalls.Events.body_step program (cbranch_false _ _ heap _ _ _ _
    (by simp [getArm_noDecl, d4_noDecl]) (cvr0_ne _ _ heap refs 4 3 (navRefs p n m refs buffer) refRead (by decide)))
    "fmi3Status" stack) ?_
  exact .next (CCalls.Events.body_step program (cbranch_true _ _ heap _ _ _ _
    (by simp [getArm_noDecl, getOutputArm, Runtime.fail, Runtime.ret, CLoops.noDeclarations])
      (cvr0_eq _ _ heap refs 4 (navRefs p n m refs buffer) refRead)) "fmi3Status" stack) (.refl _)

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

/-! ### The getter behavior for each accepted reference -/

section
variable [static : StaticLiterals]
private local instance regionInterface : CInterface := cInterface static.addresses
variable (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) (program : CCalls.Events.Program E)
  (heap : Heap) (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode)

/-- The tensor getter reading the time base. -/
theorem get_behaviors_time (values : Values Tensor.scalar) (nref : n.toNat = 1) (nval : m.toNat = 1)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape outputShape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) (allowed : Reference.Allowed .get kind mode)
    (refRead : load heap (refs.index 0) = some (.integer 0))
    (readable : Reads heap (p.member timeName) values) (writable : Writable heap buffer 1)
    (separate : ∀ a < 1, ∀ b < 1, (p.member timeName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap buffer values 1⟩ :=
  get_behaviors_of shape outputShape program heap p refs buffer n m kind mode timeName Tensor.scalar values
    nref nval (by decide) defined hk hm allowed readable writable separate
    (fun types0 => get_nav_time program shape outputShape p refs buffer n m types0 heap .done refRead) behavior

/-- The tensor getter reading the input `u`. -/
theorem get_behaviors_input (values : Values shape) (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape outputShape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) (allowed : Reference.Allowed .get kind mode)
    (refRead : load heap (refs.index 0) = some (.integer 1))
    (readable : Reads heap (p.member inputName) values) (writable : Writable heap buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume, (p.member inputName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap buffer values shape.volume⟩ :=
  get_behaviors_of shape outputShape program heap p refs buffer n m kind mode inputName shape values
    nref nval (nval ▸ m.toNat_lt_size) defined hk hm allowed readable writable separate
    (fun types0 => get_nav_input program shape outputShape p refs buffer n m types0 heap .done refRead) behavior

/-- The tensor getter reading the state `x`. -/
theorem get_behaviors_state (values : Values shape) (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape outputShape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) (allowed : Reference.Allowed .get kind mode)
    (refRead : load heap (refs.index 0) = some (.integer 2))
    (readable : Reads heap (p.member stateName) values) (writable : Writable heap buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume, (p.member stateName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap buffer values shape.volume⟩ :=
  get_behaviors_of shape outputShape program heap p refs buffer n m kind mode stateName shape values
    nref nval (nval ▸ m.toNat_lt_size) defined hk hm allowed readable writable separate
    (fun types0 => get_nav_state program shape outputShape p refs buffer n m types0 heap .done refRead) behavior

/-- The tensor getter reading the derivative `der(x)`. -/
theorem get_behaviors_deriv (values : Values shape) (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape outputShape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) (allowed : Reference.Allowed .get kind mode)
    (refRead : load heap (refs.index 0) = some (.integer 3))
    (readable : Reads heap (p.member derivativeName) values) (writable : Writable heap buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume, (p.member derivativeName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap buffer values shape.volume⟩ :=
  get_behaviors_of shape outputShape program heap p refs buffer n m kind mode derivativeName shape values
    nref nval (nval ▸ m.toNat_lt_size) defined hk hm allowed readable writable separate
    (fun types0 => get_nav_deriv program shape outputShape p refs buffer n m types0 heap .done refRead) behavior

/-- The tensor getter reading the output `J`, present in the record. -/
theorem get_behaviors_output (os : Tensor.Shape) (present : outputShape = some os) (values : Values os)
    (nref : n.toNat = 1) (nval : m.toNat = os.volume)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape outputShape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) (allowed : Reference.Allowed .get kind mode)
    (refRead : load heap (refs.index 0) = some (.integer 4))
    (readable : Reads heap (p.member outputName) values) (writable : Writable heap buffer os.volume)
    (separate : ∀ a < os.volume, ∀ b < os.volume, (p.member outputName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap buffer values os.volume⟩ :=
  get_behaviors_of shape outputShape program heap p refs buffer n m kind mode outputName os values
    nref nval (nval ▸ m.toNat_lt_size) defined hk hm allowed readable writable separate
    (fun types0 => get_nav_output program shape outputShape p refs buffer n m types0 heap .done os present refRead)
    behavior

end

/-! ### The getter bound to the static tensor instance record -/

section
variable [static : StaticLiterals]
private local instance instGetInterface : CInterface := cInterface static.addresses
variable (program : CCalls.Events.Program E) (backing : Heap) (pool : Address) (i : Nat)
  (shape oshape : Tensor.Shape) (time : Values Tensor.scalar) (state input : Values shape)
  (output : Option (Values oshape)) (refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode)

/-- The tensor getter reading the state region of instance `i`: it writes exactly
the state into the caller buffer and changes no instance cell. -/
theorem get_instance_behaviors_state (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape (output.map fun _ => oshape))))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load (TensorInstance.store backing pool i shape oshape time state input output)
      (refs.index 0) = some (.integer 2))
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
  get_behaviors_state shape (output.map fun _ => oshape) program _ (TensorInstance.record pool i) refs buffer
    n m kind mode state nref nval defined hk hm allowed refRead
    (TensorInstance.reads_state backing pool i shape oshape time state input output) writable separate behavior

/-- The tensor getter reading the input region of instance `i`. -/
theorem get_instance_behaviors_input (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape (output.map fun _ => oshape))))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load (TensorInstance.store backing pool i shape oshape time state input output)
      (refs.index 0) = some (.integer 1))
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
  get_behaviors_input shape (output.map fun _ => oshape) program _ (TensorInstance.record pool i) refs buffer
    n m kind mode input nref nval defined hk hm allowed refRead
    (TensorInstance.reads_input backing pool i shape oshape time state input output) writable separate behavior

/-- The tensor getter reading the time base of instance `i`. -/
theorem get_instance_behaviors_time (nref : n.toNat = 1) (nval : m.toNat = 1)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape (output.map fun _ => oshape))))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load (TensorInstance.store backing pool i shape oshape time state input output)
      (refs.index 0) = some (.integer 0))
    (writable : Writable (TensorInstance.store backing pool i shape oshape time state input output) buffer 1)
    (separate : ∀ a < 1, ∀ b < 1, (TensorInstance.field pool i timeName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
        (TensorInstance.store backing pool i shape oshape time state input output) .done) behavior ↔
      behavior = .terminates []
        ⟨.integer 0, written (TensorInstance.store backing pool i shape oshape time state input output)
          buffer time 1⟩ :=
  get_behaviors_time shape (output.map fun _ => oshape) program _ (TensorInstance.record pool i) refs buffer
    n m kind mode time nref nval defined hk hm allowed refRead
    (reads_time backing pool i shape oshape time state input output) writable separate behavior

/-- The tensor getter reading the output region of instance `i`, present in the record. -/
theorem get_instance_behaviors_output (J : Values oshape) (nref : n.toNat = 1) (nval : m.toNat = oshape.volume)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape (some oshape))))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input (some J))
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input (some J))
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load (TensorInstance.store backing pool i shape oshape time state input (some J))
      (refs.index 0) = some (.integer 4))
    (writable : Writable (TensorInstance.store backing pool i shape oshape time state input (some J))
      buffer oshape.volume)
    (separate : ∀ a < oshape.volume, ∀ b < oshape.volume,
      (TensorInstance.field pool i outputName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
        (TensorInstance.store backing pool i shape oshape time state input (some J)) .done) behavior ↔
      behavior = .terminates []
        ⟨.integer 0, written (TensorInstance.store backing pool i shape oshape time state input (some J))
          buffer J oshape.volume⟩ :=
  get_behaviors_output shape (some oshape) program _ (TensorInstance.record pool i) refs buffer n m kind mode
    oshape rfl J nref nval defined hk hm allowed refRead
    (reads_output backing pool i shape oshape time state input J) writable separate behavior

/-- The tensor getter reading the derivative region of instance `i`, after the
right-hand side has written it (the derivative values are the current contents). -/
theorem get_instance_behaviors_deriv (derivatives : Values shape) (nref : n.toNat = 1)
    (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape (output.map fun _ => oshape))))
    (hk : load (written (TensorInstance.store backing pool i shape oshape time state input output)
      (TensorInstance.field pool i derivativeName) derivatives shape.volume)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (written (TensorInstance.store backing pool i shape oshape time state input output)
      (TensorInstance.field pool i derivativeName) derivatives shape.volume)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode)
    (refRead : load (written (TensorInstance.store backing pool i shape oshape time state input output)
      (TensorInstance.field pool i derivativeName) derivatives shape.volume)
      (refs.index 0) = some (.integer 3))
    (writable : Writable (written (TensorInstance.store backing pool i shape oshape time state input output)
      (TensorInstance.field pool i derivativeName) derivatives shape.volume) buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
        (written (TensorInstance.store backing pool i shape oshape time state input output)
          (TensorInstance.field pool i derivativeName) derivatives shape.volume) .done) behavior ↔
      behavior = .terminates []
        ⟨.integer 0, written (written (TensorInstance.store backing pool i shape oshape time state input output)
          (TensorInstance.field pool i derivativeName) derivatives shape.volume) buffer derivatives shape.volume⟩ :=
  get_behaviors_deriv shape (output.map fun _ => oshape) program _ (TensorInstance.record pool i) refs buffer
    n m kind mode derivatives nref nval defined hk hm allowed refRead
    (written_reads _ (TensorInstance.field pool i derivativeName) derivatives) writable separate behavior

end

/-! ### The setter body -/

/-- The setter finiteness check applied to each caller value before any write. -/
def validateBody : List Stmt :=
  [Runtime.reject (Runtime.negate (Runtime.finite output)) "Only finite Float64 values may be set"]

theorem validateBody_closed : validateBody.all CLoops.noDeclarations = true := by
  simp [validateBody, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, CLoops.noDeclarations]

/-- The setter loop suffix: validate finiteness, then copy the caller values. -/
def setLoopSuffix : List Stmt :=
  [.declare "size_t" "k" (Runtime.n 0), CLoops.loop "k" (Runtime.v "expected") validateBody,
    .assign (Runtime.v "k") (Runtime.n 0), CLoops.loop "k" (Runtime.v "expected") setCopyBody, Runtime.ok]

/-- One setter dispatch arm stages the writable region pointer and its count. -/
def setArm (member : String) (count : Nat) : List Stmt :=
  [.assign (Runtime.v "dst") (.address (Runtime.field member)), .assign (Runtime.v "expected") (Runtime.n count)]

/-- Setter dispatch tail for reference 2 (the state `x`). -/
def setDispatch2 (shape : Tensor.Shape) : List Stmt :=
  [Runtime.branch (Runtime.eqv vr0 (Runtime.n 2)) (setArm stateName shape.volume)
    [Runtime.fail "Unknown or read-only value reference"]]

/-- The setter dispatch: only the input `u` (1) and state `x` (2) are writable. -/
def setDispatch (shape : Tensor.Shape) : Stmt :=
  Runtime.branch (Runtime.eqv vr0 (Runtime.n 1)) (setArm inputName shape.volume) (setDispatch2 shape)

def setRest (shape : Tensor.Shape) : List Stmt :=
  [.declare "fmi3Float64 *" "dst" Expr.nullPointer, .declare "size_t" "expected" (Runtime.n 0),
    setDispatch shape, countReject] ++ setLoopSuffix

def setBody (shape : Tensor.Shape) : List Stmt :=
  Runtime.require .setStart ++ (basicReject :: setRest shape)

def setFunction (shape : Tensor.Shape) : CTree.Function :=
  ⟨Float64Calls.signature true, setBody shape, false⟩

theorem setArm_noDecl (member : String) (count : Nat) :
    (setArm member count).all CLoops.noDeclarations = true := by simp [setArm, CLoops.noDeclarations]

theorem setDispatch2_noDecl (shape : Tensor.Shape) :
    (setDispatch2 shape).all CLoops.noDeclarations = true := by
  simp [setDispatch2, setArm, Runtime.branch, Runtime.eqv, Runtime.fail, Runtime.ret, Runtime.v,
    CLoops.noDeclarations]

theorem setBody_closed (shape : Tensor.Shape) :
    (setFunction shape).body.all CBodyEmbedding.closedBlocks = true := by
  simp [setFunction, setBody, setRest, setDispatch, setDispatch2, basicReject, countReject, setLoopSuffix,
    setArm, validateBody, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject,
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
    simp [output, Runtime.v, CBody.eval, valuesBound, counter, Value.address, read]
  simp [validateBody, Runtime.reject, Runtime.branch, Runtime.negate, Runtime.finite, Runtime.call,
    Runtime.v, CLoops.next, CLoops.eval, CLoops.noDeclarations, Runtime.fail, Runtime.ret, CBody.eval,
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
    simpa [Runtime.v, CBody.eval, counterEnv, CBody.bind, resolve] using count
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
theorem set_guard_reaches (shape : Tensor.Shape) (program : CCalls.Events.Program E) (heap : Heap)
    (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode) (nref : n.toNat = 1)
    (stack : CCalls.Typed.Continuation) :
    ∃ types0, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3SetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap stack)
      (.body (.running (setRest shape) (guardEnv p refs buffer n m) types0 heap) "fmi3Status" stack) := by
  have accepted := LifecycleGuard.accept (parameters (some p) (some refs) (some buffer) n m) heap p
    .setStart kind mode (basicReject :: setRest shape)
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  have hc : CBody.eval (guardEnv p refs buffer n m) heap
      (Runtime.any [Runtime.nev (Runtime.v "nValueReferences") (Runtime.n 1),
        Runtime.negate (Runtime.v "valueReferences"), Runtime.negate (Runtime.v "values")]) =
      some (boolean false) := by
    simp [Runtime.any, Runtime.either, Runtime.negate, Runtime.nev, Runtime.v, Runtime.n, CBody.eval,
      guardEnv, parameters, CBody.bind, CBody.resolve, CBody.comparison, boolean, Value.truth, nref]
  have prefix_run : CBody.run 4 (.running (setBody shape)
      (parameters (some p) (some refs) (some buffer) n m) heap) =
      some (.running (setRest shape) (guardEnv p refs buffer n m) heap) := by
    rw [setBody, show (4 : Nat) = 3 + 1 from rfl, CBody.run_add, accepted, Option.bind_some]
    exact run_one (reject_false (guardEnv p refs buffer n m) heap _
      "Invalid Float64 array lengths or pointers" (setRest shape) hc)
  exact CCalls.Events.body_prefix_reaches program (setFunction shape)
    (arguments (some p) (some refs) (some buffer) n m) (parameters (some p) (some refs) (some buffer) n m)
    (guardEnv p refs buffer n m) heap heap (setRest shape) stack 4 defined
    (parameters_bound true _ _ _ _ _) (setBody_closed shape) prefix_run

/-- The setter's two staging declarations. -/
theorem set_declares_reaches (program : CCalls.Events.Program E) (shape : Tensor.Shape) (env0 : Locals)
    (types0 : Types) (heap : Heap) (stack : CCalls.Typed.Continuation)
    (fresh_dst : env0 "dst" = none) (fresh_exp : env0 "expected" = none) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (setRest shape) env0 types0 heap) "fmi3Status" stack)
      (.body (.running (setDispatch shape :: countReject :: setLoopSuffix)
        (setDeclaredEnv env0) (setDeclaredTypes types0) heap) "fmi3Status" stack) := by
  have s1 : CLoops.next (.running (setRest shape) env0 types0 heap) =
      some (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        setDispatch shape :: countReject :: setLoopSuffix)
        (CBody.bind env0 "dst" (.pointer none)) (CLoops.bindType types0 "dst" .pointer) heap) :=
    declare_step_e env0 types0 heap "fmi3Float64 *" "dst" Expr.nullPointer .pointer (.pointer none)
      (.pointer none) _ fresh_dst rfl
      (by simp [Expr.nullPointer, CLoops.eval, CBody.eval, CBody.expressionCast, CBody.zeroLiteral]) rfl
  have s2 : CLoops.next (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        setDispatch shape :: countReject :: setLoopSuffix)
        (CBody.bind env0 "dst" (.pointer none)) (CLoops.bindType types0 "dst" .pointer) heap) =
      some (.running (setDispatch shape :: countReject :: setLoopSuffix)
        (setDeclaredEnv env0) (setDeclaredTypes types0) heap) := by
    have := declare_step_e (CBody.bind env0 "dst" (.pointer none)) (CLoops.bindType types0 "dst" .pointer)
      heap "size_t" "expected" (Runtime.n 0) .size (.integer 0) (.integer 0)
      (setDispatch shape :: countReject :: setLoopSuffix)
      (by simp [CBody.bind, fresh_exp]) rfl (by simp [Runtime.n, CLoops.eval, CBody.eval]) rfl
    simpa [setDeclaredEnv, setDeclaredTypes] using this
  exact .next (CCalls.Events.body_step program s1 "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s2 "fmi3Status" stack) (.refl _))

/-- The setter's two dispatch assignments stage the writable region pointer and count. -/
theorem set_stage_reaches (program : CCalls.Events.Program E) (env0 : Locals) (types0 : Types) (heap : Heap)
    (p regionBase : Address) (member : String) (count : Nat) (rest : List Stmt)
    (stack : CCalls.Typed.Continuation) (bounded : count < 2 ^ 64)
    (mBound : env0 "m" = some (.pointer (some p))) (regionEq : p.member member = regionBase) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (setArm member count ++ rest) (setDeclaredEnv env0) (setDeclaredTypes types0) heap)
        "fmi3Status" stack)
      (.body (.running rest (stagedSetEnv env0 regionBase count) (setDeclaredTypes types0) heap)
        "fmi3Status" stack) := by
  have addr : CLoops.eval (setDeclaredEnv env0) (setDeclaredTypes types0) heap (.address (Runtime.field member)) =
      some (.pointer (some regionBase)) := by
    apply CBodyEmbedding.eval_refines
    simp [Runtime.field, Runtime.v, CBody.eval, CBody.lvalue, setDeclaredEnv, CBody.bind, CBody.resolve,
      mBound, Value.address, regionEq]
  have s1 : CLoops.next (.running (setArm member count ++ rest) (setDeclaredEnv env0) (setDeclaredTypes types0) heap) =
      some (.running (.assign (Runtime.v "expected") (Runtime.n count) :: rest)
        (CBody.bind (setDeclaredEnv env0) "dst" (.pointer (some regionBase))) (setDeclaredTypes types0) heap) := by
    have := CLoops.assign_local (setDeclaredEnv env0) (setDeclaredTypes types0) heap "dst"
      (.address (Runtime.field member)) (.assign (Runtime.v "expected") (Runtime.n count) :: rest)
      (.pointer none) (.pointer (some regionBase)) (.pointer (some regionBase)) .pointer
      (by simp [setDeclaredEnv, CBody.bind]) (by simp [setDeclaredTypes, CLoops.bindType]) addr rfl
    simpa [setArm, Runtime.v] using this
  have s2 : CLoops.next (.running (.assign (Runtime.v "expected") (Runtime.n count) :: rest)
        (CBody.bind (setDeclaredEnv env0) "dst" (.pointer (some regionBase))) (setDeclaredTypes types0) heap) =
      some (.running rest (stagedSetEnv env0 regionBase count) (setDeclaredTypes types0) heap) := by
    have := CLoops.assign_local (CBody.bind (setDeclaredEnv env0) "dst" (.pointer (some regionBase)))
      (setDeclaredTypes types0) heap "expected" (Runtime.n count) rest (.integer 0) (.integer count)
      (.integer count) .size (by simp [setDeclaredEnv, CBody.bind]) (by simp [setDeclaredTypes, CLoops.bindType])
      (by simp [Runtime.n, CLoops.eval, CBody.eval]) (CLoops.convert_size_nat count bounded)
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
    simp [Runtime.nev, Runtime.v, CLoops.eval, CBody.eval, nvalBound, expBound, matched,
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

/-! ### Setter navigation and per-reference behavior -/

section
variable [interface : CInterface]
variable (program : CCalls.Events.Program E) (shape : Tensor.Shape) (p refs buffer : Address) (n m : UInt64)
  (types0 : Types) (heap : Heap) (stack : CCalls.Typed.Continuation)

/-- Navigate the setter dispatch to reference 1 (the input `u`). -/
theorem set_nav_input (refRead : load heap (refs.index 0) = some (.integer 1)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (setDispatch shape :: countReject :: setLoopSuffix)
        (setDeclaredEnv (guardEnv p refs buffer n m)) (setDeclaredTypes types0) heap) "fmi3Status" stack)
      (.body (.running (setArm inputName shape.volume ++ (countReject :: setLoopSuffix))
        (setDeclaredEnv (guardEnv p refs buffer n m)) (setDeclaredTypes types0) heap) "fmi3Status" stack) := by
  have rBound : resolve (setDeclaredEnv (guardEnv p refs buffer n m)) "valueReferences" =
      some (.pointer (some refs)) := by
    simp [setDeclaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve]
  exact .next (CCalls.Events.body_step program (cbranch_true _ _ heap _ _ _ _
    (by simp [setArm_noDecl, setDispatch2_noDecl]) (cvr0_eq _ _ heap refs 1 rBound refRead))
    "fmi3Status" stack) (.refl _)

/-- Navigate the setter dispatch to reference 2 (the state `x`). -/
theorem set_nav_state (refRead : load heap (refs.index 0) = some (.integer 2)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (setDispatch shape :: countReject :: setLoopSuffix)
        (setDeclaredEnv (guardEnv p refs buffer n m)) (setDeclaredTypes types0) heap) "fmi3Status" stack)
      (.body (.running (setArm stateName shape.volume ++ (countReject :: setLoopSuffix))
        (setDeclaredEnv (guardEnv p refs buffer n m)) (setDeclaredTypes types0) heap) "fmi3Status" stack) := by
  have rBound : resolve (setDeclaredEnv (guardEnv p refs buffer n m)) "valueReferences" =
      some (.pointer (some refs)) := by
    simp [setDeclaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve]
  refine .next (CCalls.Events.body_step program (cbranch_false _ _ heap _ _ _ _
    (by simp [setArm_noDecl, setDispatch2_noDecl]) (cvr0_ne _ _ heap refs 2 1 rBound refRead (by decide)))
    "fmi3Status" stack) ?_
  exact .next (CCalls.Events.body_step program (cbranch_true _ _ heap _ _ _ _
    (by simp [setArm_noDecl, Runtime.fail, Runtime.ret, CLoops.noDeclarations])
      (cvr0_eq _ _ heap refs 2 rBound refRead)) "fmi3Status" stack) (.refl _)

end

section
variable [static : StaticLiterals]
private local instance setBehaviorInterface : CInterface := cInterface static.addresses

/-- The complete setter for one writable value reference, given the navigation. -/
theorem set_reaches_of (shape : Tensor.Shape) (program : CCalls.Events.Program E) (heap : Heap)
    (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (member : String)
    (rshape : Tensor.Shape) (values : Values rshape) (stack : CCalls.Typed.Continuation)
    (nref : n.toNat = 1) (matched : m.toNat = rshape.volume) (bounded : rshape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (readable : Reads heap buffer values)
    (writable : Writable heap (p.member member) rshape.volume)
    (separate : ∀ a < rshape.volume, ∀ b < rshape.volume, (p.member member).index a ≠ buffer.index b)
    (nav : ∀ types0, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (setDispatch shape :: countReject :: setLoopSuffix)
        (setDeclaredEnv (guardEnv p refs buffer n m)) (setDeclaredTypes types0) heap) "fmi3Status" stack)
      (.body (.running (setArm member rshape.volume ++ (countReject :: setLoopSuffix))
        (setDeclaredEnv (guardEnv p refs buffer n m)) (setDeclaredTypes types0) heap) "fmi3Status" stack)) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3SetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap stack)
      (.returning (.integer 0) (written heap (p.member member) values rshape.volume) stack) := by
  obtain ⟨types0, entered⟩ := set_guard_reaches shape program heap p refs buffer n m kind mode defined
    hk hm allowed nref stack
  refine entered.trans ((set_declares_reaches program shape (guardEnv p refs buffer n m) types0 heap stack
    (by simp [guardEnv, parameters, CBody.bind]) (by simp [guardEnv, parameters, CBody.bind])).trans ?_)
  refine (nav types0).trans ?_
  refine (set_stage_reaches program (guardEnv p refs buffer n m) types0 heap p (p.member member) member
    rshape.volume (countReject :: setLoopSuffix) stack bounded (by simp [guardEnv, parameters, CBody.bind])
    rfl).trans ?_
  exact set_tail_reaches program (guardEnv p refs buffer n m) (setDeclaredTypes types0) heap (p.member member)
    buffer rshape values m stack bounded matched
    (by simp [stagedSetEnv, setDeclaredEnv, CBody.bind, CBody.resolve])
    (by simp [stagedSetEnv, CBody.bind, CBody.resolve])
    (by simp [stagedSetEnv, setDeclaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve])
    (by simp [stagedSetEnv, setDeclaredEnv, guardEnv, parameters, CBody.bind, CBody.resolve])
    (by simp [stagedSetEnv, setDeclaredEnv, guardEnv, parameters, CBody.bind])
    (by simp [stagedSetEnv, setDeclaredEnv, guardEnv, parameters, CBody.bind]) readable writable separate

private theorem set_behaviors_wrap (shape : Tensor.Shape) (program : CCalls.Events.Program E) (heap : Heap)
    (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (member : String)
    (rshape : Tensor.Shape) (values : Values rshape)
    (nref : n.toNat = 1) (matched : m.toNat = rshape.volume) (bounded : rshape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (readable : Reads heap buffer values)
    (writable : Writable heap (p.member member) rshape.volume)
    (separate : ∀ a < rshape.volume, ∀ b < rshape.volume, (p.member member).index a ≠ buffer.index b)
    (nav : ∀ types0, Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (setDispatch shape :: countReject :: setLoopSuffix)
        (setDeclaredEnv (guardEnv p refs buffer n m)) (setDeclaredTypes types0) heap) "fmi3Status" .done)
      (.body (.running (setArm member rshape.volume ++ (countReject :: setLoopSuffix))
        (setDeclaredEnv (guardEnv p refs buffer n m)) (setDeclaredTypes types0) heap) "fmi3Status" .done))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap (p.member member) values rshape.volume⟩ :=
  (CCalls.Events.internal_prefix program (set_reaches_of shape program heap p refs buffer n m kind mode member
    rshape values .done nref matched bounded defined hk hm allowed readable writable separate nav)
    (CCalls.Events.return_forced program _ _)).behaviors behavior

/-- The tensor setter writing the input `u`. -/
theorem set_behaviors_input (shape : Tensor.Shape) (program : CCalls.Events.Program E) (heap : Heap)
    (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (values : Values shape)
    (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (refRead : load heap (refs.index 0) = some (.integer 1))
    (readable : Reads heap buffer values)
    (writable : Writable heap (p.member inputName) shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume, (p.member inputName).index a ≠ buffer.index b)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap (p.member inputName) values shape.volume⟩ :=
  set_behaviors_wrap shape program heap p refs buffer n m kind mode inputName shape values nref nval
    (nval ▸ m.toNat_lt_size) defined hk hm allowed readable writable separate
    (fun types0 => set_nav_input program shape p refs buffer n m types0 heap .done refRead) behavior

/-- The tensor setter writing the state `x`. -/
theorem set_behaviors_state (shape : Tensor.Shape) (program : CCalls.Events.Program E) (heap : Heap)
    (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (values : Values shape)
    (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (refRead : load heap (refs.index 0) = some (.integer 2))
    (readable : Reads heap buffer values)
    (writable : Writable heap (p.member stateName) shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume, (p.member stateName).index a ≠ buffer.index b)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap (p.member stateName) values shape.volume⟩ :=
  set_behaviors_wrap shape program heap p refs buffer n m kind mode stateName shape values nref nval
    (nval ▸ m.toNat_lt_size) defined hk hm allowed readable writable separate
    (fun types0 => set_nav_state program shape p refs buffer n m types0 heap .done refRead) behavior

end

/-! ### Printed-text denotation -/

section
open CTree.Printer CTree.Syntax

set_option maxHeartbeats 4000000 in
/-- Every statement of the getter body prints its intended C token grammar. -/
theorem getBody_printable (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) :
    ∀ stmt ∈ (getFunction shape outputShape).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  cases outputShape <;>
    (simp only [getFunction, getBody, getRest, getDispatch, getDispatch1, getDispatch2, getDispatch3,
        getDispatch4, getArm, getOutputArm, getLoopSuffix, basicReject, countReject, vr0,
        Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression,
        permittedModes, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok,
        Runtime.field, Runtime.v, Runtime.n, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.either,
        Runtime.negate, Runtime.any, Runtime.mode, Runtime.lt, Runtime.call, getCopyBody, srcCell, output,
        CLoops.loop, CLoops.counterStep,
        List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
        List.not_mem_nil, List.forall_mem_nil, or_false, or_imp, forall_and, List.cons_append,
        List.nil_append, forall_eq] <;>
      repeat first
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
            Postfix, FieldBase])

set_option maxHeartbeats 4000000 in
/-- Every statement of the setter body prints its intended C token grammar. -/
theorem setBody_printable (shape : Tensor.Shape) :
    ∀ stmt ∈ (setFunction shape).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  simp only [setFunction, setBody, setRest, setDispatch, setDispatch2, setArm, setLoopSuffix, validateBody,
      basicReject, countReject, vr0, Runtime.require, Runtime.instancePrefix, Runtime.modeGuard,
      Runtime.allowedExpression, permittedModes, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret,
      Runtime.ok, Runtime.field, Runtime.v, Runtime.n, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.either,
      Runtime.negate, Runtime.any, Runtime.mode, Runtime.lt, Runtime.call, Runtime.finite, setCopyBody,
      dstCell, output, CLoops.loop, CLoops.counterStep, List.foldr_cons, List.foldr_nil, List.map_cons,
      List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, List.forall_mem_nil, or_false, or_imp,
      forall_and, List.cons_append, List.nil_append, forall_eq] <;>
    repeat first
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
theorem getFunction_denotes (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) :
    FunctionDenotes RuntimePrinter.typedefs (getFunction shape outputShape).render
      (getFunction shape outputShape) :=
  CTree.Printer.function_denotes ⟨signature_printable false, getBody_printable shape outputShape⟩

/-- The rendered setter denotes its function under the shared C printer. -/
theorem setFunction_denotes (shape : Tensor.Shape) :
    FunctionDenotes RuntimePrinter.typedefs (setFunction shape).render (setFunction shape) :=
  CTree.Printer.function_denotes ⟨signature_printable true, setBody_printable shape⟩

end

/-! ### Null-handle rejections -/

section
variable [static : StaticLiterals]
private local instance rejectInterface : CInterface := cInterface static.addresses

/-- A null instance handle is rejected with `fmi3Error`, changing nothing. -/
theorem null_get_behaviors (shape : Tensor.Shape) (outputShape : Option Tensor.Shape)
    (program : CCalls.Events.Program E) (heap : Heap) (refs buffer : Option Address) (n m : UInt64)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape outputShape)))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (getFunction shape outputShape)
    (Runtime.modeGuard .get :: basicReject :: getRest shape outputShape)
    (arguments none refs buffer n m) (parameters none refs buffer n m) heap defined
    (parameters_bound false _ _ _ _ _) (by simp [getFunction, getBody, Runtime.require, List.append_assoc])
    rfl (getBody_closed shape outputShape)
  all_goals simp [parameters, CBody.bind]

/-- A null instance handle is rejected with `fmi3Error`, changing nothing. -/
theorem null_set_behaviors (shape : Tensor.Shape) (program : CCalls.Events.Program E) (heap : Heap)
    (refs buffer : Option Address) (n m : UInt64)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction shape))) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (setFunction shape)
    (Runtime.modeGuard .setStart :: basicReject :: setRest shape)
    (arguments none refs buffer n m) (parameters none refs buffer n m) heap defined
    (parameters_bound true _ _ _ _ _) (by simp [setFunction, setBody, Runtime.require, List.append_assoc])
    rfl (setBody_closed shape)
  all_goals simp [parameters, CBody.bind]

end

/-! ### Unknown or unsupported value-reference failure paths

The tensor Float64 dispatch reaches the scalar `fail` statement before the copy
loop for a value reference that names no supported region: an unknown getter
reference (`r ∉ {0,1,2,3,4}`), the output reference `4` on a record with no dense
output (`outputShape = none`), and any non-writable setter reference. The
memory-machine execution witness leaves the heap unchanged up to that statement;
`GuardedCalls.FailurePrefix.silent_behaviors` then returns `fmi3Error`. -/

section
variable [static : StaticLiterals]
private local instance failPathInterface : CInterface := cInterface static.addresses

/-- The basic request check passes for a non-null single-reference request. -/
private theorem basic_pass (heap : Heap) (p refs buffer : Address) (n m : UInt64) (nref : n.toNat = 1) :
    CBody.eval (guardEnv p refs buffer n m) heap
      (Runtime.any [Runtime.nev (Runtime.v "nValueReferences") (Runtime.n 1),
        Runtime.negate (Runtime.v "valueReferences"), Runtime.negate (Runtime.v "values")]) =
      some (boolean false) := by
  simp [Runtime.any, Runtime.either, Runtime.negate, Runtime.nev, Runtime.v, Runtime.n, CBody.eval,
    guardEnv, parameters, CBody.bind, CBody.resolve, CBody.comparison, boolean, Value.truth, nref]

/-- The getter's memory-machine execution reaches its `fail` statement before the
copy loop, leaving the heap unchanged, for an unknown reference or the output
reference on a record without a dense output. -/
theorem get_fail_prefix (shape : Tensor.Shape) (outputShape : Option Tensor.Shape)
    (heap : Heap) (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (r : Nat)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .get kind mode) (nref : n.toNat = 1)
    (refRead : load heap (refs.index 0) = some (.integer r))
    (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r = 4 → outputShape = none) :
    GuardedCalls.FailurePrefix (getFunction shape outputShape)
      (arguments (some p) (some refs) (some buffer) n m) heap p "Unknown value reference" heap := by
  set env0 := parameters (some p) (some refs) (some buffer) n m with henv0
  set g := guardEnv p refs buffer n m with hg
  set d := declaredEnv g with hd
  have rv : resolve d "valueReferences" = some (.pointer (some refs)) := by
    simp [hd, declaredEnv, hg, guardEnv, parameters, CBody.bind, CBody.resolve]
  -- guard, then the basic request check passes
  have s_accept : CBody.run 3 (.running (getBody shape outputShape) env0 heap) =
      some (.running (basicReject :: getRest shape outputShape) g heap) :=
    LifecycleGuard.accept env0 heap p .get kind mode (basicReject :: getRest shape outputShape)
      (by simp [henv0, parameters, CBody.bind]) (by simp [henv0, parameters, CBody.bind]) hk hm allowed
  have s_reject : CBody.run 1 (.running (basicReject :: getRest shape outputShape) g heap) =
      some (.running (getRest shape outputShape) g heap) :=
    run_one (reject_false g heap _ "Invalid Float64 array lengths or pointers" (getRest shape outputShape)
      (basic_pass heap p refs buffer n m nref))
  -- stage the two declarations
  have s_src : CBody.run 1 (.running (getRest shape outputShape) g heap) =
      some (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (CBody.bind g "src" (.pointer none)) heap) :=
    run_one (declare_next g heap "fmi3Float64 *" "src" Expr.nullPointer (.pointer none) (.pointer none) _
      (by simp [hg, guardEnv, parameters, CBody.bind])
      (by simp [Expr.nullPointer, CBody.eval, CBody.expressionCast, CBody.zeroLiteral])
      (by simp [CBody.cast, convert]))
  have s_exp : CBody.run 1 (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        getDispatch shape outputShape :: countReject :: getLoopSuffix)
        (CBody.bind g "src" (.pointer none)) heap) =
      some (.running (getDispatch shape outputShape :: countReject :: getLoopSuffix) d heap) :=
    run_one (declare_next (CBody.bind g "src" (.pointer none)) heap "size_t" "expected" (Runtime.n 0)
      (.integer 0) (.integer 0) _ (by simp [hg, guardEnv, parameters, CBody.bind])
      (by simp [Runtime.n, CBody.eval]) (by simp [CBody.cast, convert]))
  -- dispatch: branch 0..3 fall through
  have b0 : CBody.run 1 (.running (getDispatch shape outputShape :: countReject :: getLoopSuffix) d heap) =
      some (.running (getDispatch1 shape outputShape ++ (countReject :: getLoopSuffix)) d heap) :=
    run_one (branch_false d heap _ (getArm timeName 1) (getDispatch1 shape outputShape) _
      (vr0_bne d heap refs r 0 rv refRead h0))
  have b1 : CBody.run 1 (.running (getDispatch1 shape outputShape ++ (countReject :: getLoopSuffix)) d heap) =
      some (.running (getDispatch2 shape outputShape ++ (countReject :: getLoopSuffix)) d heap) :=
    run_one (branch_false d heap _ (getArm inputName shape.volume) (getDispatch2 shape outputShape) _
      (vr0_bne d heap refs r 1 rv refRead h1))
  have b2 : CBody.run 1 (.running (getDispatch2 shape outputShape ++ (countReject :: getLoopSuffix)) d heap) =
      some (.running (getDispatch3 shape outputShape ++ (countReject :: getLoopSuffix)) d heap) :=
    run_one (branch_false d heap _ (getArm stateName shape.volume) (getDispatch3 shape outputShape) _
      (vr0_bne d heap refs r 2 rv refRead h2))
  have b3 : CBody.run 1 (.running (getDispatch3 shape outputShape ++ (countReject :: getLoopSuffix)) d heap) =
      some (.running (getDispatch4 outputShape ++ (countReject :: getLoopSuffix)) d heap) :=
    run_one (branch_false d heap _ (getArm derivativeName shape.volume) (getDispatch4 outputShape) _
      (vr0_bne d heap refs r 3 rv refRead h3))
  -- branch 4: either falls through (r ≠ 4) or takes the empty output arm (no output)
  have b4 : CBody.run 1 (.running (getDispatch4 outputShape ++ (countReject :: getLoopSuffix)) d heap) =
      some (.running (Runtime.fail "Unknown value reference" :: countReject :: getLoopSuffix) d heap) := by
    by_cases hr4 : r = 4
    · have hnone : outputShape = none := h4 hr4
      subst hnone
      refine run_one (branch_true d heap _ (getOutputArm none) [Runtime.fail "Unknown value reference"] _ ?_)
      have := vr0_cmp d heap refs r 4 rv refRead
      simpa [hr4, getOutputArm] using this
    · exact run_one (branch_false d heap _ (getOutputArm outputShape)
        [Runtime.fail "Unknown value reference"] _ (vr0_bne d heap refs r 4 rv refRead hr4))
  have chain : CBody.run 11 (.running (getBody shape outputShape) env0 heap) =
      some (.running (Runtime.fail "Unknown value reference" :: countReject :: getLoopSuffix) d heap) :=
    run_append s_accept (run_append s_reject (run_append s_src (run_append s_exp
      (run_append b0 (run_append b1 (run_append b2 (run_append b3 b4)))))))
  refine ⟨rfl, getBody_closed shape outputShape, env0, d, countReject :: getLoopSuffix, 11,
    parameters_bound false _ _ _ _ _, chain, ?_, ?_⟩
  · simp [hd, declaredEnv, hg, guardEnv, parameters, CBody.bind]
  · simp [hd, declaredEnv, hg, guardEnv, parameters, CBody.bind, CBody.resolve]

/-- The setter's memory-machine execution reaches its `fail` statement before the
copy loop for a reference that names no writable region (`r ∉ {1,2}`). -/
theorem set_fail_prefix (shape : Tensor.Shape)
    (heap : Heap) (p refs buffer : Address) (n m : UInt64) (kind : Kind) (mode : Mode) (r : Nat)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode) (nref : n.toNat = 1)
    (refRead : load heap (refs.index 0) = some (.integer r))
    (h1 : r ≠ 1) (h2 : r ≠ 2) :
    GuardedCalls.FailurePrefix (setFunction shape)
      (arguments (some p) (some refs) (some buffer) n m) heap p "Unknown or read-only value reference" heap := by
  set env0 := parameters (some p) (some refs) (some buffer) n m with henv0
  set g := guardEnv p refs buffer n m with hg
  set d := setDeclaredEnv g with hd
  have rv : resolve d "valueReferences" = some (.pointer (some refs)) := by
    simp [hd, setDeclaredEnv, hg, guardEnv, parameters, CBody.bind, CBody.resolve]
  have s_accept : CBody.run 3 (.running (setBody shape) env0 heap) =
      some (.running (basicReject :: setRest shape) g heap) :=
    LifecycleGuard.accept env0 heap p .setStart kind mode (basicReject :: setRest shape)
      (by simp [henv0, parameters, CBody.bind]) (by simp [henv0, parameters, CBody.bind]) hk hm allowed
  have s_reject : CBody.run 1 (.running (basicReject :: setRest shape) g heap) =
      some (.running (setRest shape) g heap) :=
    run_one (reject_false g heap _ "Invalid Float64 array lengths or pointers" (setRest shape)
      (basic_pass heap p refs buffer n m nref))
  have s_dst : CBody.run 1 (.running (setRest shape) g heap) =
      some (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        setDispatch shape :: countReject :: setLoopSuffix)
        (CBody.bind g "dst" (.pointer none)) heap) :=
    run_one (declare_next g heap "fmi3Float64 *" "dst" Expr.nullPointer (.pointer none) (.pointer none) _
      (by simp [hg, guardEnv, parameters, CBody.bind])
      (by simp [Expr.nullPointer, CBody.eval, CBody.expressionCast, CBody.zeroLiteral])
      (by simp [CBody.cast, convert]))
  have s_exp : CBody.run 1 (.running (.declare "size_t" "expected" (Runtime.n 0) ::
        setDispatch shape :: countReject :: setLoopSuffix)
        (CBody.bind g "dst" (.pointer none)) heap) =
      some (.running (setDispatch shape :: countReject :: setLoopSuffix) d heap) :=
    run_one (declare_next (CBody.bind g "dst" (.pointer none)) heap "size_t" "expected" (Runtime.n 0)
      (.integer 0) (.integer 0) _ (by simp [hg, guardEnv, parameters, CBody.bind])
      (by simp [Runtime.n, CBody.eval]) (by simp [CBody.cast, convert]))
  have b1 : CBody.run 1 (.running (setDispatch shape :: countReject :: setLoopSuffix) d heap) =
      some (.running (setDispatch2 shape ++ (countReject :: setLoopSuffix)) d heap) :=
    run_one (branch_false d heap _ (setArm inputName shape.volume) (setDispatch2 shape) _
      (vr0_bne d heap refs r 1 rv refRead h1))
  have b2 : CBody.run 1 (.running (setDispatch2 shape ++ (countReject :: setLoopSuffix)) d heap) =
      some (.running (Runtime.fail "Unknown or read-only value reference" :: countReject :: setLoopSuffix) d heap) :=
    run_one (branch_false d heap _ (setArm stateName shape.volume)
      [Runtime.fail "Unknown or read-only value reference"] _ (vr0_bne d heap refs r 2 rv refRead h2))
  have chain : CBody.run 8 (.running (setBody shape) env0 heap) =
      some (.running (Runtime.fail "Unknown or read-only value reference" :: countReject :: setLoopSuffix) d heap) :=
    run_append s_accept (run_append s_reject (run_append s_dst (run_append s_exp
      (run_append b1 b2))))
  refine ⟨rfl, setBody_closed shape, env0, d, countReject :: setLoopSuffix, 8,
    parameters_bound true _ _ _ _ _, chain, ?_, ?_⟩
  · simp [hd, setDeclaredEnv, hg, guardEnv, parameters, CBody.bind]
  · simp [hd, setDeclaredEnv, hg, guardEnv, parameters, CBody.bind, CBody.resolve]

/-- The getter's whole behavior on an unknown or unsupported reference with
logging disabled: it reaches `fail` before the copy loop and returns `fmi3Error`,
its only heap change the terminated lifecycle mode. -/
theorem get_fail_behaviors (shape : Tensor.Shape) (outputShape : Option Tensor.Shape)
    (program : CCalls.Events.Program E) (heap : Heap) (p refs buffer message : Address)
    (n m : UInt64) (kind : Kind) (mode : Mode) (r : Nat) (logger : Option Address)
    (defined : program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape outputShape)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses "Unknown value reference" = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hmode : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (allowed : Reference.Allowed .get kind mode) (nref : n.toNat = 1)
    (refRead : load heap (refs.index 0) = some (.integer r))
    (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r = 4 → outputShape = none)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  have hmodeLoad : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hmode, convert, Mode.code]
  exact GuardedCalls.FailurePrefix.silent_behaviors program (getFunction shape outputShape)
    (arguments (some p) (some refs) (some buffer) n m) heap heap p message "Unknown value reference"
    (some (.integer mode.code)) logger
    (get_fail_prefix shape outputShape heap p refs buffer n m kind mode r hk hmodeLoad allowed nref refRead
      h0 h1 h2 h3 h4) defined helper messageBound hmode hl hg behavior

/-- The setter's whole behavior on a reference that names no writable region
with logging disabled: it reaches `fail` before the copy loop and returns
`fmi3Error`, its only heap change the terminated lifecycle mode. -/
theorem set_fail_behaviors (shape : Tensor.Shape)
    (program : CCalls.Events.Program E) (heap : Heap) (p refs buffer message : Address)
    (n m : UInt64) (kind : Kind) (mode : Mode) (r : Nat) (logger : Option Address)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction shape)))
    (helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]))
    (messageBound : static.addresses "Unknown or read-only value reference" = some message)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hmode : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (allowed : Reference.Allowed .setStart kind mode) (nref : n.toNat = 1)
    (refRead : load heap (refs.index 0) = some (.integer r)) (h1 : r ≠ 1) (h2 : r ≠ 2)
    (hl : load heap (p.member "logger") = some (.pointer logger))
    (hg : load heap (p.member "logging") = some (.integer 0)) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments (some p) (some refs) (some buffer) n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode heap p .terminated⟩ := by
  have hmodeLoad : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, hmode, convert, Mode.code]
  exact GuardedCalls.FailurePrefix.silent_behaviors program (setFunction shape)
    (arguments (some p) (some refs) (some buffer) n m) heap heap p message "Unknown or read-only value reference"
    (some (.integer mode.code)) logger
    (set_fail_prefix shape heap p refs buffer n m kind mode r hk hmodeLoad allowed nref refRead h1 h2)
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

/-- The tensor setter writing the state region of instance `i` replaces exactly
that region with the caller's finite values. -/
theorem set_instance_behaviors_state (newValues : Values shape) (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction shape)))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (refRead : load (TensorInstance.store backing pool i shape oshape time state input output)
      (refs.index 0) = some (.integer 2))
    (readable : Reads (TensorInstance.store backing pool i shape oshape time state input output) buffer newValues)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i stateName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
        (TensorInstance.store backing pool i shape oshape time state input output) .done) behavior ↔
      behavior = .terminates []
        ⟨.integer 0, written (TensorInstance.store backing pool i shape oshape time state input output)
          (TensorInstance.field pool i stateName) newValues shape.volume⟩ :=
  set_behaviors_state shape program _ (TensorInstance.record pool i) refs buffer n m kind mode newValues
    nref nval defined hk hm allowed refRead readable
    (writable_state backing pool i shape oshape time state input output) separate behavior

/-- The tensor setter writing the input region of instance `i` (writable input). -/
theorem set_instance_behaviors_input (newValues : Values shape) (nref : n.toNat = 1) (nval : m.toNat = shape.volume)
    (defined : program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction shape)))
    (hk : load (inputWritableStore backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (inputWritableStore backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStart kind mode)
    (refRead : load (inputWritableStore backing pool i shape oshape time state input output)
      (refs.index 0) = some (.integer 1))
    (readable : Reads (inputWritableStore backing pool i shape oshape time state input output) buffer newValues)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i inputName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments (some (TensorInstance.record pool i)) (some refs) (some buffer) n m)
        (inputWritableStore backing pool i shape oshape time state input output) .done) behavior ↔
      behavior = .terminates []
        ⟨.integer 0, written (inputWritableStore backing pool i shape oshape time state input output)
          (TensorInstance.field pool i inputName) newValues shape.volume⟩ :=
  set_behaviors_input shape program _ (TensorInstance.record pool i) refs buffer n m kind mode newValues
    nref nval defined hk hm allowed refRead readable
    (inputWritableStore_writable backing pool i shape oshape time state input output) separate behavior

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
printer, and a rejection guarantee for a null handle. -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The tensor `fmi3GetFloat64` function contract. -/
structure GetContract (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) (text : String) : Prop where
  printed : text = (getFunction shape outputShape).render
  closed : (getFunction shape outputShape).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (getFunction shape outputShape)
  rejected : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (refs buffer : Option Address)
    (n m : UInt64),
    program.internal.definitions "fmi3GetFloat64" = some (.tree (getFunction shape outputShape)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

/-- The tensor `fmi3SetFloat64` function contract. -/
structure SetContract (shape : Tensor.Shape) (text : String) : Prop where
  printed : text = (setFunction shape).render
  closed : (setFunction shape).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (setFunction shape)
  rejected : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (refs buffer : Option Address)
    (n m : UInt64),
    program.internal.definitions "fmi3SetFloat64" = some (.tree (setFunction shape)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetFloat64" (arguments none refs buffer n m) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem get_contract (shape : Tensor.Shape) (outputShape : Option Tensor.Shape) :
    GetContract shape outputShape (getFunction shape outputShape).render where
  printed := rfl
  closed := getBody_closed shape outputShape
  denotes := getFunction_denotes shape outputShape
  rejected program heap refs buffer n m defined :=
    null_get_behaviors shape outputShape program heap refs buffer n m defined

theorem set_contract (shape : Tensor.Shape) : SetContract shape (setFunction shape).render where
  printed := rfl
  closed := setBody_closed shape
  denotes := setFunction_denotes shape
  rejected program heap refs buffer n m defined :=
    null_set_behaviors shape program heap refs buffer n m defined

end
end Rumoca.FMI3.TensorFloat64
