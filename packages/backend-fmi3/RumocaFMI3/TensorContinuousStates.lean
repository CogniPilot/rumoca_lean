import RumocaFMI3.TensorFloat64Access
import RumocaFMI3.TensorInstanceRhs
import RumocaFMI3.TensorInstanceJacobian

/-! Tensor continuous-state interface bodies over the static tensor instance
record, as package-checked products.

The Model Exchange continuous-state functions `fmi3GetContinuousStates`,
`fmi3SetContinuousStates` and `fmi3GetContinuousStateDerivatives` move a whole
tensor region between the caller's `fmi3Float64` buffer and one instance record
of the static pool, in the same authored C subset the scalar runtime uses. Each
body validates the instance handle and lifecycle guard exactly as the scalar
bodies do (`Runtime.require`), then checks that `nContinuousStates` equals the
symbolic state volume and that the buffer is non-null. The getter copies the
state tensor `x` into the caller's buffer; the setter validates finiteness of
every caller value and then copies them into `x`; the derivative getter runs the
prepared derivative entry on the instance (through the machinery of
`TensorInstanceRhs`), writing the finite tensor derivative into the instance's
`der(x)` region, and then copies that region into the caller's buffer. The copy
uses one counted `size_t` loop whose bound is the symbolic state volume, so no
tensor coordinate is enumerated.

This is a package-checked product only: no production artifact is emitted, no
CLI or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. Every theorem is universal in the tensor shape,
the instance index of the static pool, the request length and the heap. -/
noncomputable section
namespace Rumoca.FMI3.TensorContinuousStates
open CTree CMemory CBody CLoops
open Rumoca.CMemory.TensorView Rumoca.CMemory.TensorRegion Rumoca.FMI3.TensorInstance
open Rumoca.FMI3.TensorFloat64 (getCopyBody setCopyBody getLoopSuffix setLoopSuffix validateBody
  getCopy_reaches setCopy_reaches validate_reaches)

/-- The continuous-state ABI: `(instance, continuousStates[], nContinuousStates)`.
The setter keeps the pointee's const qualifier. -/
def signature (write : Bool) : Signature :=
  ⟨"fmi3Status", if write then "fmi3SetContinuousStates" else "fmi3GetContinuousStates",
    [⟨"fmi3Instance", "instance", false⟩,
     ⟨if write then "const fmi3Float64" else "fmi3Float64", "continuousStates", true⟩,
     ⟨"size_t", "nContinuousStates", false⟩]⟩

def arguments (handle buffer : Option Address) (count : UInt64) : List Value :=
  [.pointer handle, .pointer buffer, .integer count.toNat]

def parameters (handle buffer : Option Address) (count : UInt64) : Locals :=
  bind (bind (bind (fun _ => none) "nContinuousStates" (.integer count.toNat))
    "continuousStates" (.pointer buffer)) "instance" (.pointer handle)

/-- Local bindings after the handle/lifecycle guard: the instance pointer. -/
def guardEnv (p buffer : Address) (count : UInt64) : Locals :=
  bind (parameters (some p) (some buffer) count) "m" (.pointer (some p))

/-- The request check: `nContinuousStates` must equal the state volume and the
buffer must be non-null. -/
def countReject (volume : Nat) : Stmt :=
  Runtime.reject (Runtime.any [Runtime.nev (Runtime.v "nContinuousStates") (Runtime.n volume),
    Runtime.negate (Runtime.v "continuousStates")]) "Invalid continuous state count or pointer"

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem parameters_bound (write : Bool) (handle buffer : Option Address) (count : UInt64) :
    CCalls.parameters (signature write).parameters (arguments handle buffer count) =
      some (parameters handle buffer count) := by
  have cc : CBody.cast "size_t" (.integer count.toNat) = some (.integer count.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ rfl (CLoops.convert_size_nat _ count.toNat_lt_size)
  cases write <;>
    simp only [signature, arguments, CCalls.parameters, CCalls.parameterType, Bool.false_eq_true,
      ↓reduceIte, cc]
  all_goals rfl

/-- The request check passes for a matched non-null request. -/
theorem count_pass (heap : Heap) (p buffer : Address) (count : UInt64) (volume : Nat)
    (matched : count.toNat = volume) :
    CBody.eval (guardEnv p buffer count) heap
      (Runtime.any [Runtime.nev (Runtime.v "nContinuousStates") (Runtime.n volume),
        Runtime.negate (Runtime.v "continuousStates")]) = some (boolean false) := by
  simp [Runtime.any, Runtime.either, Runtime.negate, Runtime.nev, Runtime.v, Runtime.n, CBody.eval,
    guardEnv, parameters, CBody.bind, CBody.resolve, CBody.comparison, boolean, Value.truth, matched]

/-! ### The getter -/

def getTail (shape : Tensor.Shape) : List Stmt :=
  .declare "fmi3Float64 *" "src" ((Runtime.region stateName)) ::
  .declare "fmi3Float64 *" "values" (Runtime.v "continuousStates") ::
  .declare "size_t" "expected" (Runtime.n shape.volume) :: getLoopSuffix

def getBody (shape : Tensor.Shape) : List Stmt :=
  Runtime.require .getStates ++ (countReject shape.volume :: getTail shape)

def getFunction (shape : Tensor.Shape) : CTree.Function :=
  ⟨signature false, getBody shape, false⟩

theorem getBody_closed (shape : Tensor.Shape) :
    (getFunction shape).body.all CBodyEmbedding.closedBlocks = true := by
  simp [getFunction, getBody, getTail, countReject, getLoopSuffix, getCopyBody, Runtime.require,
    Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret,
    Runtime.ok, Runtime.field, Runtime.v, CBodyEmbedding.closedBlocks, CLoops.noDeclarations, CLoops.loop,
    CLoops.counterStep]

/-- The staged environment at the copy loop: instance guard plus `src` (the
state region base), `values` (the caller buffer) and `expected` (the volume). -/
def stagedGetEnv (p buffer : Address) (count : UInt64) (shape : Tensor.Shape) : Locals :=
  bind (bind (bind (guardEnv p buffer count) "src" (.pointer (some (p.member stateName))))
    "values" (.pointer (some buffer))) "expected" (.integer shape.volume)

def stagedGetTypes (types0 : Types) : Types :=
  bindType (bindType (bindType types0 "src" .pointer) "values" .pointer) "expected" .size

section
variable (program : CCalls.Events.Program E)

/-- The complete getter: it copies the state region of the instance record at `p`
into the caller buffer and changes no other cell. -/
theorem get_reaches (shape : Tensor.Shape) (heap : Heap) (p buffer : Address) (count : UInt64)
    (kind : Kind) (mode : Mode) (state : Values shape) (stack : CCalls.Typed.Continuation)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetContinuousStates" = some (.tree (getFunction shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getStates kind mode)
    (readable : Reads heap (p.member stateName) state)
    (writable : Writable heap buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume, (p.member stateName).index a ≠ buffer.index b) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3GetContinuousStates" (arguments (some p) (some buffer) count) heap stack)
      (.returning (.integer 0) (written heap buffer state shape.volume) stack) := by
  -- guard, memory machine, then enter the typed body at `getTail`
  have accepted := LifecycleGuard.accept (parameters (some p) (some buffer) count) heap p
    .getStates kind mode (countReject shape.volume :: getTail shape)
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  have prefix_run : CBody.run 4 (.running (getBody shape) (parameters (some p) (some buffer) count) heap) =
      some (.running (getTail shape) (guardEnv p buffer count) heap) := by
    rw [getBody, show (4 : Nat) = 3 + 1 from rfl, CBody.run_add, accepted, Option.bind_some]
    exact TensorFloat64.run_one (TensorFloat64.reject_false (guardEnv p buffer count) heap _
      "Invalid continuous state count or pointer" (getTail shape) (count_pass heap p buffer count _ matched))
  obtain ⟨types0, entered⟩ := CCalls.Events.body_prefix_reaches program (getFunction shape)
    (arguments (some p) (some buffer) count) (parameters (some p) (some buffer) count)
    (guardEnv p buffer count) heap heap (getTail shape) stack 4 defined (parameters_bound false _ _ _)
    (getBody_closed shape) prefix_run
  refine entered.trans ?_
  -- stage `src`, `values`, `expected`
  have mBound : guardEnv p buffer count "m" = some (.pointer (some p)) := by
    simp [guardEnv, CBody.bind]
  have s_src : CLoops.next (.running (getTail shape) (guardEnv p buffer count) types0 heap) =
      some (.running (.declare "fmi3Float64 *" "values" (Runtime.v "continuousStates") ::
        .declare "size_t" "expected" (Runtime.n shape.volume) :: getLoopSuffix)
        (bind (guardEnv p buffer count) "src" (.pointer (some (p.member stateName))))
        (bindType types0 "src" .pointer) heap) :=
    TensorFloat64.declare_step_e (guardEnv p buffer count) types0 heap "fmi3Float64 *" "src"
      ((Runtime.region stateName)) .pointer (.pointer (some (p.member stateName)))
      (.pointer (some (p.member stateName))) _ (by simp [guardEnv, parameters, CBody.bind]) rfl
      (by apply CBodyEmbedding.eval_refines
          simp [Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.lvalue, guardEnv, parameters, CBody.bind,
            CBody.resolve, mBound, Value.address]) rfl
  have s_values : CLoops.next (.running (.declare "fmi3Float64 *" "values" (Runtime.v "continuousStates") ::
        .declare "size_t" "expected" (Runtime.n shape.volume) :: getLoopSuffix)
        (bind (guardEnv p buffer count) "src" (.pointer (some (p.member stateName))))
        (bindType types0 "src" .pointer) heap) =
      some (.running (.declare "size_t" "expected" (Runtime.n shape.volume) :: getLoopSuffix)
        (bind (bind (guardEnv p buffer count) "src" (.pointer (some (p.member stateName))))
          "values" (.pointer (some buffer))) (bindType (bindType types0 "src" .pointer) "values" .pointer) heap) :=
    TensorFloat64.declare_step_e _ _ heap "fmi3Float64 *" "values" (Runtime.v "continuousStates") .pointer
      (.pointer (some buffer)) (.pointer (some buffer)) _ (by simp [guardEnv, parameters, CBody.bind]) rfl
      (by simp [Runtime.v, CLoops.eval, CBody.eval, guardEnv, parameters, CBody.bind, CBody.resolve]) rfl
  have s_exp : CLoops.next (.running (.declare "size_t" "expected" (Runtime.n shape.volume) :: getLoopSuffix)
        (bind (bind (guardEnv p buffer count) "src" (.pointer (some (p.member stateName))))
          "values" (.pointer (some buffer))) (bindType (bindType types0 "src" .pointer) "values" .pointer) heap) =
      some (.running getLoopSuffix (stagedGetEnv p buffer count shape) (stagedGetTypes types0) heap) :=
    TensorFloat64.declare_step_e _ _ heap "size_t" "expected" (Runtime.n shape.volume) .size
      (.integer shape.volume) (.integer shape.volume) _ (by simp [guardEnv, parameters, CBody.bind])
      rfl (by simp [Runtime.n, CLoops.eval, CBody.eval]) (CLoops.convert_size_nat _ bounded)
  refine .next (CCalls.Events.body_step program s_src "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s_values "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s_exp "fmi3Status" stack) ?_))
  -- the counted copy loop, then return ok
  set env := stagedGetEnv p buffer count shape with henv
  have fresh_k : env "k" = none := by simp [henv, stagedGetEnv, guardEnv, parameters, CBody.bind]
  have expBound : resolve env "expected" = some (.integer shape.volume) := by
    simp [henv, stagedGetEnv, CBody.bind, CBody.resolve]
  have srcBound : resolve env "src" = some (.pointer (some (p.member stateName))) := by
    simp [henv, stagedGetEnv, guardEnv, parameters, CBody.bind, CBody.resolve]
  have valuesBound : resolve env "values" = some (.pointer (some buffer)) := by
    simp [henv, stagedGetEnv, CBody.bind, CBody.resolve]
  have fmiok : env "fmi3OK" = none := by simp [henv, stagedGetEnv, guardEnv, parameters, CBody.bind]
  refine .next (CCalls.Events.body_step program
    (CLoops.counter_initialize env (stagedGetTypes types0) heap "k"
      (CLoops.loop "k" (Runtime.v "expected") getCopyBody :: [Runtime.ok]) fresh_k rfl) _ stack) ?_
  refine (getCopy_reaches program env (CLoops.bindType (stagedGetTypes types0) "k" .size) heap
    (p.member stateName) buffer state [Runtime.ok] _ stack bounded (by simp [CLoops.bindType]) expBound
    srcBound valuesBound readable writable separate).trans ?_
  exact DerivativeCalls.finish program _ (counterEnv env "k" shape.volume)
    (CLoops.bindType (stagedGetTypes types0) "k" .size) stack (by simp [counterEnv, CBody.bind, fmiok])

theorem get_behaviors (shape : Tensor.Shape) (heap : Heap) (p buffer : Address) (count : UInt64)
    (kind : Kind) (mode : Mode) (state : Values shape)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetContinuousStates" = some (.tree (getFunction shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getStates kind mode)
    (readable : Reads heap (p.member stateName) state)
    (writable : Writable heap buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume, (p.member stateName).index a ≠ buffer.index b)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetContinuousStates" (arguments (some p) (some buffer) count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap buffer state shape.volume⟩ :=
  (CCalls.Events.internal_prefix program (get_reaches program shape heap p buffer count kind mode state
    .done matched bounded defined hk hm allowed readable writable separate)
    (CCalls.Events.return_forced program _ _)).behaviors behavior

end
/-! ### The setter -/

def setTail (shape : Tensor.Shape) : List Stmt :=
  .declare "fmi3Float64 *" "dst" ((Runtime.region stateName)) ::
  .declare "const fmi3Float64 *" "values" (Runtime.v "continuousStates") ::
  .declare "size_t" "expected" (Runtime.n shape.volume) :: setLoopSuffix

def setBody (shape : Tensor.Shape) : List Stmt :=
  Runtime.require .setStates ++ (countReject shape.volume :: setTail shape)

def setFunction (shape : Tensor.Shape) : CTree.Function :=
  ⟨signature true, setBody shape, false⟩

theorem setBody_closed (shape : Tensor.Shape) :
    (setFunction shape).body.all CBodyEmbedding.closedBlocks = true := by
  simp [setFunction, setBody, setTail, countReject, setLoopSuffix, setCopyBody, validateBody,
    Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject, Runtime.branch,
    Runtime.fail, Runtime.ret, Runtime.ok, Runtime.field, Runtime.v, CBodyEmbedding.closedBlocks,
    CLoops.noDeclarations, CLoops.loop, CLoops.counterStep]

def stagedSetEnv (p buffer : Address) (count : UInt64) (shape : Tensor.Shape) : Locals :=
  bind (bind (bind (guardEnv p buffer count) "dst" (.pointer (some (p.member stateName))))
    "values" (.pointer (some buffer))) "expected" (.integer shape.volume)

def stagedSetTypes (types0 : Types) : Types :=
  bindType (bindType (bindType types0 "dst" .pointer) "values" .pointer) "expected" .size

section
variable (program : CCalls.Events.Program E)

/-- The complete setter: it validates finiteness of every caller value and then
replaces exactly the instance's state region with those values. -/
theorem set_reaches (shape : Tensor.Shape) (heap : Heap) (p buffer : Address) (count : UInt64)
    (kind : Kind) (mode : Mode) (values : Values shape) (stack : CCalls.Typed.Continuation)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3SetContinuousStates" = some (.tree (setFunction shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStates kind mode)
    (readable : Reads heap buffer values)
    (writable : Writable heap (p.member stateName) shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume, (p.member stateName).index a ≠ buffer.index b) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3SetContinuousStates" (arguments (some p) (some buffer) count) heap stack)
      (.returning (.integer 0) (written heap (p.member stateName) values shape.volume) stack) := by
  have accepted := LifecycleGuard.accept (parameters (some p) (some buffer) count) heap p
    .setStates kind mode (countReject shape.volume :: setTail shape)
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  have prefix_run : CBody.run 4 (.running (setBody shape) (parameters (some p) (some buffer) count) heap) =
      some (.running (setTail shape) (guardEnv p buffer count) heap) := by
    rw [setBody, show (4 : Nat) = 3 + 1 from rfl, CBody.run_add, accepted, Option.bind_some]
    exact TensorFloat64.run_one (TensorFloat64.reject_false (guardEnv p buffer count) heap _
      "Invalid continuous state count or pointer" (setTail shape) (count_pass heap p buffer count _ matched))
  obtain ⟨types0, entered⟩ := CCalls.Events.body_prefix_reaches program (setFunction shape)
    (arguments (some p) (some buffer) count) (parameters (some p) (some buffer) count)
    (guardEnv p buffer count) heap heap (setTail shape) stack 4 defined (parameters_bound true _ _ _)
    (setBody_closed shape) prefix_run
  refine entered.trans ?_
  have mBound : guardEnv p buffer count "m" = some (.pointer (some p)) := by simp [guardEnv, CBody.bind]
  have s_dst : CLoops.next (.running (setTail shape) (guardEnv p buffer count) types0 heap) =
      some (.running (.declare "const fmi3Float64 *" "values" (Runtime.v "continuousStates") ::
        .declare "size_t" "expected" (Runtime.n shape.volume) :: setLoopSuffix)
        (bind (guardEnv p buffer count) "dst" (.pointer (some (p.member stateName))))
        (bindType types0 "dst" .pointer) heap) :=
    TensorFloat64.declare_step_e (guardEnv p buffer count) types0 heap "fmi3Float64 *" "dst"
      ((Runtime.region stateName)) .pointer (.pointer (some (p.member stateName)))
      (.pointer (some (p.member stateName))) _ (by simp [guardEnv, parameters, CBody.bind]) rfl
      (by apply CBodyEmbedding.eval_refines
          simp [Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.lvalue, guardEnv, parameters, CBody.bind,
            CBody.resolve, mBound, Value.address]) rfl
  have s_values : CLoops.next (.running (.declare "const fmi3Float64 *" "values" (Runtime.v "continuousStates") ::
        .declare "size_t" "expected" (Runtime.n shape.volume) :: setLoopSuffix)
        (bind (guardEnv p buffer count) "dst" (.pointer (some (p.member stateName))))
        (bindType types0 "dst" .pointer) heap) =
      some (.running (.declare "size_t" "expected" (Runtime.n shape.volume) :: setLoopSuffix)
        (bind (bind (guardEnv p buffer count) "dst" (.pointer (some (p.member stateName))))
          "values" (.pointer (some buffer))) (bindType (bindType types0 "dst" .pointer) "values" .pointer) heap) :=
    TensorFloat64.declare_step_e _ _ heap "const fmi3Float64 *" "values" (Runtime.v "continuousStates") .pointer
      (.pointer (some buffer)) (.pointer (some buffer)) _ (by simp [guardEnv, parameters, CBody.bind]) rfl
      (by simp [Runtime.v, CLoops.eval, CBody.eval, guardEnv, parameters, CBody.bind, CBody.resolve]) rfl
  have s_exp : CLoops.next (.running (.declare "size_t" "expected" (Runtime.n shape.volume) :: setLoopSuffix)
        (bind (bind (guardEnv p buffer count) "dst" (.pointer (some (p.member stateName))))
          "values" (.pointer (some buffer))) (bindType (bindType types0 "dst" .pointer) "values" .pointer) heap) =
      some (.running setLoopSuffix (stagedSetEnv p buffer count shape) (stagedSetTypes types0) heap) :=
    TensorFloat64.declare_step_e _ _ heap "size_t" "expected" (Runtime.n shape.volume) .size
      (.integer shape.volume) (.integer shape.volume) _ (by simp [guardEnv, parameters, CBody.bind])
      rfl (by simp [Runtime.n, CLoops.eval, CBody.eval]) (CLoops.convert_size_nat _ bounded)
  refine .next (CCalls.Events.body_step program s_dst "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s_values "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s_exp "fmi3Status" stack) ?_))
  set env := stagedSetEnv p buffer count shape with henv
  have fresh_k : env "k" = none := by simp [henv, stagedSetEnv, guardEnv, parameters, CBody.bind]
  have expBound : resolve env "expected" = some (.integer shape.volume) := by
    simp [henv, stagedSetEnv, CBody.bind, CBody.resolve]
  have dstBound : resolve env "dst" = some (.pointer (some (p.member stateName))) := by
    simp [henv, stagedSetEnv, guardEnv, parameters, CBody.bind, CBody.resolve]
  have valuesBound : resolve env "values" = some (.pointer (some buffer)) := by
    simp [henv, stagedSetEnv, CBody.bind, CBody.resolve]
  have fmiok : env "fmi3OK" = none := by simp [henv, stagedSetEnv, guardEnv, parameters, CBody.bind]
  -- declare the counter, validate every value, reset, then copy
  refine .next (CCalls.Events.body_step program
    (CLoops.counter_initialize env (stagedSetTypes types0) heap "k"
      (CLoops.loop "k" (Runtime.v "expected") validateBody :: .assign (Runtime.v "k") (Runtime.n 0) ::
        CLoops.loop "k" (Runtime.v "expected") setCopyBody :: [Runtime.ok]) fresh_k rfl) _ stack) ?_
  refine (validate_reaches program env (CLoops.bindType (stagedSetTypes types0) "k" .size) heap buffer values
    (.assign (Runtime.v "k") (Runtime.n 0) :: CLoops.loop "k" (Runtime.v "expected") setCopyBody ::
      [Runtime.ok]) _ stack bounded (by simp [CLoops.bindType]) expBound valuesBound readable).trans ?_
  refine .next (CCalls.Events.body_step program
    (CLoops.counter_reset env (CLoops.bindType (stagedSetTypes types0) "k" .size) heap "k" shape.volume
      (CLoops.loop "k" (Runtime.v "expected") setCopyBody :: [Runtime.ok]) (by simp [CLoops.bindType]))
    _ stack) ?_
  refine (setCopy_reaches program env (CLoops.bindType (stagedSetTypes types0) "k" .size) heap
    (p.member stateName) buffer values [Runtime.ok] _ stack bounded (by simp [CLoops.bindType]) expBound
    dstBound valuesBound readable writable separate).trans ?_
  exact DerivativeCalls.finish program _ (counterEnv env "k" shape.volume)
    (CLoops.bindType (stagedSetTypes types0) "k" .size) stack (by simp [counterEnv, CBody.bind, fmiok])

theorem set_behaviors (shape : Tensor.Shape) (heap : Heap) (p buffer : Address) (count : UInt64)
    (kind : Kind) (mode : Mode) (values : Values shape)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3SetContinuousStates" = some (.tree (setFunction shape)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStates kind mode)
    (readable : Reads heap buffer values)
    (writable : Writable heap (p.member stateName) shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume, (p.member stateName).index a ≠ buffer.index b)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetContinuousStates" (arguments (some p) (some buffer) count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, written heap (p.member stateName) values shape.volume⟩ :=
  (CCalls.Events.internal_prefix program (set_reaches program shape heap p buffer count kind mode values
    .done matched bounded defined hk hm allowed readable writable separate)
    (CCalls.Events.return_forced program _ _)).behaviors behavior

/-! ### Null-handle rejections -/

theorem null_get_behaviors (shape : Tensor.Shape) (heap : Heap) (buffer : Option Address) (count : UInt64)
    (defined : program.internal.definitions "fmi3GetContinuousStates" = some (.tree (getFunction shape)))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetContinuousStates" (arguments none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (getFunction shape)
    (Runtime.modeGuard .getStates :: countReject shape.volume :: getTail shape)
    (arguments none buffer count) (parameters none buffer count) heap defined
    (parameters_bound false _ _ _) (by simp [getFunction, getBody, Runtime.require, List.append_assoc])
    rfl (getBody_closed shape)
  all_goals simp [parameters, CBody.bind]

theorem null_set_behaviors (shape : Tensor.Shape) (heap : Heap) (buffer : Option Address) (count : UInt64)
    (defined : program.internal.definitions "fmi3SetContinuousStates" = some (.tree (setFunction shape)))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetContinuousStates" (arguments none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (setFunction shape)
    (Runtime.modeGuard .setStates :: countReject shape.volume :: setTail shape)
    (arguments none buffer count) (parameters none buffer count) heap defined
    (parameters_bound true _ _ _) (by simp [setFunction, setBody, Runtime.require, List.append_assoc])
    rfl (setBody_closed shape)
  all_goals simp [parameters, CBody.bind]

end

/-! ### Bound to the static tensor instance record -/

section
variable (program : CCalls.Events.Program E) (backing : Heap) (pool : Address) (i : Nat)
  (shape oshape : Tensor.Shape) (time : Values Tensor.scalar) (state input : Values shape)
  (output : Option (Values oshape)) (buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode)

/-- The tensor `fmi3GetContinuousStates` on instance `i` copies exactly the state
region into the caller buffer and changes no instance cell. -/
theorem get_instance_behaviors (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetContinuousStates" = some (.tree (getFunction shape)))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getStates kind mode)
    (writable : Writable (TensorInstance.store backing pool i shape oshape time state input output)
      buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i stateName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetContinuousStates"
        (arguments (some (TensorInstance.record pool i)) (some buffer) count)
        (TensorInstance.store backing pool i shape oshape time state input output) .done) behavior ↔
      behavior = .terminates []
        ⟨.integer 0, written (TensorInstance.store backing pool i shape oshape time state input output)
          buffer state shape.volume⟩ :=
  get_behaviors program shape _ (TensorInstance.record pool i) buffer count kind mode state matched bounded
    defined hk hm allowed (TensorInstance.reads_state backing pool i shape oshape time state input output)
    writable separate behavior

/-- The tensor `fmi3SetContinuousStates` on instance `i` replaces exactly its
state region with the caller's finite values. -/
theorem set_instance_behaviors (newValues : Values shape) (matched : count.toNat = shape.volume)
    (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3SetContinuousStates" = some (.tree (setFunction shape)))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .setStates kind mode)
    (readable : Reads (TensorInstance.store backing pool i shape oshape time state input output) buffer newValues)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i stateName).index a ≠ buffer.index b) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetContinuousStates"
        (arguments (some (TensorInstance.record pool i)) (some buffer) count)
        (TensorInstance.store backing pool i shape oshape time state input output) .done) behavior ↔
      behavior = .terminates []
        ⟨.integer 0, written (TensorInstance.store backing pool i shape oshape time state input output)
          (TensorInstance.field pool i stateName) newValues shape.volume⟩ :=
  set_behaviors program shape _ (TensorInstance.record pool i) buffer count kind mode newValues matched bounded
    defined hk hm allowed readable
    (TensorFloat64.writable_state backing pool i shape oshape time state input output) separate behavior

/-- The successful setter's result heap preserves every tensor cell of every
other instance in the static pool. -/
theorem set_preserves_other_instances (H : Heap) (newValues : Values shape)
    (j : Nat) (b : String) (k : Nat) (different : j ≠ i) :
    written H (TensorInstance.field pool i stateName) newValues shape.volume
        ((TensorInstance.field pool j b).index k) = H ((TensorInstance.field pool j b).index k) :=
  written_frame H (TensorInstance.field pool i stateName) newValues shape.volume
    ((TensorInstance.field pool j b).index k)
    (fun j' _ => Address.instances_separate pool j i different b stateName k j')

end
end

/-! ### Printed-text denotation -/

section
open CTree.Printer CTree.Syntax

/-- The continuous-state signature prints its intended C token grammar. -/
theorem signature_printable (write : Bool) :
    SignaturePrintable RuntimePrinter.typedefs (signature write) := by
  cases write <;>
    (refine ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel, ?_⟩
     intro param member
     simp only [signature, Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at member
     rcases member with rfl | rfl | rfl <;>
       refine ⟨?_, by decide +kernel⟩ <;>
       first
         | exact .named (.typedefName (by decide +kernel) (by decide +kernel))
         | exact .const (show TypeSpelling RuntimePrinter.typedefs "fmi3Float64" from
             .named (.typedefName (by decide +kernel) (by decide +kernel))))

set_option maxHeartbeats 4000000 in
/-- Every statement of the getter body prints its intended C token grammar. -/
theorem getBody_printable (shape : Tensor.Shape) :
    ∀ stmt ∈ (getFunction shape).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  simp only [getFunction, getBody, getTail, countReject, getLoopSuffix, Runtime.region, Runtime.require,
      Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression, permittedModes,
      Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, Runtime.field, Runtime.v,
      Runtime.n, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.either, Runtime.negate, Runtime.any,
      Runtime.mode, Runtime.lt, Runtime.call, getCopyBody, TensorFloat64.srcCell, Float64Calls.output,
      CLoops.loop, CLoops.counterStep, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, List.forall_mem_nil, or_false, or_imp, forall_and,
      List.cons_append, List.nil_append, forall_eq] <;>
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

set_option maxHeartbeats 4000000 in
/-- Every statement of the setter body prints its intended C token grammar. -/
theorem setBody_printable (shape : Tensor.Shape) :
    ∀ stmt ∈ (setFunction shape).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have cfType : TypeSpelling RuntimePrinter.typedefs "const fmi3Float64 *" :=
    .const (.pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel))))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  simp only [setFunction, setBody, setTail, countReject, setLoopSuffix, Runtime.region, Runtime.require,
      Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression, permittedModes,
      Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, Runtime.field, Runtime.v,
      Runtime.n, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.either, Runtime.negate, Runtime.any,
      Runtime.mode, Runtime.lt, Runtime.call, Runtime.finite, setCopyBody, validateBody,
      TensorFloat64.dstCell, Float64Calls.output, CLoops.loop, CLoops.counterStep, List.foldr_cons,
      List.foldr_nil, List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil,
      List.forall_mem_nil, or_false, or_imp, forall_and, List.cons_append, List.nil_append, forall_eq] <;>
    repeat first
      | exact CNull.literal_printable _
      | exact iType
      | exact fType
      | exact cfType
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

/-- The rendered getter denotes its function under the shared C printer. -/
theorem getFunction_denotes (shape : Tensor.Shape) :
    FunctionDenotes RuntimePrinter.typedefs (getFunction shape).render (getFunction shape) :=
  CTree.Printer.function_denotes ⟨signature_printable false, getBody_printable shape⟩

/-- The rendered setter denotes its function under the shared C printer. -/
theorem setFunction_denotes (shape : Tensor.Shape) :
    FunctionDenotes RuntimePrinter.typedefs (setFunction shape).render (setFunction shape) :=
  CTree.Printer.function_denotes ⟨signature_printable true, setBody_printable shape⟩

end

/-! ### Consumable function contracts

These mirror the tensor Float64 accessor contracts: the printed function text, its
declaration closedness, its printed-text denotation under the shared C printer,
and a rejection guarantee for a null handle. -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The tensor `fmi3GetContinuousStates` function contract. -/
structure GetContract (shape : Tensor.Shape) (text : String) : Prop where
  printed : text = (getFunction shape).render
  closed : (getFunction shape).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (getFunction shape)
  rejected : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (buffer : Option Address) (count : UInt64),
    program.internal.definitions "fmi3GetContinuousStates" = some (.tree (getFunction shape)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetContinuousStates" (arguments none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

/-- The tensor `fmi3SetContinuousStates` function contract. -/
structure SetContract (shape : Tensor.Shape) (text : String) : Prop where
  printed : text = (setFunction shape).render
  closed : (setFunction shape).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (setFunction shape)
  rejected : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (buffer : Option Address) (count : UInt64),
    program.internal.definitions "fmi3SetContinuousStates" = some (.tree (setFunction shape)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3SetContinuousStates" (arguments none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem get_contract (shape : Tensor.Shape) : GetContract shape (getFunction shape).render where
  printed := rfl
  closed := getBody_closed shape
  denotes := getFunction_denotes shape
  rejected program heap buffer count defined := null_get_behaviors program shape heap buffer count defined

theorem set_contract (shape : Tensor.Shape) : SetContract shape (setFunction shape).render where
  printed := rfl
  closed := setBody_closed shape
  denotes := setFunction_denotes shape
  rejected program heap buffer count defined := null_set_behaviors program shape heap buffer count defined

end

/-! ### The derivative getter

`fmi3GetContinuousStateDerivatives` guards, checks the count, invokes the prepared
tensor derivative entry on the instance (`rumoca_rhs`, whose execution is the
package product `TensorInstanceRhs.derivative_writes`), then copies the written
`der(x)` region into the caller's buffer with the shared copy core.

The entry writes `der(x) = result` and preserves every other instance
(`TensorInstanceRhs.derivative_writes`, in the typed tensor call machine
`CCalls.Typed.machine`); `deriv_delivers` is the copy suffix, universal in the
heap that already holds the derivative in `der(x)`, run in the observable call
machine `CCalls.Events.machine`. Composing them across the entry call as a single
`CCalls.Events` execution needs an observable-machine execution of the tensor
entry tree, which currently lives only in the typed machine through
`TensorModelRhs`; that fused single-run theorem is the one remaining open item of
this increment, recorded in `dev/tensor-ad.md`. -/

def derivParameters (handle buffer : Option Address) (count : UInt64) : Locals :=
  bind (bind (bind (fun _ => none) "nContinuousStates" (.integer count.toNat))
    "derivatives" (.pointer buffer)) "instance" (.pointer handle)

def derivGuardEnv (p buffer : Address) (count : UInt64) : Locals :=
  bind (derivParameters (some p) (some buffer) count) "m" (.pointer (some p))

def derivCountReject (volume : Nat) : Stmt :=
  Runtime.reject (Runtime.any [Runtime.nev (Runtime.v "nContinuousStates") (Runtime.n volume),
    Runtime.negate (Runtime.v "derivatives")]) "Invalid continuous state count or pointer"

/-- The C arguments of the prepared derivative entry: pointers to the instance's
`x`, `u` and `der(x)` regions and the element count. -/
def derivEntryArgs : List Expr :=
  [(Runtime.region stateName), (Runtime.region inputName),
    (Runtime.region derivativeName), Runtime.v "nContinuousStates"]

/-- The C arguments of the prepared square-Jacobian diagonal entry: a pointer to
the instance's input region `u` (the coefficients), a pointer to its output region
`J` (the dense matrix), the state element count and the flattened matrix cell
count. This is the argument form `(&(m->u[0]), &(m->J[0]), nContinuousStates,
cells)`; the cell count is the row-major volume of the `N*N` matrix, emitted as a
decimal literal. -/
def jacobianEntryArgs (shape : Tensor.Shape) : List Expr :=
  [(Runtime.region inputName), (Runtime.region outputName),
    Runtime.v "nContinuousStates",
    Runtime.n (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume]

/-- The copy suffix that stages the `der(x)` region and moves it into the buffer. -/
def derivCopyTail (shape : Tensor.Shape) : List Stmt :=
  .declare "fmi3Float64 *" "src" ((Runtime.region derivativeName)) ::
  .declare "fmi3Float64 *" "values" (Runtime.v "derivatives") ::
  .declare "size_t" "expected" (Runtime.n shape.volume) :: getLoopSuffix

/-- The prepared square-Jacobian diagonal call statement, evaluated for its
effect on the instance's output region `J`. -/
def jacobianCall (shape : Tensor.Shape) : Stmt :=
  .eval (Runtime.call "rumoca_square_jacobian_diag" (jacobianEntryArgs shape))

/-- The derivative getter's tail after the `rumoca_rhs` call. When the prepared
problem exposes a dense observation, the square-Jacobian diagonal entry runs
before the `der(x)` copy suffix; otherwise the copy suffix runs directly. -/
def derivTail (shape : Tensor.Shape) : Bool → List Stmt
  | false => derivCopyTail shape
  | true => jacobianCall shape :: derivCopyTail shape

def derivBody (shape : Tensor.Shape) (hasOutput : Bool) : List Stmt :=
  Runtime.require .getDerivatives ++
    (derivCountReject shape.volume :: .eval (Runtime.call "rumoca_rhs" derivEntryArgs) ::
      derivTail shape hasOutput)

def derivFunction (shape : Tensor.Shape) (hasOutput : Bool) : CTree.Function :=
  ⟨DerivativeCalls.signature, derivBody shape hasOutput, false⟩

section
variable [static : StaticLiterals]
private local instance derivInterface : CInterface := cInterface static.addresses

theorem derivParameters_bound (handle buffer : Option Address) (count : UInt64) :
    CCalls.parameters DerivativeCalls.signature.parameters
      (DerivativeCalls.values handle buffer count) = some (derivParameters handle buffer count) := by
  have cc : CBody.cast "size_t" (.integer count.toNat) = some (.integer count.toNat) :=
    CLoops.Calls.cast_of_type "size_t" .size _ _ rfl (CLoops.convert_size_nat _ count.toNat_lt_size)
  simp only [DerivativeCalls.signature, DerivativeCalls.values, CCalls.parameters, CCalls.parameterType,
    Bool.false_eq_true, ↓reduceIte, cc]
  rfl

theorem derivBody_closed (shape : Tensor.Shape) (hasOutput : Bool) :
    (derivFunction shape hasOutput).body.all CBodyEmbedding.closedBlocks = true := by
  cases hasOutput <;>
    simp [derivFunction, derivBody, derivTail, jacobianCall, jacobianEntryArgs, derivCopyTail,
      derivCountReject, derivEntryArgs, getLoopSuffix, getCopyBody, Runtime.require,
      Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject, Runtime.branch, Runtime.fail,
      Runtime.ret, Runtime.ok, Runtime.field, Runtime.v, Runtime.n, Runtime.region, Runtime.call,
      CBodyEmbedding.closedBlocks, CLoops.noDeclarations, CLoops.loop, CLoops.counterStep]

/-- The derivative count/pointer check passes for a matched non-null request. -/
theorem derivCount_pass (heap : Heap) (p buffer : Address) (count : UInt64) (volume : Nat)
    (matched : count.toNat = volume) :
    CBody.eval (derivGuardEnv p buffer count) heap
      (Runtime.any [Runtime.nev (Runtime.v "nContinuousStates") (Runtime.n volume),
        Runtime.negate (Runtime.v "derivatives")]) = some (boolean false) := by
  simp [Runtime.any, Runtime.either, Runtime.negate, Runtime.nev, Runtime.v, Runtime.n, CBody.eval,
    derivGuardEnv, derivParameters, CBody.bind, CBody.resolve, CBody.comparison, boolean, Value.truth, matched]

variable (program : CCalls.Events.Program E)

/-- The entry-call step: from the checked prefix the observable scheduler enters
the prepared tensor derivative entry `rumoca_rhs`, resolved directly by name,
with the instance's `x`, `u` and `der(x)` region pointers and the element count
as arguments and the copy suffix saved as the caller continuation. -/
theorem deriv_enter (shape : Tensor.Shape) (p buffer : Address) (count : UInt64)
    (types0 : Types) (H : Heap) (rest : List Stmt) (stack : CCalls.Typed.Continuation) :
    CCalls.Events.internalNext program
      (.body (.running (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: rest)
        (derivGuardEnv p buffer count) types0 H) "fmi3Status" stack) =
      some (.calling "rumoca_rhs"
        [.pointer (some (p.member stateName)), .pointer (some (p.member inputName)),
         .pointer (some (p.member derivativeName)), .integer count.toNat] H
        (.caller .discard rest (derivGuardEnv p buffer count) types0 "fmi3Status" stack)) := by
  simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CLoops.next, CLoops.eval,
    derivEntryArgs, Runtime.call, Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval,
    CBody.lvalue,
    CCalls.Events.enterCall, CCalls.Events.resolve, CCalls.Indirect.operand, CCalls.Indirect.resolve,
    CCalls.arguments, derivGuardEnv, derivParameters, CBody.bind, CBody.resolve, CBody.constants,
    Value.address]

/-- The Jacobian entry-call step: from the resumed `der(x)` frame the observable
scheduler enters the prepared square-Jacobian diagonal entry
`rumoca_square_jacobian_diag`, resolved directly by name, with the instance's `u`
and `J` region pointers, the element count and the flattened matrix cell count as
arguments and the remaining copy suffix saved as the caller continuation. -/
theorem jac_enter (shape : Tensor.Shape) (p buffer : Address) (count : UInt64)
    (types0 : Types) (H : Heap) (rest : List Stmt) (stack : CCalls.Typed.Continuation) :
    CCalls.Events.internalNext program
      (.body (.running (jacobianCall shape :: rest)
        (derivGuardEnv p buffer count) types0 H) "fmi3Status" stack) =
      some (.calling "rumoca_square_jacobian_diag"
        [.pointer (some (p.member inputName)), .pointer (some (p.member outputName)),
         .integer count.toNat, .integer (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume] H
        (.caller .discard rest (derivGuardEnv p buffer count) types0 "fmi3Status" stack)) := by
  simp [jacobianCall, CCalls.Events.internalNext, CCalls.Typed.nextWith, CLoops.next, CLoops.eval,
    jacobianEntryArgs, Runtime.call, Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval,
    CBody.lvalue,
    CCalls.Events.enterCall, CCalls.Events.resolve, CCalls.Indirect.operand, CCalls.Indirect.resolve,
    CCalls.arguments, derivGuardEnv, derivParameters, CBody.bind, CBody.resolve, CBody.constants,
    Value.address]

/-- The copy suffix of the derivative getter: over any heap whose `der(x)` region
already holds the finite derivative `result`, it delivers `result` into the
caller buffer in row-major order and changes no other cell. -/
theorem deriv_delivers (shape : Tensor.Shape) (H : Heap) (p buffer : Address) (count : UInt64)
    (types0 : Types) (result : Values shape) (stack : CCalls.Typed.Continuation)
    (bounded : shape.volume < 2 ^ 64)
    (readable : Reads H (p.member derivativeName) result)
    (writable : Writable H buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume, (p.member derivativeName).index a ≠ buffer.index b) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (derivCopyTail shape) (derivGuardEnv p buffer count) types0 H) "fmi3Status" stack)
      (.returning (.integer 0) (written H buffer result shape.volume) stack) := by
  have mBound : derivGuardEnv p buffer count "m" = some (.pointer (some p)) := by
    simp [derivGuardEnv, CBody.bind]
  have s_src : CLoops.next (.running (derivCopyTail shape) (derivGuardEnv p buffer count) types0 H) =
      some (.running (.declare "fmi3Float64 *" "values" (Runtime.v "derivatives") ::
        .declare "size_t" "expected" (Runtime.n shape.volume) :: getLoopSuffix)
        (bind (derivGuardEnv p buffer count) "src" (.pointer (some (p.member derivativeName))))
        (bindType types0 "src" .pointer) H) :=
    TensorFloat64.declare_step_e (derivGuardEnv p buffer count) types0 H "fmi3Float64 *" "src"
      ((Runtime.region derivativeName)) .pointer (.pointer (some (p.member derivativeName)))
      (.pointer (some (p.member derivativeName))) _ (by simp [derivGuardEnv, derivParameters, CBody.bind])
      rfl (by apply CBodyEmbedding.eval_refines
              simp [Runtime.region, Runtime.field, Runtime.v, Runtime.n, CBody.eval, CBody.lvalue, derivGuardEnv, derivParameters,
                CBody.bind, CBody.resolve, mBound, Value.address]) rfl
  have s_values : CLoops.next (.running (.declare "fmi3Float64 *" "values" (Runtime.v "derivatives") ::
        .declare "size_t" "expected" (Runtime.n shape.volume) :: getLoopSuffix)
        (bind (derivGuardEnv p buffer count) "src" (.pointer (some (p.member derivativeName))))
        (bindType types0 "src" .pointer) H) =
      some (.running (.declare "size_t" "expected" (Runtime.n shape.volume) :: getLoopSuffix)
        (bind (bind (derivGuardEnv p buffer count) "src" (.pointer (some (p.member derivativeName))))
          "values" (.pointer (some buffer))) (bindType (bindType types0 "src" .pointer) "values" .pointer) H) :=
    TensorFloat64.declare_step_e _ _ H "fmi3Float64 *" "values" (Runtime.v "derivatives") .pointer
      (.pointer (some buffer)) (.pointer (some buffer)) _ (by simp [derivGuardEnv, derivParameters, CBody.bind])
      rfl (by simp [Runtime.v, CLoops.eval, CBody.eval, derivGuardEnv, derivParameters, CBody.bind, CBody.resolve]) rfl
  set env := bind (bind (bind (derivGuardEnv p buffer count) "src" (.pointer (some (p.member derivativeName))))
    "values" (.pointer (some buffer))) "expected" (.integer shape.volume) with henv
  set types := bindType (bindType (bindType types0 "src" .pointer) "values" .pointer) "expected" .size with htypes
  have s_exp : CLoops.next (.running (.declare "size_t" "expected" (Runtime.n shape.volume) :: getLoopSuffix)
        (bind (bind (derivGuardEnv p buffer count) "src" (.pointer (some (p.member derivativeName))))
          "values" (.pointer (some buffer))) (bindType (bindType types0 "src" .pointer) "values" .pointer) H) =
      some (.running getLoopSuffix env types H) :=
    TensorFloat64.declare_step_e _ _ H "size_t" "expected" (Runtime.n shape.volume) .size
      (.integer shape.volume) (.integer shape.volume) _ (by simp [derivGuardEnv, derivParameters, CBody.bind])
      rfl (by simp [Runtime.n, CLoops.eval, CBody.eval]) (CLoops.convert_size_nat _ bounded)
  refine .next (CCalls.Events.body_step program s_src "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s_values "fmi3Status" stack)
    (.next (CCalls.Events.body_step program s_exp "fmi3Status" stack) ?_))
  have fresh_k : env "k" = none := by simp [henv, derivGuardEnv, derivParameters, CBody.bind]
  have expBound : resolve env "expected" = some (.integer shape.volume) := by
    simp [henv, CBody.bind, CBody.resolve]
  have srcBound : resolve env "src" = some (.pointer (some (p.member derivativeName))) := by
    simp [henv, derivGuardEnv, derivParameters, CBody.bind, CBody.resolve]
  have valuesBound : resolve env "values" = some (.pointer (some buffer)) := by
    simp [henv, CBody.bind, CBody.resolve]
  have fmiok : env "fmi3OK" = none := by simp [henv, derivGuardEnv, derivParameters, CBody.bind]
  refine .next (CCalls.Events.body_step program
    (CLoops.counter_initialize env types H "k"
      (CLoops.loop "k" (Runtime.v "expected") getCopyBody :: [Runtime.ok]) fresh_k rfl) _ stack) ?_
  refine (getCopy_reaches program env (CLoops.bindType types "k" .size) H (p.member derivativeName) buffer
    result [Runtime.ok] _ stack bounded (by simp [CLoops.bindType]) expBound srcBound valuesBound
    readable writable separate).trans ?_
  exact DerivativeCalls.finish program _ (counterEnv env "k" shape.volume) (CLoops.bindType types "k" .size)
    stack (by simp [counterEnv, CBody.bind, fmiok])

/-- The derivative getter over instance `i`, after the prepared entry has written
`der(x) = derivatives` (the situation established by
`TensorInstanceRhs.derivative_writes`): its copy suffix delivers `derivatives`
into the caller buffer, leaving every other cell of the written heap unchanged. -/
theorem deriv_instance_delivers (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Tensor.Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (output : Option (Values oshape))
    (derivatives : Values shape) (buffer : Address) (count : UInt64) (types0 : Types)
    (stack : CCalls.Typed.Continuation) (bounded : shape.volume < 2 ^ 64)
    (writable : Writable (written (TensorInstance.store backing pool i shape oshape time state input output)
      (TensorInstance.field pool i derivativeName) derivatives shape.volume) buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (derivCopyTail shape) (derivGuardEnv (TensorInstance.record pool i) buffer count) types0
        (written (TensorInstance.store backing pool i shape oshape time state input output)
          (TensorInstance.field pool i derivativeName) derivatives shape.volume)) "fmi3Status" stack)
      (.returning (.integer 0)
        (written (written (TensorInstance.store backing pool i shape oshape time state input output)
          (TensorInstance.field pool i derivativeName) derivatives shape.volume) buffer derivatives shape.volume)
        stack) :=
  deriv_delivers program shape _ (TensorInstance.record pool i) buffer count types0 derivatives stack bounded
    (written_reads _ (TensorInstance.field pool i derivativeName) derivatives) writable separate

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile in
/-- The fused single-run derivative getter over instance `i`: guarding, checking
the count, invoking the prepared tensor derivative entry through the transfer
lemma, and copying the written `der(x)` region into the caller buffer, all as one
observable-machine execution. It reaches `fmi3OK` with the caller buffer holding
the finite tensor derivative (`written finalHeap buffer result`), the instance's
`der(x)` region holding the same values (`reads`), and every other cell of every
other instance preserved (`others`). The `resolves` premise records that the
nested tensor helper calls the entry visits resolve directly by name. -/
theorem deriv_reaches (shape oshape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state input result : Values shape) (output : Option (Values oshape))
    (buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivFunction shape false)))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives kind mode)
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
        (.calling "fmi3GetContinuousStateDerivatives"
          (DerivativeCalls.values (some (TensorInstance.record pool i)) (some buffer) count)
          (TensorInstance.store backing pool i shape oshape time state input output) stack)
        (.returning (.integer 0)
          (written finalHeap buffer result shape.volume) stack) := by
  set H := TensorInstance.store backing pool i shape oshape time state input output with hH
  set m := TensorInstance.record pool i with hm'
  have accepted := LifecycleGuard.accept (derivParameters (some m) (some buffer) count) H m
    .getDerivatives kind mode
    (derivCountReject shape.volume :: .eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: derivCopyTail shape)
    (by simp [derivParameters, CBody.bind]) (by simp [derivParameters, CBody.bind]) hk hm allowed
  have prefixRun : CBody.run 4 (.running (derivBody shape false) (derivParameters (some m) (some buffer) count) H) =
      some (.running (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: derivCopyTail shape)
        (derivGuardEnv m buffer count) H) := by
    rw [derivBody]; simp only [derivTail]
    rw [show (4 : Nat) = 3 + 1 from rfl, CBody.run_add, accepted, Option.bind_some]
    exact TensorFloat64.run_one (TensorFloat64.reject_false (derivGuardEnv m buffer count) H
      (Runtime.any [Runtime.nev (Runtime.v "nContinuousStates") (Runtime.n shape.volume),
        Runtime.negate (Runtime.v "derivatives")]) "Invalid continuous state count or pointer"
      (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: derivCopyTail shape)
      (derivCount_pass H m buffer count shape.volume matched))
  obtain ⟨types0, entered⟩ := CCalls.Events.body_prefix_reaches program (derivFunction shape false)
    (DerivativeCalls.values (some m) (some buffer) count) (derivParameters (some m) (some buffer) count)
    (derivGuardEnv m buffer count) H H
    (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: derivCopyTail shape) stack 4 defined
    (derivParameters_bound _ _ _) (derivBody_closed shape false) prefixRun
  have argsEq : [Value.pointer (some (m.member stateName)), .pointer (some (m.member inputName)),
      .pointer (some (m.member derivativeName)), .integer count.toNat] =
      Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
        (TensorInstanceRhs.args pool i shape) := by
    rw [hm', matched]; rfl
  have enterStep : CCalls.Events.internalNext program
      (.body (.running (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: derivCopyTail shape)
        (derivGuardEnv m buffer count) types0 H) "fmi3Status" stack) =
      some (.calling "rumoca_rhs"
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) H
        (.caller .discard (derivCopyTail shape) (derivGuardEnv m buffer count) types0 "fmi3Status" stack)) := by
    rw [← argsEq]; exact deriv_enter program shape m buffer count types0 H (derivCopyTail shape) stack
  obtain ⟨finalHeap, reads, _writableDeriv, frameH, others, ran⟩ :=
    TensorInstanceRhs.derivative_writes_events (shape := shape) definitions program linked library found
      backing pool i oshape time state input result output bounded executed resolves
      (.caller .discard (derivCopyTail shape) (derivGuardEnv m buffer count) types0 "fmi3Status" stack)
  have resumeStep : CCalls.Events.internalNext program
      (.returning .void finalHeap
        (.caller .discard (derivCopyTail shape) (derivGuardEnv m buffer count) types0 "fmi3Status" stack)) =
      some (.body (.running (derivCopyTail shape) (derivGuardEnv m buffer count) types0 finalHeap)
        "fmi3Status" stack) := by
    simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CCalls.Typed.resume]
  have writableFinal : Writable finalHeap buffer shape.volume := by
    intro b hb
    obtain ⟨old, ho⟩ := writable b hb
    exact ⟨old, (frameH (buffer.index b)
      (TensorInstanceRhs.buffer_outside pool i buffer b hb separate)).trans ho⟩
  have deliver := deriv_delivers program shape finalHeap m buffer count types0 result stack bounded
    reads writableFinal separate
  refine ⟨finalHeap, reads, others, entered.trans (.next enterStep (ran.trans (.next resumeStep deliver)))⟩

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile in
/-- The fused derivative getter's sole terminating observable behavior over
instance `i`: it returns `fmi3OK` with the finite tensor derivative delivered to
the caller buffer, the instance's `der(x)` region holding the same values, and
every other cell of every other instance preserved. -/
theorem deriv_behaviors (shape oshape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state input result : Values shape) (output : Option (Values oshape))
    (buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivFunction shape false)))
    (hk : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives kind mode)
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
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3GetContinuousStateDerivatives"
          (DerivativeCalls.values (some (TensorInstance.record pool i)) (some buffer) count)
          (TensorInstance.store backing pool i shape oshape time state input output) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, written finalHeap buffer result shape.volume⟩ := by
  obtain ⟨finalHeap, reads, others, ran⟩ :=
    deriv_reaches program shape oshape definitions linked library found backing pool i time state input result
      output buffer count kind mode .done matched bounded defined hk hm allowed executed writable separate resolves
  exact ⟨finalHeap, reads, others, fun behavior =>
    (CCalls.Events.internal_prefix program ran (CCalls.Events.return_forced program _ _)).behaviors behavior⟩

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile Rumoca.CTensor in
/-- The fused single-run output-aware derivative getter over instance `i`:
guarding, checking the count, invoking the prepared derivative entry `rumoca_rhs`,
then the prepared square-Jacobian diagonal entry `rumoca_square_jacobian_diag`,
and copying the written `der(x)` region into the caller buffer, all as one
observable-machine execution. It reaches `fmi3OK` with the caller buffer holding
the finite tensor derivative, the instance's `der(x)` region holding the same
values (`reads`), its `J` region holding the dense Jacobian `diag(2*u)`
(`jacReads`), and every other cell of every other instance preserved (`others`).
The `resolves`/`jacResolves` premises record that the nested tensor helper calls
each entry visits resolve directly by name, and `adds` is the explicit no-overflow
condition on the doubled input cells. -/
theorem deriv_output_reaches (shape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (jacFound : definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function)
    (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state input result : Values shape)
    (J : Values (Rumoca.Tensor.matrixShape shape.volume shape.volume))
    (buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (bounded2 : (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivFunction shape true)))
    (hk : load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives kind mode)
    (executed : Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment state input) result)
    (writable : Writable (TensorInstance.store backing pool i shape
      (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input (some J)) buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b)
    (separateOutput : ∀ a < (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume, ∀ b < shape.volume,
      (TensorInstance.field pool i outputName).index a ≠ buffer.index b)
    (adds : ∀ k : Fin shape.volume,
      Binary64.Adds input[k] input[k] (.finite (SquareDiagonal.doubled input)[k]))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape))
        (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
          time state input (some J)) .done) v →
      CCalls.Events.Resolves program v)
    (jacResolves : ∀ (H' : Heap) v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling SquareDiagonal.function.signature.name
        (Diagonal.argumentValues (TensorInstance.field pool i inputName)
          (TensorInstance.field pool i outputName) shape) H' .done) v →
      CCalls.Events.Resolves program v) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName) result ∧
      Reads finalHeap (TensorInstance.field pool i outputName)
        (Diagonal.matrix (SquareDiagonal.doubled input)) ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          backing ((TensorInstance.field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling "fmi3GetContinuousStateDerivatives"
          (DerivativeCalls.values (some (TensorInstance.record pool i)) (some buffer) count)
          (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
            time state input (some J)) stack)
        (.returning (.integer 0)
          (written finalHeap buffer result shape.volume) stack) := by
  set H := TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
    time state input (some J) with hH
  set m := TensorInstance.record pool i with hm'
  -- guard, count check, then enter the typed body at the two entry calls plus the copy suffix
  have accepted := LifecycleGuard.accept (derivParameters (some m) (some buffer) count) H m
    .getDerivatives kind mode
    (derivCountReject shape.volume :: .eval (Runtime.call "rumoca_rhs" derivEntryArgs) ::
      jacobianCall shape :: derivCopyTail shape)
    (by simp [derivParameters, CBody.bind]) (by simp [derivParameters, CBody.bind]) hk hm allowed
  have prefixRun : CBody.run 4 (.running (derivBody shape true) (derivParameters (some m) (some buffer) count) H) =
      some (.running (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: jacobianCall shape :: derivCopyTail shape)
        (derivGuardEnv m buffer count) H) := by
    rw [derivBody]; simp only [derivTail]
    rw [show (4 : Nat) = 3 + 1 from rfl, CBody.run_add, accepted, Option.bind_some]
    exact TensorFloat64.run_one (TensorFloat64.reject_false (derivGuardEnv m buffer count) H
      (Runtime.any [Runtime.nev (Runtime.v "nContinuousStates") (Runtime.n shape.volume),
        Runtime.negate (Runtime.v "derivatives")]) "Invalid continuous state count or pointer"
      (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: jacobianCall shape :: derivCopyTail shape)
      (derivCount_pass H m buffer count shape.volume matched))
  obtain ⟨types0, entered⟩ := CCalls.Events.body_prefix_reaches program (derivFunction shape true)
    (DerivativeCalls.values (some m) (some buffer) count) (derivParameters (some m) (some buffer) count)
    (derivGuardEnv m buffer count) H H
    (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: jacobianCall shape :: derivCopyTail shape) stack 4 defined
    (derivParameters_bound _ _ _) (derivBody_closed shape true) prefixRun
  -- the derivative entry `rumoca_rhs`
  have argsEq : [Value.pointer (some (m.member stateName)), .pointer (some (m.member inputName)),
      .pointer (some (m.member derivativeName)), .integer count.toNat] =
      Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
        (TensorInstanceRhs.args pool i shape) := by
    rw [hm', matched]; rfl
  have enterStep : CCalls.Events.internalNext program
      (.body (.running (.eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: jacobianCall shape :: derivCopyTail shape)
        (derivGuardEnv m buffer count) types0 H) "fmi3Status" stack) =
      some (.calling "rumoca_rhs"
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape)) H
        (.caller .discard (jacobianCall shape :: derivCopyTail shape) (derivGuardEnv m buffer count) types0
          "fmi3Status" stack)) := by
    rw [← argsEq]
    exact deriv_enter program shape m buffer count types0 H (jacobianCall shape :: derivCopyTail shape) stack
  obtain ⟨finalHeap1, reads, _writableDeriv, frameH, others, ran⟩ :=
    TensorInstanceRhs.derivative_writes_events (shape := shape) definitions program linked library found
      backing pool i (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input result (some J)
      bounded executed resolves
      (.caller .discard (jacobianCall shape :: derivCopyTail shape) (derivGuardEnv m buffer count) types0
        "fmi3Status" stack)
  have resumeStep1 : CCalls.Events.internalNext program
      (.returning .void finalHeap1
        (.caller .discard (jacobianCall shape :: derivCopyTail shape) (derivGuardEnv m buffer count) types0
          "fmi3Status" stack)) =
      some (.body (.running (jacobianCall shape :: derivCopyTail shape) (derivGuardEnv m buffer count) types0
        finalHeap1) "fmi3Status" stack) := by
    simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CCalls.Typed.resume]
  -- the input region is readable and the output region writable on the post-RHS heap
  have readsInputFinal : Reads finalHeap1 (TensorInstance.field pool i inputName) input := by
    intro k
    have hpt := frameH ((TensorInstance.field pool i inputName).index k.val)
      (TensorInstanceRhs.field_outside pool i inputName k.val (by decide +kernel))
    have h := TensorInstance.reads_input backing pool i shape
      (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input (some J) k
    simp only [load] at h ⊢
    rw [hpt]; exact h
  have writableOutputFinal : Writable finalHeap1 (TensorInstance.field pool i outputName)
      (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume := by
    intro b hb
    obtain ⟨old, ho⟩ := TensorInstance.writable_output backing pool i shape
      (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input J b hb
    exact ⟨old, (frameH _ (TensorInstanceRhs.field_outside pool i outputName b (by decide +kernel))).trans ho⟩
  -- the Jacobian entry `rumoca_square_jacobian_diag`
  have argsEqJac : [Value.pointer (some (m.member inputName)), .pointer (some (m.member outputName)),
      .integer count.toNat, .integer (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume] =
      Diagonal.argumentValues (TensorInstance.field pool i inputName)
        (TensorInstance.field pool i outputName) shape := by
    rw [hm', matched]; rfl
  have jacEnterStep : CCalls.Events.internalNext program
      (.body (.running (jacobianCall shape :: derivCopyTail shape) (derivGuardEnv m buffer count) types0 finalHeap1)
        "fmi3Status" stack) =
      some (.calling "rumoca_square_jacobian_diag"
        (Diagonal.argumentValues (TensorInstance.field pool i inputName)
          (TensorInstance.field pool i outputName) shape) finalHeap1
        (.caller .discard (derivCopyTail shape) (derivGuardEnv m buffer count) types0 "fmi3Status" stack)) := by
    rw [← argsEqJac]
    exact jac_enter program shape m buffer count types0 finalHeap1 (derivCopyTail shape) stack
  obtain ⟨jacReads, jacFrame, jacRan⟩ :=
    TensorInstanceJacobian.jacobian_writes_events (shape := shape) definitions program linked library jacFound
      pool i input finalHeap1 bounded2 readsInputFinal writableOutputFinal adds (jacResolves finalHeap1)
      (.caller .discard (derivCopyTail shape) (derivGuardEnv m buffer count) types0 "fmi3Status" stack)
  set finalHeap2 := Diagonal.resultHeap finalHeap1 (TensorInstance.field pool i outputName)
    (SquareDiagonal.doubled input) with hfh2
  have resumeStep2 : CCalls.Events.internalNext program
      (.returning .void finalHeap2
        (.caller .discard (derivCopyTail shape) (derivGuardEnv m buffer count) types0 "fmi3Status" stack)) =
      some (.body (.running (derivCopyTail shape) (derivGuardEnv m buffer count) types0 finalHeap2)
        "fmi3Status" stack) := by
    simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CCalls.Typed.resume]
  -- der(x) survives the Jacobian write, and every other instance is preserved
  have derReadFinal : Reads finalHeap2 (TensorInstance.field pool i derivativeName) result := by
    intro k
    have hpt := jacFrame ((TensorInstance.field pool i derivativeName).index k.val)
      (fun a _ => TensorInstance.fields_separate pool i derivativeName outputName (by decide +kernel) k.val a)
    simp only [load] at reads ⊢
    rw [hpt]; exact reads k
  have others2 : ∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
      finalHeap2 ((TensorInstance.field pool j b).index k) = backing ((TensorInstance.field pool j b).index k) := by
    intro j b k hji
    rw [jacFrame ((TensorInstance.field pool j b).index k)
      (fun a _ => Address.instances_separate pool j i hji b outputName k a)]
    exact others j b k hji
  -- the caller buffer stays writable across both writes, then the copy suffix delivers der(x)
  have writableBufferFinal : Writable finalHeap2 buffer shape.volume := by
    intro b hb
    obtain ⟨old, ho⟩ := writable b hb
    refine ⟨old, ?_⟩
    rw [jacFrame _ (fun a ha => (separateOutput a ha b hb).symm),
      frameH _ (TensorInstanceRhs.buffer_outside pool i buffer b hb separate)]
    exact ho
  have deliver := deriv_delivers program shape finalHeap2 m buffer count types0 result stack bounded
    derReadFinal writableBufferFinal separate
  exact ⟨finalHeap2, derReadFinal, jacReads, others2,
    entered.trans (.next enterStep (ran.trans (.next resumeStep1
      (.next jacEnterStep (jacRan.trans (.next resumeStep2 deliver))))))⟩

open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile Rumoca.CTensor in
/-- The output-aware derivative getter's sole terminating observable behavior over
instance `i`: it returns `fmi3OK` with the finite tensor derivative delivered to
the caller buffer, the instance's `der(x)` region holding the same values, its `J`
region holding the dense Jacobian `diag(2*u)`, and every other cell of every other
instance preserved. -/
theorem deriv_output_behaviors (shape : Tensor.Shape) (definitions : CLoops.Calls.Definitions)
    (linked : CCalls.Typed.Extends definitions program.internal)
    (library : Rumoca.CTensor.Lowering.Library definitions)
    (found : definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree)
    (jacFound : definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function)
    (backing : Heap) (pool : Address) (i : Nat)
    (time : Values Tensor.scalar) (state input result : Values shape)
    (J : Values (Rumoca.Tensor.matrixShape shape.volume shape.volume))
    (buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode)
    (matched : count.toNat = shape.volume) (bounded : shape.volume < 2 ^ 64)
    (bounded2 : (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivFunction shape true)))
    (hk : load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) ((TensorInstance.record pool i).member "kind") = some (.integer kind.code))
    (hm : load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) ((TensorInstance.record pool i).member "mode") = some (.integer mode.code))
    (allowed : Reference.Allowed .getDerivatives kind mode)
    (executed : Finite.Executes (TensorInstanceRhs.kernel shape).derivative
      (ArrayProfile.environment state input) result)
    (writable : Writable (TensorInstance.store backing pool i shape
      (Rumoca.Tensor.matrixShape shape.volume shape.volume) time state input (some J)) buffer shape.volume)
    (separate : ∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b)
    (separateOutput : ∀ a < (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume, ∀ b < shape.volume,
      (TensorInstance.field pool i outputName).index a ≠ buffer.index b)
    (adds : ∀ k : Fin shape.volume,
      Binary64.Adds input[k] input[k] (.finite (SquareDiagonal.doubled input)[k]))
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape))
        (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
          time state input (some J)) .done) v →
      CCalls.Events.Resolves program v)
    (jacResolves : ∀ (H' : Heap) v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling SquareDiagonal.function.signature.name
        (Diagonal.argumentValues (TensorInstance.field pool i inputName)
          (TensorInstance.field pool i outputName) shape) H' .done) v →
      CCalls.Events.Resolves program v) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName) result ∧
      Reads finalHeap (TensorInstance.field pool i outputName)
        (Diagonal.matrix (SquareDiagonal.doubled input)) ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          backing ((TensorInstance.field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3GetContinuousStateDerivatives"
          (DerivativeCalls.values (some (TensorInstance.record pool i)) (some buffer) count)
          (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
            time state input (some J)) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, written finalHeap buffer result shape.volume⟩ := by
  obtain ⟨finalHeap, dReads, jReads, others, ran⟩ :=
    deriv_output_reaches program shape definitions linked library found jacFound backing pool i time state input
      result J buffer count kind mode .done matched bounded bounded2 defined hk hm allowed executed writable
      separate separateOutput adds resolves jacResolves
  exact ⟨finalHeap, dReads, jReads, others, fun behavior =>
    (CCalls.Events.internal_prefix program ran (CCalls.Events.return_forced program _ _)).behaviors behavior⟩

/-- A null instance handle is rejected with `fmi3Error`, changing nothing. -/
theorem null_deriv_behaviors (shape : Tensor.Shape) (hasOutput : Bool) (heap : Heap)
    (buffer : Option Address) (count : UInt64)
    (defined : program.internal.definitions "fmi3GetContinuousStateDerivatives" =
      some (.tree (derivFunction shape hasOutput)))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetContinuousStateDerivatives" (DerivativeCalls.values none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (derivFunction shape hasOutput)
    (Runtime.modeGuard .getDerivatives :: derivCountReject shape.volume ::
      .eval (Runtime.call "rumoca_rhs" derivEntryArgs) :: derivTail shape hasOutput)
    (DerivativeCalls.values none buffer count) (derivParameters none buffer count) heap defined
    (derivParameters_bound _ _ _)
    (by cases hasOutput <;> simp [derivFunction, derivBody, derivTail, Runtime.require, List.append_assoc])
    rfl (derivBody_closed shape hasOutput)
  all_goals simp [derivParameters, CBody.bind]

end

/-! ### Printed-text denotation of the derivative getter -/

section
open CTree.Printer CTree.Syntax

set_option maxHeartbeats 4000000 in
theorem derivBody_printable (shape : Tensor.Shape) (hasOutput : Bool) :
    ∀ stmt ∈ (derivFunction shape hasOutput).body, ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  cases hasOutput <;>
    simp only [derivFunction, derivBody, derivTail, jacobianCall, jacobianEntryArgs, derivCopyTail,
      derivCountReject, derivEntryArgs, getLoopSuffix, Runtime.region,
      Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.allowedExpression, permittedModes,
      Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret, Runtime.ok, Runtime.field, Runtime.v,
      Runtime.n, Runtime.eqv, Runtime.nev, Runtime.both, Runtime.either, Runtime.negate, Runtime.any,
      Runtime.mode, Runtime.lt, Runtime.call, getCopyBody, TensorFloat64.srcCell, Float64Calls.output,
      CLoops.loop, CLoops.counterStep, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, List.forall_mem_nil, or_false, or_imp, forall_and,
      List.cons_append, List.nil_append, forall_eq] <;>
    repeat first
      | exact CNull.literal_printable _
      | exact iType
      | exact fType
      | exact sType
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

theorem derivSignature_printable :
    SignaturePrintable RuntimePrinter.typedefs DerivativeCalls.signature := by
  refine ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel, ?_⟩
  intro param member
  simp only [DerivativeCalls.signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  all_goals exact ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩

/-- The rendered derivative getter denotes its function under the shared C printer. -/
theorem derivFunction_denotes (shape : Tensor.Shape) (hasOutput : Bool) :
    FunctionDenotes RuntimePrinter.typedefs (derivFunction shape hasOutput).render (derivFunction shape hasOutput) :=
  CTree.Printer.function_denotes ⟨derivSignature_printable, derivBody_printable shape hasOutput⟩

end

/-! ### Consumable derivative-getter contract

This mirrors the scalar `DerivativeContract`-style `FunctionContract`: the printed
function text, its declaration closedness, its printed-text denotation under the
shared C printer, the fused single-run execution over the tensor instance record,
and the null-handle rejection. A tensor adapter contract can consume it. -/

section
open CTree.Printer
open Rumoca.CTensor.Lowering Solve.Tensor Rumoca.ArrayProfile Rumoca.CTensor
variable [static : StaticLiterals]
private local instance derivContractInterface : CInterface := cInterface static.addresses

/-- The fused single-run execution of the output-free derivative getter
(`derivFunction shape false`): it delivers the finite tensor derivative into the
caller buffer, preserving every other instance. -/
def DerivExecutionFree (shape : Tensor.Shape) : Prop :=
  ∀ {E} (program : CCalls.Events.Program E) (definitions : CLoops.Calls.Definitions),
    CCalls.Typed.Extends definitions program.internal → Rumoca.CTensor.Lowering.Library definitions →
    definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree →
    ∀ (backing : Heap) (pool : Address) (i : Nat) (oshape : Tensor.Shape)
      (time : Values Tensor.scalar) (state input result : Values shape) (output : Option (Values oshape))
      (buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode),
    count.toNat = shape.volume → shape.volume < 2 ^ 64 →
    program.internal.definitions "fmi3GetContinuousStateDerivatives" = some (.tree (derivFunction shape false)) →
    load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "kind") = some (.integer kind.code) →
    load (TensorInstance.store backing pool i shape oshape time state input output)
      ((TensorInstance.record pool i).member "mode") = some (.integer mode.code) →
    Reference.Allowed .getDerivatives kind mode →
    Finite.Executes (TensorInstanceRhs.kernel shape).derivative (ArrayProfile.environment state input) result →
    Writable (TensorInstance.store backing pool i shape oshape time state input output) buffer shape.volume →
    (∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b) →
    (∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape))
        (TensorInstance.store backing pool i shape oshape time state input output) .done) v →
      CCalls.Events.Resolves program v) →
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName) result ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          backing ((TensorInstance.field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3GetContinuousStateDerivatives"
          (DerivativeCalls.values (some (TensorInstance.record pool i)) (some buffer) count)
          (TensorInstance.store backing pool i shape oshape time state input output) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, written finalHeap buffer result shape.volume⟩

/-- The fused single-run execution of the output-aware derivative getter
(`derivFunction shape true`): it delivers the finite tensor derivative into the
caller buffer and, in addition, writes the dense Jacobian `diag(2*u)` into the
instance's `J` region, preserving every other instance. -/
def DerivExecutionOutput (shape : Tensor.Shape) : Prop :=
  ∀ {E} (program : CCalls.Events.Program E) (definitions : CLoops.Calls.Definitions),
    CCalls.Typed.Extends definitions program.internal → Rumoca.CTensor.Lowering.Library definitions →
    definitions (TensorInstanceRhs.plan shape).derivative.function.name =
      some (TensorInstanceRhs.plan shape).derivative.function.tree →
    definitions SquareDiagonal.function.signature.name = some SquareDiagonal.function →
    ∀ (backing : Heap) (pool : Address) (i : Nat)
      (time : Values Tensor.scalar) (state input result : Values shape)
      (J : Values (Rumoca.Tensor.matrixShape shape.volume shape.volume))
      (buffer : Address) (count : UInt64) (kind : Kind) (mode : Mode),
    count.toNat = shape.volume → shape.volume < 2 ^ 64 →
    (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume < 2 ^ 64 →
    program.internal.definitions "fmi3GetContinuousStateDerivatives" = some (.tree (derivFunction shape true)) →
    load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) ((TensorInstance.record pool i).member "kind") = some (.integer kind.code) →
    load (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) ((TensorInstance.record pool i).member "mode") = some (.integer mode.code) →
    Reference.Allowed .getDerivatives kind mode →
    Finite.Executes (TensorInstanceRhs.kernel shape).derivative (ArrayProfile.environment state input) result →
    Writable (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
      time state input (some J)) buffer shape.volume →
    (∀ a < shape.volume, ∀ b < shape.volume,
      (TensorInstance.field pool i derivativeName).index a ≠ buffer.index b) →
    (∀ a < (Rumoca.Tensor.matrixShape shape.volume shape.volume).volume, ∀ b < shape.volume,
      (TensorInstance.field pool i outputName).index a ≠ buffer.index b) →
    (∀ k : Fin shape.volume,
      Binary64.Adds input[k] input[k] (.finite (SquareDiagonal.doubled input)[k])) →
    (∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (TensorInstanceRhs.plan shape).derivative.function.name
        (Arguments.values (TensorInstanceRhs.plan shape).derivative.function.parameters
          (TensorInstanceRhs.args pool i shape))
        (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
          time state input (some J)) .done) v →
      CCalls.Events.Resolves program v) →
    (∀ (H' : Heap) v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling SquareDiagonal.function.signature.name
        (Diagonal.argumentValues (TensorInstance.field pool i inputName)
          (TensorInstance.field pool i outputName) shape) H' .done) v →
      CCalls.Events.Resolves program v) →
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i derivativeName) result ∧
      Reads finalHeap (TensorInstance.field pool i outputName)
        (Diagonal.matrix (SquareDiagonal.doubled input)) ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) =
          backing ((TensorInstance.field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling "fmi3GetContinuousStateDerivatives"
          (DerivativeCalls.values (some (TensorInstance.record pool i)) (some buffer) count)
          (TensorInstance.store backing pool i shape (Rumoca.Tensor.matrixShape shape.volume shape.volume)
            time state input (some J)) .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, written finalHeap buffer result shape.volume⟩

theorem deriv_execution_free (shape : Tensor.Shape) : DerivExecutionFree shape :=
  fun program definitions linked library found backing pool i oshape time state input result output
      buffer count kind mode matched bounded defined hk hm allowed executed writable separate resolves =>
    deriv_behaviors program shape oshape definitions linked library found backing pool i time state input
      result output buffer count kind mode matched bounded defined hk hm allowed executed writable separate resolves

theorem deriv_execution_output (shape : Tensor.Shape) : DerivExecutionOutput shape :=
  fun program definitions linked library found jacFound backing pool i time state input result J
      buffer count kind mode matched bounded bounded2 defined hk hm allowed executed writable separate
      separateOutput adds resolves jacResolves =>
    deriv_output_behaviors program shape definitions linked library found jacFound backing pool i time state
      input result J buffer count kind mode matched bounded bounded2 defined hk hm allowed executed writable
      separate separateOutput adds resolves jacResolves

/-- The tensor `fmi3GetContinuousStateDerivatives` function contract, parameterized
on whether the prepared problem exposes a dense observation. The fused execution
carries the extra Jacobian conjunct exactly in the output case. -/
structure DerivContract (shape : Tensor.Shape) (hasOutput : Bool) (text : String) : Prop where
  printed : text = (derivFunction shape hasOutput).render
  closed : (derivFunction shape hasOutput).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (derivFunction shape hasOutput)
  rejected : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (buffer : Option Address) (count : UInt64),
    program.internal.definitions "fmi3GetContinuousStateDerivatives" = some (.tree (derivFunction shape hasOutput)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3GetContinuousStateDerivatives" (DerivativeCalls.values none buffer count) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩
  execution : cond hasOutput (DerivExecutionOutput shape) (DerivExecutionFree shape)

theorem deriv_contract (shape : Tensor.Shape) (hasOutput : Bool) :
    DerivContract shape hasOutput (derivFunction shape hasOutput).render where
  printed := rfl
  closed := derivBody_closed shape hasOutput
  denotes := derivFunction_denotes shape hasOutput
  rejected program heap buffer count defined :=
    null_deriv_behaviors program shape hasOutput heap buffer count defined
  execution := by
    cases hasOutput
    · exact deriv_execution_free shape
    · exact deriv_execution_output shape

end

end Rumoca.FMI3.TensorContinuousStates
