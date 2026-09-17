import RumocaFMI3.TensorReset
import RumocaFMI3.InstanceInitializationCode
import RumocaC.BodyEvents
import RumocaC.TypedMemory
import RumocaC.Storage
import RumocaC.StorageTransfer

/-! Reserved tensor instance-record initializer over the static tensor pool, as a
package-checked product.

After a slot is reserved and its array element selected, the tensor factory
initializes the reserved record entirely inline: it stores the reserved slot
index `m->slot`, writes the FMI lifecycle metadata (`kind`, mode `Instantiated`,
the captured environment and logger, the logging flag), resets the independent
time base to `+0`, and zero-fills the state region `x` with the same counted
`size_t` loop the tensor reset uses (`FMI3.TensorReset.zeroBody`). The loop bound
is the symbolic state volume, so no tensor coordinate is enumerated. The block
ends by returning the record cast to `fmi3Instance`.

The metadata writes are single-cell stores established by a bounded body run and
lifted into the observable call machine; the state-region fill and the handle
return complete in the same call machine. No tensor solver value is initialized
here: the initialization program value of the admitted kernel is the fixed-zero
fill, which the loop re-establishes (`FMI3.TensorReset.initialization_is_zero`).

This is a package-checked product only: no production artifact is emitted, no CLI
or grammar case is added, and the scalar adapter, `Runtime.lean` and every
existing contract are unchanged. Every theorem is universal in the tensor shape,
the instance address and the heap. -/
noncomputable section
namespace Rumoca.FMI3.TensorInstanceInit
open CTree CMemory CBody CLoops
open Rumoca.CMemory.TensorView Rumoca.CMemory.TensorRegion
open Rumoca.FMI3.TensorFloat64 (declare_step_e)
open Rumoca.FMI3.TensorInstance
open Rumoca.FMI3.TensorReset (zeroValues zeroBody zeroBody_closed zeroCopy_reaches)
open Rumoca.FMI3.InstanceInitialization (returnHandle)
open Binary64 (toBits)

/-- The reserved-slot index store: `m->slot = slot`. Its target cell is `size_t`,
so it is handled by a single size-typed store, separately from the concrete
metadata block. -/
def slotStore : Stmt := Runtime.put "slot" (Runtime.v "slot")

/-- The concrete FMI lifecycle metadata and time base of the reserved record:
`kind`, `mode = Instantiated`, the captured environment and logger, the logging
flag, and the time base at `+0`. Every statement is a single-cell assignment
whose right-hand value is concrete or a captured pointer/flag. -/
def metaCode (kind : Kind) : List Stmt := [
  Runtime.put "kind" (Runtime.n kind.code),
  Runtime.put "mode" (Runtime.n Mode.instantiated.code),
  Runtime.put "environment" (Runtime.v "instanceEnvironment"),
  Runtime.put "logger" (Runtime.v "logMessage"),
  Runtime.put "logging" (Runtime.v "loggingOn"),
  Runtime.put "time" (Runtime.n 0)]

/-- The state-region fill and handle return: stage the region pointer and count,
run the zero-fill loop, then return the record cast to `fmi3Instance`. -/
def stateTail (shape : Tensor.Shape) : List Stmt :=
  .declare "fmi3Float64 *" "dst" (.address (Runtime.field stateName)) ::
  .declare "size_t" "expected" (Runtime.n shape.volume) ::
  .declare "size_t" "k" (Runtime.n 0) ::
  loop "k" (Runtime.v "expected") zeroBody :: [returnHandle]

/-- The complete reserved-record initializer: slot store, metadata, state fill,
handle return. Selecting storage (`InstanceSlot.selectInstance`) is prepended by
the factory reservation suffix, not here. -/
def code (shape : Tensor.Shape) (kind : Kind) : List Stmt :=
  slotStore :: metaCode kind ++ stateTail shape

/-! ### Bindings and storage premises -/

section
variable [interface : CInterface]

/-- The local environment established by the reservation suffix before the
initializer runs. -/
structure Bindings (env : Locals) (p : Address) (slot : Nat)
    (environment logger : Option Address) (logging : Bool) : Prop where
  instanceBound : resolve env "m" = some (.pointer (some p))
  slotBound : resolve env "slot" = some (.integer slot)
  environmentBound : resolve env "instanceEnvironment" = some (.pointer environment)
  loggerBound : resolve env "logMessage" = some (.pointer logger)
  loggingBound : resolve env "loggingOn" = some (boolean logging)
  dstFresh : env "dst" = none
  expectedFresh : env "expected" = none
  counterFresh : env "k" = none

end

/-- The writable cells of the reserved record: the FMI metadata members, the
time base, and the full state region. Every extent is symbolic in the shape. -/
structure Storage (heap : Heap) (p : Address) (shape : Tensor.Shape) : Prop where
  slot : ∃ old, heap (p.member "slot") = some ⟨.size, true, old⟩
  kind : ∃ old, heap (p.member "kind") = some ⟨.int32, true, old⟩
  mode : ∃ old, heap (p.member "mode") = some ⟨.int32, true, old⟩
  environment : ∃ old, heap (p.member "environment") = some ⟨.pointer, true, old⟩
  logger : ∃ old, heap (p.member "logger") = some ⟨.pointer, true, old⟩
  logging : ∃ old, heap (p.member "logging") = some ⟨.boolean, true, old⟩
  time : ∃ old, heap (p.member "time") = some ⟨.float64, true, old⟩
  state : Writable heap (p.member stateName) shape.volume

/-- The reserved-record storage survives an atomic-scan reservation (or any
storage-preserving execution), so initialization can proceed after reservation. -/
theorem Storage.preserved {before after : Heap} {p : Address} {shape : Tensor.Shape}
    (storage : Storage before p shape) (preserved : CStorage.Preserves before after) :
    Storage after p shape := by
  obtain ⟨⟨_, hs⟩, ⟨_, hk⟩, ⟨_, hm⟩, ⟨_, hv⟩, ⟨_, hl⟩, ⟨_, hg⟩, ⟨_, ht⟩, hstate⟩ := storage
  refine ⟨preserved.cell hs, preserved.cell hk, preserved.cell hm, preserved.cell hv,
    preserved.cell hl, preserved.cell hg, preserved.cell ht, fun i hi => ?_⟩
  obtain ⟨_, h⟩ := hstate i hi
  exact preserved.cell h

/-! ### The initialized heap -/

/-- The heap after the reserved-slot store. -/
def slotHeap (heap : Heap) (p : Address) (slot : Nat) : Heap :=
  replace heap (p.member "slot") ⟨.size, true, some (.integer slot)⟩

/-- The heap after the metadata block: the reserved slot, `kind`, mode
`Instantiated`, the captured environment and logger, the logging flag, and the
time base at `+0`, over the reserved-record backing. -/
def metaHeap (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) : Heap :=
  replace (replace (replace (replace (replace (replace (slotHeap heap p slot)
    (p.member "kind") ⟨.int32, true, some (.integer kind.code)⟩)
    (p.member "mode") ⟨.int32, true, some (.integer Mode.instantiated.code)⟩)
    (p.member "environment") ⟨.pointer, true, some (.pointer environment)⟩)
    (p.member "logger") ⟨.pointer, true, some (.pointer logger)⟩)
    (p.member "logging") ⟨.boolean, true, some (boolean logging)⟩)
    (p.member "time") ⟨.float64, true, some (.finite Binary64.positiveZero)⟩

/-- The heap after the full initializer: the metadata heap with the state region
`x` zero-filled. -/
def finalHeap (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape) : Heap :=
  written (metaHeap heap p slot kind environment logger logging) (p.member stateName)
    (zeroValues shape) shape.volume

theorem code_closed (shape : Tensor.Shape) (kind : Kind) :
    (code shape kind).all CBodyEmbedding.closedBlocks = true := by
  cases kind <;>
    simp [code, slotStore, metaCode, stateTail, zeroBody, Runtime.put, Runtime.field, Runtime.v, Runtime.n,
      returnHandle, CLoops.loop, CLoops.counterStep, CLoops.noDeclarations,
      CBodyEmbedding.closedBlocks]

/-- Distinct scalar metadata members of the record never share a cell. -/
theorem member_ne (p : Address) (a b : String) (different : a ≠ b) : p.member a ≠ p.member b := by
  simpa using member_separate p a b different 0 0

theorem state_ne_meta (p : Address) (name : String) (different : name ≠ stateName) (i : Nat) :
    (p.member stateName).index i ≠ p.member name := by
  simpa using member_separate p stateName name (fun h => different h.symm) i 0

/-- The metadata block never touches a state-region cell. -/
theorem metaHeap_state (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (i : Nat) :
    metaHeap heap p slot kind environment logger logging ((p.member stateName).index i) =
      heap ((p.member stateName).index i) := by
  unfold metaHeap slotHeap
  rw [replace_other _ _ _ _ (state_ne_meta p "time" (by decide +kernel) i),
    replace_other _ _ _ _ (state_ne_meta p "logging" (by decide +kernel) i),
    replace_other _ _ _ _ (state_ne_meta p "logger" (by decide +kernel) i),
    replace_other _ _ _ _ (state_ne_meta p "environment" (by decide +kernel) i),
    replace_other _ _ _ _ (state_ne_meta p "mode" (by decide +kernel) i),
    replace_other _ _ _ _ (state_ne_meta p "kind" (by decide +kernel) i),
    replace_other _ _ _ _ (state_ne_meta p "slot" (by decide +kernel) i)]

theorem metaHeap_state_writable (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape)
    (writable : Writable heap (p.member stateName) shape.volume) :
    Writable (metaHeap heap p slot kind environment logger logging) (p.member stateName) shape.volume := by
  intro i hi
  obtain ⟨old, ho⟩ := writable i hi
  exact ⟨old, (metaHeap_state heap p slot kind environment logger logging i).trans ho⟩

/-! ### Framing outside the record and the initialized values -/

/-- The initializer never touches a cell outside the reserved record. -/
theorem frame (heap : Heap) (p query : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape)
    (outside : ¬ p.InRecord query) :
    finalHeap heap p slot kind environment logger logging shape query = heap query := by
  have ne (name : String) : query ≠ p.member name := fun h => outside (h ▸ p.member_in_record name)
  rw [finalHeap, written_frame _ _ _ _ query
    (fun i _ h => outside (h ▸ (p.member_in_record stateName).index i))]
  unfold metaHeap slotHeap
  rw [replace_other _ _ _ _ (ne "time"), replace_other _ _ _ _ (ne "logging"),
    replace_other _ _ _ _ (ne "logger"), replace_other _ _ _ _ (ne "environment"),
    replace_other _ _ _ _ (ne "mode"), replace_other _ _ _ _ (ne "kind"),
    replace_other _ _ _ _ (ne "slot")]

/-- Preparing instance `i`'s storage leaves every cell of another instance of the
static pool untouched. -/
theorem other_instance (heap : Heap) (base : Address) (i j : Nat) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape) (query : Address)
    (different : i ≠ j) (inside : (base.index j).InRecord query) :
    finalHeap heap (base.index i) slot kind environment logger logging shape query = heap query :=
  frame heap (base.index i) query slot kind environment logger logging shape
    (fun own => Address.records_separate base i j different own inside rfl)

/-- The post-initialization state region reads the fixed-zero fill. -/
theorem reads_state (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape) :
    Reads (finalHeap heap p slot kind environment logger logging shape) (p.member stateName)
      (zeroValues shape) := by
  intro i
  have cell := written_at (metaHeap heap p slot kind environment logger logging) (p.member stateName)
    (zeroValues shape) shape.volume (le_refl _) i
  simp only [i.isLt, if_true] at cell
  simp [finalHeap, load, cell, convert, Value.finite]

/-- The initialized record exposes the metadata and state values the tensor
lifecycle, derivative and free bodies consume. -/
structure Initialized (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape) : Prop where
  slotValue : load (finalHeap heap p slot kind environment logger logging shape) (p.member "slot") =
    some (.integer slot)
  kindValue : load (finalHeap heap p slot kind environment logger logging shape) (p.member "kind") =
    some (.integer kind.code)
  modeCell : finalHeap heap p slot kind environment logger logging shape (p.member "mode") =
    some ⟨.int32, true, some (.integer Mode.instantiated.code)⟩
  environmentValue : load (finalHeap heap p slot kind environment logger logging shape)
    (p.member "environment") = some (.pointer environment)
  loggerValue : load (finalHeap heap p slot kind environment logger logging shape)
    (p.member "logger") = some (.pointer logger)
  loggingValue : load (finalHeap heap p slot kind environment logger logging shape)
    (p.member "logging") = some (boolean logging)
  state : Reads (finalHeap heap p slot kind environment logger logging shape) (p.member stateName)
    (zeroValues shape)

/-- Reading a metadata member of the final heap frames past the state fill. -/
private theorem final_meta (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape) (name : String)
    (different : name ≠ stateName) :
    finalHeap heap p slot kind environment logger logging shape (p.member name) =
      metaHeap heap p slot kind environment logger logging (p.member name) := by
  rw [finalHeap, written_frame _ _ _ _ (p.member name)
    (fun i _ => (state_ne_meta p name different i).symm)]

theorem initialized (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (shape : Tensor.Shape)
    (bounded : slot < 2 ^ 64) :
    Initialized heap p slot kind environment logger logging shape := by
  have mne : ∀ a b, a ≠ b → p.member a ≠ p.member b := fun a b h => member_ne p a b h
  have fm : ∀ name, name ≠ stateName →
      finalHeap heap p slot kind environment logger logging shape (p.member name) =
        metaHeap heap p slot kind environment logger logging (p.member name) :=
    fun name diff => final_meta heap p slot kind environment logger logging shape name diff
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, reads_state heap p slot kind environment logger logging shape⟩
  · have cell : finalHeap heap p slot kind environment logger logging shape (p.member "slot") =
        some ⟨.size, true, some (.integer slot)⟩ :=
      (fm "slot" (by decide +kernel)).trans (by
        simp [metaHeap, slotHeap, replace, mne "slot" "time", mne "slot" "logging", mne "slot" "logger",
          mne "slot" "environment", mne "slot" "mode", mne "slot" "kind"])
    exact load_converted _ _ .size true (.integer slot) cell (by decide +kernel)
      (CLoops.convert_size_nat slot bounded)
  · have cell : finalHeap heap p slot kind environment logger logging shape (p.member "kind") =
        some ⟨.int32, true, some (.integer kind.code)⟩ :=
      (fm "kind" (by decide +kernel)).trans (by
        simp [metaHeap, slotHeap, replace, mne "kind" "time", mne "kind" "logging", mne "kind" "logger",
          mne "kind" "environment", mne "kind" "mode"])
    cases kind <;> exact load_converted _ _ .int32 true _ cell (by decide +kernel) (by decide +kernel)
  · rw [fm "mode" (by decide +kernel)]
    simp [metaHeap, slotHeap, replace, mne "mode" "time", mne "mode" "logging", mne "mode" "logger",
      mne "mode" "environment"]
  · have cell : finalHeap heap p slot kind environment logger logging shape (p.member "environment") =
        some ⟨.pointer, true, some (.pointer environment)⟩ :=
      (fm "environment" (by decide +kernel)).trans (by
        simp [metaHeap, slotHeap, replace, mne "environment" "time", mne "environment" "logging",
          mne "environment" "logger"])
    exact load_converted _ _ .pointer true _ cell (by decide +kernel) (by simp [convert])
  · have cell : finalHeap heap p slot kind environment logger logging shape (p.member "logger") =
        some ⟨.pointer, true, some (.pointer logger)⟩ :=
      (fm "logger" (by decide +kernel)).trans (by
        simp [metaHeap, slotHeap, replace, mne "logger" "time", mne "logger" "logging"])
    exact load_converted _ _ .pointer true _ cell (by decide +kernel) (by simp [convert])
  · have cell : finalHeap heap p slot kind environment logger logging shape (p.member "logging") =
        some ⟨.boolean, true, some (boolean logging)⟩ :=
      (fm "logging" (by decide +kernel)).trans (by
        simp [metaHeap, slotHeap, replace, mne "logging" "time"])
    cases logging <;> exact load_converted _ _ .boolean true _ cell (by decide +kernel) (by decide +kernel)


section
variable [interface : CInterface]

/-- One metadata store: evaluate the right-hand value and write a single writable
member cell of the record. -/
theorem put_step (name : String) (rhs : Expr) (env : Locals) (heap : Heap) (p : Address)
    (type : CType) (v out : Value) (old : Option Value) (rest : List Stmt)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (evalRhs : CBody.eval env heap rhs = some v)
    (cell : heap (p.member name) = some ⟨type, true, old⟩)
    (ordinary : type ≠ .atomicBoolean) (conv : convert type v = some out) :
    CBody.next (.running (Runtime.put name rhs :: rest) env heap) =
      some (.running rest env (replace heap (p.member name) ⟨type, true, some out⟩)) := by
  simp [Runtime.put, Runtime.field, Runtime.v, CBody.next, CBody.eval, CBody.lvalue, instanceBound,
    Value.address, evalRhs, store_converted heap (p.member name) type old v out cell ordinary conv]

/-- The reserved-slot store writes the size-typed slot index. -/
theorem slot_step (env : Locals) (heap : Heap) (p : Address) (slot : Nat) (rest : List Stmt)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (slotBound : resolve env "slot" = some (.integer slot))
    (cellStore : ∃ old, heap (p.member "slot") = some ⟨.size, true, old⟩) (bounded : slot < 2 ^ 64) :
    CBody.next (.running (slotStore :: rest) env heap) =
      some (.running rest env (slotHeap heap p slot)) := by
  obtain ⟨old, cell⟩ := cellStore
  simpa [slotStore, slotHeap] using put_step "slot" (Runtime.v "slot") env heap p .size (.integer slot)
    (.integer slot) old rest instanceBound (by simp [Runtime.v, CBody.eval, slotBound]) cell (by decide +kernel)
    (CLoops.convert_size_nat slot bounded)

/-- The concrete metadata block runs to the metadata heap over the slot heap in
the bounded body machine. No `size_t` conversion appears, so the whole block
reduces without evaluating the 64-bit bound. -/
theorem metaCode_run (shape : Tensor.Shape) (kind : Kind) (env : Locals) (heap : Heap) (p : Address)
    (slot : Nat) (environment logger : Option Address) (logging : Bool) (rest : List Stmt)
    (storage : Storage heap p shape) (bindings : Bindings env p slot environment logger logging) :
    CBody.run 6 (.running (metaCode kind ++ rest) env (slotHeap heap p slot)) =
      some (.running rest env (metaHeap heap p slot kind environment logger logging)) := by
  obtain ⟨_, ⟨kindOld, hkind⟩, ⟨modeOld, hmode⟩, ⟨envOld, henv⟩,
    ⟨logOld, hlog⟩, ⟨lgOld, hlg⟩, ⟨timeOld, htime⟩, _⟩ := storage
  have mne : ∀ a b, a ≠ b → p.member a ≠ p.member b := fun a b h => member_ne p a b h
  cases kind <;> cases logging <;>
    simp [metaCode, Runtime.put, Runtime.field, Runtime.v, Runtime.n, CBody.run, CBody.next,
      CBody.eval, CBody.lvalue, bindings.instanceBound, bindings.environmentBound, bindings.loggerBound,
      bindings.loggingBound, Value.address, Value.finite, CMemory.store, convert, boolean, Value.truth,
      slotHeap, replace, metaHeap, Mode.code, Kind.code, hkind, hmode, henv, hlog, hlg, htime,
      mne "kind" "slot", mne "mode" "slot", mne "mode" "kind", mne "environment" "slot",
      mne "environment" "kind", mne "environment" "mode", mne "logger" "slot", mne "logger" "kind",
      mne "logger" "mode", mne "logger" "environment", mne "logging" "slot", mne "logging" "kind",
      mne "logging" "mode", mne "logging" "environment", mne "logging" "logger", mne "time" "slot",
      mne "time" "kind", mne "time" "mode", mne "time" "environment", mne "time" "logger",
      mne "time" "logging"]

end

/-! ### The initializer runs to the returned handle in the observable call machine -/

section
variable [interface : CInterface] (program : CCalls.Events.Program E)

/-- The complete reserved-record initializer runs to the initialized heap and
returns the record as an `fmi3Instance` handle, in the observable call machine.
The metadata block runs in the bounded body machine and is lifted; the state
region is zero-filled by the same loop the tensor reset uses. -/
theorem return_reaches (shape : Tensor.Shape) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (heap : Heap) (p : Address) (slot : Nat) (environment logger : Option Address) (logging : Bool)
    (stack : CCalls.Typed.Continuation) (storage : Storage heap p shape)
    (bindings : Bindings env p slot environment logger logging)
    (bounded : slot < 2 ^ 64) (volumeBounded : shape.volume < 2 ^ 64)
    (float : interface.types "fmi3Float64 *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (code shape kind) env types heap) "fmi3Instance" stack)
      (.returning (.pointer (some p)) (finalHeap heap p slot kind environment logger logging shape) stack) := by
  set mh := metaHeap heap p slot kind environment logger logging with hmh
  -- Phase A: the slot store and metadata block reach the metadata heap.
  have runA : CBody.run 7 (.running (code shape kind) env heap) =
      some (.running (stateTail shape) env mh) := by
    rw [code, show (7 : Nat) = 1 + 6 from rfl, CBody.run_add]
    rw [show slotStore :: metaCode kind ++ stateTail shape =
        slotStore :: (metaCode kind ++ stateTail shape) from rfl, CBody.run,
      slot_step env heap p slot (metaCode kind ++ stateTail shape) bindings.instanceBound
        bindings.slotBound storage.slot bounded]
    simpa using metaCode_run shape kind env heap p slot environment logger logging (stateTail shape)
      storage bindings
  obtain ⟨types', executed, _⟩ := CBodyEmbedding.run_refines 7 (.running (code shape kind) env heap)
    (.running (stateTail shape) env mh) types (code_closed shape kind) runA
  refine (CCalls.Events.body_reaches program (CLoops.run_reaches executed) "fmi3Instance" stack).trans ?_
  -- Phase B: stage the region pointer and count, run the fill loop, return the handle.
  have mBound : resolve env "m" = some (.pointer (some p)) := bindings.instanceBound
  set stagedEnv := CBody.bind (CBody.bind env "dst" (.pointer (some (p.member stateName)))) "expected"
    (.integer shape.volume) with hstaged
  set stagedTypes := CLoops.bindType (CLoops.bindType types' "dst" .pointer) "expected" .size with hstyp
  have s_dst : CLoops.next (.running (stateTail shape) env types' mh) =
      some (.running (.declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") zeroBody :: [returnHandle])
        (CBody.bind env "dst" (.pointer (some (p.member stateName)))) (CLoops.bindType types' "dst" .pointer) mh) :=
    declare_step_e env types' mh "fmi3Float64 *" "dst" (.address (Runtime.field stateName)) .pointer
      (.pointer (some (p.member stateName))) (.pointer (some (p.member stateName))) _ bindings.dstFresh float
      (by apply CBodyEmbedding.eval_refines
          simp [Runtime.field, Runtime.v, CBody.eval, CBody.lvalue, mBound, Value.address]) rfl
  have s_exp : CLoops.next (.running (.declare "size_t" "expected" (Runtime.n shape.volume) ::
        .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") zeroBody :: [returnHandle])
        (CBody.bind env "dst" (.pointer (some (p.member stateName)))) (CLoops.bindType types' "dst" .pointer) mh) =
      some (.running (.declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") zeroBody :: [returnHandle])
        stagedEnv stagedTypes mh) :=
    declare_step_e _ _ mh "size_t" "expected" (Runtime.n shape.volume) .size (.integer shape.volume)
      (.integer shape.volume) _ bindings.expectedFresh size (by simp [Runtime.n, CLoops.eval, CBody.eval])
      (CLoops.convert_size_nat _ volumeBounded)
  refine .next (CCalls.Events.body_step program s_dst "fmi3Instance" stack)
    (.next (CCalls.Events.body_step program s_exp "fmi3Instance" stack) ?_)
  have fresh_k : stagedEnv "k" = none := by
    simp [hstaged, CBody.bind, bindings.counterFresh]
  have expBound : resolve stagedEnv "expected" = some (.integer shape.volume) := by
    simp [hstaged, CBody.bind, CBody.resolve]
  have dstBound : resolve stagedEnv "dst" = some (.pointer (some (p.member stateName))) := by
    simp [hstaged, CBody.bind, CBody.resolve]
  have writable : Writable mh (p.member stateName) shape.volume :=
    metaHeap_state_writable heap p slot kind environment logger logging shape storage.state
  refine .next (CCalls.Events.body_step program
    (CLoops.counter_initialize stagedEnv stagedTypes mh "k"
      (loop "k" (Runtime.v "expected") zeroBody :: [returnHandle]) fresh_k size) _ stack) ?_
  refine (zeroCopy_reaches program stagedEnv (CLoops.bindType stagedTypes "k" .size) mh
    (p.member stateName) [returnHandle] "fmi3Instance" stack volumeBounded (by simp [CLoops.bindType])
    expBound dstBound writable).trans ?_
  -- Return the record cast to `fmi3Instance`.
  set envK := counterEnv stagedEnv "k" shape.volume with henvK
  have mBoundK : resolve envK "m" = some (.pointer (some p)) := by
    simpa [henvK, counterEnv, CBody.bind, resolve, hstaged] using mBound
  have retStep : CLoops.next (.running [returnHandle] envK (CLoops.bindType stagedTypes "k" .size)
      (finalHeap heap p slot kind environment logger logging shape)) =
      some (.returned ⟨.pointer (some p), finalHeap heap p slot kind environment logger logging shape⟩) := by
    simp [returnHandle, CLoops.next, CLoops.eval, CBody.eval, CBody.cast, mBoundK, handle, convert]
  refine .next (CCalls.Events.body_step program retStep "fmi3Instance" stack) (.next ?_ (.refl _))
  simp [CCalls.Events.internalNext, CCalls.Typed.nextWith, CCalls.returnCast, CBody.cast, handle, convert]

/-- The reserved-record initializer terminates returning the initialized handle,
and preserves every existing object cell (it only writes the reserved record's own
cells). This is the successful-creation suffix from the selected-slot body state. -/
theorem complete (shape : Tensor.Shape) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (heap : Heap) (p : Address) (slot : Nat) (environment logger : Option Address) (logging : Bool)
    (storage : Storage heap p shape) (bindings : Bindings env p slot environment logger logging)
    (bounded : slot < 2 ^ 64) (volumeBounded : shape.volume < 2 ^ 64)
    (float : interface.types "fmi3Float64 *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.body (.running (code shape kind) env types heap) "fmi3Instance" .done) behavior ↔
      behavior = .terminates [] ⟨.pointer (some p),
        finalHeap heap p slot kind environment logger logging shape⟩) ∧
    CStorage.Preserves heap (finalHeap heap p slot kind environment logger logging shape) := by
  have path := return_reaches program shape kind env types heap p slot environment logger logging .done
    storage bindings bounded volumeBounded float size handle
  exact ⟨(CCalls.Events.internal_prefix program path
    (CCalls.Events.return_forced program (.pointer (some p))
      (finalHeap heap p slot kind environment logger logging shape))).behaviors,
    CStorage.internal_reaches program path⟩

end
end Rumoca.FMI3.TensorInstanceInit
