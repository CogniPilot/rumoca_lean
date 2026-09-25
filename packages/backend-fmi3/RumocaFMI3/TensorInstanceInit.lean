import RumocaFMI3.TensorReset
import RumocaFMI3.InstanceInitializationCode
import RumocaC.BodyEvents
import RumocaC.TypedMemory
import RumocaC.Storage
import RumocaC.StorageTransfer

/-! Reserved tensor instance-record initializer over the static tensor pool, as a
package-checked product.

After a slot is reserved and its array element selected, the tensor factory
initializes every member of the reserved record inline. It stores the handle
members (the reserved slot index `m->slot`, the instance `kind`, the captured
environment and logger, the logging flag), then runs the restore block
`TensorReset.restoreCode` that `fmi3Reset` also runs: every region of the record
layout is zero-filled, one counted `size_t` loop per region whose bound is the
region's symbolic volume, and the time base, the event-time and stop-time
bookkeeping, the stop flag and the lifecycle mode are reset. The block ends by
returning the record cast to `fmi3Instance`.

Every member of the record layout is written (`covers`), and every restored cell
is determined independently of the slot's earlier contents, so an instance that
reuses a freed slot starts from the declared start values, exactly like a reset
instance (`reset_matches`). No tensor solver value is initialized here: the
initialization program value of the admitted kernel is the fixed-zero fill
(`FMI3.TensorReset.initialization_is_zero`).

The tensor adapter consumes these bodies and proofs. This module alone does
not establish source acceptance or certify an actual artifact; those obligations
belong to the composed adapter/compiler contracts. Every theorem is universal in
the region shapes, the instance address and the heap. -/
noncomputable section
namespace Rumoca.FMI3.TensorInstanceInit
open CTree CMemory CBody CLoops
open Rumoca.CMemory.TensorView Rumoca.CMemory.TensorRegion
open Rumoca.FMI3.TensorInstance
open Rumoca.FMI3.TensorReset (Regions zeroValues restoreCode restoreHeap Restored restoredScalars)
open Rumoca.FMI3.InstanceInitialization (returnHandle)
open Binary64 (toBits)

/-- The reserved-slot index store: `m->slot = slot`. Its target cell is `size_t`,
so it is handled by a single size-typed store, separately from the concrete
metadata block. -/
def slotStore : Stmt := Runtime.put "slot" (Runtime.v "slot")

/-- The handle members fixed at instantiation after the slot index: the instance
kind, the captured environment and logger, and the logging flag. -/
def metaCode (kind : Kind) : List Stmt := [
  Runtime.put "kind" (Runtime.n kind.code),
  Runtime.put "environment" (Runtime.v "instanceEnvironment"),
  Runtime.put "logger" (Runtime.v "logMessage"),
  Runtime.put "logging" (Runtime.v "loggingOn")]

/-- The handle members the initializer stores and `fmi3Reset` keeps. -/
def handleNames : List String := ["slot", "kind", "environment", "logger", "logging"]

/-- The complete reserved-record initializer: slot store, handle members, the
shared restore block, handle return. Selecting storage
(`InstanceSlot.selectInstance`) is prepended by the factory reservation suffix,
not here. -/
def code (regions : Regions) (kind : Kind) : List Stmt :=
  slotStore :: metaCode kind ++ (restoreCode regions ++ [returnHandle])

/-- Every member of the record layout is written by the initializer: a handle
member, a restored region or a restored scalar. -/
theorem covers (shape : Tensor.Shape) (hasInput hasOutput : Bool) :
    ∀ name ∈ (TensorStorage.membersG shape hasInput hasOutput).map TensorStorage.Member.baseName,
      name ∈ handleNames ∨ name ∈ (TensorStorage.regions shape hasInput hasOutput).map Prod.fst ∨
        name ∈ restoredScalars := by
  rw [TensorStorage.members_names]
  intro name member
  simp only [List.mem_cons, List.mem_append] at member
  rcases member with rfl | inRegions | inBook
  · exact Or.inr (Or.inr (by simp [restoredScalars, TensorInstance.timeName]))
  · exact Or.inr (Or.inl inRegions)
  · simp only [TensorStorage.bookkeepingMembers, TensorStorage.Member.baseName, List.map_cons,
      List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at inBook
    rcases inBook with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [handleNames, restoredScalars]

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

/-- The writable cells of the reserved record: every scalar member and every
region of the layout. Every extent is symbolic in the region shapes. -/
structure Storage (heap : Heap) (p : Address) (regions : Regions) : Prop where
  slot : ∃ old, heap (p.member "slot") = some ⟨.size, true, old⟩
  kind : ∃ old, heap (p.member "kind") = some ⟨.int32, true, old⟩
  mode : ∃ old, heap (p.member "mode") = some ⟨.int32, true, old⟩
  environment : ∃ old, heap (p.member "environment") = some ⟨.pointer, true, old⟩
  logger : ∃ old, heap (p.member "logger") = some ⟨.pointer, true, old⟩
  logging : ∃ old, heap (p.member "logging") = some ⟨.boolean, true, old⟩
  time : ∃ old, heap (p.member "time") = some ⟨.float64, true, old⟩
  timeMin : ∃ old, heap (p.member "timeMin") = some ⟨.float64, true, old⟩
  eventTime : ∃ old, heap (p.member "eventTime") = some ⟨.float64, true, old⟩
  lastCompleted : ∃ old, heap (p.member "lastCompleted") = some ⟨.float64, true, old⟩
  stop : ∃ old, heap (p.member "stop") = some ⟨.float64, true, old⟩
  stopDefined : ∃ old, heap (p.member "stopDefined") = some ⟨.boolean, true, old⟩
  regions : ∀ r ∈ regions, Writable heap (p.member r.1) r.2.volume

/-- The reserved-record storage survives an atomic-scan reservation (or any
storage-preserving execution), so initialization can proceed after reservation. -/
theorem Storage.preserved {before after : Heap} {p : Address} {regions : Regions}
    (storage : Storage before p regions) (preserved : CStorage.Preserves before after) :
    Storage after p regions := by
  obtain ⟨⟨_, hs⟩, ⟨_, hk⟩, ⟨_, hm⟩, ⟨_, hv⟩, ⟨_, hl⟩, ⟨_, hg⟩, ⟨_, ht⟩,
    ⟨_, htm⟩, ⟨_, het⟩, ⟨_, hlc⟩, ⟨_, hst⟩, ⟨_, hsd⟩, hregions⟩ := storage
  refine ⟨preserved.cell hs, preserved.cell hk, preserved.cell hm, preserved.cell hv,
    preserved.cell hl, preserved.cell hg, preserved.cell ht,
    preserved.cell htm, preserved.cell het, preserved.cell hlc, preserved.cell hst, preserved.cell hsd,
    fun r member i hi => ?_⟩
  obtain ⟨_, h⟩ := hregions r member i hi
  exact preserved.cell h

/-! ### The initialized heap -/

/-- The heap after the reserved-slot store. -/
def slotHeap (heap : Heap) (p : Address) (slot : Nat) : Heap :=
  replace heap (p.member "slot") ⟨.size, true, some (.integer slot)⟩

/-- The heap after the handle members: the reserved slot, `kind`, the captured
environment and logger, and the logging flag, over the reserved-record backing. -/
def metaHeap (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) : Heap :=
  replace (replace (replace (replace (slotHeap heap p slot)
    (p.member "kind") ⟨.int32, true, some (.integer kind.code)⟩)
    (p.member "environment") ⟨.pointer, true, some (.pointer environment)⟩)
    (p.member "logger") ⟨.pointer, true, some (.pointer logger)⟩)
    (p.member "logging") ⟨.boolean, true, some (boolean logging)⟩

/-- The heap after the full initializer: the handle members, then the shared
restore block. -/
def finalHeap (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (regions : Regions) : Heap :=
  restoreHeap (metaHeap heap p slot kind environment logger logging) p regions

theorem code_closed (regions : Regions) (kind : Kind) :
    (code regions kind).all CBodyEmbedding.closedBlocks = true := by
  simp only [code, List.all_cons, List.all_append, TensorReset.restoreCode_closed, Bool.true_and]
  cases kind <;>
    simp [slotStore, metaCode, Runtime.put, Runtime.field, Runtime.v, Runtime.n,
      returnHandle, CBodyEmbedding.closedBlocks]

/-- Distinct scalar members of the record never share a cell. -/
theorem member_ne (p : Address) (a b : String) (different : a ≠ b) : p.member a ≠ p.member b := by
  simpa using member_separate p a b different 0 0

/-- The handle stores write only the handle members. -/
theorem metaHeap_frame (heap : Heap) (p q : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool)
    (outside : ∀ name ∈ handleNames, q ≠ p.member name) :
    metaHeap heap p slot kind environment logger logging q = heap q := by
  simp only [handleNames, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at outside
  obtain ⟨hs, hk, he, hl, hg⟩ := outside
  simp only [metaHeap, slotHeap, replace_other _ _ _ _ hg, replace_other _ _ _ _ hl,
    replace_other _ _ _ _ he, replace_other _ _ _ _ hk, replace_other _ _ _ _ hs]

/-- A handle member is neither a region cell nor a restored scalar. -/
theorem handle_not_restored (p : Address) (regions : Regions) (distinct : TensorStorage.Distinct regions)
    (name : String) (handle : name ∈ handleNames) : ¬ Restored p regions (p.member name) := by
  have scalar : name ∈ TensorStorage.scalarNames := by
    simp only [handleNames, List.mem_cons, List.not_mem_nil, or_false] at handle
    rcases handle with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  rintro (⟨r, member, i, _, same⟩ | ⟨other, named, same⟩)
  · exact TensorReset.region_ne_member p r.1 name
      (fun equal => distinct.2 r member (equal ▸ scalar)) i same.symm
  · have equal : name = other := by simpa [Address.member_inj] using same
    subst equal
    simp only [handleNames, List.mem_cons, List.not_mem_nil, or_false] at handle
    simp only [restoredScalars, List.mem_cons, List.not_mem_nil, or_false] at named
    rcases handle with rfl | rfl | rfl | rfl | rfl <;> simp at named

/-! ### Framing outside the record and the initialized values -/

/-- The initializer never touches a cell outside the reserved record. -/
theorem frame (heap : Heap) (p query : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (regions : Regions)
    (outside : ¬ p.InRecord query) :
    finalHeap heap p slot kind environment logger logging regions query = heap query := by
  rw [finalHeap, TensorReset.restoreHeap_frame _ p query regions outside]
  exact metaHeap_frame heap p query slot kind environment logger logging
    (fun name _ h => outside (h ▸ p.member_in_record name))

/-- Preparing instance `i`'s storage leaves every cell of another instance of the
static pool untouched. -/
theorem other_instance (heap : Heap) (base : Address) (i j : Nat) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (regions : Regions) (query : Address)
    (different : i ≠ j) (inside : (base.index j).InRecord query) :
    finalHeap heap (base.index i) slot kind environment logger logging regions query = heap query :=
  frame heap (base.index i) query slot kind environment logger logging regions
    (fun own => Address.records_separate base i j different own inside rfl)

/-- The initialized record exposes the handle members the lifecycle, derivative
and free bodies consume, and the restored value of every other member. -/
structure Initialized (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (regions : Regions) : Prop where
  slotValue : load (finalHeap heap p slot kind environment logger logging regions) (p.member "slot") =
    some (.integer slot)
  kindValue : load (finalHeap heap p slot kind environment logger logging regions) (p.member "kind") =
    some (.integer kind.code)
  modeCell : finalHeap heap p slot kind environment logger logging regions (p.member "mode") =
    some ⟨.int32, true, some (.integer Mode.instantiated.code)⟩
  environmentValue : load (finalHeap heap p slot kind environment logger logging regions)
    (p.member "environment") = some (.pointer environment)
  loggerValue : load (finalHeap heap p slot kind environment logger logging regions)
    (p.member "logger") = some (.pointer logger)
  loggingValue : load (finalHeap heap p slot kind environment logger logging regions)
    (p.member "logging") = some (boolean logging)
  clocks : ∀ name ∈ ["time", "timeMin", "eventTime", "lastCompleted", "stop"],
    load (finalHeap heap p slot kind environment logger logging regions) (p.member name) =
      some (.finite Binary64.positiveZero)
  stopDefinedValue : load (finalHeap heap p slot kind environment logger logging regions)
    (p.member "stopDefined") = some (boolean false)
  regions : ∀ r ∈ regions,
    Reads (finalHeap heap p slot kind environment logger logging regions) (p.member r.1) (zeroValues r.2)

/-- The post-initialization handle cells hold the stored handle values. -/
private theorem final_handle (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (regions : Regions)
    (distinct : TensorStorage.Distinct regions) (name : String) (handle : name ∈ handleNames) :
    finalHeap heap p slot kind environment logger logging regions (p.member name) =
      metaHeap heap p slot kind environment logger logging (p.member name) := by
  have scalar : name ∈ TensorStorage.scalarNames := by
    simp only [handleNames, List.mem_cons, List.not_mem_nil, or_false] at handle
    rcases handle with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have notRestored : name ∉ restoredScalars := by
    simp only [handleNames, List.mem_cons, List.not_mem_nil, or_false] at handle
    rcases handle with rfl | rfl | rfl | rfl | rfl <;> simp [restoredScalars]
  rw [finalHeap, TensorReset.restoreHeap, TensorReset.bookHeap_frame _ p _
      (fun other named same => notRestored (by
        have equal : name = other := by simpa [Address.member_inj] using same
        exact equal ▸ named)),
    TensorReset.fillHeap_frame _ p _ regions (fun r member i _ same =>
      TensorReset.region_ne_member p r.1 name (fun equal => distinct.2 r member (equal ▸ scalar)) i same.symm)]

theorem initialized (heap : Heap) (p : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (regions : Regions)
    (distinct : TensorStorage.Distinct regions) (bounded : slot < 2 ^ 64) :
    Initialized heap p slot kind environment logger logging regions := by
  have mne : ∀ a b, a ≠ b → p.member a ≠ p.member b := fun a b h => member_ne p a b h
  have fm := final_handle heap p slot kind environment logger logging regions distinct
  have scalars := TensorReset.restoreHeap_scalars (metaHeap heap p slot kind environment logger logging) p regions
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r member =>
    TensorReset.restoreHeap_reads _ p regions distinct r member⟩
  · have cell : finalHeap heap p slot kind environment logger logging regions (p.member "slot") =
        some ⟨.size, true, some (.integer slot)⟩ :=
      (fm "slot" (by simp [handleNames])).trans (by
        simp [metaHeap, slotHeap, replace, mne "slot" "logging", mne "slot" "logger",
          mne "slot" "environment", mne "slot" "kind"])
    exact load_converted _ _ .size true (.integer slot) cell (by decide +kernel)
      (CLoops.convert_size_nat slot bounded)
  · have cell : finalHeap heap p slot kind environment logger logging regions (p.member "kind") =
        some ⟨.int32, true, some (.integer kind.code)⟩ :=
      (fm "kind" (by simp [handleNames])).trans (by
        simp [metaHeap, replace, mne "kind" "logging", mne "kind" "logger", mne "kind" "environment"])
    cases kind <;> exact load_converted _ _ .int32 true _ cell (by decide +kernel) (by decide +kernel)
  · simpa [finalHeap, Mode.code] using scalars.2.2.2.2.2.2
  · have cell : finalHeap heap p slot kind environment logger logging regions (p.member "environment") =
        some ⟨.pointer, true, some (.pointer environment)⟩ :=
      (fm "environment" (by simp [handleNames])).trans (by
        simp [metaHeap, replace, mne "environment" "logging", mne "environment" "logger"])
    exact load_converted _ _ .pointer true _ cell (by decide +kernel) (by simp [convert])
  · have cell : finalHeap heap p slot kind environment logger logging regions (p.member "logger") =
        some ⟨.pointer, true, some (.pointer logger)⟩ :=
      (fm "logger" (by simp [handleNames])).trans (by
        simp [metaHeap, replace, mne "logger" "logging"])
    exact load_converted _ _ .pointer true _ cell (by decide +kernel) (by simp [convert])
  · have cell : finalHeap heap p slot kind environment logger logging regions (p.member "logging") =
        some ⟨.boolean, true, some (boolean logging)⟩ :=
      (fm "logging" (by simp [handleNames])).trans (by simp [metaHeap, replace])
    cases logging <;> exact load_converted _ _ .boolean true _ cell (by decide +kernel) (by decide +kernel)
  · intro name named
    simp only [List.mem_cons, List.not_mem_nil, or_false] at named
    rcases named with rfl | rfl | rfl | rfl | rfl <;>
      simp [finalHeap, load, scalars.1, scalars.2.1, scalars.2.2.1, scalars.2.2.2.1, scalars.2.2.2.2.1,
        convert, Value.finite]
  · exact load_converted _ _ .boolean true _ scalars.2.2.2.2.2.1 (by decide +kernel) (by decide +kernel)

/-- A newly created instance and a reset instance agree on every restored cell,
whatever either heap held before: instantiation and `fmi3Reset` restore the
same values. -/
theorem reset_matches (before heap : Heap) (p q : Address) (slot : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (regions : Regions)
    (distinct : TensorStorage.Distinct regions) (restored : Restored p regions q) :
    restoreHeap before p regions q = finalHeap heap p slot kind environment logger logging regions q :=
  TensorReset.restoreHeap_restored _ _ p q regions distinct restored

section
variable [interface : CInterface]

/-- One handle store: evaluate the right-hand value and write a single writable
member cell of the record. -/
theorem put_step (name : String) (rhs : Expr) (env : Locals) (heap : Heap) (p : Address)
    (type : CType) (v out : Value) (old : Option Value) (rest : List Stmt)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (evalRhs : CBody.eval env heap rhs = some v)
    (cell : heap (p.member name) = some ⟨type, true, old⟩)
    (ordinary : type ≠ .atomicBoolean) (conv : convert type v = some out) :
    CBody.next (.running (Runtime.put name rhs :: rest) env heap) =
      some (.running rest env (replace heap (p.member name) ⟨type, true, some out⟩)) := by
  simp [Runtime.put, Runtime.field, Runtime.v, CBody.next, CBody.nextWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.lvalue, CBody.lvalueWith, instanceBound,
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
    (.integer slot) old rest instanceBound (by simp [Runtime.v, CBody.eval, CBody.evalWith, slotBound]) cell (by decide +kernel)
    (CLoops.convert_size_nat slot bounded)

/-- The handle stores run to the handle heap over the slot heap in the bounded body
machine. -/
theorem metaCode_run (regions : Regions) (kind : Kind) (env : Locals) (heap : Heap) (p : Address)
    (slot : Nat) (environment logger : Option Address) (logging : Bool) (rest : List Stmt)
    (storage : Storage heap p regions) (bindings : Bindings env p slot environment logger logging) :
    CBody.run 4 (.running (metaCode kind ++ rest) env (slotHeap heap p slot)) =
      some (.running rest env (metaHeap heap p slot kind environment logger logging)) := by
  obtain ⟨_, ⟨kindOld, hkind⟩, _, ⟨envOld, henv⟩, ⟨logOld, hlog⟩, ⟨lgOld, hlg⟩, _⟩ := storage
  have mne : ∀ a b, a ≠ b → p.member a ≠ p.member b := fun a b h => member_ne p a b h
  cases kind <;> cases logging <;>
    simp [metaCode, Runtime.put, Runtime.field, Runtime.v, Runtime.n, CBody.run, CBody.next, CBody.nextWith, CBody.legacyExpressions,
      CBody.eval, CBody.evalWith, CBody.lvalue, CBody.lvalueWith, bindings.instanceBound, bindings.environmentBound, bindings.loggerBound,
      bindings.loggingBound, Value.address, CMemory.store, convert, boolean, Value.truth,
      slotHeap, replace, metaHeap, Kind.code, hkind, henv, hlog, hlg,
      mne "kind" "slot", mne "environment" "slot",
      mne "environment" "kind", mne "logger" "slot", mne "logger" "kind",
      mne "logger" "environment", mne "logging" "slot", mne "logging" "kind",
      mne "logging" "environment", mne "logging" "logger"]

end

/-! ### The initializer runs to the returned handle in the observable call machine -/

section
variable [interface : CInterface] (program : CCalls.Events.Program E)

/-- The complete reserved-record initializer runs to the initialized heap and
returns the record as an `fmi3Instance` handle, in the observable call machine.
The handle stores run in the bounded body machine and are lifted; the shared
restore block then fills every region and resets every restored scalar. -/
theorem return_reaches (regions : Regions) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (heap : Heap) (p : Address) (slot : Nat) (environment logger : Option Address) (logging : Bool)
    (stack : CCalls.Typed.Continuation) (storage : Storage heap p regions)
    (bindings : Bindings env p slot environment logger logging)
    (distinct : TensorStorage.Distinct regions)
    (bounded : slot < 2 ^ 64) (volumeBounded : ∀ r ∈ regions, r.2.volume < 2 ^ 64)
    (float : interface.types "fmi3Float64 *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (code regions kind) env types heap) "fmi3Instance" stack)
      (.returning (.pointer (some p)) (finalHeap heap p slot kind environment logger logging regions) stack) := by
  set mh := metaHeap heap p slot kind environment logger logging with hmh
  -- Phase A: the slot store and handle stores reach the handle heap.
  have runA : CBody.run 5 (.running (code regions kind) env heap) =
      some (.running (restoreCode regions ++ [returnHandle]) env mh) := by
    rw [code, show (5 : Nat) = 1 + 4 from rfl, CBody.run_add]
    rw [show slotStore :: metaCode kind ++ (restoreCode regions ++ [returnHandle]) =
        slotStore :: (metaCode kind ++ (restoreCode regions ++ [returnHandle])) from rfl, CBody.run,
      slot_step env heap p slot (metaCode kind ++ (restoreCode regions ++ [returnHandle]))
        bindings.instanceBound bindings.slotBound storage.slot bounded]
    simpa using metaCode_run regions kind env heap p slot environment logger logging
      (restoreCode regions ++ [returnHandle]) storage bindings
  obtain ⟨types', executed, _⟩ := CBodyEmbedding.run_refines 5 (.running (code regions kind) env heap)
    (.running (restoreCode regions ++ [returnHandle]) env mh) types (code_closed regions kind) runA
  refine (CCalls.Events.body_reaches program (CLoops.run_reaches executed) "fmi3Instance" stack).trans ?_
  -- Phase B: the shared restore block over the handle heap.
  have keep (name : String) (named : name ∈ restoredScalars) : mh (p.member name) = heap (p.member name) :=
    metaHeap_frame heap p _ slot kind environment logger logging (fun other handle same => by
      have equal : name = other := by simpa [Address.member_inj] using same
      subst equal
      simp only [handleNames, List.mem_cons, List.not_mem_nil, or_false] at handle
      simp only [restoredScalars, List.mem_cons, List.not_mem_nil, or_false] at named
      rcases handle with rfl | rfl | rfl | rfl | rfl <;> simp at named)
  obtain ⟨_, hmode⟩ := storage.mode
  obtain ⟨_, htime⟩ := storage.time
  obtain ⟨_, hmin⟩ := storage.timeMin
  obtain ⟨_, hevent⟩ := storage.eventTime
  obtain ⟨_, hlast⟩ := storage.lastCompleted
  obtain ⟨_, hstop⟩ := storage.stop
  obtain ⟨_, hdefined⟩ := storage.stopDefined
  have writable : ∀ r ∈ regions, Writable mh (p.member r.1) r.2.volume := by
    intro r member i hi
    obtain ⟨old, ho⟩ := storage.regions r member i hi
    refine ⟨old, (metaHeap_frame heap p _ slot kind environment logger logging ?_).trans ho⟩
    intro name handle same
    have scalar : name ∈ TensorStorage.scalarNames := by
      simp only [handleNames, List.mem_cons, List.not_mem_nil, or_false] at handle
      rcases handle with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    exact TensorReset.region_ne_member p r.1 name (fun equal => distinct.2 r member (equal ▸ scalar)) i same
  obtain ⟨envB, typesB, frameB, restored⟩ := TensorReset.restore_reaches program regions [returnHandle] env
    types' mh p "fmi3Instance" stack distinct volumeBounded bindings.instanceBound bindings.dstFresh
    bindings.expectedFresh bindings.counterFresh float size writable _ _ _ _ _ _ _
    ((keep "time" (by simp [restoredScalars])).trans htime)
    ((keep "timeMin" (by simp [restoredScalars])).trans hmin)
    ((keep "eventTime" (by simp [restoredScalars])).trans hevent)
    ((keep "lastCompleted" (by simp [restoredScalars])).trans hlast)
    ((keep "stop" (by simp [restoredScalars])).trans hstop)
    ((keep "stopDefined" (by simp [restoredScalars])).trans hdefined)
    ((keep "mode" (by simp [restoredScalars])).trans hmode)
  refine restored.trans ?_
  -- Return the record cast to `fmi3Instance`.
  have mBoundB : resolve envB "m" = some (.pointer (some p)) := by
    simpa [resolve, frameB "m" (by decide) (by decide) (by decide)] using bindings.instanceBound
  have retStep : CLoops.next (.running [returnHandle] envB typesB
      (finalHeap heap p slot kind environment logger logging regions)) =
      some (.returned ⟨.pointer (some p), finalHeap heap p slot kind environment logger logging regions⟩) := by
    simp [returnHandle, CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.cast, mBoundB, handle, convert]
  refine .next (CCalls.Events.body_step program retStep "fmi3Instance" stack) (.next ?_ (.refl _))
  simp [CCalls.Events.internalNext, CCalls.Events.internalNextWith, CCalls.Typed.nextWithExpressions, CCalls.returnCast, CBody.cast, handle, convert]

/-- The reserved-record initializer terminates returning the initialized handle,
and preserves every existing object cell (it only writes the reserved record's own
cells). This is the successful-creation suffix from the selected-slot body state. -/
theorem complete (regions : Regions) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (heap : Heap) (p : Address) (slot : Nat) (environment logger : Option Address) (logging : Bool)
    (storage : Storage heap p regions) (bindings : Bindings env p slot environment logger logging)
    (distinct : TensorStorage.Distinct regions)
    (bounded : slot < 2 ^ 64) (volumeBounded : ∀ r ∈ regions, r.2.volume < 2 ^ 64)
    (float : interface.types "fmi3Float64 *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (handle : interface.types "fmi3Instance" = some .pointer) :
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.body (.running (code regions kind) env types heap) "fmi3Instance" .done) behavior ↔
      behavior = .terminates [] ⟨.pointer (some p),
        finalHeap heap p slot kind environment logger logging regions⟩) ∧
    CStorage.Preserves heap (finalHeap heap p slot kind environment logger logging regions) := by
  have path := return_reaches program regions kind env types heap p slot environment logger logging .done
    storage bindings distinct bounded volumeBounded float size handle
  exact ⟨(CCalls.Events.internal_prefix program path
    (CCalls.Events.return_forced program (.pointer (some p))
      (finalHeap heap p slot kind environment logger logging regions))).behaviors,
    CStorage.internal_reaches program path⟩

end
end Rumoca.FMI3.TensorInstanceInit
