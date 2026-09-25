import RumocaFMI3.TensorSetTime
import RumocaFMI3.TensorStorageCode
import RumocaC.CallPolicyProofs

/-! Tensor `fmi3Reset` body over the static tensor instance record, and the
restore block it shares with the tensor factory, as package-checked products.

The restore block writes every member of an instance record except the handle
members fixed at instantiation (`slot`, `kind`, `environment`, `logger`,
`logging`). It zero-fills every region of the record layout
(`TensorStorage.regions`: the state `x`, the input `u` when present, the
derivative `dx` and the Jacobian `J` when present) in declaration order, one
counted `size_t` loop per region whose bound is the region's symbolic volume, so
no tensor coordinate is enumerated. It then resets the time base and the
bookkeeping cells in the scalar reset's order: `time`, `timeMin`, `eventTime`,
`lastCompleted` and `stop` to zero, `stopDefined` to false, and the lifecycle
`mode` cell to Instantiated. The zero fill is the prepared kernel's
initialization value and every input's declared start value, so a restored record
carries no value from an earlier use of its slot.

The reset body validates the instance handle and lifecycle guard exactly as the
scalar body does (`Runtime.require` with the `reset` command), then runs the
restore block. The factory runs the same block after recording the handle
members, so a reset instance holds exactly the values of a newly instantiated one
(FMI 3.0.2, `fmi3Reset`). Because the mode cell reads Instantiated after reset, a
following `fmi3EnterInitializationMode` is admitted.

The tensor adapter consumes these bodies and proofs. This module alone does
not establish source acceptance or certify an actual artifact; those obligations
belong to the composed adapter/compiler contracts. Every theorem is universal in
the region shapes, the instance address (and, for the framing corollary, the
instance index of the static pool) and the heap. -/
noncomputable section
namespace Rumoca.FMI3.TensorReset
open CTree CMemory CBody CLoops
open Rumoca.CMemory.TensorView
open Rumoca.FMI3.TensorFloat64 (dstCell dstCell_lvalue run_one reject_false declare_step_e)
open Rumoca.FMI3.TensorInstance
open Binary64 (toBits)

/-- The fixed-zero fill of a region: every cell is `+0`. -/
def zeroValues (shape : Tensor.Shape) : Values shape := Tensor.Value.fill shape Binary64.positiveZero

/-- The fill loop body: `dst[k] = 0;`, writing `+0` into the staged region cell.
The integer literal `0` converts to the `+0` binary64 value. -/
def zeroBody : List Stmt := [.assign dstCell (Runtime.n 0)]

theorem zeroBody_closed : zeroBody.all CLoops.noDeclarations = true := by
  simp [zeroBody, dstCell, CLoops.noDeclarations]

/-- An indexed cell of one member is never a scalar member of a different name.
This keeps every scalar cell the restore block writes disjoint from every
zero-filled region without a per-cell separation premise. -/
theorem region_ne_member (p : Address) (region name : String) (h : region ≠ name) (a : Nat) :
    (p.member region).index a ≠ p.member name := by
  intro heq
  exact absurd (congrArg Address.members heq) (by simp [Address.index, Address.member, h])
section
variable [interface : CInterface]

/-- One reset iteration writes `+0` into the region cell `dst[k]`. -/
theorem zeroCopy_step (env : Locals) (types : Types) (heap : Heap) (regionBase : Address) {shape : Tensor.Shape}
    (i : Fin shape.volume) (old : Option Value) (rest : List Stmt)
    (dstBound : resolve env "dst" = some (.pointer (some regionBase)))
    (counter : resolve env "k" = some (.integer i.val))
    (regionStore : heap (regionBase.index i.val) = some ⟨.float64, true, old⟩) :
    CLoops.next (.running (zeroBody ++ rest) env types heap) =
      some (.running rest env types
        (StateProofs.written heap (regionBase.index i.val) (toBits Binary64.positiveZero).val)) := by
  have address : CBody.lvalue env heap dstCell = some (regionBase.index i.val) :=
    dstCell_lvalue env heap regionBase i.val dstBound counter
  have rhs : CLoops.eval env types heap (Runtime.n 0) = some (.integer 0) := by
    simp [Runtime.n, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith]
  simp only [CLoops.eval, CBody.legacyExpressions] at rhs
  simp only [dstCell] at address
  simp [zeroBody, dstCell, CLoops.next, CLoops.nextWith, CBody.legacyExpressions, address, rhs, CMemory.store, regionStore, convert,
    Binary64.exactInteger_zero, Value.finite, StateProofs.written]

/-- One scalar bookkeeping write `m->name = 0;` in the call scheduler, resolving
the instance pointer and storing the integer literal `0` converted to the cell's
type. The result replaces exactly the addressed member cell. This is the single
step reused for the time reset and every lifecycle bookkeeping reset. -/
theorem putZero_step (env : Locals) (types : Types) (heap : Heap) (p : Address) (name : String)
    (result : Value) (t : CType) (old : Option Value) (rest : List Stmt)
    (hne : t ≠ .atomicBoolean)
    (mBound : resolve env "m" = some (.pointer (some p)))
    (cell : heap (p.member name) = some ⟨t, true, old⟩)
    (hconv : convert t (.integer 0) = some result) :
    CLoops.next (.running (Runtime.put name (Runtime.n 0) :: rest) env types heap) =
      some (.running rest env types (replace heap (p.member name) ⟨t, true, some result⟩)) := by
  have hstore : CMemory.store heap (p.member name) (.integer 0) =
      some (replace heap (p.member name) ⟨t, true, some result⟩) :=
    store_of_convert heap (p.member name) old (.integer 0) result t hne cell hconv
  simp [Runtime.put, Runtime.field, Runtime.v, Runtime.n, CLoops.next, CLoops.nextWith, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith,
    CBody.lvalue, CBody.lvalueWith, mBound, Value.address, hstore]

end

section
variable [interface : CInterface]

/-- The reset loop fills the whole region with `+0`, cell by cell, in the call
scheduler. The caller supplies only the original writable region storage. -/
theorem zeroCopy_reaches (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (regionBase : Address) {shape : Tensor.Shape}
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (bounded : shape.volume < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "expected" = some (.integer shape.volume))
    (dstBound : resolve env "dst" = some (.pointer (some regionBase)))
    (writable : Writable heap regionBase shape.volume) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "expected") zeroBody :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running rest (counterEnv env "k" shape.volume) types
        (written heap regionBase (zeroValues shape) shape.volume)) resultType stack) := by
  apply CCalls.Events.loop_reaches program "k" (Runtime.v "expected") zeroBody rest
    (fun _ => env) types (written heap regionBase (zeroValues shape)) shape.volume resultType stack typed
    bounded zeroBody_closed
  · intro i inside
    simpa [Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, counterEnv, CBody.bind, resolve] using count
  · intro i inside
    obtain ⟨old, storage⟩ := Float64Calls.pending_output heap regionBase (zeroValues shape) writable i inside
    have counter : resolve (counterEnv env "k" i) "k" = some (.integer i) := by
      simp [counterEnv, CBody.bind, resolve]
    have step := zeroCopy_step (counterEnv env "k" i) types (written heap regionBase (zeroValues shape) i)
      regionBase ⟨i, inside⟩ old
      (counterStep "k" :: loop "k" (Runtime.v "expected") zeroBody :: rest)
      (by simpa [counterEnv, CBody.bind, resolve] using dstBound) counter storage
    have next : StateProofs.written (written heap regionBase (zeroValues shape) i) (regionBase.index i)
        (toBits Binary64.positiveZero).val = written heap regionBase (zeroValues shape) (i + 1) := by
      simp [written, dif_pos inside, StateProofs.written, Value.finite, zeroValues]
    rw [next] at step
    exact .next (CCalls.Events.body_step program step resultType stack) (.refl _)

end

/-! ### The shared restore block -/

/-- The regions of an instance record, each member name paired with its element
shape, in layout order (`TensorStorage.regions`). -/
abbrev Regions := List (String × Tensor.Shape)

/-- Stage the first region's pointer, element count and counter in fresh locals,
then zero-fill the region. -/
def fillFirst (region : String × Tensor.Shape) : List Stmt := [
  .declare "fmi3Float64 *" "dst" (Runtime.region region.1),
  .declare "size_t" "expected" (Runtime.n region.2.volume),
  .declare "size_t" "k" (Runtime.n 0),
  loop "k" (Runtime.v "expected") zeroBody]

/-- Restage the same locals for a later region, then zero-fill it. -/
def fillNext (region : String × Tensor.Shape) : List Stmt := [
  .assign (Runtime.v "dst") (Runtime.region region.1),
  .assign (Runtime.v "expected") (Runtime.n region.2.volume),
  .assign (Runtime.v "k") (Runtime.n 0),
  loop "k" (Runtime.v "expected") zeroBody]

/-- Zero-fill every region, in order. -/
def fillCode : Regions → List Stmt
  | [] => []
  | region :: rest => fillFirst region ++ rest.flatMap fillNext

/-- The scalar restores after the region fills: the time base and the clock
bookkeeping cells (`timeMin`, `eventTime`, `lastCompleted`, `stop`) become `+0`,
`stopDefined` becomes false and the lifecycle mode becomes Instantiated. -/
def bookkeepingCode : List Stmt := [
  Runtime.put "time" (Runtime.n 0), Runtime.put "timeMin" (Runtime.n 0),
  Runtime.put "eventTime" (Runtime.n 0), Runtime.put "lastCompleted" (Runtime.n 0),
  Runtime.put "stop" (Runtime.n 0), Runtime.put "stopDefined" (Runtime.n 0),
  Runtime.setMode .instantiated]

/-- The restore block shared by the factory and `fmi3Reset`. -/
def restoreCode (regions : Regions) : List Stmt := fillCode regions ++ bookkeepingCode

/-- The scalar members the restore block writes, in order. -/
def restoredScalars : List String :=
  ["time", "timeMin", "eventTime", "lastCompleted", "stop", "stopDefined", "mode"]

/-- The heap after zero-filling every region. -/
def fillHeap (heap : Heap) (p : Address) : Regions → Heap
  | [] => heap
  | region :: rest =>
    fillHeap (written heap (p.member region.1) (zeroValues region.2) region.2.volume) p rest

/-- The scalar restores applied to a post-fill heap `F`, in `bookkeepingCode` order. -/
def bookHeap (F : Heap) (p : Address) : Heap :=
  replace (replace (replace (replace (replace (replace (replace F
    (p.member "time")          ⟨.float64, true, some (.finite Binary64.positiveZero)⟩)
    (p.member "timeMin")       ⟨.float64, true, some (.finite Binary64.positiveZero)⟩)
    (p.member "eventTime")     ⟨.float64, true, some (.finite Binary64.positiveZero)⟩)
    (p.member "lastCompleted") ⟨.float64, true, some (.finite Binary64.positiveZero)⟩)
    (p.member "stop")          ⟨.float64, true, some (.finite Binary64.positiveZero)⟩)
    (p.member "stopDefined")   ⟨.boolean, true, some (boolean false)⟩)
    (p.member "mode")          ⟨.int32, true, some (.integer 0)⟩

/-- The heap after the restore block. -/
def restoreHeap (heap : Heap) (p : Address) (regions : Regions) : Heap :=
  bookHeap (fillHeap heap p regions) p

theorem fillCode_closed (regions : Regions) :
    (fillCode regions).all CBodyEmbedding.closedBlocks = true := by
  cases regions with
  | nil => rfl
  | cons region rest =>
    simp only [fillCode, List.all_append, List.all_flatMap, Bool.and_eq_true, List.all_eq_true]
    refine ⟨by simp [fillFirst, zeroBody, dstCell, Runtime.v, Runtime.n, Runtime.region, Runtime.field,
      CBodyEmbedding.closedBlocks, CLoops.noDeclarations, CLoops.loop, CLoops.counterStep], ?_⟩
    intro _ _
    simp [fillNext, zeroBody, dstCell, Runtime.v, Runtime.n, Runtime.region, Runtime.field,
      CBodyEmbedding.closedBlocks, CLoops.noDeclarations, CLoops.loop, CLoops.counterStep]

theorem restoreCode_closed (regions : Regions) :
    (restoreCode regions).all CBodyEmbedding.closedBlocks = true := by
  simp only [restoreCode, List.all_append, fillCode_closed, Bool.true_and]
  simp [bookkeepingCode, Runtime.put, Runtime.field, Runtime.v, Runtime.n, Runtime.setMode, Runtime.mode,
    CBodyEmbedding.closedBlocks]


open CCallPolicy in
/-- The restore block calls no function, so it satisfies every call policy. -/
theorem restoreCode_admits (permitted : Expr → Prop) (regions : Regions) :
    (∀ stmt ∈ restoreCode regions, StatementAdmits permitted stmt) ↔ True := by
  have none : (restoreCode regions).flatMap statementCalls = [] := by
    cases regions <;>
      simp [restoreCode, fillCode, fillFirst, fillNext, bookkeepingCode, zeroBody, dstCell, statementCalls,
        expressionCalls, Runtime.put, Runtime.field, Runtime.v, Runtime.n, Runtime.region, Runtime.setMode,
        Runtime.mode, CLoops.loop, CLoops.counterStep]
    all_goals
      intro x _ _ _ h
      rcases h with rfl | rfl | rfl | rfl <;> simp [statementCalls, expressionCalls]
  refine ⟨fun _ => trivial, fun _ stmt member => (statement_calls_complete permitted stmt).mp ?_⟩
  intro callee called
  simp [List.flatMap_eq_nil_iff.mp none stmt member] at called
/-! ### Restored values -/

/-- The region fills write only region cells. -/
theorem fillHeap_frame (heap : Heap) (p q : Address) (regions : Regions)
    (outside : ∀ r ∈ regions, ∀ i < r.2.volume, q ≠ (p.member r.1).index i) :
    fillHeap heap p regions q = heap q := by
  induction regions generalizing heap with
  | nil => rfl
  | cons r rest ih =>
    rw [fillHeap, ih _ (fun r' h => outside r' (List.mem_cons_of_mem _ h))]
    exact written_frame heap _ _ _ q (outside r (by simp))

/-- The scalar restores write only the restored scalar members. -/
theorem bookHeap_frame (F : Heap) (p q : Address)
    (outside : ∀ name ∈ restoredScalars, q ≠ p.member name) :
    bookHeap F p q = F q := by
  simp only [restoredScalars, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at outside
  obtain ⟨ht, hn, he, hl, hs, hd, hm⟩ := outside
  simp only [bookHeap, replace_other _ _ _ _ hm, replace_other _ _ _ _ hd, replace_other _ _ _ _ hs,
    replace_other _ _ _ _ hl, replace_other _ _ _ _ he, replace_other _ _ _ _ hn,
    replace_other _ _ _ _ ht]

/-- Every cell of a filled region holds `+0`, whatever it held before. -/
theorem fillHeap_cell (heap : Heap) (p : Address) (regions : Regions)
    (distinct : (regions.map Prod.fst).Nodup) (r : String × Tensor.Shape) (member : r ∈ regions)
    (i : Nat) (inside : i < r.2.volume) :
    fillHeap heap p regions ((p.member r.1).index i) =
      some ⟨.float64, true, some (.finite Binary64.positiveZero)⟩ := by
  induction regions generalizing heap with
  | nil => simp at member
  | cons r0 rest ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at distinct
    rcases List.mem_cons.mp member with rfl | later
    · rw [fillHeap, fillHeap_frame _ p _ rest (fun r' hr' j _ =>
        p.fields_separate r.1 r'.1 (fun same => distinct.1 r' hr' same.symm) i j)]
      have cell := written_at heap (p.member r.1) (zeroValues r.2) r.2.volume (le_refl _) ⟨i, inside⟩
      simpa [inside, zeroValues] using cell
    · rw [fillHeap]
      exact ih _ distinct.2 later

/-- Every cell of a restored region holds `+0`, whatever it held before. -/
theorem restoreHeap_region (heap : Heap) (p : Address) (regions : Regions)
    (distinct : TensorStorage.Distinct regions) (r : String × Tensor.Shape) (member : r ∈ regions)
    (i : Nat) (inside : i < r.2.volume) :
    restoreHeap heap p regions ((p.member r.1).index i) =
      some ⟨.float64, true, some (.finite Binary64.positiveZero)⟩ := by
  rw [restoreHeap, bookHeap_frame _ p _ (fun name named => region_ne_member p r.1 name
    (fun same => distinct.2 r member (by
      simp only [restoredScalars, List.mem_cons, List.not_mem_nil, or_false] at named
      rcases named with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [same] <;>
        decide +kernel)) i)]
  exact fillHeap_cell heap p regions distinct.1 r member i inside

/-- Every restored region reads the fixed-zero fill. -/
theorem restoreHeap_reads (heap : Heap) (p : Address) (regions : Regions)
    (distinct : TensorStorage.Distinct regions) (r : String × Tensor.Shape) (member : r ∈ regions) :
    Reads (restoreHeap heap p regions) (p.member r.1) (zeroValues r.2) := by
  intro i
  simp [load, restoreHeap_region heap p regions distinct r member i.val i.isLt, convert, Value.finite,
    zeroValues]

/-- Every restored scalar cell holds its restored value, whatever it held before. -/
theorem restoreHeap_scalars (heap : Heap) (p : Address) (regions : Regions) :
    restoreHeap heap p regions (p.member "time") = some ⟨.float64, true, some (.finite Binary64.positiveZero)⟩ ∧
    restoreHeap heap p regions (p.member "timeMin") = some ⟨.float64, true, some (.finite Binary64.positiveZero)⟩ ∧
    restoreHeap heap p regions (p.member "eventTime") = some ⟨.float64, true, some (.finite Binary64.positiveZero)⟩ ∧
    restoreHeap heap p regions (p.member "lastCompleted") = some ⟨.float64, true, some (.finite Binary64.positiveZero)⟩ ∧
    restoreHeap heap p regions (p.member "stop") = some ⟨.float64, true, some (.finite Binary64.positiveZero)⟩ ∧
    restoreHeap heap p regions (p.member "stopDefined") = some ⟨.boolean, true, some (boolean false)⟩ ∧
    restoreHeap heap p regions (p.member "mode") = some ⟨.int32, true, some (.integer 0)⟩ := by
  have mne : ∀ a b, a ≠ b → p.member a ≠ p.member b := fun a b h =>
    by simpa using p.fields_separate a b h 0 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [restoreHeap, bookHeap, replace, mne "time" "timeMin", mne "time" "eventTime",
      mne "time" "lastCompleted", mne "time" "stop", mne "time" "stopDefined", mne "time" "mode",
      mne "timeMin" "eventTime", mne "timeMin" "lastCompleted", mne "timeMin" "stop",
      mne "timeMin" "stopDefined", mne "timeMin" "mode", mne "eventTime" "lastCompleted",
      mne "eventTime" "stop", mne "eventTime" "stopDefined", mne "eventTime" "mode",
      mne "lastCompleted" "stop", mne "lastCompleted" "stopDefined", mne "lastCompleted" "mode",
      mne "stop" "stopDefined", mne "stop" "mode", mne "stopDefined" "mode"]

/-- A cell the restore block writes: a cell of a restored region, or a restored
scalar member. -/
def Restored (p : Address) (regions : Regions) (q : Address) : Prop :=
  (∃ r ∈ regions, ∃ i < r.2.volume, q = (p.member r.1).index i) ∨
    ∃ name ∈ restoredScalars, q = p.member name

/-- The restore block determines every cell it writes independently of the heap it
starts from: no restored cell carries a value from an earlier use of the record. -/
theorem restoreHeap_restored (before other : Heap) (p q : Address) (regions : Regions)
    (distinct : TensorStorage.Distinct regions) (restored : Restored p regions q) :
    restoreHeap before p regions q = restoreHeap other p regions q := by
  rcases restored with ⟨r, member, i, inside, rfl⟩ | ⟨name, named, rfl⟩
  · rw [restoreHeap_region before p regions distinct r member i inside,
      restoreHeap_region other p regions distinct r member i inside]
  · have b := restoreHeap_scalars before p regions
    have o := restoreHeap_scalars other p regions
    simp only [restoredScalars, List.mem_cons, List.not_mem_nil, or_false] at named
    rcases named with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact b.1.trans o.1.symm
    · exact b.2.1.trans o.2.1.symm
    · exact b.2.2.1.trans o.2.2.1.symm
    · exact b.2.2.2.1.trans o.2.2.2.1.symm
    · exact b.2.2.2.2.1.trans o.2.2.2.2.1.symm
    · exact b.2.2.2.2.2.1.trans o.2.2.2.2.2.1.symm
    · exact b.2.2.2.2.2.2.trans o.2.2.2.2.2.2.symm

/-- The restore block writes only cells of the record `p`. -/
theorem restoreHeap_frame (heap : Heap) (p q : Address) (regions : Regions)
    (outside : ¬ p.InRecord q) :
    restoreHeap heap p regions q = heap q := by
  have ne (name : String) : q ≠ p.member name := fun h => outside (h ▸ p.member_in_record name)
  rw [restoreHeap, bookHeap_frame _ p q (fun name _ => ne name)]
  exact fillHeap_frame heap p q regions
    (fun r _ i _ h => outside (h ▸ (p.member_in_record r.1).index i))

/-- Region cells stay writable across fills of other regions. -/
theorem written_writable (heap : Heap) (p : Address) (a b : String) (shape : Tensor.Shape)
    (count : Nat) (different : b ≠ a) (writable : Writable heap (p.member b) count) :
    Writable (written heap (p.member a) (zeroValues shape) shape.volume) (p.member b) count := by
  intro i hi
  obtain ⟨old, ho⟩ := writable i hi
  exact ⟨old, (written_frame heap _ _ _ _ (fun j _ => p.fields_separate b a different i j)).trans ho⟩

/-! ### Executing the restore block -/

section
variable [interface : CInterface] (program : CCalls.Events.Program E)

/-- One later region: restage `dst`, `expected` and `k`, then zero-fill it. -/
theorem fillNext_reaches (env : Locals) (types : Types) (heap : Heap) (p : Address)
    (region : String × Tensor.Shape) (rest : List Stmt) (resultType : String)
    (stack : CCalls.Typed.Continuation) (bounded : region.2.volume < 2 ^ 64)
    (mBound : resolve env "m" = some (.pointer (some p)))
    (dstPresent : ∃ v, env "dst" = some v) (expectedPresent : ∃ v, env "expected" = some v)
    (counterPresent : ∃ v, env "k" = some v)
    (dstType : types "dst" = some .pointer) (expectedType : types "expected" = some .size)
    (counterType : types "k" = some .size)
    (writable : Writable heap (p.member region.1) region.2.volume) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (fillNext region ++ rest) env types heap) resultType stack)
      (.body (.running rest
        (counterEnv (CBody.bind (CBody.bind env "dst" (.pointer (some (p.member region.1)))) "expected"
          (.integer region.2.volume)) "k" region.2.volume) types
        (written heap (p.member region.1) (zeroValues region.2) region.2.volume)) resultType stack) := by
  obtain ⟨vd, hd⟩ := dstPresent
  obtain ⟨ve, he⟩ := expectedPresent
  obtain ⟨vk, hk⟩ := counterPresent
  set env1 := CBody.bind env "dst" (.pointer (some (p.member region.1))) with h1
  set env2 := CBody.bind env1 "expected" (.integer region.2.volume) with h2
  have s1 : CLoops.next (.running (fillNext region ++ rest) env types heap) =
      some (.running (.assign (.id "expected") (.nat region.2.volume) ::
        .assign (.id "k") (.nat 0) :: loop "k" (Runtime.v "expected") zeroBody :: rest) env1 types heap) :=
    CLoops.assign_local env types heap "dst" (Runtime.region region.1) _ vd
      (.pointer (some (p.member region.1))) (.pointer (some (p.member region.1))) .pointer hd dstType
      (CBodyEmbedding.eval_refines _ _ _ _ _ (Runtime.eval_region env heap region.1 p mBound))
      (by simp [convert])
  have s2 : CLoops.next (.running (.assign (.id "expected") (.nat region.2.volume) ::
        .assign (.id "k") (.nat 0) :: loop "k" (Runtime.v "expected") zeroBody :: rest) env1 types heap) =
      some (.running (.assign (.id "k") (.nat 0) :: loop "k" (Runtime.v "expected") zeroBody :: rest)
        env2 types heap) :=
    CLoops.assign_local env1 types heap "expected" (.nat region.2.volume) _ ve
      (.integer region.2.volume) (.integer region.2.volume) .size (by simp [h1, CBody.bind, he]) expectedType
      (by simp [CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith])
      (CLoops.convert_size_nat _ bounded)
  have s3 : CLoops.next (.running (.assign (.id "k") (.nat 0) :: loop "k" (Runtime.v "expected") zeroBody :: rest)
        env2 types heap) =
      some (.running (loop "k" (Runtime.v "expected") zeroBody :: rest) (counterEnv env2 "k" 0) types heap) := by
    have step := CLoops.assign_local env2 types heap "k" (.nat 0)
      (loop "k" (Runtime.v "expected") zeroBody :: rest) vk (.integer 0) (.integer 0) .size
      (by simp [h1, h2, CBody.bind, hk]) counterType
      (by simp [CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith])
      (CLoops.convert_size_nat 0 (by decide))
    simpa [counterEnv] using step
  have count : resolve env2 "expected" = some (.integer region.2.volume) := by
    simp [h2, CBody.bind, resolve]
  have dstBound : resolve env2 "dst" = some (.pointer (some (p.member region.1))) := by
    simp [h1, h2, CBody.bind, resolve]
  exact .next (CCalls.Events.body_step program s1 resultType stack)
    (.next (CCalls.Events.body_step program s2 resultType stack)
      (.next (CCalls.Events.body_step program s3 resultType stack)
        (zeroCopy_reaches program env2 types heap (p.member region.1) rest resultType stack bounded
          counterType count dstBound writable)))

/-- The later regions: each is restaged and zero-filled in order. Only the staging
locals change. -/
theorem fillRest_reaches (rest : Regions) (tail : List Stmt) (env : Locals) (types : Types)
    (heap : Heap) (p : Address) (resultType : String) (stack : CCalls.Typed.Continuation)
    (bounded : ∀ r ∈ rest, r.2.volume < 2 ^ 64) (distinct : (rest.map Prod.fst).Nodup)
    (mBound : resolve env "m" = some (.pointer (some p)))
    (dstPresent : ∃ v, env "dst" = some v) (expectedPresent : ∃ v, env "expected" = some v)
    (counterPresent : ∃ v, env "k" = some v)
    (dstType : types "dst" = some .pointer) (expectedType : types "expected" = some .size)
    (counterType : types "k" = some .size)
    (writable : ∀ r ∈ rest, Writable heap (p.member r.1) r.2.volume) :
    ∃ env' : Locals, (∀ name, name ≠ "dst" → name ≠ "expected" → name ≠ "k" → env' name = env name) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (rest.flatMap fillNext ++ tail) env types heap) resultType stack)
        (.body (.running tail env' types (fillHeap heap p rest)) resultType stack) := by
  induction rest generalizing env heap with
  | nil => exact ⟨env, fun _ _ _ _ => rfl, by simpa [fillHeap] using .refl _⟩
  | cons r rs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at distinct
    set env1 := counterEnv (CBody.bind (CBody.bind env "dst" (.pointer (some (p.member r.1)))) "expected"
      (.integer r.2.volume)) "k" r.2.volume with h1
    have first := fillNext_reaches program env types heap p r (rs.flatMap fillNext ++ tail) resultType
      stack (bounded r (by simp)) mBound dstPresent expectedPresent counterPresent dstType expectedType
      counterType (writable r (by simp))
    have frame1 : ∀ name, name ≠ "dst" → name ≠ "expected" → name ≠ "k" → env1 name = env name := by
      intro name a b c
      simp [h1, counterEnv, CBody.bind, a, b, c]
    obtain ⟨env', frame', later⟩ := ih env1
      (written heap (p.member r.1) (zeroValues r.2) r.2.volume)
      (fun r' h => bounded r' (List.mem_cons_of_mem _ h)) distinct.2
      (by simpa [resolve, frame1 "m" (by decide) (by decide) (by decide)] using mBound)
      ⟨.pointer (some (p.member r.1)), by simp [h1, counterEnv, CBody.bind]⟩
      ⟨.integer r.2.volume, by simp [h1, counterEnv, CBody.bind]⟩
      ⟨.integer r.2.volume, by simp [h1, counterEnv, CBody.bind]⟩
      (fun r' h => written_writable heap p r.1 r'.1 r.2 r'.2.volume
        (fun same => distinct.1 r' h same) (writable r' (List.mem_cons_of_mem _ h)))
    refine ⟨env', fun name a b c => (frame' name a b c).trans (frame1 name a b c), ?_⟩
    rw [List.flatMap_cons, List.append_assoc, fillHeap]
    exact first.trans later

/-- Every region is zero-filled in order: the first region declares the staging
locals, every later region restages them. -/
theorem fillCode_reaches (regions : Regions) (tail : List Stmt) (env : Locals) (types : Types)
    (heap : Heap) (p : Address) (resultType : String) (stack : CCalls.Typed.Continuation)
    (bounded : ∀ r ∈ regions, r.2.volume < 2 ^ 64) (distinct : (regions.map Prod.fst).Nodup)
    (mBound : resolve env "m" = some (.pointer (some p)))
    (dstFresh : env "dst" = none) (expectedFresh : env "expected" = none) (counterFresh : env "k" = none)
    (float : interface.types "fmi3Float64 *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (writable : ∀ r ∈ regions, Writable heap (p.member r.1) r.2.volume) :
    ∃ (env' : Locals) (types' : Types),
      (∀ name, name ≠ "dst" → name ≠ "expected" → name ≠ "k" → env' name = env name) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (fillCode regions ++ tail) env types heap) resultType stack)
        (.body (.running tail env' types' (fillHeap heap p regions)) resultType stack) := by
  cases regions with
  | nil => exact ⟨env, types, fun _ _ _ _ => rfl, by simpa [fillCode, fillHeap] using .refl _⟩
  | cons r rs =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at distinct
    set env1 := CBody.bind env "dst" (.pointer (some (p.member r.1))) with h1
    set env2 := CBody.bind env1 "expected" (.integer r.2.volume) with h2
    set types2 := bindType (bindType types "dst" .pointer) "expected" .size with ht2
    have s1 : CLoops.next (.running (fillCode (r :: rs) ++ tail) env types heap) =
        some (.running (.declare "size_t" "expected" (Runtime.n r.2.volume) ::
          .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") zeroBody ::
          (rs.flatMap fillNext ++ tail)) env1 (bindType types "dst" .pointer) heap) := by
      simp only [fillCode, fillFirst, List.cons_append, List.nil_append]
      exact declare_step_e env types heap "fmi3Float64 *" "dst" (Runtime.region r.1) .pointer
        (.pointer (some (p.member r.1))) (.pointer (some (p.member r.1))) _ dstFresh float
        (CBodyEmbedding.eval_refines _ _ _ _ _ (Runtime.eval_region env heap r.1 p mBound))
        (by simp [convert])
    have s2 : CLoops.next (.running (.declare "size_t" "expected" (Runtime.n r.2.volume) ::
          .declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") zeroBody ::
          (rs.flatMap fillNext ++ tail)) env1 (bindType types "dst" .pointer) heap) =
        some (.running (.declare "size_t" "k" (Runtime.n 0) :: loop "k" (Runtime.v "expected") zeroBody ::
          (rs.flatMap fillNext ++ tail)) env2 types2 heap) :=
      declare_step_e env1 _ heap "size_t" "expected" (Runtime.n r.2.volume) .size
        (.integer r.2.volume) (.integer r.2.volume) _ (by simp [h1, CBody.bind, expectedFresh]) size
        (by simp [Runtime.n, CLoops.eval, CLoops.evalWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith])
        (CLoops.convert_size_nat _ (bounded r (by simp)))
    have s3 := CLoops.counter_initialize env2 types2 heap "k"
      (loop "k" (Runtime.v "expected") zeroBody :: (rs.flatMap fillNext ++ tail))
      (by simp [h1, h2, CBody.bind, counterFresh]) size
    have count : resolve env2 "expected" = some (.integer r.2.volume) := by
      simp [h2, CBody.bind, resolve]
    have dstBound : resolve env2 "dst" = some (.pointer (some (p.member r.1))) := by
      simp [h1, h2, CBody.bind, resolve]
    have fill := zeroCopy_reaches program env2 (bindType types2 "k" .size) heap (p.member r.1)
      (rs.flatMap fillNext ++ tail) resultType stack (bounded r (by simp)) (by simp [bindType])
      count dstBound (writable r (by simp))
    set env3 := counterEnv env2 "k" r.2.volume with h3
    have frame3 : ∀ name, name ≠ "dst" → name ≠ "expected" → name ≠ "k" → env3 name = env name := by
      intro name a b c
      simp [h1, h2, h3, counterEnv, CBody.bind, a, b, c]
    obtain ⟨env', frame', later⟩ := fillRest_reaches program rs tail env3 (bindType types2 "k" .size)
      (written heap (p.member r.1) (zeroValues r.2) r.2.volume) p resultType stack
      (fun r' h => bounded r' (List.mem_cons_of_mem _ h)) distinct.2
      (by simpa [resolve, frame3 "m" (by decide) (by decide) (by decide)] using mBound)
      ⟨.pointer (some (p.member r.1)), by simp [h1, h2, h3, counterEnv, CBody.bind]⟩
      ⟨.integer r.2.volume, by simp [h1, h2, h3, counterEnv, CBody.bind]⟩
      ⟨.integer r.2.volume, by simp [h3, counterEnv, CBody.bind]⟩ (by simp [ht2, bindType]) (by simp [ht2, bindType])
      (by simp [bindType])
      (fun r' h => written_writable heap p r.1 r'.1 r.2 r'.2.volume
        (fun same => distinct.1 r' h same) (writable r' (List.mem_cons_of_mem _ h)))
    refine ⟨env', bindType types2 "k" .size, fun name a b c => (frame' name a b c).trans (frame3 name a b c), ?_⟩
    exact .next (CCalls.Events.body_step program s1 resultType stack)
      (.next (CCalls.Events.body_step program s2 resultType stack)
        (.next (CCalls.Events.body_step program s3 resultType stack) (fill.trans later)))

/-- One scalar restore `m->name = 0;` over any heap, for the bookkeeping sequence. -/
theorem bookkeeping_reaches (F : Heap) (p : Address) (env : Locals) (types : Types) (tail : List Stmt)
    (resultType : String) (stack : CCalls.Typed.Continuation)
    (timeOld minOld eventOld completedOld stopOld stopDefinedOld modeOld : Option Value)
    (mBound : resolve env "m" = some (.pointer (some p)))
    (timeCell : F (p.member "time") = some ⟨.float64, true, timeOld⟩)
    (minCell : F (p.member "timeMin") = some ⟨.float64, true, minOld⟩)
    (eventCell : F (p.member "eventTime") = some ⟨.float64, true, eventOld⟩)
    (completedCell : F (p.member "lastCompleted") = some ⟨.float64, true, completedOld⟩)
    (stopCell : F (p.member "stop") = some ⟨.float64, true, stopOld⟩)
    (stopDefinedCell : F (p.member "stopDefined") = some ⟨.boolean, true, stopDefinedOld⟩)
    (modeCell : F (p.member "mode") = some ⟨.int32, true, modeOld⟩) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (bookkeepingCode ++ tail) env types F) resultType stack)
      (.body (.running tail env types (bookHeap F p)) resultType stack) := by
  have hF : convert .float64 (.integer 0) = some (.finite Binary64.positiveZero) := by
    simp [convert, Binary64.exactInteger_zero, Option.map_some]
  have hB : convert .boolean (.integer 0) = some (boolean false) := by decide
  have hI : convert .int32 (.integer 0) = some (.integer 0) := by decide
  simp only [bookkeepingCode, List.cons_append, List.nil_append]
  refine .next (CCalls.Events.body_step program
    (putZero_step env types F p "time" (.finite Binary64.positiveZero) .float64 timeOld _
      (by decide) mBound timeCell hF) resultType stack) ?_
  refine .next (CCalls.Events.body_step program
    (putZero_step env types _ p "timeMin" (.finite Binary64.positiveZero) .float64 minOld _
      (by decide) mBound
      (by rw [replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide)]; exact minCell)
      hF) resultType stack) ?_
  refine .next (CCalls.Events.body_step program
    (putZero_step env types _ p "eventTime" (.finite Binary64.positiveZero) .float64 eventOld _
      (by decide) mBound
      (by rw [replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide)]
          exact eventCell)
      hF) resultType stack) ?_
  refine .next (CCalls.Events.body_step program
    (putZero_step env types _ p "lastCompleted" (.finite Binary64.positiveZero) .float64 completedOld _
      (by decide) mBound
      (by rw [replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide)]
          exact completedCell)
      hF) resultType stack) ?_
  refine .next (CCalls.Events.body_step program
    (putZero_step env types _ p "stop" (.finite Binary64.positiveZero) .float64 stopOld _
      (by decide) mBound
      (by rw [replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide)]
          exact stopCell)
      hF) resultType stack) ?_
  refine .next (CCalls.Events.body_step program
    (putZero_step env types _ p "stopDefined" (boolean false) .boolean stopDefinedOld _
      (by decide) mBound
      (by rw [replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide)]
          exact stopDefinedCell)
      hB) resultType stack) ?_
  refine .next (CCalls.Events.body_step program
    (putZero_step env types _ p "mode" (.integer 0) .int32 modeOld _
      (by decide) mBound
      (by rw [replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide),
             replace_other _ _ _ _ (by simp only [ne_eq, Address.member_inj]; decide)]
          exact modeCell)
      hI) resultType stack) ?_
  exact .refl _

/-- The restore block runs to the restored heap from any heap whose restored cells
are writable. Only the staging locals `dst`, `expected` and `k` change. -/
theorem restore_reaches (regions : Regions) (tail : List Stmt) (env : Locals) (types : Types)
    (heap : Heap) (p : Address) (resultType : String) (stack : CCalls.Typed.Continuation)
    (distinct : TensorStorage.Distinct regions) (bounded : ∀ r ∈ regions, r.2.volume < 2 ^ 64)
    (mBound : resolve env "m" = some (.pointer (some p)))
    (dstFresh : env "dst" = none) (expectedFresh : env "expected" = none) (counterFresh : env "k" = none)
    (float : interface.types "fmi3Float64 *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (writable : ∀ r ∈ regions, Writable heap (p.member r.1) r.2.volume)
    (timeOld minOld eventOld completedOld stopOld stopDefinedOld modeOld : Option Value)
    (timeCell : heap (p.member "time") = some ⟨.float64, true, timeOld⟩)
    (minCell : heap (p.member "timeMin") = some ⟨.float64, true, minOld⟩)
    (eventCell : heap (p.member "eventTime") = some ⟨.float64, true, eventOld⟩)
    (completedCell : heap (p.member "lastCompleted") = some ⟨.float64, true, completedOld⟩)
    (stopCell : heap (p.member "stop") = some ⟨.float64, true, stopOld⟩)
    (stopDefinedCell : heap (p.member "stopDefined") = some ⟨.boolean, true, stopDefinedOld⟩)
    (modeCell : heap (p.member "mode") = some ⟨.int32, true, modeOld⟩) :
    ∃ (env' : Locals) (types' : Types),
      (∀ name, name ≠ "dst" → name ≠ "expected" → name ≠ "k" → env' name = env name) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.body (.running (restoreCode regions ++ tail) env types heap) resultType stack)
        (.body (.running tail env' types' (restoreHeap heap p regions)) resultType stack) := by
  obtain ⟨env', types', frame, fills⟩ := fillCode_reaches program regions (bookkeepingCode ++ tail) env types
    heap p resultType stack bounded distinct.1 mBound dstFresh expectedFresh counterFresh float size writable
  have kept (name : String) (named : name ∈ restoredScalars) :
      fillHeap heap p regions (p.member name) = heap (p.member name) :=
    fillHeap_frame heap p _ regions (fun r member i _ => (region_ne_member p r.1 name
      (fun same => distinct.2 r member (by
        simp only [restoredScalars, List.mem_cons, List.not_mem_nil, or_false] at named
        rcases named with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [same] <;>
          decide +kernel)) i).symm)
  refine ⟨env', types', frame, ?_⟩
  rw [restoreCode, List.append_assoc]
  exact fills.trans (bookkeeping_reaches program (fillHeap heap p regions) p env' types' tail resultType stack
    timeOld minOld eventOld completedOld stopOld stopDefinedOld modeOld
    (by simpa [resolve, frame "m" (by decide) (by decide) (by decide)] using mBound)
    ((kept "time" (by simp [restoredScalars])).trans timeCell)
    ((kept "timeMin" (by simp [restoredScalars])).trans minCell)
    ((kept "eventTime" (by simp [restoredScalars])).trans eventCell)
    ((kept "lastCompleted" (by simp [restoredScalars])).trans completedCell)
    ((kept "stop" (by simp [restoredScalars])).trans stopCell)
    ((kept "stopDefined" (by simp [restoredScalars])).trans stopDefinedCell)
    ((kept "mode" (by simp [restoredScalars])).trans modeCell))

end

/-! ### The reset body -/

def signature : Signature :=
  ⟨"fmi3Status", "fmi3Reset", [⟨"fmi3Instance", "instance", false⟩]⟩

def arguments (handle : Option Address) : List Value := [.pointer handle]

def parameters (handle : Option Address) : Locals := bind (fun _ => none) "instance" (.pointer handle)

def guardEnv (p : Address) : Locals := bind (parameters (some p)) "m" (.pointer (some p))

/-- The guarded reset: the instance and lifecycle guard, the shared restore block,
then `fmi3OK`. -/
def body (regions : Regions) : List Stmt :=
  Runtime.require .reset ++ (restoreCode regions ++ [Runtime.ok])

def function (regions : Regions) : CTree.Function := ⟨signature, body regions, false⟩

theorem body_closed (regions : Regions) :
    (function regions).body.all CBodyEmbedding.closedBlocks = true := by
  simp only [function, body, List.all_append, restoreCode_closed, Bool.true_and]
  simp [Runtime.require, Runtime.instancePrefix, Runtime.modeGuard, Runtime.reject, Runtime.branch,
    Runtime.fail, Runtime.ret, Runtime.ok, Runtime.v, Runtime.call, CBodyEmbedding.closedBlocks,
    CLoops.noDeclarations]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem parameters_bound (handle : Option Address) :
    CCalls.parameters signature.parameters (arguments handle) = some (parameters handle) := rfl

section
variable (program : CCalls.Events.Program E)

/-- The complete reset: it restores every region and every restored scalar member
of the instance record, changing no other cell. -/
theorem reset_reaches (regions : Regions) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (timeOld minOld eventOld completedOld stopOld stopDefinedOld : Option Value)
    (stack : CCalls.Typed.Continuation) (distinct : TensorStorage.Distinct regions)
    (bounded : ∀ r ∈ regions, r.2.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3Reset" = some (.tree (function regions)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (modeStore : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (allowed : Reference.Allowed .reset kind mode)
    (writable : ∀ r ∈ regions, Writable heap (p.member r.1) r.2.volume)
    (timeCell : heap (p.member "time") = some ⟨.float64, true, timeOld⟩)
    (minCell : heap (p.member "timeMin") = some ⟨.float64, true, minOld⟩)
    (eventCell : heap (p.member "eventTime") = some ⟨.float64, true, eventOld⟩)
    (completedCell : heap (p.member "lastCompleted") = some ⟨.float64, true, completedOld⟩)
    (stopCell : heap (p.member "stop") = some ⟨.float64, true, stopOld⟩)
    (stopDefinedCell : heap (p.member "stopDefined") = some ⟨.boolean, true, stopDefinedOld⟩) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.calling "fmi3Reset" (arguments (some p)) heap stack)
      (.returning (.integer 0) (restoreHeap heap p regions) stack) := by
  have hm : load heap (p.member "mode") = some (.integer mode.code) := by
    cases mode <;> simp [load, modeStore, convert, Mode.code]
  have accepted : CBody.run 3 (.running (body regions) (parameters (some p)) heap) =
      some (.running (restoreCode regions ++ [Runtime.ok]) (guardEnv p) heap) := by
    rw [body]
    exact LifecycleGuard.accept (parameters (some p)) heap p .reset kind mode
      (restoreCode regions ++ [Runtime.ok])
      (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm allowed
  obtain ⟨types0, entered⟩ := CCalls.Events.body_prefix_reaches program (function regions)
    (arguments (some p)) (parameters (some p)) (guardEnv p) heap heap
    (restoreCode regions ++ [Runtime.ok]) stack 3 defined
    (parameters_bound _) (body_closed regions) accepted
  obtain ⟨env', types', frame, restored⟩ := restore_reaches program regions [Runtime.ok] (guardEnv p)
    types0 heap p "fmi3Status" stack distinct bounded
    (by simp [guardEnv, CBody.bind, resolve]) (by simp [guardEnv, parameters, CBody.bind])
    (by simp [guardEnv, parameters, CBody.bind]) (by simp [guardEnv, parameters, CBody.bind]) rfl rfl
    writable timeOld minOld eventOld completedOld stopOld stopDefinedOld (some (.integer mode.code))
    timeCell minCell eventCell completedCell stopCell stopDefinedCell modeStore
  have ok : env' "fmi3OK" = none := by
    rw [frame "fmi3OK" (by decide) (by decide) (by decide)]
    simp [guardEnv, parameters, CBody.bind]
  exact entered.trans (restored.trans (DerivativeCalls.finish program _ env' types' stack ok))

theorem reset_behaviors (regions : Regions) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (timeOld minOld eventOld completedOld stopOld stopDefinedOld : Option Value)
    (distinct : TensorStorage.Distinct regions) (bounded : ∀ r ∈ regions, r.2.volume < 2 ^ 64)
    (defined : program.internal.definitions "fmi3Reset" = some (.tree (function regions)))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (modeStore : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (allowed : Reference.Allowed .reset kind mode)
    (writable : ∀ r ∈ regions, Writable heap (p.member r.1) r.2.volume)
    (timeCell : heap (p.member "time") = some ⟨.float64, true, timeOld⟩)
    (minCell : heap (p.member "timeMin") = some ⟨.float64, true, minOld⟩)
    (eventCell : heap (p.member "eventTime") = some ⟨.float64, true, eventOld⟩)
    (completedCell : heap (p.member "lastCompleted") = some ⟨.float64, true, completedOld⟩)
    (stopCell : heap (p.member "stop") = some ⟨.float64, true, stopOld⟩)
    (stopDefinedCell : heap (p.member "stopDefined") = some ⟨.boolean, true, stopDefinedOld⟩)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3Reset" (arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, restoreHeap heap p regions⟩ :=
  (CCalls.Events.internal_prefix program (reset_reaches program regions heap p kind mode
    timeOld minOld eventOld completedOld stopOld stopDefinedOld .done distinct
    bounded defined hk modeStore allowed writable timeCell minCell eventCell completedCell stopCell
    stopDefinedCell)
    (CCalls.Events.return_forced program _ _)).behaviors behavior

theorem null_behaviors (regions : Regions) (heap : Heap)
    (defined : program.internal.definitions "fmi3Reset" = some (.tree (function regions))) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling "fmi3Reset" (arguments none) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩ := by
  apply GuardedCalls.null_behaviors program (function regions)
    (Runtime.modeGuard .reset :: (restoreCode regions ++ [Runtime.ok]))
    (arguments none) (parameters none) heap defined (parameters_bound _)
    (by simp [function, body, Runtime.require, List.append_assoc]) rfl (body_closed regions)
  all_goals simp [parameters, CBody.bind]

end

end

/-- After reset every region of the record reads the fixed-zero fill: the prepared
initialization value of the state and the declared start value of every input,
derivative and output region. -/
theorem reads_initialization (regions : Regions) (distinct : TensorStorage.Distinct regions)
    (heap : Heap) (p : Address) (r : String × Tensor.Shape) (member : r ∈ regions) :
    Reads (restoreHeap heap p regions) (p.member r.1) (zeroValues r.2) :=
  restoreHeap_reads heap p regions distinct r member

/-- After reset the lifecycle `mode` cell reads Instantiated. This is the guard
input a following `fmi3EnterInitializationMode` requires (its permitted mode is
Instantiated), so a reset instance re-initializes exactly as the scalar adapter's
does. -/
theorem reset_mode_instantiated (regions : Regions) (heap : Heap) (p : Address) :
    load (restoreHeap heap p regions) (p.member "mode") = some (.integer Mode.instantiated.code) := by
  simp [load, (restoreHeap_scalars heap p regions).2.2.2.2.2.2, convert, Mode.code]

/-- The prepared IVP initialization program of the admitted kernel evaluates to
the fixed-zero fill that reset restores. -/
theorem initialization_is_zero (shape : Tensor.Shape)
    (ops : Tensor.ScalarOps Binary64.Value) (one : Binary64.Value) :
    (TensorInstanceRhs.kernel shape).problem.initial ops Binary64.positiveZero one =
      zeroValues shape := rfl

/-! ### Framing across instances -/

/-- The successful reset of instance `i` preserves every tensor cell of every
other instance of the static pool. -/
theorem preserves_other_instances (heap : Heap) (pool : Address) (i j : Nat) (regions : Regions)
    (b : String) (k : Nat) (different : j ≠ i) :
    restoreHeap heap (TensorInstance.record pool i) regions ((TensorInstance.field pool j b).index k) =
      heap ((TensorInstance.field pool j b).index k) :=
  restoreHeap_frame heap _ _ regions (fun own => Address.records_separate pool i j (Ne.symm different)
    own (((pool.index j).member_in_record b).index k) rfl)

/-! ### Printed text and denotation -/

section
open CTree.Printer CTree.Syntax

theorem signature_printable : SignaturePrintable RuntimePrinter.typedefs signature := by
  refine ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel, ?_⟩
  intro param member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl
  exact ⟨.named (.typedefName (by decide +kernel) (by decide +kernel)), by decide +kernel⟩


set_option maxHeartbeats 4000000 in
/-- Every statement of the restore block over a record layout prints its intended
C token grammar. -/
theorem restoreCode_printable (shape : Tensor.Shape) (hasInput hasOutput : Bool) :
    ∀ stmt ∈ restoreCode (TensorStorage.regions shape hasInput hasOutput),
      ItemPrintable RuntimePrinter.typedefs stmt := by
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  cases hasInput <;> cases hasOutput <;>
  simp only [restoreCode, fillCode, fillFirst, fillNext, bookkeepingCode,
      TensorStorage.regions, TensorInstance.stateName, TensorInstance.inputName,
      TensorInstance.derivativeName, TensorInstance.outputName, Bool.false_eq_true, ↓reduceIte,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.cons_append,
      zeroBody, dstCell, Runtime.region, Runtime.put, Runtime.field, Runtime.v, Runtime.n,
      Runtime.setMode, Runtime.mode,
      CLoops.loop, CLoops.counterStep,
      List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
      forall_eq] <;>
    repeat first
      | exact fType
      | exact sType
      | apply And.intro
      | apply ItemPrintable.declare
      | apply ItemPrintable.assign
      | apply ItemPrintable.whileLoop
      | apply Printable.binary
      | apply Printable.address
      | apply Printable.field
      | apply Printable.index
      | exact Printable.natural
      | apply Printable.identifier
      | solve | intro stmt impossible; cases impossible
      | decide +kernel
      | simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
          Postfix, FieldBase]
set_option maxHeartbeats 4000000 in
theorem body_printable (shape : Tensor.Shape) (hasInput hasOutput : Bool) :
    ∀ stmt ∈ (function (TensorStorage.regions shape hasInput hasOutput)).body,
      ItemPrintable RuntimePrinter.typedefs stmt := by
  have iType : TypeSpelling RuntimePrinter.typedefs "Instance *" :=
    .pointer (text := "Instance") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have fType : TypeSpelling RuntimePrinter.typedefs "fmi3Float64 *" :=
    .pointer (text := "fmi3Float64") (.named (.typedefName (by decide +kernel) (by decide +kernel)))
  have sType : TypeSpelling RuntimePrinter.typedefs "size_t" :=
    .named (.typedefName (by decide +kernel) (by decide +kernel))
  cases hasInput <;> cases hasOutput <;>
  simp only [function, body, restoreCode, fillCode, fillFirst, fillNext, bookkeepingCode,
      TensorStorage.regions, TensorInstance.stateName, TensorInstance.inputName,
      TensorInstance.derivativeName, TensorInstance.outputName, Bool.false_eq_true, ↓reduceIte,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, List.nil_append, List.cons_append,
      zeroBody, dstCell, Runtime.region, Runtime.require,
      Runtime.instancePrefix,
      Runtime.modeGuard, Runtime.allowedExpression, Runtime.kindModes, permittedModes, Runtime.reject, Runtime.branch,
      Runtime.fail, Runtime.ret, Runtime.ok, Runtime.put, Runtime.field, Runtime.v, Runtime.n,
      Runtime.eqv, Runtime.both, Runtime.negate, Runtime.any, Expr.disjunction, Runtime.setMode, Runtime.mode,
      Runtime.call,
      CLoops.loop, CLoops.counterStep, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, or_imp, forall_and,
      forall_eq] <;>
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
      | apply Printable.dereference
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

theorem function_denotes (shape : Tensor.Shape) (hasInput hasOutput : Bool) :
    FunctionDenotes RuntimePrinter.typedefs (function (TensorStorage.regions shape hasInput hasOutput)).render
      (function (TensorStorage.regions shape hasInput hasOutput)) :=
  CTree.Printer.function_denotes ⟨signature_printable, body_printable shape hasInput hasOutput⟩

end

/-! ### The reset contract -/

section
open CTree.Printer
variable [static : StaticLiterals]
private local instance contractInterface : CInterface := cInterface static.addresses

/-- The tensor `fmi3Reset` function contract over the regions of one record
layout, mirroring the scalar `Reset.FunctionContract` shape. -/
structure Contract (regions : Regions) (text : String) : Prop where
  printed : text = (function regions).render
  closed : (function regions).body.all CBodyEmbedding.closedBlocks = true
  denotes : FunctionDenotes RuntimePrinter.typedefs text (function regions)
  successful : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (kind : Kind) (mode : Mode)
    (timeOld minOld eventOld completedOld stopOld stopDefinedOld : Option Value),
    (∀ r ∈ regions, r.2.volume < 2 ^ 64) →
    program.internal.definitions "fmi3Reset" = some (.tree (function regions)) →
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
    Reference.Allowed .reset kind mode →
    (∀ r ∈ regions, Writable heap (p.member r.1) r.2.volume) →
    heap (p.member "time") = some ⟨.float64, true, timeOld⟩ →
    heap (p.member "timeMin") = some ⟨.float64, true, minOld⟩ →
    heap (p.member "eventTime") = some ⟨.float64, true, eventOld⟩ →
    heap (p.member "lastCompleted") = some ⟨.float64, true, completedOld⟩ →
    heap (p.member "stop") = some ⟨.float64, true, stopOld⟩ →
    heap (p.member "stopDefined") = some ⟨.boolean, true, stopDefinedOld⟩ →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3Reset" (arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, restoreHeap heap p regions⟩
  restores : ∀ heap p, ∀ r ∈ regions, Reads (restoreHeap heap p regions) (p.member r.1) (zeroValues r.2)
  reinitializes : ∀ heap p,
    load (restoreHeap heap p regions) (p.member "mode") = some (.integer Mode.instantiated.code)
  independent : ∀ before other p q, Restored p regions q →
    restoreHeap before p regions q = restoreHeap other p regions q
  null : ∀ {E} (program : CCalls.Events.Program E) (heap : Heap),
    program.internal.definitions "fmi3Reset" = some (.tree (function regions)) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling "fmi3Reset" (arguments none) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem contract (shape : Tensor.Shape) (hasInput hasOutput : Bool) :
    Contract (TensorStorage.regions shape hasInput hasOutput)
      (function (TensorStorage.regions shape hasInput hasOutput)).render where
  printed := rfl
  closed := body_closed _
  denotes := function_denotes shape hasInput hasOutput
  successful program heap p kind mode timeOld minOld eventOld completedOld stopOld stopDefinedOld
      bounded defined hk modeStore allowed writable timeCell minCell eventCell completedCell stopCell
      stopDefinedCell :=
    reset_behaviors program _ heap p kind mode timeOld minOld eventOld completedOld stopOld
      stopDefinedOld (TensorStorage.regions_distinct shape hasInput hasOutput) bounded defined hk
      modeStore allowed writable timeCell minCell eventCell completedCell stopCell stopDefinedCell
  restores heap p r member :=
    reads_initialization _ (TensorStorage.regions_distinct shape hasInput hasOutput) heap p r member
  reinitializes heap p := reset_mode_instantiated _ heap p
  independent before other p q restored :=
    restoreHeap_restored before other p q _ (TensorStorage.regions_distinct shape hasInput hasOutput) restored
  null program heap defined := null_behaviors program _ heap defined

end

end Rumoca.FMI3.TensorReset
