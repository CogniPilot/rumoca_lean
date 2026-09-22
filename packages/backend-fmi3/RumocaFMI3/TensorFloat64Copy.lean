import RumocaFMI3.Float64Read
import RumocaFMI3.TensorInstanceStorage

/-! Reusable counted copy loops between a staged pointer local and the caller's
Float64 request buffer, in the shared C memory/execution model.

The tensor `fmi3GetFloat64`/`fmi3SetFloat64` bodies stage the address and element
count of the selected instance region into ordinary locals (`src`/`dst` and
`expected`) and then run one counted loop that copies element by element. The
loop bound is the symbolic element count of the region; no tensor coordinate is
enumerated in Lean. These lemmas execute that loop in the actual call scheduler,
preserving any saved caller continuation, so both accessor bodies and every
supported region reuse the same copy proof. -/
noncomputable section
namespace Rumoca.FMI3.TensorFloat64
open CTree CMemory CBody CLoops Float64Calls
open Rumoca.CMemory.TensorView

/-- The indexed source cell `src[k]` read by the getter's copy loop. -/
def srcCell : Expr := .index (Runtime.v "src") (Runtime.v "k")

/-- The indexed destination cell `dst[k]` written by the setter's copy loop. -/
def dstCell : Expr := .index (Runtime.v "dst") (Runtime.v "k")

/-- The getter copy-loop body: `values[k] = src[k];`. -/
def getCopyBody : List Stmt := [.assign output srcCell]

/-- The setter copy-loop body: `dst[k] = values[k];`, writing into the staged
region pointer local `dst`. -/
def setCopyBody : List Stmt := [.assign dstCell output]

theorem getCopyBody_closed : getCopyBody.all noDeclarations = true := by
  simp [getCopyBody, noDeclarations]
theorem setCopyBody_closed : setCopyBody.all noDeclarations = true := by
  simp [setCopyBody, noDeclarations]

section
variable [interface : CInterface]

/-- `src[k]` evaluates to the region cell held at `regionBase.index k`. -/
theorem srcCell_eval (env : Locals) (heap : Heap) (regionBase : Address) (k : Nat)
    (pointer : resolve env "src" = some (.pointer (some regionBase)))
    (counter : resolve env "k" = some (.integer k)) :
    CBody.eval env heap srcCell = load heap (regionBase.index k) := by
  simp [srcCell, Runtime.v, CBody.eval, CBody.evalWith, pointer, counter, Value.address]

/-- `values[k]` addresses the caller buffer cell `buffer.index k`. -/
theorem out_lvalue (env : Locals) (heap : Heap) (buffer : Address) (k : Nat)
    (pointer : resolve env "values" = some (.pointer (some buffer)))
    (counter : resolve env "k" = some (.integer k)) :
    CBody.lvalue env heap output = some (buffer.index k) := by
  simp [output, Runtime.v, CBody.lvalue, CBody.lvalueWith, CBody.evalWith, pointer, counter, Value.address]

/-- `dst[k]` addresses the region cell at `regionBase.index k`. -/
theorem dstCell_lvalue (env : Locals) (heap : Heap) (regionBase : Address) (k : Nat)
    (pointer : resolve env "dst" = some (.pointer (some regionBase)))
    (counter : resolve env "k" = some (.integer k)) :
    CBody.lvalue env heap dstCell = some (regionBase.index k) := by
  simp [dstCell, Runtime.v, CBody.lvalue, CBody.lvalueWith, CBody.evalWith, pointer, counter, Value.address]

/-- One getter iteration reads the region cell and writes the buffer cell. -/
theorem getCopy_step (env : Locals) (types : Types) (heap : Heap) (regionBase buffer : Address)
    (regionValues : Values shape) (i : Fin shape.volume) (old : Option Value) (rest : List Stmt)
    (srcBound : resolve env "src" = some (.pointer (some regionBase)))
    (valuesBound : resolve env "values" = some (.pointer (some buffer)))
    (counter : resolve env "k" = some (.integer i.val))
    (srcRead : load heap (regionBase.index i.val) = some (.finite regionValues[i]))
    (dstStore : heap (buffer.index i.val) = some ⟨.float64, true, old⟩) :
    CLoops.next (.running (getCopyBody ++ rest) env types heap) =
      some (.running rest env types
        (StateProofs.written heap (buffer.index i.val) (Binary64.toBits regionValues[i]).val)) := by
  have address : CBody.lvalue env heap output = some (buffer.index i.val) :=
    out_lvalue env heap buffer i.val valuesBound counter
  have rhs : CLoops.eval env types heap srcCell = some (.finite regionValues[i]) := by
    simpa [CLoops.eval, CLoops.evalWith, CBody.legacyExpressions] using (srcCell_eval env heap regionBase i.val srcBound counter).trans srcRead
  simp only [CLoops.eval, CBody.legacyExpressions] at rhs
  simp only [output] at address
  simp [getCopyBody, output, CLoops.next, CLoops.nextWith, CBody.legacyExpressions, address, rhs, Value.finite,
    store_float64 heap _ old _ dstStore, StateProofs.written]

/-- One setter iteration reads the caller buffer cell and writes the region cell. -/
theorem setCopy_step (env : Locals) (types : Types) (heap : Heap) (regionBase buffer : Address)
    (values : Values shape) (i : Fin shape.volume) (old : Option Value) (rest : List Stmt)
    (dstBound : resolve env "dst" = some (.pointer (some regionBase)))
    (valuesBound : resolve env "values" = some (.pointer (some buffer)))
    (counter : resolve env "k" = some (.integer i.val))
    (bufferRead : load heap (buffer.index i.val) = some (.finite values[i]))
    (regionStore : heap (regionBase.index i.val) = some ⟨.float64, true, old⟩) :
    CLoops.next (.running (setCopyBody ++ rest) env types heap) =
      some (.running rest env types
        (StateProofs.written heap (regionBase.index i.val) (Binary64.toBits values[i]).val)) := by
  have address : CBody.lvalue env heap dstCell = some (regionBase.index i.val) :=
    dstCell_lvalue env heap regionBase i.val dstBound counter
  have rhs : CLoops.eval env types heap output = some (.finite values[i]) := by
    have base : CBody.eval env heap output = load heap (buffer.index i.val) := by
      simp [output, Runtime.v, CBody.eval, CBody.evalWith, valuesBound, counter, Value.address]
    simpa [CLoops.eval, CLoops.evalWith, CBody.legacyExpressions] using base.trans bufferRead
  simp only [CLoops.eval, CBody.legacyExpressions] at rhs
  simp only [dstCell] at address
  simp [setCopyBody, dstCell, CLoops.next, CLoops.nextWith, CBody.legacyExpressions, address, rhs, Value.finite,
    store_float64 heap _ old _ regionStore, StateProofs.written]

end

section
variable [interface : CInterface]

/-- Every getter iteration reads its region cell from the original heap through
the buffer-write frame, and writes the caller buffer cell. Request order is
retained; the caller supplies only the original region/buffer storage. -/
theorem getCopy_reaches (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (regionBase buffer : Address) (regionValues : Values shape)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (bounded : shape.volume < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "expected" = some (.integer shape.volume))
    (srcBound : resolve env "src" = some (.pointer (some regionBase)))
    (valuesBound : resolve env "values" = some (.pointer (some buffer)))
    (readable : Reads heap regionBase regionValues)
    (writable : Writable heap buffer shape.volume)
    (separate : ∀ i < shape.volume, ∀ j < shape.volume, regionBase.index i ≠ buffer.index j) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "expected") getCopyBody :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running rest (counterEnv env "k" shape.volume) types
        (written heap buffer regionValues shape.volume)) resultType stack) := by
  apply CCalls.Events.loop_reaches program "k" (Runtime.v "expected") getCopyBody rest
    (fun _ => env) types (written heap buffer regionValues) shape.volume resultType stack typed bounded
    getCopyBody_closed
  · intro i inside
    simpa [Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, counterEnv, CBody.bind, resolve] using count
  · intro i inside
    obtain ⟨old, storage⟩ := pending_output heap buffer regionValues writable i inside
    have srcRead : load (written heap buffer regionValues i) (regionBase.index i) =
        some (.finite regionValues[(⟨i, inside⟩ : Fin shape.volume)]) := by
      have frame := written_frame heap buffer regionValues i (regionBase.index i)
        (fun j hj => separate i inside j hj)
      have loaded := readable ⟨i, inside⟩
      simp only [load, frame] at loaded ⊢
      exact loaded
    have counter : resolve (counterEnv env "k" i) "k" = some (.integer i) := by
      simp [counterEnv, CBody.bind, resolve]
    have step := getCopy_step (counterEnv env "k" i) types (written heap buffer regionValues i)
      regionBase buffer regionValues ⟨i, inside⟩ old
      (counterStep "k" :: loop "k" (Runtime.v "expected") getCopyBody :: rest)
      (by simpa [counterEnv, CBody.bind, resolve] using srcBound)
      (by simpa [counterEnv, CBody.bind, resolve] using valuesBound)
      counter srcRead storage
    have next : StateProofs.written (written heap buffer regionValues i) (buffer.index i)
        (Binary64.toBits regionValues[(⟨i, inside⟩ : Fin shape.volume)]).val =
          written heap buffer regionValues (i + 1) := by
      simp [written, dif_pos inside, StateProofs.written, Value.finite]
    rw [next] at step
    exact .next (CCalls.Events.body_step program step resultType stack) (.refl _)

/-- Every setter iteration reads its caller buffer cell from the original heap
through the region-write frame, and writes the instance region cell. The staged
region pointer receives exactly the caller's values in order. -/
theorem setCopy_reaches (program : CCalls.Events.Program E) (env : Locals) (types : Types)
    (heap : Heap) (regionBase buffer : Address) (values : Values shape)
    (rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (bounded : shape.volume < 2 ^ 64) (typed : types "k" = some .size)
    (count : resolve env "expected" = some (.integer shape.volume))
    (dstBound : resolve env "dst" = some (.pointer (some regionBase)))
    (valuesBound : resolve env "values" = some (.pointer (some buffer)))
    (readable : Reads heap buffer values)
    (writable : Writable heap regionBase shape.volume)
    (separate : ∀ i < shape.volume, ∀ j < shape.volume, regionBase.index i ≠ buffer.index j) :
    Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
      (.body (.running (loop "k" (Runtime.v "expected") setCopyBody :: rest)
        (counterEnv env "k" 0) types heap) resultType stack)
      (.body (.running rest (counterEnv env "k" shape.volume) types
        (written heap regionBase values shape.volume)) resultType stack) := by
  apply CCalls.Events.loop_reaches program "k" (Runtime.v "expected") setCopyBody rest
    (fun _ => env) types (written heap regionBase values) shape.volume resultType stack typed bounded
    setCopyBody_closed
  · intro i inside
    simpa [Runtime.v, CBody.eval, CBody.evalWith, CDeclaredMembers.memberValue, CDeclaredMembers.arrayAt, CDeclaredMembers.fieldAt, counterEnv, CBody.bind, resolve] using count
  · intro i inside
    obtain ⟨old, storage⟩ := pending_output heap regionBase values writable i inside
    have bufferRead : load (written heap regionBase values i) (buffer.index i) =
        some (.finite values[(⟨i, inside⟩ : Fin shape.volume)]) := by
      have frame := written_frame heap regionBase values i (buffer.index i)
        (fun j hj => (separate j hj i inside).symm)
      have loaded := readable ⟨i, inside⟩
      simp only [load, frame] at loaded ⊢
      exact loaded
    have counter : resolve (counterEnv env "k" i) "k" = some (.integer i) := by
      simp [counterEnv, CBody.bind, resolve]
    have step := setCopy_step (counterEnv env "k" i) types (written heap regionBase values i)
      regionBase buffer values ⟨i, inside⟩ old
      (counterStep "k" :: loop "k" (Runtime.v "expected") setCopyBody :: rest)
      (by simpa [counterEnv, CBody.bind, resolve] using dstBound)
      (by simpa [counterEnv, CBody.bind, resolve] using valuesBound)
      counter bufferRead storage
    have next : StateProofs.written (written heap regionBase values i) (regionBase.index i)
        (Binary64.toBits values[(⟨i, inside⟩ : Fin shape.volume)]).val =
          written heap regionBase values (i + 1) := by
      simp [written, dif_pos inside, StateProofs.written, Value.finite]
    rw [next] at step
    exact .next (CCalls.Events.body_step program step resultType stack) (.refl _)

end
end Rumoca.FMI3.TensorFloat64
