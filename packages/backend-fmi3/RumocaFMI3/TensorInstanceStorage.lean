import RumocaC.TensorRegions

/-! Static object storage for one tensor model instance.

The instance record holds the FMI-visible tensors of a prepared
`Solve.TensorFMI3Model shape`: the independent time base, the input tensor `u`,
the state tensor `x`, the state derivative `der(x)`, and, when the prepared
problem exposes a dense output, the output tensor `J`. Each tensor member is a
contiguous array of `double` whose extent is the shape volume, addressed inside
one record of the static instance pool; there is no dynamic allocation. Records
are addressed by an instance index into the pool, so distinct instances occupy
distinct array elements.

This reuses the shared tensor region machinery (`CMemory.TensorRegion`): a
member array is a `place`d range of `float64` cells, distinct members never
alias (`member_separate`), and distinct instances never alias
(`separate_instances`). The addresses stay symbolic in the tensor rank and
extents; no tensor coordinate is enumerated. It specifies valid call-entry
memory, not a native allocator execution. -/
noncomputable section
namespace Rumoca.FMI3.TensorInstance
open Rumoca.Tensor Rumoca.CMemory Rumoca.CMemory.TensorView Rumoca.CMemory.TensorRegion

/-- Member names of the static tensor instance record. -/
def timeName : String := "time"
def stateName : String := "x"
def inputName : String := "u"
def derivativeName : String := "dx"
def outputName : String := "J"

/-- The FMI-visible member names of a tensor instance record. The output member
is present when the prepared problem exposes a dense observation. -/
def fieldNames : List String := [timeName, stateName, inputName, derivativeName, outputName]

/-- Address of instance `i` inside the static pool rooted at `pool`. Distinct
instances are distinct elements of the pool array. -/
def record (pool : Address) (i : Nat) : Address := pool.index i

/-- Address of a named tensor member of instance `i`. -/
def field (pool : Address) (i : Nat) (name : String) : Address := (record pool i).member name

/-- The core instance heap: the time base (a rank-0 double), the state tensor
`x` and input tensor `u` initialized from the supplied values, and the writable
derivative tensor `der(x)`. Every member is a contiguous array of `double`;
extents are the shape volumes. -/
def core (backing : Heap) (pool : Address) (i : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape) : Heap :=
  place (place (place (place backing
    ((record pool i).member timeName) Tensor.scalar true (some time))
    ((record pool i).member stateName) shape true (some state))
    ((record pool i).member inputName) shape false (some input))
    ((record pool i).member derivativeName) shape true none

/-- The full instance heap. The dense output tensor `J` is present exactly when
the prepared problem exposes an observation; its extent is `oshape` (the dense
matrix volume for a diagonal output). -/
def store (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape)
    (output : Option (Values oshape)) : Heap :=
  match output with
  | none => core backing pool i shape time state input
  | some J => place (core backing pool i shape time state input)
      ((record pool i).member outputName) oshape true (some J)

/-! ### Framing member reads and writability through other members -/

/-- A member read survives a `place` on a different member. -/
theorem reads_place_other {shape sh : Shape} {H : Heap} {r : Address} {a b : String}
    {writable : Bool} {init : Option (Values sh)} {values : Values shape}
    (different : b ≠ a) (reads : Reads H (r.member b) values) :
    Reads (place H (r.member a) sh writable init) (r.member b) values := by
  intro i
  have frame := place_other_member H r a b sh writable init different i.val
  simp only [load, frame]
  exact reads i

/-- Writability survives a `place` on a different member. -/
theorem writable_place_other {sh : Shape} {H : Heap} {r : Address} {a b : String} {shape : Shape}
    {writable : Bool} {init : Option (Values sh)}
    (different : b ≠ a) (wr : Writable H (r.member b) shape.volume) :
    Writable (place H (r.member a) sh writable init) (r.member b) shape.volume := by
  intro i hi
  obtain ⟨old, ho⟩ := wr i hi
  exact ⟨old, (place_other_member H r a b sh writable init different i).trans ho⟩

/-! ### The bound tensors are readable and writable in the instance heap -/

theorem core_reads_state (backing : Heap) (pool : Address) (i : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape) :
    Reads (core backing pool i shape time state input) (field pool i stateName) state := by
  unfold core field
  exact reads_place_other (by decide +kernel)
    (reads_place_other (by decide +kernel) (place_reads _ _ _ _))

theorem core_reads_input (backing : Heap) (pool : Address) (i : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape) :
    Reads (core backing pool i shape time state input) (field pool i inputName) input := by
  unfold core field
  exact reads_place_other (by decide +kernel) (place_reads _ _ _ _)

theorem core_writable_derivative (backing : Heap) (pool : Address) (i : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape) :
    Writable (core backing pool i shape time state input) (field pool i derivativeName) shape.volume := by
  unfold core field
  exact place_writable _ _ _ none

theorem reads_state (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (output : Option (Values oshape)) :
    Reads (store backing pool i shape oshape time state input output) (field pool i stateName) state := by
  cases output with
  | none => exact core_reads_state backing pool i shape time state input
  | some J => exact reads_place_other (by decide +kernel) (core_reads_state backing pool i shape time state input)

theorem reads_input (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (output : Option (Values oshape)) :
    Reads (store backing pool i shape oshape time state input output) (field pool i inputName) input := by
  cases output with
  | none => exact core_reads_input backing pool i shape time state input
  | some J => exact reads_place_other (by decide +kernel) (core_reads_input backing pool i shape time state input)

theorem writable_derivative (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (output : Option (Values oshape)) :
    Writable (store backing pool i shape oshape time state input output)
      (field pool i derivativeName) shape.volume := by
  cases output with
  | none => exact core_writable_derivative backing pool i shape time state input
  | some J => exact writable_place_other (by decide +kernel) (core_writable_derivative backing pool i shape time state input)

/-- When the prepared problem exposes a dense output, the output region `J` is a
writable range whose extent is the dense observation volume `oshape`. -/
theorem writable_output (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (J : Values oshape) :
    Writable (store backing pool i shape oshape time state input (some J))
      (field pool i outputName) oshape.volume := by
  show Writable (place (core backing pool i shape time state input)
      ((record pool i).member outputName) oshape true (some J)) ((record pool i).member outputName) oshape.volume
  exact place_writable _ _ _ (some J)

/-! ### Pairwise separation of the instance's tensor regions -/

/-- Distinct tensor members of one instance never share a cell, for arbitrary
ranks, extents and offsets. -/
theorem fields_separate (pool : Address) (i : Nat) (a b : String) (different : a ≠ b) (m n : Nat) :
    (field pool i a).index m ≠ (field pool i b).index n :=
  member_separate (record pool i) a b different m n

/-! ### Separation across instances of the static pool -/

/-- Distinct instances of the pool never share a cell of any tensor member. -/
theorem instances_separate (pool : Address) (i j : Nat) (different : i ≠ j)
    (a b : String) (count : Nat) :
    Separate (field pool i a) (field pool j b) count :=
  separate_instances pool i j different a b count

/-- Preparing instance `i`'s storage leaves every cell of another instance
untouched, even when both are in the same static pool array. -/
theorem core_other_instance (backing : Heap) (pool : Address) (i j : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (b : String) (k : Nat)
    (different : j ≠ i) :
    core backing pool i shape time state input ((field pool j b).index k) =
      backing ((field pool j b).index k) := by
  unfold core field record
  rw [place_other_instance _ _ _ _ _ _ _ _ _ different,
      place_other_instance _ _ _ _ _ _ _ _ _ different,
      place_other_instance _ _ _ _ _ _ _ _ _ different,
      place_other_instance _ _ _ _ _ _ _ _ _ different]

theorem store_other_instance (backing : Heap) (pool : Address) (i j : Nat) (shape oshape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (output : Option (Values oshape))
    (b : String) (k : Nat) (different : j ≠ i) :
    store backing pool i shape oshape time state input output ((field pool j b).index k) =
      backing ((field pool j b).index k) := by
  cases output with
  | none => exact core_other_instance backing pool i j shape time state input b k different
  | some J =>
    show place (core backing pool i shape time state input) ((record pool i).member outputName)
        oshape true (some J) ((field pool j b).index k) = backing ((field pool j b).index k)
    unfold field record
    rw [place_other_instance _ _ _ _ _ _ _ _ _ different]
    exact core_other_instance backing pool i j shape time state input b k different

/-! ### Record profile

The instance record's FMI-visible region set is parameterized by a `Profile`:
whether the read-only input region `u` and the dense output region `J` are
present. The tensor profile carries both; the constant-rate profile (`G01`)
carries neither, storing only the time base, the state vector and its writable
derivative. The generic heaps `coreOpt`/`storeOpt` take the input and output as
options: the current tensor definitions are the both-present instance and the
constant definitions are the both-absent instance, each recovered by `rfl`. -/

/-- Presence of the FMI-visible input and output regions of an instance record. -/
structure Profile where
  hasInput : Bool
  hasOutput : Bool
deriving DecidableEq, Repr

/-- The tensor profile: input `u` present, dense output `J` present. -/
def tensorProfile : Profile := { hasInput := true, hasOutput := true }

/-- The constant-rate profile: no input tensor and no output tensor. -/
def constantProfile : Profile := { hasInput := false, hasOutput := false }

/-- The core instance heap, generic in the presence of the input region. When the
input is present the read-only tensor `u` is placed between the state and the
derivative regions; otherwise it is omitted. The time base, state and writable
derivative are always present. -/
def coreOpt (backing : Heap) (pool : Address) (i : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state : Values shape) (input : Option (Values shape)) : Heap :=
  match input with
  | some u =>
    place (place (place (place backing
      ((record pool i).member timeName) Tensor.scalar true (some time))
      ((record pool i).member stateName) shape true (some state))
      ((record pool i).member inputName) shape false (some u))
      ((record pool i).member derivativeName) shape true none
  | none =>
    place (place (place backing
      ((record pool i).member timeName) Tensor.scalar true (some time))
      ((record pool i).member stateName) shape true (some state))
      ((record pool i).member derivativeName) shape true none

/-- The full instance heap, generic in the input and output regions. -/
def storeOpt (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Shape)
    (time : Values Tensor.scalar) (state : Values shape) (input : Option (Values shape))
    (output : Option (Values oshape)) : Heap :=
  match output with
  | none => coreOpt backing pool i shape time state input
  | some J => place (coreOpt backing pool i shape time state input)
      ((record pool i).member outputName) oshape true (some J)

/-- The tensor profile is the input-present instance of the generic core. -/
theorem core_eq_opt (backing : Heap) (pool : Address) (i : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape) :
    core backing pool i shape time state input
      = coreOpt backing pool i shape time state (some input) := rfl

/-- The tensor profile is the input-present instance of the generic store. -/
theorem store_eq_opt (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Shape)
    (time : Values Tensor.scalar) (state input : Values shape) (output : Option (Values oshape)) :
    store backing pool i shape oshape time state input output
      = storeOpt backing pool i shape oshape time state (some input) output := by
  cases output <;> rfl

/-! ### The constant-rate (no-input, no-output) profile

The constant-rate profile stores only the time base, the state vector and its
writable derivative. Its heap is the input-absent instance of the generic core
and the output-absent instance of the generic store. -/

/-- The constant-rate core instance heap: the time base, the state vector and its
writable derivative, with no input region. -/
def coreNoInput (backing : Heap) (pool : Address) (i : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state : Values shape) : Heap :=
  place (place (place backing
    ((record pool i).member timeName) Tensor.scalar true (some time))
    ((record pool i).member stateName) shape true (some state))
    ((record pool i).member derivativeName) shape true none

/-- The constant-rate core is the input-absent instance of the generic core. -/
theorem coreOpt_none (backing : Heap) (pool : Address) (i : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state : Values shape) :
    coreOpt backing pool i shape time state none = coreNoInput backing pool i shape time state := rfl

/-- The constant-rate instance heap: the constant core, with no output region. -/
def constantStore (backing : Heap) (pool : Address) (i : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state : Values shape) : Heap :=
  coreNoInput backing pool i shape time state

/-- The constant-rate store is the input-absent, output-absent instance of the
generic store. -/
theorem constantStore_eq_opt (backing : Heap) (pool : Address) (i : Nat) (shape oshape : Shape)
    (time : Values Tensor.scalar) (state : Values shape) :
    storeOpt backing pool i shape oshape time state none (none : Option (Values oshape))
      = constantStore backing pool i shape time state := rfl

/-- The constant-rate instance's state region is readable, reading the supplied
initial state. -/
theorem constant_reads_state (backing : Heap) (pool : Address) (i : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state : Values shape) :
    Reads (constantStore backing pool i shape time state) (field pool i stateName) state := by
  unfold constantStore coreNoInput field
  exact reads_place_other (by decide +kernel) (place_reads _ _ _ _)

/-- The constant-rate instance's derivative region is writable. -/
theorem constant_writable_derivative (backing : Heap) (pool : Address) (i : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state : Values shape) :
    Writable (constantStore backing pool i shape time state) (field pool i derivativeName) shape.volume := by
  unfold constantStore coreNoInput field
  exact place_writable _ _ _ none

/-- Distinct tensor members of one constant-rate instance never share a cell. -/
theorem constant_fields_separate (pool : Address) (i : Nat) (a b : String) (different : a ≠ b) (m n : Nat) :
    (field pool i a).index m ≠ (field pool i b).index n :=
  member_separate (record pool i) a b different m n

/-- Distinct constant-rate instances of the pool never share a cell. -/
theorem constant_instances_separate (pool : Address) (i j : Nat) (different : i ≠ j)
    (a b : String) (count : Nat) :
    Separate (field pool i a) (field pool j b) count :=
  separate_instances pool i j different a b count

/-- Preparing constant-rate instance `i`'s storage leaves every cell of another
instance untouched. -/
theorem constant_store_other_instance (backing : Heap) (pool : Address) (i j : Nat) (shape : Shape)
    (time : Values Tensor.scalar) (state : Values shape) (b : String) (k : Nat)
    (different : j ≠ i) :
    constantStore backing pool i shape time state ((field pool j b).index k) =
      backing ((field pool j b).index k) := by
  unfold constantStore coreNoInput field record
  rw [place_other_instance _ _ _ _ _ _ _ _ _ different,
      place_other_instance _ _ _ _ _ _ _ _ _ different,
      place_other_instance _ _ _ _ _ _ _ _ _ different]

end Rumoca.FMI3.TensorInstance
