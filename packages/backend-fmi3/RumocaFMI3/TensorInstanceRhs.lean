import RumocaFMI3.TensorInstanceStorage
import RumocaFMI3.TensorModelRhs
import RumocaCore.Array.Solve
import RumocaCore.Array.Lowering
import RumocaCore.Solve.TensorFMI3

/-! The prepared tensor model right-hand side bound to static instance storage.

The admitted development kernel (`TensorSquare`: `der(x) = u .* u`) is deployed
into the static tensor instance record of `TensorInstance`. The derivative
entry's parameters and result are pointed at the instance's `x` and `u`
(inputs) and `dx` (`der(x)`, output) regions. A well-formed instance heap then
satisfies the tensor derivative entry's `Arguments.Valid`, `LayoutBound`,
`Represents` and `Ready` predicates, so `FMI3.TensorModelRhs.behaviors` applies.

The resulting theorem is universal in the tensor shape and the instance index of
the static pool: running the derivative entry on an instance writes the finite
tensor derivative into that instance's `der(x)` region and preserves every other
cell, including every tensor cell of every other instance in the pool. This is a
package-checked product; it emits no production artifact, adds no CLI or grammar
case, and changes no existing contract or the scalar adapter. -/
noncomputable section
namespace Rumoca.FMI3.TensorInstanceRhs
open CTree CMemory CMemory.TensorView Solve.Tensor Rumoca.CTensor.Lowering Rumoca.Tensor

/-- The admitted `TensorSquare` kernel: fixed-zero initialization and the
pointwise RHS `der(x) = u .* u`. The dense Jacobian observation is deferred for
this storage increment, so `diagonal` is `none`. -/
def kernel (shape : Shape) : Solve.PointwiseIVP shape :=
  ⟨fill shape .zero, ArrayProfile.squareProgram shape, none⟩

/-- The prepared tensor FMI 3 model for the admitted kernel. -/
def model (shape : Shape) : Solve.TensorFMI3Model shape := ⟨"TensorSquare", kernel shape⟩

/-- A named C buffer of the instance record, addressed by a member name and the
element-count parameter. -/
def namedBuffer (shape : Shape) (name : String) : Named.Buffer shape := ⟨name, "count"⟩

def initialParameters : List Syntax.Parameter :=
  [⟨.output, TensorInstance.stateName⟩, ⟨.count, "count"⟩]

def derivativeParameters : List Syntax.Parameter :=
  [⟨.input, TensorInstance.stateName⟩, ⟨.input, TensorInstance.inputName⟩,
    ⟨.output, TensorInstance.derivativeName⟩, ⟨.count, "count"⟩]

/-- The derivative entry reads the instance's state `x` (register 0) and input
`u` (register 1). -/
def derivativeLayout (shape : Shape) : Named.Layout [shape, shape]
  | _, .here => namedBuffer shape TensorInstance.stateName
  | _, .there .here => namedBuffer shape TensorInstance.inputName

/-- The prepared tensor IVP plan: an initializer writing `x`, and the RHS
reading `x`/`u` and writing `dx`. -/
def plan (shape : Shape) : PointwisePlan (kernel shape) where
  initial := ⟨"rumoca_initialize", initialParameters, ⟨namedBuffer shape TensorInstance.stateName, ()⟩,
    fun r => nomatch r⟩
  derivative := ⟨"rumoca_rhs", derivativeParameters, ⟨namedBuffer shape TensorInstance.derivativeName, ()⟩,
    derivativeLayout shape⟩
  diagonal := ()

theorem derivative_valid (shape : Shape) : (plan shape).derivative.function.valid = true := by
  have shapeFree : (plan shape).derivative.function = (plan Tensor.scalar).derivative.function := rfl
  rw [shapeFree]; decide +kernel

/-- The C argument values supplied to the entry: a pointer to each named member
of instance `i`, and the element count. -/
def args (pool : Address) (i : Nat) (shape : Shape) : Arguments.Values := fun name =>
  if name = "count" then .integer shape.volume
  else .pointer (some (TensorInstance.field pool i name))

/-- The address environment pointing every entry buffer at the corresponding
member of instance `i`'s record. -/
def locations (pool : Address) (i : Nat) : Locations := fun buffer =>
  match buffer.pointer with
  | .id name => TensorInstance.field pool i name
  | _ => TensorInstance.record pool i

theorem derivativeBuffer_eq (shape : Shape) (pool : Address) (i : Nat) :
    TensorModelRhs.derivativeBuffer (kernel shape) (plan shape) (locations pool i) =
      TensorInstance.field pool i TensorInstance.derivativeName := rfl

variable [interface : CInterface]

/-- Every named buffer of the instance record resolves to the member address and
element count under the supplied argument locals. -/
theorem parameter_bound (parameters : List Syntax.Parameter) (pool : Address) (i : Nat) (shape : Shape)
    (name : String) (member : name ∈ parameters.map Syntax.Parameter.name)
    (countMember : "count" ∈ parameters.map Syntax.Parameter.name) (different : name ≠ "count") :
    Bound (Arguments.locals parameters (args pool i shape)) (locations pool i)
      (namedBuffer shape name).erase := by
  have pointer := Arguments.locals_present parameters (args pool i shape) name member
  have count := Arguments.locals_present parameters (args pool i shape) "count" countMember
  intro heap
  simp only [namedBuffer, Named.Buffer.erase, CBody.eval, CBody.resolve, pointer, count, args,
    if_neg different, ↓reduceIte, Option.orElse_some, locations, and_self]

/-- A well-formed instance heap satisfies the derivative entry's argument
validity, layout bounds, representation and readiness, so
`FMI3.TensorModelRhs.behaviors` applies. Running the derivative entry on instance
`i` writes the finite tensor derivative into that instance's `der(x)` region,
preserves every cell outside it, and in particular preserves every tensor cell of
every other instance in the static pool. Universal in the tensor shape and the
instance index. -/
theorem derivative_writes {shape : Shape}
    (definitions : CLoops.Calls.Definitions) (target : CCalls.Program)
    (linked : CCalls.Typed.Extends definitions target) (library : Library definitions)
    (found : definitions (plan shape).derivative.function.name = some (plan shape).derivative.function.tree)
    (backing : Heap) (pool : Address) (i : Nat) (oshape : Shape)
    (time : Values Tensor.scalar) (state input result : Values shape)
    (output : Option (Values oshape)) (bounded : shape.volume < 2 ^ 64)
    (executed : Finite.Executes (kernel shape).derivative (ArrayProfile.environment state input) result) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i TensorInstance.derivativeName) result ∧
      Writable finalHeap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume ∧
      (∀ q, Outside (locations pool i) (kernel shape).derivative
          (TensorModelRhs.derivativePlan (kernel shape) (plan shape)) q →
        finalHeap q = TensorInstance.store backing pool i shape oshape time state input output q) ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = backing ((TensorInstance.field pool j b).index k)) ∧
      ∀ behavior, (CCalls.Typed.machine target).Behaves
        (.calling (plan shape).derivative.function.name
          (Arguments.values (plan shape).derivative.function.parameters (args pool i shape))
          (TensorInstance.store backing pool i shape oshape time state input output) .done) behavior ↔
        behavior = .terminates ⟨.void, finalHeap⟩ := by
  set H := TensorInstance.store backing pool i shape oshape time state input output with hH
  have arguments : Arguments.Valid (plan shape).derivative.function.parameters (args pool i shape) := by
    intro p member
    change p ∈ derivativeParameters at member
    simp only [derivativeParameters, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact .input _
    · exact .input _
    · exact .output _
    · exact .count _ bounded
  have bound : LayoutBound (Arguments.locals (plan shape).derivative.function.parameters (args pool i shape))
      (locations pool i) (TensorModelRhs.derivativeLayout (kernel shape) (plan shape)) := by
    intro s r
    cases r with
    | here =>
      exact parameter_bound derivativeParameters pool i shape TensorInstance.stateName
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    | there r => cases r with
      | here =>
        exact parameter_bound derivativeParameters pool i shape TensorInstance.inputName
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
      | there r => nomatch r
  have represented : Represents (locations pool i) (TensorModelRhs.derivativeLayout (kernel shape) (plan shape))
      H (ArrayProfile.environment state input) := by
    intro s r
    cases r with
    | here => exact TensorInstance.reads_state backing pool i shape oshape time state input output
    | there r => cases r with
      | here => exact TensorInstance.reads_input backing pool i shape oshape time state input output
      | there r => nomatch r
  have ready : Ready (Arguments.locals (plan shape).derivative.function.parameters (args pool i shape))
      (locations pool i) (kernel shape).derivative
      (TensorModelRhs.derivativePlan (kernel shape) (plan shape))
      (TensorModelRhs.derivativeLayout (kernel shape) (plan shape)) H := by
    refine ⟨TensorInstance.writable_derivative backing pool i shape oshape time state input output,
      bounded,
      parameter_bound derivativeParameters pool i shape TensorInstance.derivativeName
        (by decide +kernel) (by decide +kernel) (by decide +kernel), ?_, True.intro⟩
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
  obtain ⟨finalHeap, reads, frame, writableResult, behaviorsIff⟩ :=
    TensorModelRhs.behaviors (kernel shape) (plan shape) (derivative_valid shape)
      definitions target linked library found (args pool i shape) arguments
      (locations pool i) (ArrayProfile.environment state input) result H
      bound represented ready executed
  refine ⟨finalHeap, ?_, ?_, frame, ?_, behaviorsIff⟩
  · rwa [derivativeBuffer_eq] at reads
  · have writable : Writable H (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume :=
      TensorInstance.writable_derivative backing pool i shape oshape time state input output
    rw [derivativeBuffer_eq] at writableResult
    exact writableResult writable
  · intro j b k different
    have outside : Outside (locations pool i) (kernel shape).derivative
        (TensorModelRhs.derivativePlan (kernel shape) (plan shape)) ((TensorInstance.field pool j b).index k) := by
      refine ⟨fun i' _ => ?_, True.intro⟩
      exact Address.instances_separate pool j i different b TensorInstance.derivativeName k i'
    calc finalHeap ((TensorInstance.field pool j b).index k)
        = H ((TensorInstance.field pool j b).index k) := frame _ outside
      _ = backing ((TensorInstance.field pool j b).index k) :=
          TensorInstance.store_other_instance backing pool i j shape oshape time state input output b k different

omit interface in
/-- A caller buffer separate from instance `i`'s derivative region lies outside
the derivative entry's written region, so the entry's frame preserves it. -/
theorem buffer_outside {shape : Shape} (pool : Address) (i : Nat) (buffer : Address) (b : Nat)
    (hb : b < shape.volume)
    (separate : ∀ a < shape.volume, ∀ b' < shape.volume,
      (TensorInstance.field pool i TensorInstance.derivativeName).index a ≠ buffer.index b') :
    Outside (locations pool i) (kernel shape).derivative
      (TensorModelRhs.derivativePlan (kernel shape) (plan shape)) (buffer.index b) :=
  ⟨fun a ha => (separate a ha b hb).symm, True.intro⟩

omit interface in
/-- Any cell of a member of instance `i` other than the derivative region lies
outside the derivative entry's written region (which is exactly the `der(x)`
region), so the entry's frame preserves it. This covers the input region `u` and
the dense output region `J`, both read or written by neighbouring adapter code. -/
theorem field_outside {shape : Shape} (pool : Address) (i : Nat) (b : String) (k : Nat)
    (different : b ≠ TensorInstance.derivativeName) :
    Outside (locations pool i) (kernel shape).derivative
      (TensorModelRhs.derivativePlan (kernel shape) (plan shape)) ((TensorInstance.field pool i b).index k) :=
  ⟨fun a _ => TensorInstance.fields_separate pool i b TensorInstance.derivativeName different k a, True.intro⟩

/-- The observable-machine version of `derivative_writes`: running the prepared
derivative entry on instance `i` embeds into the observable call machine under
any saved caller, writing the finite tensor derivative into the instance's
`der(x)` region and preserving every other cell, including every tensor cell of
every other instance in the static pool. The additional premise `resolves`
records that the nested tensor helper calls the run visits resolve to their own
names in the observable machine (they are direct calls to helper functions,
which are not shadowed by constants). -/
theorem derivative_writes_events {shape : Shape}
    (definitions : CLoops.Calls.Definitions) {E : Type} (program : CCalls.Events.Program E)
    (linked : CCalls.Typed.Extends definitions program.internal) (library : Library definitions)
    (found : definitions (plan shape).derivative.function.name = some (plan shape).derivative.function.tree)
    (backing : Heap) (pool : Address) (i : Nat) (oshape : Shape)
    (time : Values Tensor.scalar) (state input result : Values shape)
    (output : Option (Values oshape)) (bounded : shape.volume < 2 ^ 64)
    (executed : Finite.Executes (kernel shape).derivative (ArrayProfile.environment state input) result)
    (resolves : ∀ v, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling (plan shape).derivative.function.name
        (Arguments.values (plan shape).derivative.function.parameters (args pool i shape))
        (TensorInstance.store backing pool i shape oshape time state input output) .done) v →
      CCalls.Events.Resolves program v)
    (stack : CCalls.Typed.Continuation) :
    ∃ finalHeap,
      Reads finalHeap (TensorInstance.field pool i TensorInstance.derivativeName) result ∧
      Writable finalHeap (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume ∧
      (∀ q, Outside (locations pool i) (kernel shape).derivative
          (TensorModelRhs.derivativePlan (kernel shape) (plan shape)) q →
        finalHeap q = TensorInstance.store backing pool i shape oshape time state input output q) ∧
      (∀ (j : Nat) (b : String) (k : Nat), j ≠ i →
        finalHeap ((TensorInstance.field pool j b).index k) = backing ((TensorInstance.field pool j b).index k)) ∧
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling (plan shape).derivative.function.name
          (Arguments.values (plan shape).derivative.function.parameters (args pool i shape))
          (TensorInstance.store backing pool i shape oshape time state input output) stack)
        (.returning .void finalHeap stack) := by
  set H := TensorInstance.store backing pool i shape oshape time state input output with hH
  have arguments : Arguments.Valid (plan shape).derivative.function.parameters (args pool i shape) := by
    intro p member
    change p ∈ derivativeParameters at member
    simp only [derivativeParameters, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact .input _
    · exact .input _
    · exact .output _
    · exact .count _ bounded
  have bound : LayoutBound (Arguments.locals (plan shape).derivative.function.parameters (args pool i shape))
      (locations pool i) (TensorModelRhs.derivativeLayout (kernel shape) (plan shape)) := by
    intro s r
    cases r with
    | here =>
      exact parameter_bound derivativeParameters pool i shape TensorInstance.stateName
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    | there r => cases r with
      | here =>
        exact parameter_bound derivativeParameters pool i shape TensorInstance.inputName
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
      | there r => nomatch r
  have represented : Represents (locations pool i) (TensorModelRhs.derivativeLayout (kernel shape) (plan shape))
      H (ArrayProfile.environment state input) := by
    intro s r
    cases r with
    | here => exact TensorInstance.reads_state backing pool i shape oshape time state input output
    | there r => cases r with
      | here => exact TensorInstance.reads_input backing pool i shape oshape time state input output
      | there r => nomatch r
  have ready : Ready (Arguments.locals (plan shape).derivative.function.parameters (args pool i shape))
      (locations pool i) (kernel shape).derivative
      (TensorModelRhs.derivativePlan (kernel shape) (plan shape))
      (TensorModelRhs.derivativeLayout (kernel shape) (plan shape)) H := by
    refine ⟨TensorInstance.writable_derivative backing pool i shape oshape time state input output,
      bounded,
      parameter_bound derivativeParameters pool i shape TensorInstance.derivativeName
        (by decide +kernel) (by decide +kernel) (by decide +kernel), ?_, True.intro⟩
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
    TensorModelRhs.events_reaches (kernel shape) (plan shape) (derivative_valid shape)
      definitions program linked library found (args pool i shape) arguments
      (locations pool i) (ArrayProfile.environment state input) result H
      bound represented ready executed resolves stack
  refine ⟨finalHeap, ?_, ?_, frame, ?_, ran⟩
  · rwa [derivativeBuffer_eq] at reads
  · have writable : Writable H (TensorInstance.field pool i TensorInstance.derivativeName) shape.volume :=
      TensorInstance.writable_derivative backing pool i shape oshape time state input output
    rw [derivativeBuffer_eq] at writableResult
    exact writableResult writable
  · intro j b k different
    have outside : Outside (locations pool i) (kernel shape).derivative
        (TensorModelRhs.derivativePlan (kernel shape) (plan shape)) ((TensorInstance.field pool j b).index k) := by
      refine ⟨fun i' _ => ?_, True.intro⟩
      exact Address.instances_separate pool j i different b TensorInstance.derivativeName k i'
    calc finalHeap ((TensorInstance.field pool j b).index k)
        = H ((TensorInstance.field pool j b).index k) := frame _ outside
      _ = backing ((TensorInstance.field pool j b).index k) :=
          TensorInstance.store_other_instance backing pool i j shape oshape time state input output b k different

end Rumoca.FMI3.TensorInstanceRhs
