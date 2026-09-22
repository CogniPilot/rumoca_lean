import RumocaC.TensorSquareIVPEntry

/-! Reusable address-bound IVP calls. Source record field names do not determine
the helper's formal parameter locations. No allocation or array enumeration. -/
noncomputable section
namespace Rumoca.CTensor.AddressedIVP
open CTree CMemory CMemory.TensorView Solve.Tensor Lowering ProgramFixture

def args (addresses : String → Address) (shape : Tensor.Shape) : Arguments.Values :=
  fun name => if name = "count" then .integer shape.volume else .pointer (some (addresses name))

def locations (addresses : String → Address) : Locations := fun buffer =>
  match buffer.pointer with
  | .id name => addresses name
  | _ => addresses ""

variable [interface : CInterface]

theorem parameter_bound (parameters : List Syntax.Parameter) (addresses : String → Address)
    (shape : Tensor.Shape) (name : String)
    (member : name ∈ parameters.map Syntax.Parameter.name)
    (countMember : "count" ∈ parameters.map Syntax.Parameter.name) (different : name ≠ "count") :
    Bound (Arguments.locals parameters (args addresses shape)) (locations addresses)
      (ProgramFixture.buffer shape name) := by
  have pointer := Arguments.locals_present parameters (args addresses shape) name member
  have count := Arguments.locals_present parameters (args addresses shape) "count" countMember
  intro heap
  simp only [ProgramFixture.buffer, CBody.eval, CBody.evalWith, CBody.resolve, pointer, count, args,
    if_neg different, ↓reduceIte, Option.orElse_some, locations, and_self]

omit interface in
theorem initial_arguments (addresses : String → Address) (shape : Tensor.Shape)
    (bounded : shape.volume < 2 ^ 64) :
    Arguments.Valid (IVPEntry.plan shape).initial.function.parameters (args addresses shape) := by
  intro p member
  change p ∈ [⟨.output, "x"⟩, ⟨.count, "count"⟩] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .output _
  · exact .count _ bounded

omit interface in
theorem derivative_arguments (addresses : String → Address) (shape : Tensor.Shape)
    (bounded : shape.volume < 2 ^ 64) :
    Arguments.Valid (IVPEntry.plan shape).derivative.function.parameters (args addresses shape) := by
  intro p member
  change p ∈ [⟨.input, "x"⟩, ⟨.input, "u"⟩, ⟨.output, "dx"⟩, ⟨.count, "count"⟩] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact .input _
  · exact .input _
  · exact .output _
  · exact .count _ bounded

theorem initial_call (definitions : CLoops.Calls.Definitions)
    (library : LibraryFor (IVPEntry.kernel shape).initialProgram definitions)
    (found : definitions (IVPEntry.plan shape).initial.function.name =
      some (IVPEntry.plan shape).initial.function.tree)
    (heap : Heap) (addresses : String → Address) (bounded : shape.volume < 2 ^ 64)
    (writable : Writable heap (addresses "x") shape.volume) :
    ∃ finalHeap, Reads finalHeap (addresses "x")
        ((IVPEntry.kernel shape).problem.initial Finite.ops Binary64.positiveZero Binary64.one) ∧
      Writable finalHeap (addresses "x") shape.volume ∧
      (∀ q, (∀ i < shape.volume, q ≠ (addresses "x").index i) → finalHeap q = heap q) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling (IVPEntry.plan shape).initial.function.name
          (Arguments.values (IVPEntry.plan shape).initial.function.parameters (args addresses shape))
          heap .done) behavior ↔ behavior = .terminates finalHeap := by
  have bound := parameter_bound IVPEntry.initialParameters addresses shape "x"
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have ready : Ready (Arguments.locals (IVPEntry.plan shape).initial.function.parameters (args addresses shape))
      (locations addresses) (IVPEntry.kernel shape).initialProgram
      (Named.Plan.erase _ (IVPEntry.plan shape).initial.plan)
      (Named.Layout.erase (IVPEntry.plan shape).initial.layout) heap :=
    ⟨writable, bounded, bound, (fun r => nomatch r), True.intro⟩
  obtain ⟨finalHeap, reads, _, frame, writes, behaviors⟩ :=
    program_call_refines_for (IVPEntry.plan shape).initial.function (IVPEntry.plan_valid shape).1 _ _ _
      (Named.function_matches _ _ _ _ _) definitions library found (args addresses shape)
      (initial_arguments addresses shape bounded) (locations addresses) Env.empty
      (Tensor.Value.fill shape Binary64.positiveZero) heap (fun r => nomatch r)
      (fun r => nomatch r) ready (Finite.Executes.fill Finite.Executes.ret)
  exact ⟨finalHeap, reads, writes writable, fun q h => frame q ⟨h, True.intro⟩, behaviors⟩

/-- Inputs may alias one another; only the written result must be separate.
This covers the actual public RHS call with both inputs pointing at u. -/
theorem derivative_call (definitions : CLoops.Calls.Definitions)
    (library : LibraryFor (IVPEntry.kernel shape).derivative definitions)
    (found : definitions (IVPEntry.plan shape).derivative.function.name =
      some (IVPEntry.plan shape).derivative.function.tree)
    (heap : Heap) (addresses : String → Address) (state input result : Values shape)
    (bounded : shape.volume < 2 ^ 64)
    (readsState : Reads heap (addresses "x") state) (readsInput : Reads heap (addresses "u") input)
    (writable : Writable heap (addresses "dx") shape.volume)
    (separate : ∀ name, name = "x" ∨ name = "u" → ∀ i < shape.volume, ∀ j < shape.volume,
      (addresses "dx").index i ≠ (addresses name).index j)
    (executed : Finite.Executes (IVPEntry.kernel shape).derivative
      (ArrayProfile.environment state input) result) :
    ∃ finalHeap, Reads finalHeap (addresses "dx") result ∧
      Writable finalHeap (addresses "dx") shape.volume ∧
      (∀ q, (∀ i < shape.volume, q ≠ (addresses "dx").index i) → finalHeap q = heap q) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling (IVPEntry.plan shape).derivative.function.name
          (Arguments.values (IVPEntry.plan shape).derivative.function.parameters (args addresses shape))
          heap .done) behavior ↔ behavior = .terminates finalHeap := by
  have layoutBound : LayoutBound
      (Arguments.locals (IVPEntry.plan shape).derivative.function.parameters (args addresses shape))
      (locations addresses) (Named.Layout.erase (IVPEntry.plan shape).derivative.layout) := by
    intro s r
    cases r with
    | here =>
      exact parameter_bound IVPEntry.derivativeParameters addresses shape "x"
        (by decide +kernel) (by decide +kernel) (by decide +kernel)
    | there r => cases r with
      | here =>
        exact parameter_bound IVPEntry.derivativeParameters addresses shape "u"
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
      | there r => nomatch r
  have represented : Represents (locations addresses)
      (Named.Layout.erase (IVPEntry.plan shape).derivative.layout) heap
      (ArrayProfile.environment state input) := by
    intro s r
    cases r with
    | here => exact readsState
    | there r => cases r with
      | here => exact readsInput
      | there r => nomatch r
  have ready : Ready
      (Arguments.locals (IVPEntry.plan shape).derivative.function.parameters (args addresses shape))
      (locations addresses) (IVPEntry.kernel shape).derivative
      (Named.Plan.erase _ (IVPEntry.plan shape).derivative.plan)
      (Named.Layout.erase (IVPEntry.plan shape).derivative.layout) heap := by
    refine ⟨writable, bounded, parameter_bound IVPEntry.derivativeParameters addresses shape "dx"
      (by decide +kernel) (by decide +kernel) (by decide +kernel), ?_, True.intro⟩
    intro s r i hi j hj
    cases r with
    | here => exact separate "x" (Or.inl rfl) i hi j hj
    | there r => cases r with
      | here => exact separate "u" (Or.inr rfl) i hi j hj
      | there r => nomatch r
  obtain ⟨finalHeap, reads, _, frame, writes, behaviors⟩ :=
    program_call_refines_for (IVPEntry.plan shape).derivative.function (IVPEntry.plan_valid shape).2.1 _ _ _
      (Named.function_matches _ _ _ _ _) definitions library found (args addresses shape)
      (derivative_arguments addresses shape bounded) (locations addresses)
      (ArrayProfile.environment state input) result heap layoutBound represented ready executed
  exact ⟨finalHeap, reads, writes writable, fun q h => frame q ⟨h, True.intro⟩, behaviors⟩

end Rumoca.CTensor.AddressedIVP
