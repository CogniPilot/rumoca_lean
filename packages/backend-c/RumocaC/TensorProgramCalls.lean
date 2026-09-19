import RumocaC.TensorProgramParameters
import RumocaC.TensorProgramProofs

/-! Ordinary entry, complete nested helper execution and return for tensor
programs. Syntax validity establishes parameter uniqueness and helper scope. -/
noncomputable section
namespace Rumoca.CTensor.Lowering
open CTree CMemory CMemory.TensorView Solve.Tensor
variable [interface : CInterface]

structure Library (definitions : CLoops.Calls.Definitions) : Prop where
  binaryHeader : CTensor.HeaderTypes interface
  fillHeader : Fill.HeaderTypes interface
  binaryDefined : ∀ op, definitions (CTensor.function op).signature.name = some (CTensor.function op)
  fillDefined : definitions Fill.function.signature.name = some Fill.function

omit interface in
theorem valid_nodup (f : Syntax.Function) (valid : f.valid = true) :
    (f.parameters.map Syntax.Parameter.name).Nodup := by
  simp only [Syntax.Function.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
  exact valid.1.1.1.2

omit interface in
theorem helper_absent (f : Syntax.Function) (valid : f.valid = true) (name : String)
    (helper : name ∈ ["rumoca_tensor_add", "rumoca_tensor_mul", "rumoca_tensor_sub", "rumoca_tensor_div", "rumoca_tensor_fill"]) :
    name ∉ f.parameters.map Syntax.Parameter.name := by
  intro member
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp member
  simp only [Syntax.Function.valid, Bool.and_eq_true] at valid
  have excluded := List.all_eq_true.mp valid.1.2 p hp
  have absent : p.name ∉ ["rumoca_tensor_add", "rumoca_tensor_mul", "rumoca_tensor_sub", "rumoca_tensor_div", "rumoca_tensor_fill"] := by
    simpa using excluded
  exact absent helper

theorem Library.setup (definitions : CLoops.Calls.Definitions) (library : Library definitions)
    (f : Syntax.Function) (valid : f.valid = true) (args : Arguments.Values) :
    Setup (Arguments.locals f.parameters args) definitions := by
  refine ⟨library.binaryHeader, library.fillHeader, library.binaryDefined, library.fillDefined, ?_, ?_⟩
  · intro op
    apply Arguments.locals_absent
    cases op <;> exact helper_absent f valid _ (by decide +kernel)
  · exact Arguments.locals_absent _ _ _ (helper_absent f valid _ (by decide +kernel))

theorem program_call_reaches (f : Syntax.Function) (valid : f.valid = true)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) (matched : Syntax.Matches f p plan layout)
    (definitions : CLoops.Calls.Definitions) (library : Library definitions)
    (found : definitions f.name = some f.tree) (args : Arguments.Values)
    (arguments : Arguments.Valid f.parameters args) (locations : Locations)
    (values : Env Binary64.Value Γ) (result : Values shape) (heap : Heap)
    (bound : LayoutBound (Arguments.locals f.parameters args) locations layout)
    (represented : Represents locations layout heap values)
    (ready : Ready (Arguments.locals f.parameters args) locations p plan layout heap)
    (executed : Finite.Executes p values result) (stack : CLoops.Calls.Continuation) :
    ∃ finalHeap, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling f.name (Arguments.values f.parameters args) heap stack) (.returning finalHeap stack) ∧
      Reads finalHeap (locations (emit p plan layout).result) result ∧
      Bound (Arguments.locals f.parameters args) locations (emit p plan layout).result ∧
      (∀ q, Outside locations p plan q → finalHeap q = heap q) ∧
      (Writable heap (locations (emit p plan layout).result) shape.volume →
        Writable finalHeap (locations (emit p plan layout).result) shape.volume) := by
  have nodup := valid_nodup f valid
  have parameters := Arguments.bind_parameters f.parameters args library.binaryHeader nodup arguments
  have types := Arguments.bind_types f.parameters library.binaryHeader nodup
  have entered : (CLoops.Calls.machine definitions).step
      (.calling f.name (Arguments.values f.parameters args) heap stack)
      (.body (.running f.tree.body (Arguments.locals f.parameters args) (Arguments.types f.parameters) heap) stack) := by
    simp only [CLoops.Calls.machine, CLoops.Calls.next, found, Syntax.Function.tree,
      ne_eq, not_true_eq_false, ↓reduceIte, parameters, types, bind, Option.bind_some, pure]
  obtain ⟨domain, resultEq⟩ := Finite.executes_sound executed
  obtain ⟨finalHeap, ran, readResult, boundResult, frame, writableResult⟩ :=
    emit_correct (Arguments.locals f.parameters args) (Arguments.types f.parameters) locations
      definitions (library.setup definitions f valid args) p plan layout values heap bound represented ready domain
      [.ret none] stack
  have returned : Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running [.ret none] (Arguments.locals f.parameters args) (Arguments.types f.parameters) finalHeap) stack)
      (.returning finalHeap stack) :=
    .next (t := .body (.returned ⟨.void, finalHeap⟩) stack) (by rfl)
      (.next (by simp [CLoops.Calls.machine, CLoops.Calls.next]) (.refl _))
  change f.tree.body = (emit p plan layout).code ++ [.ret none] at matched
  rw [matched] at entered
  exact ⟨finalHeap, .next entered (ran.trans returned), resultEq ▸ readResult, boundResult, frame, writableResult⟩

theorem program_call_refines (f : Syntax.Function) (valid : f.valid = true)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) (matched : Syntax.Matches f p plan layout)
    (definitions : CLoops.Calls.Definitions) (library : Library definitions)
    (found : definitions f.name = some f.tree) (args : Arguments.Values)
    (arguments : Arguments.Valid f.parameters args) (locations : Locations)
    (values : Env Binary64.Value Γ) (result : Values shape) (heap : Heap)
    (bound : LayoutBound (Arguments.locals f.parameters args) locations layout)
    (represented : Represents locations layout heap values)
    (ready : Ready (Arguments.locals f.parameters args) locations p plan layout heap)
    (executed : Finite.Executes p values result) :
    ∃ finalHeap, Reads finalHeap (locations (emit p plan layout).result) result ∧
      Bound (Arguments.locals f.parameters args) locations (emit p plan layout).result ∧
      (∀ q, Outside locations p plan q → finalHeap q = heap q) ∧
      (Writable heap (locations (emit p plan layout).result) shape.volume →
        Writable finalHeap (locations (emit p plan layout).result) shape.volume) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling f.name (Arguments.values f.parameters args) heap .done) behavior ↔
        behavior = .terminates finalHeap := by
  obtain ⟨finalHeap, ran, readResult, boundResult, frame, writableResult⟩ :=
    program_call_reaches f valid p plan layout matched
      definitions library found args arguments locations values result heap bound represented ready executed .done
  exact ⟨finalHeap, readResult, boundResult, frame, writableResult,
    fun _ => (CLoops.Calls.machine definitions).behavior_iff (ran.trans (.next (by rfl) (.refl _))) rfl⟩
end Rumoca.CTensor.Lowering
