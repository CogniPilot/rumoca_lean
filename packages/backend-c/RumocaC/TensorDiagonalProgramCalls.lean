import RumocaC.TensorDiagonalProgramProofs
import RumocaC.TensorProgramCalls

noncomputable section
namespace Rumoca.CTensor.Lowering
open CTree CMemory CMemory.TensorView Solve.Tensor

/-- The additional callee cannot be shadowed by this function or its parameters.
The existing tensor-program syntax/contract retains its original scope rules. -/
def DiagonalScope (f : Syntax.Function) : Prop :=
  f.name ≠ Diagonal.function.signature.name ∧
    Diagonal.function.signature.name ∉ f.parameters.map Syntax.Parameter.name

def DiagonalMatches (f : Syntax.Function) (p : DiagonalProgram Γ shape)
    (plan : Plan p.coefficients) (layout : Layout Γ) (output : Buffer p.shape) : Prop :=
  f.tree.body = (emitDiagonal p plan layout output).code ++ [.ret none]

variable [interface : CInterface]

theorem diagonal_call_reaches_for (f : Syntax.Function) (valid : f.valid = true) (scope : DiagonalScope f)
    (p : DiagonalProgram Γ shape) (plan : Plan p.coefficients) (layout : Layout Γ)
    (output : Buffer p.shape) (matched : DiagonalMatches f p plan layout output)
    (definitions : CLoops.Calls.Definitions) (library : LibraryFor p.coefficients definitions)
    (diagonalDefined : definitions Diagonal.function.signature.name = some Diagonal.function)
    (found : definitions f.name = some f.tree) (args : Arguments.Values)
    (arguments : Arguments.Valid f.parameters args) (locations : Locations)
    (values : Env Binary64.Value Γ) (coefficients : Values shape) (heap : Heap)
    (bound : LayoutBound (Arguments.locals f.parameters args) locations layout)
    (represented : Represents locations layout heap values)
    (ready : Ready (Arguments.locals f.parameters args) locations p.coefficients plan layout heap)
    (reserved : Reserved locations output p.coefficients plan layout)
    (outputBound : Bound (Arguments.locals f.parameters args) locations output)
    (writable : Writable heap (locations output) p.shape.volume) (bounded : p.shape.volume < 2 ^ 64)
    (executed : Finite.Executes p.coefficients values coefficients) (stack : CLoops.Calls.Continuation) :
    ∃ finalHeap, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling f.name (Arguments.values f.parameters args) heap stack) (.returning finalHeap stack) ∧
      Reads finalHeap (locations output) (p.eval Finite.ops Binary64.positiveZero Binary64.one values) ∧
      Reads finalHeap (locations (emit p.coefficients plan layout).result) coefficients ∧
      ∀ q, DiagonalOutside locations p plan output q → finalHeap q = heap q := by
  have nodup := valid_nodup f valid
  have parameters := Arguments.bind_parameters f.parameters args library.binaryHeader nodup arguments
  have types := Arguments.bind_types f.parameters library.binaryHeader nodup
  have entered : (CLoops.Calls.machine definitions).step
      (.calling f.name (Arguments.values f.parameters args) heap stack)
      (.body (.running f.tree.body (Arguments.locals f.parameters args) (Arguments.types f.parameters) heap) stack) := by
    simp only [CLoops.Calls.machine, CLoops.Calls.machineWith, CLoops.Calls.nextWith, found, Syntax.Function.tree,
      ne_eq, not_true_eq_false, ↓reduceIte, parameters, types, bind, Option.bind_some, pure]
  obtain ⟨finalHeap, ran, matrixReads, coefficientReads, frame⟩ :=
    emitDiagonal_correct_for (Arguments.locals f.parameters args) (Arguments.types f.parameters) locations
      definitions p (library.setup p.coefficients definitions f valid args) diagonalDefined
      (Arguments.locals_absent f.parameters args _ scope.2) plan layout output values coefficients heap
      bound represented ready reserved outputBound writable bounded executed [.ret none] stack
  have returned : Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running [.ret none] (Arguments.locals f.parameters args) (Arguments.types f.parameters) finalHeap) stack)
      (.returning finalHeap stack) :=
    .next (t := .body (.returned ⟨.void, finalHeap⟩) stack) (by rfl)
      (.next (by simp [CLoops.Calls.machine, CLoops.Calls.machineWith, CLoops.Calls.nextWith]) (.refl _))
  change f.tree.body = (emitDiagonal p plan layout output).code ++ [.ret none] at matched
  rw [matched] at entered
  exact ⟨finalHeap, .next entered (ran.trans returned), matrixReads, coefficientReads, frame⟩

theorem diagonal_call_reaches (f : Syntax.Function) (valid : f.valid = true) (scope : DiagonalScope f)
    (p : DiagonalProgram Γ shape) (plan : Plan p.coefficients) (layout : Layout Γ)
    (output : Buffer p.shape) (matched : DiagonalMatches f p plan layout output)
    (definitions : CLoops.Calls.Definitions) (library : Library definitions)
    (diagonalDefined : definitions Diagonal.function.signature.name = some Diagonal.function)
    (found : definitions f.name = some f.tree) (args : Arguments.Values)
    (arguments : Arguments.Valid f.parameters args) (locations : Locations)
    (values : Env Binary64.Value Γ) (coefficients : Values shape) (heap : Heap)
    (bound : LayoutBound (Arguments.locals f.parameters args) locations layout)
    (represented : Represents locations layout heap values)
    (ready : Ready (Arguments.locals f.parameters args) locations p.coefficients plan layout heap)
    (reserved : Reserved locations output p.coefficients plan layout)
    (outputBound : Bound (Arguments.locals f.parameters args) locations output)
    (writable : Writable heap (locations output) p.shape.volume) (bounded : p.shape.volume < 2 ^ 64)
    (executed : Finite.Executes p.coefficients values coefficients) (stack : CLoops.Calls.Continuation) :
    ∃ finalHeap, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.calling f.name (Arguments.values f.parameters args) heap stack) (.returning finalHeap stack) ∧
      Reads finalHeap (locations output) (p.eval Finite.ops Binary64.positiveZero Binary64.one values) ∧
      Reads finalHeap (locations (emit p.coefficients plan layout).result) coefficients ∧
      ∀ q, DiagonalOutside locations p plan output q → finalHeap q = heap q :=
  diagonal_call_reaches_for f valid scope p plan layout output matched definitions
    (library.restrict p.coefficients) diagonalDefined found args arguments locations values coefficients heap
    bound represented ready reserved outputBound writable bounded executed stack

theorem diagonal_call_refines_for (f : Syntax.Function) (valid : f.valid = true) (scope : DiagonalScope f)
    (p : DiagonalProgram Γ shape) (plan : Plan p.coefficients) (layout : Layout Γ)
    (output : Buffer p.shape) (matched : DiagonalMatches f p plan layout output)
    (definitions : CLoops.Calls.Definitions) (library : LibraryFor p.coefficients definitions)
    (diagonalDefined : definitions Diagonal.function.signature.name = some Diagonal.function)
    (found : definitions f.name = some f.tree) (args : Arguments.Values)
    (arguments : Arguments.Valid f.parameters args) (locations : Locations)
    (values : Env Binary64.Value Γ) (coefficients : Values shape) (heap : Heap)
    (bound : LayoutBound (Arguments.locals f.parameters args) locations layout)
    (represented : Represents locations layout heap values)
    (ready : Ready (Arguments.locals f.parameters args) locations p.coefficients plan layout heap)
    (reserved : Reserved locations output p.coefficients plan layout)
    (outputBound : Bound (Arguments.locals f.parameters args) locations output)
    (writable : Writable heap (locations output) p.shape.volume) (bounded : p.shape.volume < 2 ^ 64)
    (executed : Finite.Executes p.coefficients values coefficients) :
    ∃ finalHeap, Reads finalHeap (locations output) (p.eval Finite.ops Binary64.positiveZero Binary64.one values) ∧
      Reads finalHeap (locations (emit p.coefficients plan layout).result) coefficients ∧
      (∀ q, DiagonalOutside locations p plan output q → finalHeap q = heap q) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling f.name (Arguments.values f.parameters args) heap .done) behavior ↔
        behavior = .terminates finalHeap := by
  obtain ⟨finalHeap, ran, matrixReads, coefficientReads, frame⟩ :=
    diagonal_call_reaches_for f valid scope p plan layout output matched definitions library diagonalDefined found
      args arguments locations values coefficients heap bound represented ready reserved outputBound writable bounded
      executed .done
  exact ⟨finalHeap, matrixReads, coefficientReads, frame,
    fun _ => (CLoops.Calls.machine definitions).behavior_iff (ran.trans (.next (by rfl) (.refl _))) rfl⟩

theorem diagonal_call_refines (f : Syntax.Function) (valid : f.valid = true) (scope : DiagonalScope f)
    (p : DiagonalProgram Γ shape) (plan : Plan p.coefficients) (layout : Layout Γ)
    (output : Buffer p.shape) (matched : DiagonalMatches f p plan layout output)
    (definitions : CLoops.Calls.Definitions) (library : Library definitions)
    (diagonalDefined : definitions Diagonal.function.signature.name = some Diagonal.function)
    (found : definitions f.name = some f.tree) (args : Arguments.Values)
    (arguments : Arguments.Valid f.parameters args) (locations : Locations)
    (values : Env Binary64.Value Γ) (coefficients : Values shape) (heap : Heap)
    (bound : LayoutBound (Arguments.locals f.parameters args) locations layout)
    (represented : Represents locations layout heap values)
    (ready : Ready (Arguments.locals f.parameters args) locations p.coefficients plan layout heap)
    (reserved : Reserved locations output p.coefficients plan layout)
    (outputBound : Bound (Arguments.locals f.parameters args) locations output)
    (writable : Writable heap (locations output) p.shape.volume) (bounded : p.shape.volume < 2 ^ 64)
    (executed : Finite.Executes p.coefficients values coefficients) :
    ∃ finalHeap, Reads finalHeap (locations output) (p.eval Finite.ops Binary64.positiveZero Binary64.one values) ∧
      Reads finalHeap (locations (emit p.coefficients plan layout).result) coefficients ∧
      (∀ q, DiagonalOutside locations p plan output q → finalHeap q = heap q) ∧
      ∀ behavior, (CLoops.Calls.machine definitions).Behaves
        (.calling f.name (Arguments.values f.parameters args) heap .done) behavior ↔
        behavior = .terminates finalHeap :=
  diagonal_call_refines_for f valid scope p plan layout output matched definitions
    (library.restrict p.coefficients) diagonalDefined found args arguments locations values coefficients heap
    bound represented ready reserved outputBound writable bounded executed

end Rumoca.CTensor.Lowering
