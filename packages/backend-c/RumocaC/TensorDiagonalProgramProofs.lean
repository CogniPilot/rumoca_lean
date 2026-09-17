import RumocaC.TensorDiagonalProgramMemory
import RumocaC.TensorProgramProofs
import RumocaC.TensorDiagonalCalls

namespace Rumoca.CTensor.Lowering
open CTree CMemory CMemory.TensorView Solve.Tensor
noncomputable section
variable [interface : CInterface]

theorem emitDiagonal_correct (locals : CBody.Locals) (types : CLoops.Types) (locations : Locations)
    (definitions : CLoops.Calls.Definitions) (setup : Setup locals definitions)
    (diagonalDefined : definitions Diagonal.function.signature.name = some Diagonal.function)
    (diagonalUnshadowed : locals Diagonal.function.signature.name = none)
    (p : DiagonalProgram Γ shape) (plan : Plan p.coefficients) (layout : Layout Γ)
    (output : Buffer p.shape) (values : Env Binary64.Value Γ) (coefficients : Values shape) (heap : Heap)
    (bound : LayoutBound locals locations layout) (represented : Represents locations layout heap values)
    (ready : Ready locals locations p.coefficients plan layout heap)
    (reserved : Reserved locations output p.coefficients plan layout)
    (outputBound : Bound locals locations output) (writable : Writable heap (locations output) p.shape.volume)
    (bounded : p.shape.volume < 2 ^ 64) (executed : Finite.Executes p.coefficients values coefficients)
    (rest : List Stmt) (stack : CLoops.Calls.Continuation) :
    ∃ finalHeap, Transition.Reaches (CLoops.Calls.machine definitions).step
      (.body (.running ((emitDiagonal p plan layout output).code ++ rest) locals types heap) stack)
      (.body (.running rest locals types finalHeap) stack) ∧
      Reads finalHeap (locations output) (p.eval Finite.ops Binary64.positiveZero Binary64.one values) ∧
      Reads finalHeap (locations (emit p.coefficients plan layout).result) coefficients ∧
      ∀ q, DiagonalOutside locations p plan output q → finalHeap q = heap q := by
  obtain ⟨domain, resultEq⟩ := Finite.executes_sound executed
  obtain ⟨intermediate, produced, readResult, resultBound, frame, _⟩ := emit_correct locals types locations
    definitions setup p.coefficients plan layout values heap bound represented ready domain
    (Diagonal.invoke (emit p.coefficients plan layout).result.pointer output.pointer
      (emit p.coefficients plan layout).result.count output.count :: rest) stack
  have readCoefficients : Reads intermediate (locations (emit p.coefficients plan layout).result) coefficients := by
    simpa only [resultEq] using readResult
  have stillWritable := reserved_writable locations output p.coefficients plan layout heap intermediate
    reserved writable frame
  have separate := reserved_result locations output p.coefficients plan layout reserved
  have copied := Diagonal.invoke_reaches definitions (locations (emit p.coefficients plan layout).result)
    (locations output) coefficients intermediate (emit p.coefficients plan layout).result.pointer output.pointer
    (emit p.coefficients plan layout).result.count output.count locals types rest stack
    diagonalDefined setup.fillDefined setup.binaryHeader setup.fillHeader diagonalUnshadowed
    (resultBound intermediate).1 (outputBound intermediate).1 (resultBound intermediate).2
    (outputBound intermediate).2 separate readCoefficients stillWritable bounded
  refine ⟨Diagonal.resultHeap intermediate (locations output) coefficients, ?_, ?_, ?_, ?_⟩
  · simpa only [emitDiagonal, List.append_assoc, List.singleton_append] using produced.trans copied
  · have readMatrix := Diagonal.result_reads intermediate (locations output) coefficients
    have matrixEq := (congrArg Diagonal.matrix resultEq).trans (Diagonal.solve_matrix p values)
    rw [matrixEq] at readMatrix
    exact readMatrix
  · intro i
    have unchanged := Diagonal.result_frame intermediate (locations output) coefficients
      ((locations (emit p.coefficients plan layout).result).index i.val)
      (fun j hj => Ne.symm (separate j hj i.val i.isLt))
    simpa only [load, unchanged] using readCoefficients i
  · intro q outside
    exact (Diagonal.result_frame intermediate (locations output) coefficients q outside.2).trans (frame q outside.1)

end

end Rumoca.CTensor.Lowering
