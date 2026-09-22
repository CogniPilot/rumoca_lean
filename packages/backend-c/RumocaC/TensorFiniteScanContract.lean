import RumocaC.TensorFiniteScanCalls
import RumocaC.TensorFiniteScanSyntax

/-! Fixed actual-file contract for the runtime scanner. The exact C bytes,
independent token syntax, typed calls, returned classifier and unchanged heap
are required together. This helper certificate does not claim that FMI/eFMI
methods invoke the scanner or that their failure protocols are complete. -/
noncomputable section
namespace Rumoca.CTensor.FiniteScan
open CMemory CMemory.EncodedTensor

def ArtifactContract (actual : String) : Prop :=
  actual = function.render ∧ Syntax.Denotes actual ∧
  ∀ (interface : CInterface) (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program) (shape : Tensor.Shape)
    (input : Option Address) (values : Bits shape) (heap : Heap),
    HeaderTypes interface → p.definitions function.signature.name = some (.tree function) →
    Readable heap input values → shape.volume < 2 ^ 64 →
    (∀ stack, Transition.Reaches
        (@CContextMachine.machine interface (@CContextMachine.declared interface declarations objects) p).step
        (.calling function.signature.name (argumentValues input shape.volume) heap stack)
        (.returning (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values)) heap stack)) ∧
    (∀ behavior,
      (@CContextMachine.machine interface (@CContextMachine.declared interface declarations objects) p).Behaves
        (.calling function.signature.name (argumentValues input shape.volume) heap .done) behavior ↔
        behavior = .terminates ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits values), heap⟩) ∧
    (Solve.Tensor.Numerical.allFiniteBits values = true ↔
      ∀ i : Fin shape.volume, ∃ finite, values[i] = (Binary64.toBits finite).val)

theorem artifact_correct (actual : String) (emitted : actual = function.render) :
    ArtifactContract actual := by
  refine ⟨emitted, emitted ▸ Syntax.render_denotes, ?_⟩
  intro interface declarations objects p shape input values heap header found readable bounded
  letI : CInterface := interface
  exact ⟨fun stack => call_reaches declarations objects p input values heap stack found header readable bounded,
    call_correct declarations objects p input values heap found header readable bounded,
    Solve.Tensor.Numerical.allFiniteBits_iff values⟩

end Rumoca.CTensor.FiniteScan
