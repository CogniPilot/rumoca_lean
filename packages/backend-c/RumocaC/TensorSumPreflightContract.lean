import RumocaC.TensorSumPreflight
import RumocaC.TensorOperationPreflightSyntax

/-! Actual-byte contract for the read-only sum preflight: its independent token
specification, its call behavior on the canonical C machine with the heap
unchanged, and the finite-sum domain with a real overflow witness. This does
not certify invocation or failure handling by a public method, nor the native
compiler, floating environment or headers. -/
noncomputable section
namespace Rumoca.CTensor.SumPreflight
open CMemory CMemory.TensorView CMemory.EncodedTensor FinitePreflight

namespace Syntax
open _root_.Parser

def tokens : List Token := FinitePreflight.Syntax.tokens "rumoca_tensor_add_finite" "+"

def Denotes (source : String) : Prop :=
  Scanner.Lexes FiniteScan.Syntax.config source.toList tokens

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

theorem render_denotes : Denotes SumPreflight.function.render := by
  apply (Scanner.lex_correct _ _ _).mp
  have h : (Scanner.lex FiniteScan.Syntax.config SumPreflight.function.render).toOption =
      some tokens := by
    simp only [SumPreflight.function, tokens]
    tensor_expand_operation_preflight_printer
    decide +kernel
  cases hl : Scanner.lex FiniteScan.Syntax.config SumPreflight.function.render with
  | error e => simp [hl, Except.toOption] at h
  | ok ts =>
    have he : ts = tokens := by simpa only [hl, Except.toOption, Option.some.injEq] using h
    exact congrArg Except.ok he

end Syntax

def ArtifactContract (actual : String) : Prop :=
  actual = function.render ∧ Syntax.Denotes actual ∧
  (∀ (interface : CInterface) (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program) (shape : Tensor.Shape)
    (a b : Values shape) (heap : Heap) (left right : Option Address),
    FinitePreflight.HeaderTypes interface → p.definitions function.signature.name = some (.tree function) →
    FiniteScan.Readable heap left (finiteBits a) → FiniteScan.Readable heap right (finiteBits b) →
    shape.volume < 2 ^ 64 →
    (∀ stack, Transition.Reaches
        (@CContextMachine.machine interface (@CContextMachine.declared interface declarations objects) p).step
        (.calling function.signature.name (FinitePreflight.argumentValues left right shape.volume) heap stack)
        (.returning (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (result a b))) heap stack)) ∧
    (∀ behavior,
      (@CContextMachine.machine interface (@CContextMachine.declared interface declarations objects) p).Behaves
        (.calling function.signature.name (FinitePreflight.argumentValues left right shape.volume) heap .done) behavior ↔
        behavior = .terminates ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (result a b)), heap⟩)) ∧
  (∀ (shape : Tensor.Shape) (a b : Values shape),
    (Solve.Tensor.Numerical.allFiniteBits (result a b) = true ↔
      ∀ i : Fin shape.volume,
        -Binary64.overflowUnits < Binary64.units a[i] + Binary64.units b[i] ∧
          Binary64.units a[i] + Binary64.units b[i] < Binary64.overflowUnits) ∧
    (Solve.Tensor.Numerical.allFiniteBits (result a b) = false ↔
      ∃ i : Fin shape.volume,
        Binary64.value a[i] + Binary64.value b[i] ≤ -Binary64.overflowValue ∨
          Binary64.overflowValue ≤ Binary64.value a[i] + Binary64.value b[i]))

theorem artifact_correct (actual : String) (emitted : actual = function.render) :
    ArtifactContract actual := by
  refine ⟨emitted, emitted ▸ Syntax.render_denotes, ?_, ?_⟩
  · intro interface declarations objects p shape a b heap left right header found read_left read_right bounded
    letI : CInterface := interface
    exact ⟨fun stack => call_reaches declarations objects p a b heap left right stack found header
        read_left read_right bounded,
      call_correct declarations objects p a b heap left right found header read_left read_right bounded⟩
  · intro shape a b
    exact ⟨result_allFinite a b, result_overflow a b⟩

end Rumoca.CTensor.SumPreflight
