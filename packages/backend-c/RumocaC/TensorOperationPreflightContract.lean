import RumocaC.TensorOperationPreflight
import RumocaC.TensorOperationPreflightSyntax

/-! Actual-byte contract of the read-only preflight of a shared binary tensor
operation: the bytes, their independent token specification, and the call
behavior on the canonical C machine, which returns the classifier of the
operation's encoded results with the heap unchanged. Each operation supplies
its result encoding, the coordinate evaluation and the lexing of its text. -/
noncomputable section
namespace Rumoca.CTensor.FinitePreflight
open CMemory CMemory.TensorView CMemory.EncodedTensor

def OperationContract (name : String) (op : CTree.BinOp) (operator : String)
    (result : ∀ {shape : Tensor.Shape}, Values shape → Values shape → Bits shape)
    (actual : String) : Prop :=
  actual = (operation name op).render ∧ Syntax.Denotes name operator actual ∧
  ∀ (interface : CInterface) (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program) (shape : Tensor.Shape)
    (a b : Values shape) (heap : Heap) (left right : Option Address),
    HeaderTypes interface → p.definitions name = some (.tree (operation name op)) →
    FiniteScan.Readable heap left (finiteBits a) → FiniteScan.Readable heap right (finiteBits b) →
    shape.volume < 2 ^ 64 →
    (∀ stack, Transition.Reaches
        (@CContextMachine.machine interface (@CContextMachine.declared interface declarations objects) p).step
        (.calling name (argumentValues left right shape.volume) heap stack)
        (.returning (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (result a b))) heap stack)) ∧
    (∀ behavior,
      (@CContextMachine.machine interface (@CContextMachine.declared interface declarations objects) p).Behaves
        (.calling name (argumentValues left right shape.volume) heap .done) behavior ↔
        behavior = .terminates ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (result a b)), heap⟩)

theorem operation_contract (name : String) (op : CTree.BinOp) (operator : String)
    (result : ∀ {shape : Tensor.Shape}, Values shape → Values shape → Bits shape)
    (evaluates : ∀ (interface : CInterface) {shape : Tensor.Shape} (a b : Values shape) (heap : Heap)
      (left right : Option Address),
      FiniteScan.Readable heap left (finiteBits a) → FiniteScan.Readable heap right (finiteBits b) →
      @Evaluates interface shape op (result a b) heap left right)
    (lexed : Syntax.Denotes name operator (operation name op).render)
    (actual : String) (emitted : actual = (operation name op).render) :
    OperationContract name op operator result actual := by
  refine ⟨emitted, emitted ▸ lexed, ?_⟩
  intro interface declarations objects p shape a b heap left right header found read_left read_right bounded
  letI : CInterface := interface
  have evaluated := evaluates interface a b heap left right read_left read_right
  exact ⟨fun stack => call_reaches name op declarations objects p _ heap left right stack found header
      evaluated bounded,
    call_correct name op declarations objects p _ heap left right found header evaluated bounded⟩

end Rumoca.CTensor.FinitePreflight
