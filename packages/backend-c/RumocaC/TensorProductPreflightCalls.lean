import RumocaC.TensorProductPreflight

/-! Actual preflight calls in the canonical C machine. The unchanged heap is
preserved across arbitrary saved callers and declared-object contexts. -/
noncomputable section
namespace Rumoca.CTensor.ProductPreflight
open CTree CMemory CMemory.TensorView CMemory.EncodedTensor FinitePreflight
set_option maxRecDepth 10000

variable [interface : CInterface]

theorem bind_parameters (left right : Option Address) (count : Nat)
    (header : FinitePreflight.HeaderTypes interface) (bounded : count < 2 ^ 64) :
    CCalls.parameters function.signature.parameters (FinitePreflight.argumentValues left right count) =
      some (FinitePreflight.parameters left right count) :=
  FinitePreflight.bind_parameters _ .mul left right count header bounded

theorem bind_types (header : FinitePreflight.HeaderTypes interface) :
    CLoops.Calls.parameterTypes function.signature.parameters = some FinitePreflight.parameterTypes :=
  FinitePreflight.bind_types _ .mul header

omit interface in
theorem body_field_free : CDeclaredMembers.FieldFree.AdmittedBody function.body :=
  FinitePreflight.body_field_free _ .mul

theorem call_reaches (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (a b : Values shape) (heap : Heap) (left right : Option Address) (stack : CCalls.Typed.Continuation)
    (found : p.definitions function.signature.name = some (.tree function))
    (header : FinitePreflight.HeaderTypes interface)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b))
    (bounded : shape.volume < 2 ^ 64) :
    Transition.Reaches (CContextMachine.machine (CContextMachine.declared declarations objects) p).step
      (.calling function.signature.name (FinitePreflight.argumentValues left right shape.volume) heap stack)
      (.returning (CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b)))
        heap stack) :=
  FinitePreflight.call_reaches _ .mul declarations objects p _ heap left right stack found header
    (evaluates a b heap left right read_left read_right) bounded

theorem call_correct (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (a b : Values shape) (heap : Heap) (left right : Option Address)
    (found : p.definitions function.signature.name = some (.tree function))
    (header : FinitePreflight.HeaderTypes interface)
    (read_left : FiniteScan.Readable heap left (finiteBits a))
    (read_right : FiniteScan.Readable heap right (finiteBits b))
    (bounded : shape.volume < 2 ^ 64) (behavior) :
    (CContextMachine.machine (CContextMachine.declared declarations objects) p).Behaves
      (.calling function.signature.name (FinitePreflight.argumentValues left right shape.volume) heap .done) behavior ↔
      behavior = .terminates
        ⟨CBody.boolean (Solve.Tensor.Numerical.allFiniteBits (MultiplicationTotal.result a b)), heap⟩ :=
  FinitePreflight.call_correct _ .mul declarations objects p _ heap left right found header
    (evaluates a b heap left right read_left read_right) bounded behavior

end Rumoca.CTensor.ProductPreflight
