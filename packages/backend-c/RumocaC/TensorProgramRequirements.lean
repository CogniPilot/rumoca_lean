import RumocaC.TensorProgramCode

/-! Binary-helper dependencies follow the prepared instruction sequence, not
tensor coordinates. Repeated operations are retained; membership is the API.
This neither selects helpers for printing nor changes the existing emitter. -/
namespace Rumoca.CTensor.Lowering
open CTree Solve.Tensor

def requiredOps : Program Γ shape → List Tensor.BinaryOp
  | .ret _ => []
  | .fill _ _ next => requiredOps next
  | .binary op _ _ next => op :: requiredOps next

theorem binary_name_eq_iff (op other : Tensor.BinaryOp) :
    (CTensor.function op).signature.name = (CTensor.function other).signature.name ↔ op = other := by
  cases op <;> cases other <;> decide

theorem binary_name_ne_fill (op : Tensor.BinaryOp) :
    (CTensor.function op).signature.name ≠ Fill.function.signature.name := by
  cases op <;> decide

/-- Exactly the binary helper names in the actual emitted instruction list.
All instructions count, including those whose result is not returned. -/
theorem requiredOps_iff_emitted (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ)
    (op : Tensor.BinaryOp) :
    op ∈ requiredOps p ↔
      ∃ args, .eval (.call (.id (CTensor.function op).signature.name) args) ∈
        (emit p plan layout).code := by
  induction p with
  | ret => simp [requiredOps, emit]
  | fill s value next ih =>
      simpa [requiredOps, emit, Fill.invoke, binary_name_ne_fill, exists_or] using
        ih plan.2 (layout.push plan.1)
  | binary other left right next ih =>
      simp [requiredOps, emit, CTensor.invoke, exists_or, binary_name_eq_iff,
        ← ih plan.2 (layout.push plan.1)]

end Rumoca.CTensor.Lowering
