import RumocaC.TensorCode
import RumocaC.TensorFillCode
import RumocaC.Algorithm
import RumocaCore.Solve.Tensor

/-! Shape-indexed storage annotations and thin emission of complete Solve
programs. Each fill/binary instruction becomes one ordinary helper call.
The result is a buffer reference; no coordinates or implicit copies are
introduced. Callers own allocation and supply buffer/count expressions. -/
namespace Rumoca.CTensor.Lowering
open CTree Solve.Tensor

structure Buffer (shape : Tensor.Shape) where
  pointer : Expr
  count : Expr

abbrev Layout (Γ : List Tensor.Shape) := {shape : Tensor.Shape} → Ref Γ shape → Buffer shape

def Layout.push (buffer : Buffer shape) (layout : Layout Γ) : Layout (shape :: Γ)
  | _, .here => buffer
  | _, .there ref => layout ref

/-- One destination per whole-tensor instruction, with no tensor coordinates. -/
@[reducible] def Plan : Program Γ shape → Type
  | .ret _ => Unit
  | .fill s _ next => Buffer s × Plan next
  | @Program.binary _ s _ _ _ _ next => Buffer s × Plan next

structure Product (shape : Tensor.Shape) where
  code : List Stmt
  result : Buffer shape

def emit : (p : Program Γ shape) → Plan p → Layout Γ → Product shape
  | .ret ref => fun _ layout => ⟨[], layout ref⟩
  | .fill _ value next => fun plan layout =>
    let following := emit next plan.2 (layout.push plan.1)
    ⟨Fill.invoke (CAlgorithm.literal value) plan.1.pointer plan.1.count :: following.code, following.result⟩
  | .binary op left right next => fun plan layout =>
    let following := emit next plan.2 (layout.push plan.1)
    ⟨CTensor.invoke op (layout left).pointer (layout right).pointer plan.1.pointer plan.1.count ::
      following.code, following.result⟩

/-- Code size depends on the instruction sequence, never on tensor volume. -/
theorem emit_code_count (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) :
    (emit p plan layout).code.length + 1 = p.nodeCount := by
  induction p with
  | ret => rfl
  | fill s value next ih =>
    simpa only [emit, Program.nodeCount, List.length_cons] using
      congrArg (· + 1) (ih plan.2 (layout.push plan.1))
  | binary op left right next ih =>
    simpa only [emit, Program.nodeCount, List.length_cons] using
      congrArg (· + 1) (ih plan.2 (layout.push plan.1))

end Rumoca.CTensor.Lowering
