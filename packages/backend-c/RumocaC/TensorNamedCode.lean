import RumocaC.TensorProgramSyntax
import RumocaC.TensorDiagonalProgramCode

/-! Named buffer plans supply C syntax for the existing Solve emitter. Each
instruction stays a whole-tensor call; result references retain their shapes. -/
namespace Rumoca.CTensor.Lowering.Named
open CTree Solve.Tensor

structure Buffer (shape : Tensor.Shape) where
  pointer : String
  count : String

def Buffer.erase (b : Buffer shape) : Lowering.Buffer shape := ⟨.id b.pointer, .id b.count⟩

abbrev Layout (Γ : List Tensor.Shape) := {shape : Tensor.Shape} → Ref Γ shape → Buffer shape

def Layout.push (b : Buffer shape) (layout : Layout Γ) : Layout (shape :: Γ)
  | _, .here => b
  | _, .there r => layout r

def Layout.erase (layout : Layout Γ) : Lowering.Layout Γ := fun r => (layout r).erase

@[reducible] def Plan : Program Γ shape → Type
  | .ret _ => Unit
  | .fill s _ next => Buffer s × Plan next
  | @Program.binary _ s _ _ _ _ next => Buffer s × Plan next

def Plan.erase : (p : Program Γ shape) → Plan p → Lowering.Plan p
  | .ret _ => fun _ => ()
  | .fill _ _ next => fun plan => ⟨plan.1.erase, Plan.erase next plan.2⟩
  | .binary _ _ _ next => fun plan => ⟨plan.1.erase, Plan.erase next plan.2⟩

structure Product (shape : Tensor.Shape) where
  statements : List Syntax.Statement
  result : Buffer shape

def emit : (p : Program Γ shape) → Plan p → Layout Γ → Product shape
  | .ret ref => fun _ layout => ⟨[], layout ref⟩
  | .fill _ value next => fun plan layout =>
    let following := emit next plan.2 (layout.push plan.1)
    ⟨.fill value plan.1.pointer plan.1.count :: following.statements, following.result⟩
  | .binary op left right next => fun plan layout =>
    let following := emit next plan.2 (layout.push plan.1)
    ⟨.binary op (layout left).pointer (layout right).pointer plan.1.pointer plan.1.count ::
      following.statements, following.result⟩

def function (name : String) (parameters : List Syntax.Parameter)
    (p : Program Γ shape) (plan : Plan p) (layout : Layout Γ) : Syntax.Function :=
  ⟨name, parameters, (emit p plan layout).statements⟩

def diagonalFunction (name : String) (parameters : List Syntax.Parameter)
    (p : DiagonalProgram Γ shape) (plan : Plan p.coefficients) (layout : Layout Γ)
    (output : Buffer p.shape) : Syntax.Function :=
  let coefficients := emit p.coefficients plan layout
  ⟨name, parameters, coefficients.statements ++
    [.diagonal coefficients.result.pointer output.pointer coefficients.result.count output.count]⟩

end Rumoca.CTensor.Lowering.Named
