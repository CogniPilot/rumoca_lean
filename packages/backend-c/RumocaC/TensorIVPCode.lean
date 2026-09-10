import RumocaC.TensorNamedCode
import RumocaCore.Solve.Pointwise

/-! Signatures and storage plans for a prepared instantaneous IVP. This
product keeps initialization, RHS and optional diagonal observation attached
to the same Solve value; FMI policy and metadata remain adapter concerns. -/
namespace Rumoca.CTensor.Lowering
open CTree Solve.Tensor

/-- Buffer names and signatures are target storage annotations. The program
is an index, so these annotations cannot substitute a different computation. -/
structure ProgramEntry (p : Program Γ shape) where
  name : String
  parameters : List Syntax.Parameter
  plan : Named.Plan p
  layout : Named.Layout Γ

def ProgramEntry.function (entry : ProgramEntry p) : Syntax.Function :=
  Named.function entry.name entry.parameters p entry.plan entry.layout

def ProgramEntry.result {p : Program Γ shape} (entry : ProgramEntry p) : Named.Buffer shape :=
  (Named.emit p entry.plan entry.layout).result

structure DiagonalEntry (p : DiagonalProgram Γ shape) where
  name : String
  parameters : List Syntax.Parameter
  plan : Named.Plan p.coefficients
  layout : Named.Layout Γ
  output : Named.Buffer p.shape

def DiagonalEntry.function (entry : DiagonalEntry p) : Syntax.Function :=
  Named.diagonalFunction entry.name entry.parameters p entry.plan entry.layout entry.output

@[reducible] def OptionalDiagonalEntry : Option (DiagonalProgram Γ shape) → Type
  | none => Unit
  | some p => DiagonalEntry p

def OptionalDiagonalEntry.function : (p : Option (DiagonalProgram Γ shape)) →
    OptionalDiagonalEntry p → Option Syntax.Function
  | none, _ => none
  | some _, entry => some (DiagonalEntry.function entry)

/-- A complete instantaneous IVP product. Solve supplies every computation;
the target supplies signatures and whole-tensor storage, with no solver policy. -/
structure PointwisePlan (p : Solve.PointwiseIVP shape) where
  initial : ProgramEntry p.initialProgram
  derivative : ProgramEntry p.derivative
  diagonal : OptionalDiagonalEntry p.diagonal

structure PointwiseSources where
  initial : String
  derivative : String
  diagonal : Option String
  deriving Repr, BEq, DecidableEq

def PointwisePlan.sources (plan : PointwisePlan p) : PointwiseSources :=
  ⟨plan.initial.function.tree.render, plan.derivative.function.tree.render,
    (OptionalDiagonalEntry.function p.diagonal plan.diagonal).map (fun f => f.tree.render)⟩

def PointwisePlan.functions (plan : PointwisePlan p) : List Syntax.Function :=
  [plan.initial.function, plan.derivative.function] ++
    (OptionalDiagonalEntry.function p.diagonal plan.diagonal).toList

end Rumoca.CTensor.Lowering
