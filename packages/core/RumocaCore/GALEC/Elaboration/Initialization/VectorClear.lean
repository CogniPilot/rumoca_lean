import RumocaCore.GALEC.Elaboration.Surface
import RumocaCore.GALEC.StatementRelations
import RumocaCore.GALEC.VectorClear

/-! Source-AST rank-one clear through the existing generic recursive lowerer.
No parser admission, method permission, or artifact claim. -/
namespace Rumoca.GALEC.Elaboration.Initialization.VectorClear
open Elaboration Elaboration.Surface Rumoca.Tensor Rumoca.Solve.Tensor VectorBodies
open StatementRelations

def source (name binder : String) : AST.Statement :=
  unitLoop binder (dimension name 1)
    [.assign (stateReference name [iterator binder]) (.literal (.literal "0.0"))]

def lowered (target : Ref outputs ⟨[extent]⟩) : Statement inputs outputs bounds :=
  .bounded extent (.seq (.assign target vectorSubscripts (.literal .zero)) .skip)

theorem typed (table : BindingTable inputs outputs) (names : IteratorNames bounds)
    (target : Ref outputs ⟨[extent]⟩)
    (resolved : BindingTable.Resolves table [name] ⟨_, .writable target⟩)
    (known : HasShape [name] ⟨[extent]⟩)
    (positive : 0 < extent) (within : extent ≤ ceiling)
    (fresh : Loops.Binder.Fresh names binder) :
    Bodies.StatementElaborates table HasShape ceiling names (source name binder) (lowered target) := by
  have oneBound : 1 ≤ ceiling := by omega
  refine .loop (dimension_header names fresh known rfl positive within oneBound) (.cons (.assign ?_) .nil)
  exact AssignmentLowering.Elaborates.assign (target := ⟨_, target, vectorSubscripts⟩)
    (.writable (reference_typed table _ resolved (vector_indices binder names))) .zero

theorem lower (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (names : IteratorNames bounds) (target : Ref outputs ⟨[extent]⟩)
    (resolved : BindingTable.Resolves table [name] ⟨_, .writable target⟩)
    (known : HasShape [name] ⟨[extent]⟩)
    (positive : 0 < extent) (within : extent ≤ ceiling)
    (fresh : Loops.Binder.Fresh names binder) :
    Bodies.statement table lookupShape ceiling names (source name binder) = some (lowered target) :=
  Bodies.statement_complete table lookupShape HasShape correct ceiling names _ _
    (typed table names target resolved known positive within fresh)

theorem equivalent (target : Ref outputs ⟨[extent]⟩)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs) :
    Equivalent step zero one @input (bounds := bounds)
      (lowered target) (Rumoca.GALEC.VectorClear.clearVector target) :=
  bounded_congr step zero one @input extent (seq_skip_right step zero one @input _)

/-- Independent source loop execution iff exact whole-shaped update. Bounds,
binding, and shape meaning are independent premises; no destination reads or
arithmetic success is required. Unlike the core empty iteration, this source
header requires a positive dimension under the existing admitted bound policy. -/
theorem source_executes (table : BindingTable inputs outputs) (lookupShape : List String → Option Shape)
    (HasShape : List String → Shape → Prop)
    (correct : ∀ key shape, lookupShape key = some shape ↔ HasShape key shape)
    (names : IteratorNames bounds) (target : Ref outputs ⟨[extent]⟩)
    (resolved : BindingTable.Resolves table [name] ⟨_, .writable target⟩)
    (known : HasShape [name] ⟨[extent]⟩)
    (positive : 0 < extent) (within : extent ≤ ceiling)
    (fresh : Loops.Binder.Fresh names binder)
    (step : BinaryOp → α → α → α → Prop) (zero one : α) (input : Env α inputs)
    (env : IteratorEnv bounds) (before after : Env α outputs) :
    Bodies.Source.statement table HasShape ceiling step zero one @input names @env
      (source name binder) @before @after ↔
      @after = @Env.update α outputs ⟨[extent]⟩ before target (Value.fill ⟨[extent]⟩ zero) :=
  (Bodies.statement_correct table lookupShape HasShape correct ceiling names _ _
    (typed table names target resolved known positive within fresh)
    step zero one @input @env @before @after).trans
    ((equivalent target step zero one @input @env @before @after).trans
      (Rumoca.GALEC.VectorClear.clear_vector_executes_iff_update target step zero one
        @input @env @before @after))

end Rumoca.GALEC.Elaboration.Initialization.VectorClear
