import RumocaFMI3.InitializationComposition
import Rumoca.Initialization

noncomputable section
namespace Rumoca.FMI3.InitializationCalls
open Initialization
open CMemory

/-- Source initialization is tied to the finite value actually stored in the
instance at the supplied time origin. The unit source leaves that value free. -/
def SourceInitialized (source : AST.Model) (heap : Heap) (p : Address)
    (start : Binary64.Value) (trajectory : ℝ → ℝ) : Prop :=
  Source.Initializes source (Binary64.value start) trajectory ∧
  ∃ x : Binary64.Value, load heap (StateProofs.stateAddress p) = some (.finite x) ∧
    trajectory (Binary64.value start) = Binary64.value x

theorem model_source_initialized (source : AST.Model) (heap : Heap) (p : Address)
    (start : Binary64.Value) (state : ModelExchange.State)
    (resolved : AST.Resolved source) (represented : StateProofs.Represents heap p state) :
    SourceInitialized source heap p start
      (Initialization.trajectory (Binary64.value start) (Binary64.value state.x)) := by
  refine ⟨⟨resolved, ?_⟩, state.x, represented, Initialization.trajectory_initial _ _⟩
  exact Initialization.unfixed_start_is_free none _ _

theorem source_initialized_unique (first : SourceInitialized source heap p start trajectory)
    (represented : StateProofs.Represents heap p state) :
    trajectory = Initialization.trajectory (Binary64.value start) (Binary64.value state.x) := by
  obtain ⟨initialized, x, loaded, initial⟩ := first
  have encoding : (Binary64.toBits x).val = (Binary64.toBits state.x).val := by
    have same := loaded.symm.trans represented
    exact CMemory.Value.float64.inj (Option.some.inj same)
  have same : x = state.x := Binary64.finiteEncodingEquiv.injective (Subtype.ext encoding)
  have atStart : trajectory (Binary64.value start) = Binary64.value state.x := same ▸ initial
  exact Initialization.completed_solution_unique _ ⟨Binary64.value state.x, []⟩ _ _ initialized.2 atStart

theorem exited_source_initialized (model : Solve.FMI3Model source)
    (heap : Heap) (p : Address) (args : Initialization.Arguments) (kind : Kind) (state : ModelExchange.State)
    (represented : StateProofs.Represents heap p state) :
    SourceInitialized source (exitedHeap heap p args kind) p args.start
      (Initialization.trajectory (Binary64.value args.start) (Binary64.value state.x)) :=
  model_source_initialized source _ p args.start state model.solve.dae.flat.resolved
    (InitializationBodies.exit_model (InitializationEntry.model represented args) kind)

end Rumoca.FMI3.InitializationCalls
