import Rumoca.FMI3InitializationSemantics
import RumocaFMI3.InitializationQuiet

noncomputable section
namespace Rumoca.FMI3.InitializationCalls
open Initialization
open CTree CMemory

section
variable [interface : CInterface]

/-- Complete initialization calls select the source IVP from finite instance
storage. The final source solution is unique at its supplied time origin. -/
def SourceExecutionContract (source : AST.Model) (program : CCalls.Events.Program E) : Prop :=
  ∀ (heap : Heap) (p : Address) (args : Initialization.Arguments) (kind : Kind),
    Arguments.Admissible args → EntryStorage heap p →
    load heap (p.member "kind") = some (.integer kind.code) →
    (∃ x : Binary64.Value, load heap (StateProofs.stateAddress p) = some (.finite x)) →
    ∃ initialized exited trajectory,
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name (arguments (some p) (Raw.ofFinite args)) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, initialized⟩) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) initialized .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
      SourceInitialized source exited p args.start trajectory ∧
      (∀ candidate, SourceInitialized source exited p args.start candidate → candidate = trajectory)

/-- The certified public calls establish the unique source IVP selected by
the finite value in the instance, including a host override of the default.
The caller supplies storage and source-independent arguments, not a target run. -/
theorem QuietExecutionContract.source {source : AST.Model} (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (contract : QuietExecutionContract program)
    (heap : Heap) (p : Address) (args : Initialization.Arguments) (kind : Kind)
    (admissible : Arguments.Admissible args) (storage : EntryStorage heap p)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (finiteState : ∃ x : Binary64.Value, load heap (StateProofs.stateAddress p) = some (.finite x)) :
    ∃ initialized exited trajectory,
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling signature.name (arguments (some p) (Raw.ofFinite args)) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, initialized⟩) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) initialized .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
      SourceInitialized source exited p args.start trajectory ∧
      (∀ candidate, SourceInitialized source exited p args.start candidate → candidate = trajectory) := by
  obtain ⟨x, loaded⟩ := finiteState
  have represented : StateProofs.Represents heap p ⟨x⟩ := loaded
  have kept := InitializationBodies.exit_model (InitializationEntry.model represented args) kind
  refine ⟨InitializationEntry.finalHeap heap p args, exitedHeap heap p args kind,
    Initialization.trajectory (Binary64.value args.start) (Binary64.value x),
    contract.enter heap p args kind admissible storage hk,
    contract.exit _ p kind ((entered_kind heap p args).trans hk) (entered_mode heap p args),
    exited_source_initialized model heap p args kind ⟨x⟩ represented, ?_⟩
  intro candidate initialized
  exact source_initialized_unique initialized kept

theorem QuietExecutionContract.source_contract {source : AST.Model} (model : Solve.FMI3Model source)
    (program : CCalls.Events.Program E) (contract : QuietExecutionContract program) :
    SourceExecutionContract source program := by
  intro heap p args kind admissible storage hk finiteState
  exact contract.source model program heap p args kind admissible storage hk finiteState

end
end Rumoca.FMI3.InitializationCalls
