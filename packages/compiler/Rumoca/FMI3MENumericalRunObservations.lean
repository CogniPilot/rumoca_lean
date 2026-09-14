import Rumoca.FMI3MENumericalHistory
import Rumoca.FMI3InitializationSemantics
import RumocaFMI3.MENumericalRun

noncomputable section
namespace Rumoca.FMI3.MENumericalRun
open CTree CMemory

/-- Only query positions carry derivatives. Each restart contributes the three
actual public-call observations before the next run's numerical observations. -/
inductive DerivativeObservations (source : AST.Model) :
    List Action → List (MENumericalHistory.Observation E) → Prop where
  | nil : DerivativeObservations source [] []
  | numerical {action : MENumericalHistory.Action} {result : MENumericalHistory.Observation E} :
      (action = .derivative → ∃ value, result.value = some (.finite value) ∧
        ∀ d : String → ℝ, Source.Equation source d ↔ d source.state = Binary64.value value) →
      DerivativeObservations source rest values →
      DerivativeObservations source (.numerical action :: rest) (result :: values)
  | restart : DerivativeObservations source rest values →
      DerivativeObservations source (.restart args :: rest) (reset :: enter :: exit :: values)

theorem observations_source (model : Solve.Model source) (reference : MENumericalHistory.ReferenceState)
    (actions : List Action) :
    DerivativeObservations (E := E) source actions
      ((observations model.prepareFMI3 reference actions).map MENumericalHistory.Observation.ok) := by
  induction actions generalizing reference with
  | nil => exact .nil
  | cons action rest ih =>
    cases action with
    | numerical command =>
      refine .numerical ?_ (ih (command.next reference))
      intro derivative
      subst command
      exact ⟨ModelExchange.derivative model reference.state, rfl, derivative_value_source model reference.state⟩
    | restart args => exact .restart (ih (.restart args))

/-- These are the actual post-initialization heaps, before any subsequent
importer writes. Each selects the source IVP at that restart's requested time. -/
def InitializedEpochs (source : AST.Model) (p : Address) (epochs : List Epoch) : Prop :=
  ∀ epoch ∈ epochs,
    let trajectory := Initialization.trajectory (Binary64.value epoch.1.start) (Binary64.value Binary64.positiveZero)
    InitializationCalls.SourceInitialized source epoch.2 p epoch.1.start trajectory ∧
    (∀ candidate, InitializationCalls.SourceInitialized source epoch.2 p epoch.1.start candidate → candidate = trajectory)

theorem Calls.epochs_source [CInterface] {program : CCalls.Events.Program E}
    (model : Solve.Model source)
    (certified : Calls program p addresses buffer heap actions values after epochs) : InitializedEpochs source p epochs := by
  induction certified with
  | nil => intro epoch member; cases member
  | numerical _ _ ih => exact ih
  | @restart heap args rest values final epochs _ _ _ _ ih =>
    intro epoch member
    rcases List.mem_cons.mp member with same | member
    · subst epoch
      have state := InitializationBodies.exit_model
        (InitializationEntry.model (Reset.state heap p) args) .me
      exact ⟨InitializationCalls.exited_source_initialized model.prepareFMI3 (Reset.finalHeap heap p) p args .me
        ⟨Binary64.positiveZero⟩ (Reset.state heap p),
        fun _ initialized => InitializationCalls.source_initialized_unique initialized state⟩
    · exact ih epoch member

end Rumoca.FMI3.MENumericalRun
end
