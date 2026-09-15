import RumocaFMI3.CapabilityRejectionFamily
import RumocaFMI3.AbsentVariableContract
import RumocaFMI3.EventIndicatorFunction
import RumocaFMI3.DiscreteEvaluationContract
import RumocaFMI3.StepContract
import RumocaFMI3.DebugLoggingContract
import RumocaFMI3.NominalContract
import RumocaFMI3.StateContract
import RumocaFMI3.DerivativeContract
import RumocaFMI3.Float64Contract
import RumocaFMI3.Float64SetContract
import RumocaFMI3.InitializationContract
import RumocaFMI3.IdentityContract
import RumocaFMI3.FactoryAdmissionContract
import RumocaFMI3.StaticRuntimeContract
import RumocaFMI3.TerminationContract
import RumocaFMI3.TimeContract
import RumocaFMI3.EventEntryContract
import RumocaFMI3.CompletedContract
import RumocaFMI3.DiscreteContract
import RumocaFMI3.AdapterPreprocessing
import RumocaFMI3.AdapterPrinter
import RumocaFMI3.CallTypes
import RumocaFMI3.CountContract
import RumocaFMI3.Version
import RumocaFMI3.LoggingContract
import RumocaFMI3.LiteralEvents
import RumocaFMI3.ResetContract

/-! Every public function is indexed by its existing contract. A checked
coverage witness accounts for every signature in the actual emitted table.
Each per-family execution domain and native/standards boundary is retained;
coverage alone does not establish complete legal FMI histories. -/
noncomputable section
namespace Rumoca.FMI3.PublicAPI
open CTree CLiteral

inductive Entry where
  | version
  | debugLogging
  | factory (kind : Kind)
  | scheduled
  | release
  | initialization (enter : Bool)
  | reset
  | counts (events : Bool)
  | nominals
  | states (write : Bool)
  | derivatives
  | float64 (write : Bool)
  | terminate
  | time
  | entry (which : EventEntry.Entry)
  | completed
  | discrete
  | step
  | eventIndicators
  | evaluation
  | absent (ty : AbsentVariables.VariableType) (write : Bool)
  | capability (sig : Signature) (member : sig ∈ CapabilityRejection.signatures)

def Entry.signature : Entry → Signature
  | .version => Version.signature
  | .debugLogging => DebugLogging.signature
  | .factory kind => FactoryArguments.signature kind
  | .scheduled => ScheduledCreation.signature
  | .release => StaticRelease.function.signature
  | .initialization enter => if enter then InitializationCalls.signature else InitializationExit.signature
  | .reset => Reset.signature
  | .counts events => CountQueries.signature events
  | .nominals => ErrorCalls.nominalSignature
  | .states write => StateCalls.signature write
  | .derivatives => DerivativeCalls.signature
  | .float64 write => Float64Calls.signature write
  | .terminate => Termination.signature
  | .time => TimeCalls.signature
  | .entry which => EventEntry.signature which
  | .completed => CompletedCalls.signature
  | .discrete => DiscreteCalls.signature
  | .step => StepEntry.signature
  | .eventIndicators => EventIndicatorCalls.signature
  | .evaluation => DiscreteEvaluation.signature
  | .absent ty write => AbsentVariables.signature ty write
  | .capability sig _ => sig

def Entry.Contract (model : Solve.FMI3Model source) (sigs : List Signature) : Entry → Prop
  | .version => Version.FunctionContract model sigs (Runtime.function model Version.signature).render
  | .debugLogging => DebugLogging.FunctionContract model sigs (Runtime.function model DebugLogging.signature).render
  | .factory _ =>
      FactoryAdmission.FunctionContract model sigs
        (fun kind => (Runtime.function model (FactoryArguments.signature kind)).render) ∧
      StaticRuntime.FunctionContract model sigs (StaticStorage.render StaticStorage.deploymentCapacity)
  | .scheduled => ScheduledCreation.FunctionContract model sigs (Runtime.function model ScheduledCreation.signature).render
  | .release => StaticRuntime.FunctionContract model sigs (StaticStorage.render StaticStorage.deploymentCapacity)
  | .initialization _ => InitializationCalls.FunctionContract model sigs
      (Runtime.function model InitializationCalls.signature).render
      (Runtime.function model InitializationExit.signature).render
  | .reset => ∀ static : StaticLiterals,
      @Reset.FunctionContract static source model (Runtime.function model Reset.signature).render
  | .counts events => ∀ static : StaticLiterals,
      @CountQueries.FunctionContract static source model sigs events (Runtime.function model (CountQueries.signature events)).render
  | .nominals => Nominals.FunctionContract model sigs (Runtime.function model ErrorCalls.nominalSignature).render
  | .states _ => StateCalls.FunctionsContract model sigs
      (fun write => (Runtime.function model (StateCalls.signature write)).render)
  | .derivatives => DerivativeCalls.FunctionContract model sigs
      (Runtime.function model DerivativeCalls.signature).render Runtime.helpers[1].render
  | .float64 false => Float64Calls.FunctionContract model sigs
      (Runtime.function model (Float64Calls.signature false)).render Runtime.helpers[1].render
  | .float64 true => Float64Set.FunctionContract model sigs
      (Runtime.function model (Float64Calls.signature true)).render
  | .terminate => Termination.FunctionContract model sigs (Runtime.function model Termination.signature).render
  | .time => TimeCalls.FunctionContract model sigs (Runtime.function model TimeCalls.signature).render
  | .entry which => EventEntry.FunctionContract model which sigs (Runtime.function model (EventEntry.signature which)).render
  | .completed => CompletedCalls.FunctionContract model sigs (Runtime.function model CompletedCalls.signature).render
  | .discrete => DiscreteCalls.FunctionContract model sigs (Runtime.function model DiscreteCalls.signature).render
  | .step => StepCalls.FunctionContract model sigs (Runtime.function model StepEntry.signature).render
  | .eventIndicators => EventIndicatorCalls.FunctionContract model sigs (Runtime.function model EventIndicatorCalls.signature).render
  | .evaluation => DiscreteEvaluation.FunctionContract model sigs (Runtime.function model DiscreteEvaluation.signature).render
  | .absent ty write => AbsentVariables.FunctionContract model sigs ty write
      (Runtime.function model (AbsentVariables.signature ty write)).render
  | .capability sig _ => CapabilityRejection.FunctionContract model sigs sig sig.parameters.tail
      (Runtime.function model sig).render

def Covered (sigs : List Signature) : Prop :=
  ∀ sig ∈ sigs, ∃ api : Entry, api.signature = sig

/-- An independently checked header-coverage witness upgrades indexed contracts
to a claim over every function in that exact list. This theorem deliberately
retains that premise until the fixed artifact checker discharges it. -/
theorem every_export (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : Covered sigs) (contracts : ∀ api : Entry, api.Contract model sigs)
    (printed : Runtime.render model sigs = adapter) :
    ∀ sig ∈ sigs, ∃ api : Entry, api.signature = sig ∧ api.Contract model sigs ∧
      ∃ before after, adapter = before ++ (Runtime.function model sig).render ++ after := by
  intro sig member
  obtain ⟨api, same⟩ := covered sig member
  obtain ⟨before, after, located⟩ := LiteralPreparation.rendered_member model sigs sig member
  exact ⟨api, same, contracts api, before, after, printed ▸ located⟩

end Rumoca.FMI3.PublicAPI
end
