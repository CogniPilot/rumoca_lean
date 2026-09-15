import RumocaFMI3.FactoryRejection
import RumocaFMI3.RuntimeEnvironment
import RumocaC.CallSignature

/-! Complete rejection of the existing Scheduled Execution factory. All
prototype arguments are retained; unused name/resource/callback pointers are
opaque. This proves defensive execution, without adding Scheduled Execution
to the supported FMI interface profile. -/
noncomputable section
namespace Rumoca.FMI3.ScheduledCreation
open CTree CMemory CBody CCalls.Events StaticFactory CLiteral.Interface

def signature : Signature := ⟨"fmi3Instance", "fmi3InstantiateScheduledExecution",
  [⟨"fmi3String", "instanceName", false⟩,
   ⟨"fmi3String", "instantiationToken", false⟩,
   ⟨"fmi3String", "resourcePath", false⟩,
   ⟨"fmi3Boolean", "visible", false⟩,
   ⟨"fmi3Boolean", "loggingOn", false⟩,
   ⟨"fmi3InstanceEnvironment", "instanceEnvironment", false⟩,
   ⟨"fmi3LogMessageCallback", "logMessage", false⟩,
   ⟨"fmi3ClockUpdateCallback", "clockUpdate", false⟩,
   ⟨"fmi3LockPreemptionCallback", "lockPreemption", false⟩,
   ⟨"fmi3UnlockPreemptionCallback", "unlockPreemption", false⟩]⟩

def message : String := "Scheduled Execution is unsupported"

structure Raw where
  name : Option Address
  token : Option Address
  resource : Option Address
  visible : Bool
  logging : Bool
  environment : Option Address
  logger : Option Address
  clockUpdate : Option Address
  lockPreemption : Option Address
  unlockPreemption : Option Address

def Raw.values (args : Raw) : List Value :=
  [.pointer args.name, .pointer args.token, .pointer args.resource,
   boolean args.visible, boolean args.logging, .pointer args.environment,
   .pointer args.logger, .pointer args.clockUpdate,
   .pointer args.lockPreemption, .pointer args.unlockPreemption]

def Raw.locals (args : Raw) : Locals :=
  CCalls.Signature.locals signature.parameters args.values

structure Scope (args : Raw) (env : Locals) : Prop where
  logger : env "logMessage" = some (.pointer args.logger)
  logging : env "loggingOn" = some (boolean args.logging)
  environment : env "instanceEnvironment" = some (.pointer args.environment)
  null : env "NULL" = none
  error : env "fmi3Error" = none

theorem scope (args : Raw) : Scope args args.locals := by
  constructor <;> simp [Raw.locals, Raw.values, signature, CCalls.Signature.locals, List.lookup]

theorem body (model : Solve.FMI3Model source) :
    Runtime.body model signature = FactoryRejection.code message := rfl

theorem arguments_converted (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (args : Raw) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    CCalls.Signature.Arguments signature.parameters args.values args.values := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  have converted (flag : Bool) : convert .boolean (boolean flag) = some (boolean flag) := by
    cases flag <;> rfl
  simp only [signature, Raw.values]
  repeat' first
    | exact CCalls.Signature.Arguments.nil
    | refine CCalls.Signature.Arguments.cons (type := .pointer) (by rfl) (by rfl) ?_
    | refine CCalls.Signature.Arguments.cons (type := .boolean) (by rfl) (converted _) ?_

theorem call_entry {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (args : Raw) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Program E) (heap : Heap) (stack : CCalls.Typed.Continuation),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      ∃ types, internalNext program (.calling signature.name args.values heap stack) =
        some (.body (.running (FactoryRejection.code message) args.locals types heap) "fmi3Instance" stack) ∧
        CCalls.Parameters.Coherent args.locals types := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap stack defined
  have bound := CCalls.Signature.parameters_bound (arguments_converted header objects literals args)
    (by decide +kernel : (signature.parameters.map Parameter.name).Nodup)
  obtain ⟨types, typed, coherent⟩ := CCalls.Parameters.parameters_typed _ _ _ bound
  refine ⟨types, ?_, coherent⟩
  simpa only [Runtime.function, body] using CCalls.Events.tree_entry program _ _ heap stack
    (Runtime.function model signature) args.locals types defined bound typed

theorem quiet_call {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (args : Raw) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Program E) (heap : Heap),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      (args.logger.isSome && args.logging) = false →
      ∀ observed, (machine program).Behaves (.calling signature.name args.values heap .done) observed ↔
        observed = .terminates [] ⟨.pointer none, heap⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap defined quiet observed
  obtain ⟨types, entered, _⟩ := call_entry header objects literals model args program heap .done defined
  rw [internal_prefix_behaviors program (.next entered (.refl _)) observed]
  have localScope := scope args
  have logger : CBody.resolve args.locals "logMessage" = some (.pointer args.logger) := by
    simp [CBody.resolve, localScope.logger]
  have logging : CBody.resolve args.locals "loggingOn" = some (boolean args.logging) := by
    simp [CBody.resolve, localScope.logging]
  have null : CBody.resolve args.locals "NULL" = some (.pointer none) := by
    simp only [CBody.resolve, localScope.null]
    rfl
  have rest := FactoryRejection.silent_equivalence program message args.locals types heap [] .done
    args.logger args.logging logger logging null (by rfl) quiet observed
  simpa only [List.append_nil] using rest.trans ((return_forced program (.pointer none) heap).behaviors observed)

theorem logged_call {E : Type} (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (args : Raw) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Program E) (heap : Heap) (logger category text : Address)
      (name : String) (foreign : External E),
      program.internal.definitions signature.name = some (.tree (Runtime.function model signature)) →
      args.logger = some logger → args.logging = true →
      literals "logStatus" = some category → literals message = some text →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      ∀ observed, (machine program).Behaves (.calling signature.name args.values heap .done) observed ↔
        (∃ events value after, foreign.execute (Logging.arguments args.environment category text)
          heap events value after ∧ observed = .terminates events ⟨.pointer none, after⟩) ∨
        ((∀ events value after, ¬ foreign.execute (Logging.arguments args.environment category text)
          heap events value after) ∧ observed = .wrong []) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap logger category text name foreign defined loggerBound logging categoryBound bound
    address external prototype observed
  obtain ⟨types, entered, _⟩ := call_entry header objects literals model args program heap .done defined
  rw [internal_prefix_behaviors program (.next entered (.refl _)) observed]
  have localScope := scope args
  have localLogger : args.locals "logMessage" = some (.pointer (some logger)) := loggerBound ▸ localScope.logger
  have localLogging : CBody.resolve args.locals "loggingOn" = some (boolean true) := by
    simp [CBody.resolve, localScope.logging, logging]
  have environment : CBody.resolve args.locals "instanceEnvironment" = some (.pointer args.environment) := by
    simp [CBody.resolve, localScope.environment]
  have error : CBody.resolve args.locals "fmi3Error" = some (.integer 3) := by
    simp only [CBody.resolve, localScope.error]
    rfl
  have null : CBody.resolve args.locals "NULL" = some (.pointer none) := by
    simp only [CBody.resolve, localScope.null]
    rfl
  simpa only [List.append_nil] using FactoryRejection.all_behaviors program message args.locals types heap []
    logger category text args.environment name foreign localLogger localLogging environment error null
    categoryBound bound address external prototype (by rfl)
    (by rfl) observed

end Rumoca.FMI3.ScheduledCreation
end

