import RumocaFMI3.StaticFactoryAdmission
import RumocaFMI3.FactoryNull
import RumocaFMI3.FactoryUnsupported

/-! All pre-storage rejection cases of the public static factories. Only
nonnull identity validation needs readable string buffers and string-library
bindings. No constructor assumes a successful C execution or host callback. -/
noncomputable section
namespace Rumoca.FMI3.StaticFactory
open CTree CMemory CBody

section
variable [interface : CInterface]

/-- Independent rejection conditions and the definitions needed by the
traversed prefix. The message index fixes the diagnostic for each cause. -/
inductive Rejected (program : CCalls.Events.Program E) (model : Solve.FMI3Model source)
    (kind : Kind) (args : FactoryArguments.Raw) (heap : Heap) : String → Prop where
  | unsupported (cs : kind = .cs) (requested : FactoryEntry.unsupported args = true) :
      Rejected program model kind args heap "Events and intermediate updates are unsupported"
  | missing (supported : kind = .me ∨ FactoryEntry.unsupported args = false)
      (missing : (args.name.isNone || args.token.isNone) = true)
      (expected whitespace : Address)
      (expectedBound : interface.literals (token model) = some expected)
      (whitespaceBound : interface.literals " \t\n\r\u000c\u000b" = some whitespace)
      (helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function)) :
      Rejected program model kind args heap "Invalid name or instantiation token"
  | identity (request : IdentityRequest interface.literals model kind args heap false)
      (bindings : Identity.Bindings program)
      (helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function)) :
      Rejected program model kind args heap "Invalid name or instantiation token"

end

/-- Every pre-storage rejection returns null without touching memory when
logging is disabled or absent. No reservation/storage readiness is required. -/
theorem public_rejected_silent {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (model : Solve.FMI3Model source)
    (kind : Kind) (args : FactoryArguments.Raw) (heap : Heap) (message : String)
    (_rejected : Rejected program model kind args heap message)
    (_defined : program.internal.definitions (FactoryArguments.signature kind).name =
      some (.tree (function model kind)))
    (_quiet : (args.logger.isSome && args.logging) = false) (behavior),
    (CCalls.Events.machine program).Behaves
      (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) heap .done) behavior ↔
      behavior = .terminates [] ⟨.pointer none, heap⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program model kind args heap message rejected defined quiet behavior
  cases rejected with
  | unsupported cs requested =>
      subst kind
      exact FactoryUnsupported.silent_behaviors program
        (FactoryPrefix.validation model :: FactoryPrefix.identityGuard :: code model.solve .cs)
        args heap (factory_types objects literals) defined requested rfl quiet behavior
  | missing supported missing expected whitespace expectedBound whitespaceBound helper =>
      exact FactoryNull.silent_behaviors program model kind (code model.solve kind) args heap expected whitespace
        defined helper (factory_types objects literals) rfl rfl rfl rfl rfl supported missing
        expectedBound whitespaceBound quiet behavior
  | identity request bindings helper =>
      exact FactoryValidation.rejected_silent program bindings model kind (code model.solve kind) args heap
        request.name request.suppliedToken request.expected request.whitespace
        request.nameBytes request.tokenBytes request.expectedBytes request.whitespaceBytes
        defined helper (factory_types objects literals) rfl rfl request.supported request.nameBound request.tokenBound
        request.expectedBound request.whitespaceBound request.nameStored request.tokenStored
        request.expectedStored request.whitespaceStored request.fits request.accepted quiet behavior

/-- Enabled logging preserves the exact diagnostic, all represented callback
events/effects and the missing-outcome failure case. Rejection cannot silently
continue into reservation, initialization or a successful handle return. -/
theorem public_rejected_logged {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (model : Solve.FMI3Model source)
    (kind : Kind) (args : FactoryArguments.Raw) (heap : Heap) (message : String)
    (_rejected : Rejected program model kind args heap message)
    (_defined : program.internal.definitions (FactoryArguments.signature kind).name =
      some (.tree (function model kind)))
    (logger category text : Address) (name : String) (foreign : CCalls.Events.External E)
    (_loggerBound : args.logger = some logger) (_logging : args.logging = true)
    (_categoryBound : literals "logStatus" = some category)
    (_messageBound : literals message = some text)
    (_address : program.addresses logger = some name)
    (_external : program.externals name = some foreign)
    (_prototype : foreign.signature = Logging.signature name) (behavior),
    (CCalls.Events.machine program).Behaves
      (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) heap .done) behavior ↔
    (∃ events value after, foreign.execute (Logging.arguments args.environment category text)
      heap events value after ∧ behavior = .terminates events ⟨.pointer none, after⟩) ∨
    ((∀ events value after, ¬ foreign.execute (Logging.arguments args.environment category text)
      heap events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := executionInterface objects literals
  intro program model kind args heap message rejected defined logger category text name foreign
    loggerBound logging categoryBound messageBound address external prototype behavior
  have converted : CCalls.Events.convertedArguments (Logging.signature name).parameters
      (Logging.arguments args.environment category text) = some (Logging.arguments args.environment category text) := by rfl
  cases rejected with
  | unsupported cs requested =>
      subst kind
      exact FactoryUnsupported.logged_behaviors program
        (FactoryPrefix.validation model :: FactoryPrefix.identityGuard :: code model.solve .cs)
        args heap logger category text name foreign (factory_types objects literals) defined requested rfl
        loggerBound logging categoryBound messageBound address external prototype rfl converted behavior
  | missing supported missing expected whitespace expectedBound whitespaceBound helper =>
      exact FactoryNull.logged_behaviors program model kind (code model.solve kind) args heap
        expected whitespace logger category text name foreign defined helper (factory_types objects literals)
        rfl rfl rfl rfl rfl supported missing expectedBound whitespaceBound
        loggerBound logging categoryBound messageBound address external prototype rfl converted behavior
  | identity request bindings helper =>
      exact FactoryValidation.rejected_logged program bindings model kind (code model.solve kind) args heap
        request.name request.suppliedToken request.expected request.whitespace logger category text
        request.nameBytes request.tokenBytes request.expectedBytes request.whitespaceBytes name foreign
        defined helper (factory_types objects literals) rfl rfl request.supported request.nameBound request.tokenBound
        request.expectedBound request.whitespaceBound request.nameStored request.tokenStored
        request.expectedStored request.whitespaceStored request.fits request.accepted
        loggerBound logging categoryBound messageBound address external prototype rfl converted behavior

end Rumoca.FMI3.StaticFactory
