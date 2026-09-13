import RumocaFMI3.FactoryEntry

/-! Complete public ME/CS null-identity rejection, from fresh parameter
binding through the actual validator and optional importer logging. No string
storage, successful callback or allocation execution is assumed. -/
noncomputable section
namespace Rumoca.FMI3.FactoryNull
open CTree CMemory CBody FactoryArguments
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

def rejected (kind : Kind) (args : Raw) : Locals :=
  CBody.bind (parameters kind args) "validIdentity" (boolean false)

theorem reaches_rejection (program : CCalls.Events.Program E) (model : Solve.FMI3Model source)
    (kind : Kind) (args : Raw) (heap : Heap) (stack : CCalls.Typed.Continuation)
    (expected whitespace : Address)
    (defined : program.internal.definitions (signature kind).name =
      some (.tree (Runtime.function model (signature kind))))
    (helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (supported : kind = .me ∨ FactoryEntry.unsupported args = false)
    (missing : (args.name.isNone || args.token.isNone) = true)
    (expectedBound : static.addresses (token model) = some expected)
    (whitespaceBound : static.addresses " \t\n\r\u000c\u000b" = some whitespace) :
    ∃ types, ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling (signature kind).name (arguments kind args) heap stack) behavior ↔
      (CCalls.Events.machine program).Behaves
        (.body (.running
          (FactoryRejection.code "Invalid name or instantiation token" ++ (Runtime.makeInstance model kind).drop 2)
          (rejected kind args) types heap) "fmi3Instance" stack) behavior := by
  obtain ⟨types, entered, _, scope⟩ := FactoryEntry.validation_entry program model kind args heap stack defined supported
  refine ⟨CLoops.bindType types "validIdentity" .boolean, ?_⟩
  intro behavior
  rw [CCalls.Events.internal_prefix_behaviors program entered behavior]
  rw [Identity.factory_null program helper rfl rfl rfl rfl rfl model kind
    (parameters kind args) types heap "fmi3Instance" stack args.name args.token expected whitespace
    scope.result scope.helper rfl scope.name scope.token expectedBound whitespaceBound missing behavior]
  exact CCalls.Events.internal_prefix_behaviors program
    (.next (FactoryRejection.identity_guard program model kind (rejected kind args)
      (CLoops.bindType types "validIdentity" .boolean) heap stack false
      (by simp [rejected, CBody.bind, resolve])) (.refl _)) behavior

theorem silent_behaviors (program : CCalls.Events.Program E) (model : Solve.FMI3Model source)
    (kind : Kind) (args : Raw) (heap : Heap) (expected whitespace : Address)
    (defined : program.internal.definitions (signature kind).name =
      some (.tree (Runtime.function model (signature kind))))
    (helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (supported : kind = .me ∨ FactoryEntry.unsupported args = false)
    (missing : (args.name.isNone || args.token.isNone) = true)
    (expectedBound : static.addresses (token model) = some expected)
    (whitespaceBound : static.addresses " \t\n\r\u000c\u000b" = some whitespace)
    (quiet : (args.logger.isSome && args.logging) = false) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature kind).name (arguments kind args) heap .done) behavior ↔
      behavior = .terminates [] ⟨.pointer none, heap⟩ := by
  obtain ⟨types, path⟩ := reaches_rejection program model kind args heap .done expected whitespace
    defined helper supported missing expectedBound whitespaceBound
  rw [path behavior]
  have scope := FactoryArguments.scope kind args
  rw [FactoryRejection.silent_equivalence program "Invalid name or instantiation token"
    (rejected kind args) types heap ((Runtime.makeInstance model kind).drop 2) .done args.logger args.logging
    (by simp [rejected, CBody.bind, resolve, scope.logger])
    (by simp [rejected, CBody.bind, resolve, scope.logging])
    (by simp [rejected, CBody.bind, resolve, scope.null, constants]) quiet behavior]
  exact (CCalls.Events.return_forced program (.pointer none) heap).behaviors behavior

theorem logged_behaviors (program : CCalls.Events.Program E) (model : Solve.FMI3Model source)
    (kind : Kind) (args : Raw) (heap : Heap) (expected whitespace logger category message : Address)
    (name : String) (foreign : CCalls.Events.External E)
    (defined : program.internal.definitions (signature kind).name =
      some (.tree (Runtime.function model (signature kind))))
    (helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (supported : kind = .me ∨ FactoryEntry.unsupported args = false)
    (missing : (args.name.isNone || args.token.isNone) = true)
    (expectedBound : static.addresses (token model) = some expected)
    (whitespaceBound : static.addresses " \t\n\r\u000c\u000b" = some whitespace)
    (loggerBound : args.logger = some logger) (logging : args.logging = true)
    (categoryBound : static.addresses "logStatus" = some category)
    (messageBound : static.addresses "Invalid name or instantiation token" = some message)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature kind).name (arguments kind args) heap .done) behavior ↔
    (∃ events value after, foreign.execute (Logging.arguments args.environment category message)
      heap events value after ∧ behavior = .terminates events ⟨.pointer none, after⟩) ∨
    ((∀ events value after, ¬ foreign.execute (Logging.arguments args.environment category message)
      heap events value after) ∧ behavior = .wrong []) := by
  obtain ⟨types, path⟩ := reaches_rejection program model kind args heap .done expected whitespace
    defined helper supported missing expectedBound whitespaceBound
  rw [path behavior]
  have scope := FactoryArguments.scope kind args
  exact FactoryRejection.all_behaviors program "Invalid name or instantiation token"
    (rejected kind args) types heap ((Runtime.makeInstance model kind).drop 2) logger category message
    args.environment name foreign
    (by simp [rejected, CBody.bind, scope.logger, loggerBound])
    (by simp [rejected, CBody.bind, resolve, scope.logging, logging])
    (by simp [rejected, CBody.bind, resolve, scope.environment])
    (by simp [rejected, CBody.bind, resolve, scope.error, constants])
    (by simp [rejected, CBody.bind, resolve, scope.null, constants])
    categoryBound messageBound address external prototype behavior

end Rumoca.FMI3.FactoryNull
