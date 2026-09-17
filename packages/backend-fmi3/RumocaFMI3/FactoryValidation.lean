import RumocaFMI3.FactoryEntry

/-! Nonnull identity validation from actual public ME/CS call entry. The
independent byte predicate selects the emitted rejection or creation suffix;
all observations of that suffix are retained, without assuming allocation. -/
noncomputable section
namespace Rumoca.FMI3.FactoryValidation
open CTree CMemory CBody CStringMemory FactoryArguments

def locals (kind : Kind) (args : Raw) (valid : Bool) : Locals :=
  CBody.bind (parameters kind args) "validIdentity" (boolean valid)

def remaining (creation : List Stmt) (valid : Bool) : List Stmt :=
  (if valid then [] else FactoryRejection.code "Invalid name or instantiation token") ++
    creation

section
variable [interface : CInterface]

theorem admission_equivalence (program : CCalls.Events.Program E) (bindings : Identity.Bindings program)
    (model : Solve.FMI3Model source) (tok : String := token model) (kind : Kind) (creation : List Stmt) (args : Raw) (heap : Heap)
    (stack : CCalls.Typed.Continuation) (name suppliedToken expected whitespace : Address)
    (nameBytes tokenBytes expectedBytes whitespaceBytes : List UInt8)
    (defined : program.internal.definitions (signature kind).name =
      some (.tree ⟨signature kind, FactoryPrefix.body model kind creation tok, false⟩))
    (helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (typeBindings : FactoryArguments.Types)
    (named : interface.constants Identity.function.signature.name = none)
    (supported : kind = .me ∨ FactoryEntry.unsupported args = false)
    (nameBound : args.name = some name) (tokenBound : args.token = some suppliedToken)
    (expectedBound : interface.literals tok = some expected)
    (whitespaceBound : interface.literals " \t\n\r\u000c\u000b" = some whitespace)
    (nameStored : Contents heap name nameBytes) (tokenStored : Contents heap suppliedToken tokenBytes)
    (expectedStored : Contents heap expected expectedBytes) (whitespaceStored : Contents heap whitespace whitespaceBytes)
    (fits : nameBytes.length < 2^64) :
    ∃ types, ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.calling (signature kind).name (arguments kind args) heap stack) behavior ↔
      (CCalls.Events.machine program).Behaves
        (.body (.running (remaining creation (Identity.accepted nameBytes whitespaceBytes tokenBytes expectedBytes))
          (locals kind args (Identity.accepted nameBytes whitespaceBytes tokenBytes expectedBytes)) types heap)
          "fmi3Instance" stack) behavior := by
  obtain ⟨types, entered, _, scope⟩ := FactoryEntry.validation_entry program
    (FactoryPrefix.validation model tok :: FactoryPrefix.identityGuard :: creation)
    kind args heap stack typeBindings defined supported
  refine ⟨CLoops.bindType types "validIdentity" .boolean, ?_⟩
  intro behavior
  rw [CCalls.Events.internal_prefix_behaviors program entered behavior]
  rw [Identity.factory_validates program bindings helper model tok (FactoryPrefix.identityGuard :: creation) (parameters kind args) types heap
    "fmi3Instance" stack name suppliedToken expected whitespace nameBytes tokenBytes expectedBytes whitespaceBytes
    scope.result scope.helper named (by simpa [nameBound] using scope.name)
    (by simpa [tokenBound] using scope.token) expectedBound whitespaceBound
    nameStored tokenStored expectedStored whitespaceStored fits behavior]
  exact CCalls.Events.internal_prefix_behaviors program
    (.next (FactoryRejection.identity_guard program creation
      (locals kind args (Identity.accepted nameBytes whitespaceBytes tokenBytes expectedBytes))
      (CLoops.bindType types "validIdentity" .boolean) heap stack _
      (by simp [locals, CBody.bind, resolve])) (.refl _)) behavior


/-- A rejected valid-buffer request returns null with unchanged memory when
logging is disabled or no callback was supplied. -/
theorem rejected_silent (program : CCalls.Events.Program E) (bindings : Identity.Bindings program)
    (model : Solve.FMI3Model source) (tok : String := token model) (kind : Kind) (creation : List Stmt) (args : Raw) (heap : Heap)
    (name suppliedToken expected whitespace : Address)
    (nameBytes tokenBytes expectedBytes whitespaceBytes : List UInt8)
    (defined : program.internal.definitions (signature kind).name =
      some (.tree ⟨signature kind, FactoryPrefix.body model kind creation tok, false⟩))
    (helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (typeBindings : FactoryArguments.Types)
    (named : interface.constants Identity.function.signature.name = none)
    (nullConstant : interface.constants "NULL" = some (.pointer none))
    (supported : kind = .me ∨ FactoryEntry.unsupported args = false)
    (nameBound : args.name = some name) (tokenBound : args.token = some suppliedToken)
    (expectedBound : interface.literals tok = some expected)
    (whitespaceBound : interface.literals " \t\n\r\u000c\u000b" = some whitespace)
    (nameStored : Contents heap name nameBytes) (tokenStored : Contents heap suppliedToken tokenBytes)
    (expectedStored : Contents heap expected expectedBytes) (whitespaceStored : Contents heap whitespace whitespaceBytes)
    (fits : nameBytes.length < 2^64)
    (rejected : Identity.accepted nameBytes whitespaceBytes tokenBytes expectedBytes = false)
    (quiet : (args.logger.isSome && args.logging) = false) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature kind).name (arguments kind args) heap .done) behavior ↔
      behavior = .terminates [] ⟨.pointer none, heap⟩ := by
  obtain ⟨types, path⟩ := admission_equivalence program bindings model tok kind creation args heap .done
    name suppliedToken expected whitespace nameBytes tokenBytes expectedBytes whitespaceBytes
    defined helper typeBindings named supported nameBound tokenBound expectedBound whitespaceBound
    nameStored tokenStored expectedStored whitespaceStored fits
  rw [path behavior, rejected]
  have scope := FactoryArguments.scope kind args
  change (CCalls.Events.machine program).Behaves
    (.body (.running (FactoryRejection.code "Invalid name or instantiation token" ++
      creation) (locals kind args false) types heap) "fmi3Instance" .done) behavior ↔ _
  rw [FactoryRejection.silent_equivalence program "Invalid name or instantiation token"
    (locals kind args false) types heap creation .done args.logger args.logging
    (by simp [locals, CBody.bind, resolve, scope.logger])
    (by simp [locals, CBody.bind, resolve, scope.logging])
    (by simp [locals, CBody.bind, resolve, scope.null, constants, nullConstant]) typeBindings.handle quiet behavior]
  exact (CCalls.Events.return_forced program (.pointer none) heap).behaviors behavior

/-- Enabled rejection logging retains every represented host outcome. The
result cannot be mistaken for successful instance creation. -/
theorem rejected_logged (program : CCalls.Events.Program E) (bindings : Identity.Bindings program)
    (model : Solve.FMI3Model source) (tok : String := token model) (kind : Kind) (creation : List Stmt) (args : Raw) (heap : Heap)
    (name suppliedToken expected whitespace logger category message : Address)
    (nameBytes tokenBytes expectedBytes whitespaceBytes : List UInt8)
    (loggerName : String) (foreign : CCalls.Events.External E)
    (defined : program.internal.definitions (signature kind).name =
      some (.tree ⟨signature kind, FactoryPrefix.body model kind creation tok, false⟩))
    (helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (typeBindings : FactoryArguments.Types)
    (named : interface.constants Identity.function.signature.name = none)
    (nullConstant : interface.constants "NULL" = some (.pointer none))
    (supported : kind = .me ∨ FactoryEntry.unsupported args = false)
    (nameBound : args.name = some name) (tokenBound : args.token = some suppliedToken)
    (expectedBound : interface.literals tok = some expected)
    (whitespaceBound : interface.literals " \t\n\r\u000c\u000b" = some whitespace)
    (nameStored : Contents heap name nameBytes) (tokenStored : Contents heap suppliedToken tokenBytes)
    (expectedStored : Contents heap expected expectedBytes) (whitespaceStored : Contents heap whitespace whitespaceBytes)
    (fits : nameBytes.length < 2^64)
    (rejected : Identity.accepted nameBytes whitespaceBytes tokenBytes expectedBytes = false)
    (loggerBound : args.logger = some logger) (logging : args.logging = true)
    (categoryBound : interface.literals "logStatus" = some category)
    (messageBound : interface.literals "Invalid name or instantiation token" = some message)
    (address : program.addresses logger = some loggerName)
    (external : program.externals loggerName = some foreign)
    (prototype : foreign.signature = Logging.signature loggerName)
    (errorConstant : interface.constants "fmi3Error" = some (.integer 3))
    (converted : CCalls.Events.convertedArguments (Logging.signature loggerName).parameters
      (Logging.arguments args.environment category message) = some (Logging.arguments args.environment category message))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature kind).name (arguments kind args) heap .done) behavior ↔
    (∃ events value after, foreign.execute (Logging.arguments args.environment category message)
      heap events value after ∧ behavior = .terminates events ⟨.pointer none, after⟩) ∨
    ((∀ events value after, ¬ foreign.execute (Logging.arguments args.environment category message)
      heap events value after) ∧ behavior = .wrong []) := by
  obtain ⟨types, path⟩ := admission_equivalence program bindings model tok kind creation args heap .done
    name suppliedToken expected whitespace nameBytes tokenBytes expectedBytes whitespaceBytes
    defined helper typeBindings named supported nameBound tokenBound expectedBound whitespaceBound
    nameStored tokenStored expectedStored whitespaceStored fits
  rw [path behavior, rejected]
  have scope := FactoryArguments.scope kind args
  exact FactoryRejection.all_behaviors program "Invalid name or instantiation token"
    (locals kind args false) types heap creation logger category message
    args.environment loggerName foreign
    (by simp [locals, CBody.bind, scope.logger, loggerBound])
    (by simp [locals, CBody.bind, resolve, scope.logging, logging])
    (by simp [locals, CBody.bind, resolve, scope.environment])
    (by simp [locals, CBody.bind, resolve, scope.error, constants, errorConstant])
    (by simp [locals, CBody.bind, resolve, scope.null, constants, nullConstant])
    categoryBound messageBound address external prototype typeBindings.handle converted behavior

end
end Rumoca.FMI3.FactoryValidation
