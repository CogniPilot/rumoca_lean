import RumocaFMI3.FactoryEntry

/-! Complete rejection of unsupported CS creation requests, before validation
or instance storage. No name/token pointer validity or helper binding is needed. -/
noncomputable section
namespace Rumoca.FMI3.FactoryUnsupported
open CTree CMemory CBody FactoryArguments
variable [interface : CInterface]

def message : String := "Events and intermediate updates are unsupported"

theorem rejection_entry (program : CCalls.Events.Program E) (rest : List Stmt)
    (args : Raw) (heap : Heap) (stack : CCalls.Typed.Continuation)
    (typeBindings : FactoryArguments.Types)
    (defined : program.internal.definitions (signature .cs).name =
      some (.tree ⟨signature .cs, FactoryPrefix.entry .cs rest, false⟩))
    (unsupported : FactoryEntry.unsupported args = true) :
    ∃ types,
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling (signature .cs).name (arguments .cs args) heap stack)
        (.body (.running (FactoryRejection.code message ++ rest)
          (parameters .cs args) types heap) "fmi3Instance" stack) := by
  obtain ⟨types, entered, _, _⟩ := FactoryArguments.call_entry program (FactoryPrefix.entry .cs rest)
    .cs args heap stack typeBindings defined
  have guarded := FactoryEntry.coSimulation_guard program (rest) args types heap stack
  rw [unsupported] at guarded
  exact ⟨types, .next entered (.next guarded (.refl _))⟩

theorem silent_behaviors (program : CCalls.Events.Program E) (rest : List Stmt)
    (args : Raw) (heap : Heap)
    (typeBindings : FactoryArguments.Types)
    (defined : program.internal.definitions (signature .cs).name =
      some (.tree ⟨signature .cs, FactoryPrefix.entry .cs rest, false⟩))
    (unsupported : FactoryEntry.unsupported args = true)
    (nullConstant : interface.constants "NULL" = some (.pointer none))
    (quiet : (args.logger.isSome && args.logging) = false) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature .cs).name (arguments .cs args) heap .done) behavior ↔
      behavior = .terminates [] ⟨.pointer none, heap⟩ := by
  obtain ⟨types, entered⟩ := rejection_entry program rest args heap .done typeBindings defined unsupported
  rw [CCalls.Events.internal_prefix_behaviors program entered behavior]
  have scope := FactoryArguments.scope .cs args
  rw [FactoryRejection.silent_equivalence program message (parameters .cs args) types heap
    (rest) .done args.logger args.logging
    (by simp [resolve, scope.logger]) (by simp [resolve, scope.logging])
    (by simp [resolve, scope.null, constants, nullConstant]) typeBindings.handle quiet behavior]
  exact (CCalls.Events.return_forced program (.pointer none) heap).behaviors behavior

theorem logged_behaviors (program : CCalls.Events.Program E) (rest : List Stmt)
    (args : Raw) (heap : Heap) (logger category text : Address)
    (name : String) (foreign : CCalls.Events.External E)
    (typeBindings : FactoryArguments.Types)
    (defined : program.internal.definitions (signature .cs).name =
      some (.tree ⟨signature .cs, FactoryPrefix.entry .cs rest, false⟩))
    (unsupported : FactoryEntry.unsupported args = true)
    (nullConstant : interface.constants "NULL" = some (.pointer none))
    (loggerBound : args.logger = some logger) (logging : args.logging = true)
    (categoryBound : interface.literals "logStatus" = some category)
    (messageBound : interface.literals message = some text)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name)
    (errorConstant : interface.constants "fmi3Error" = some (.integer 3))
    (converted : CCalls.Events.convertedArguments (Logging.signature name).parameters
      (Logging.arguments args.environment category text) = some (Logging.arguments args.environment category text))
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature .cs).name (arguments .cs args) heap .done) behavior ↔
    (∃ events value after, foreign.execute (Logging.arguments args.environment category text)
      heap events value after ∧ behavior = .terminates events ⟨.pointer none, after⟩) ∨
    ((∀ events value after, ¬ foreign.execute (Logging.arguments args.environment category text)
      heap events value after) ∧ behavior = .wrong []) := by
  obtain ⟨types, entered⟩ := rejection_entry program rest args heap .done typeBindings defined unsupported
  rw [CCalls.Events.internal_prefix_behaviors program entered behavior]
  have scope := FactoryArguments.scope .cs args
  exact FactoryRejection.all_behaviors program message (parameters .cs args) types heap
    (rest) logger category text args.environment name foreign
    (by simpa [loggerBound] using scope.logger)
    (by simp [resolve, scope.logging, logging]) (by simp [resolve, scope.environment])
    (by simp [resolve, scope.error, constants, errorConstant]) (by simp [resolve, scope.null, constants, nullConstant])
    categoryBound messageBound address external prototype typeBindings.handle converted behavior

end Rumoca.FMI3.FactoryUnsupported
