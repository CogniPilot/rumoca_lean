import RumocaFMI3.FactoryEntry

/-! Complete rejection of unsupported CS creation requests, before validation
or instance storage. No name/token pointer validity or helper binding is needed. -/
noncomputable section
namespace Rumoca.FMI3.FactoryUnsupported
open CTree CMemory CBody FactoryArguments
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

def message : String := "Events and intermediate updates are unsupported"

theorem rejection_entry (program : CCalls.Events.Program E) (model : Solve.FMI3Model source)
    (args : Raw) (heap : Heap) (stack : CCalls.Typed.Continuation)
    (defined : program.internal.definitions (signature .cs).name =
      some (.tree (Runtime.function model (signature .cs))))
    (unsupported : FactoryEntry.unsupported args = true) :
    ∃ types,
      Transition.Reaches (fun s t => CCalls.Events.internalNext program s = some t)
        (.calling (signature .cs).name (arguments .cs args) heap stack)
        (.body (.running (FactoryRejection.code message ++ Runtime.makeInstance model .cs)
          (parameters .cs args) types heap) "fmi3Instance" stack) := by
  obtain ⟨types, entered, _, _⟩ := FactoryArguments.call_entry program model .cs args heap stack defined
  have guarded := FactoryEntry.coSimulation_guard program model args types heap stack
  rw [unsupported] at guarded
  exact ⟨types, .next entered (.next guarded (.refl _))⟩

theorem silent_behaviors (program : CCalls.Events.Program E) (model : Solve.FMI3Model source)
    (args : Raw) (heap : Heap)
    (defined : program.internal.definitions (signature .cs).name =
      some (.tree (Runtime.function model (signature .cs))))
    (unsupported : FactoryEntry.unsupported args = true)
    (quiet : (args.logger.isSome && args.logging) = false) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature .cs).name (arguments .cs args) heap .done) behavior ↔
      behavior = .terminates [] ⟨.pointer none, heap⟩ := by
  obtain ⟨types, entered⟩ := rejection_entry program model args heap .done defined unsupported
  rw [CCalls.Events.internal_prefix_behaviors program entered behavior]
  have scope := FactoryArguments.scope .cs args
  rw [FactoryRejection.silent_equivalence program message (parameters .cs args) types heap
    (Runtime.makeInstance model .cs) .done args.logger args.logging
    (by simp [resolve, scope.logger]) (by simp [resolve, scope.logging])
    (by simp [resolve, scope.null, constants]) quiet behavior]
  exact (CCalls.Events.return_forced program (.pointer none) heap).behaviors behavior

theorem logged_behaviors (program : CCalls.Events.Program E) (model : Solve.FMI3Model source)
    (args : Raw) (heap : Heap) (logger category text : Address)
    (name : String) (foreign : CCalls.Events.External E)
    (defined : program.internal.definitions (signature .cs).name =
      some (.tree (Runtime.function model (signature .cs))))
    (unsupported : FactoryEntry.unsupported args = true)
    (loggerBound : args.logger = some logger) (logging : args.logging = true)
    (categoryBound : static.addresses "logStatus" = some category)
    (messageBound : static.addresses message = some text)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling (signature .cs).name (arguments .cs args) heap .done) behavior ↔
    (∃ events value after, foreign.execute (Logging.arguments args.environment category text)
      heap events value after ∧ behavior = .terminates events ⟨.pointer none, after⟩) ∨
    ((∀ events value after, ¬ foreign.execute (Logging.arguments args.environment category text)
      heap events value after) ∧ behavior = .wrong []) := by
  obtain ⟨types, entered⟩ := rejection_entry program model args heap .done defined unsupported
  rw [CCalls.Events.internal_prefix_behaviors program entered behavior]
  have scope := FactoryArguments.scope .cs args
  exact FactoryRejection.all_behaviors program message (parameters .cs args) types heap
    (Runtime.makeInstance model .cs) logger category text args.environment name foreign
    (by simpa [loggerBound] using scope.logger)
    (by simp [resolve, scope.logging, logging]) (by simp [resolve, scope.environment])
    (by simp [resolve, scope.error, constants]) (by simp [resolve, scope.null, constants])
    categoryBound messageBound address external prototype behavior

end Rumoca.FMI3.FactoryUnsupported
