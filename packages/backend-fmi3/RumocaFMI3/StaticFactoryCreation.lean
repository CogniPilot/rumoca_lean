import RumocaFMI3.StaticFactoryExhaustion

/-! Complete sequential behavior of the static creation suffix from typed
entry storage. The independent scan outcome is derived, never supplied as a
successful C execution premise. Public admission and global-artifact binding
must still establish this entry state in the same execution context. -/
noncomputable section
namespace Rumoca.FMI3.StaticFactory
open CTree CMemory CBody
variable [interface : CInterface]

structure CreationStorage (heap : Heap) (base flags : Address) (capacity : Nat) : Prop where
  instances : ∀ slot : Fin capacity, InstanceSlot.Storage heap (base.index slot.val)
  flagsReady : CAtomicScan.Ready flags capacity heap
  bounded : capacity < 2^64

structure CreationTypes : Prop where
  pointer : interface.types "Instance *" = some .pointer
  double : interface.types "double" = some .float64
  handle : interface.types "fmi3Instance" = some .pointer

/-- Every admitted storage state either returns a fully initialized instance
or reports exhaustion. The returned index and atomic work are bounded by the
configured capacity, and there is no assumed terminating execution. -/
theorem create_silent (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (before : Heap) (base flags : Address) (capacity : Nat)
    (environment logger : Option Address) (logging : Bool)
    (scope : Scope env base flags capacity environment logger logging)
    (storage : CreationStorage before base flags capacity)
    (bindings : ReservationBindings program tag) (typeBindings : CreationTypes)
    (nullBound : resolve env "NULL" = some (.pointer none))
    (quiet : (logger.isSome && logging) = false) :
    ∃ trace slot after, CAtomicScan.Outcome flags capacity 0 before trace slot after ∧
      slot ≤ capacity ∧ trace.length ≤ capacity ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.body (.running (code model kind) env types before) "fmi3Instance" .done) behavior ↔
      if slot < capacity then
        behavior = .terminates (trace.map tag) ⟨.pointer (some (base.index slot)),
          InstanceSlot.finalHeap after (base.index slot) slot kind environment logger logging⟩
      else behavior = .terminates (trace.map tag) ⟨.pointer none, before⟩ := by
  obtain ⟨trace, slot, after, outcome⟩ := CAtomicScan.outcome_exists storage.flagsReady (Nat.zero_le capacity)
  have bounds := CAtomicScan.outcome_bounds outcome
  refine ⟨trace, slot, after, outcome, bounds.2.1, by simpa using bounds.2.2, ?_⟩
  intro behavior
  by_cases inside : slot < capacity
  · rw [if_pos inside]
    exact successful program tag model kind env types before after base flags capacity environment logger logging
      scope storage.instances bindings.boolean bindings.atomicPointer bindings.size bindings.constantSize
      typeBindings.pointer typeBindings.double typeBindings.handle bindings.namedHelper bindings.namedAtomic
      bindings.atomicBound bindings.defined storage.bounded outcome inside behavior
  · rw [if_neg inside]
    have same : slot = capacity := by omega
    subst slot
    exact exhausted_silent program tag model kind env types before after base flags capacity environment logger logging
      scope bindings storage.bounded outcome typeBindings.handle nullBound quiet behavior

/-- The enabled-logger case admits every represented callback outcome on
exhaustion, including its memory effect and the absent-outcome failure case.
Successful creation does not call this rejection logger. -/
theorem create_logged (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (before : Heap) (base flags : Address) (capacity : Nat)
    (environment : Option Address) (logger category message : Address)
    (name : String) (foreign : CCalls.Events.External E)
    (scope : Scope env base flags capacity environment (some logger) true)
    (storage : CreationStorage before base flags capacity)
    (bindings : ReservationBindings program tag) (typeBindings : CreationTypes)
    (loggerBound : env "logMessage" = some (.pointer (some logger)))
    (nullBound : resolve env "NULL" = some (.pointer none))
    (errorBound : resolve env "fmi3Error" = some (.integer 3))
    (categoryBound : interface.literals "logStatus" = some category)
    (messageBound : interface.literals "Instance capacity exhausted" = some message)
    (address : program.addresses logger = some name)
    (external : program.externals name = some foreign)
    (prototype : foreign.signature = Logging.signature name)
    (converted : CCalls.Events.convertedArguments (Logging.signature name).parameters
      (Logging.arguments environment category message) = some (Logging.arguments environment category message)) :
    ∃ trace slot after, CAtomicScan.Outcome flags capacity 0 before trace slot after ∧
      slot ≤ capacity ∧ trace.length ≤ capacity ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.body (.running (code model kind) env types before) "fmi3Instance" .done) behavior ↔
      if slot < capacity then
        behavior = .terminates (trace.map tag) ⟨.pointer (some (base.index slot)),
          InstanceSlot.finalHeap after (base.index slot) slot kind environment (some logger) true⟩
      else
        (∃ events value heap, foreign.execute (Logging.arguments environment category message)
          before events value heap ∧ behavior = .terminates (trace.map tag ++ events) ⟨.pointer none, heap⟩) ∨
        ((∀ events value heap, ¬ foreign.execute (Logging.arguments environment category message)
          before events value heap) ∧ behavior = .wrong (trace.map tag)) := by
  obtain ⟨trace, slot, after, outcome⟩ := CAtomicScan.outcome_exists storage.flagsReady (Nat.zero_le capacity)
  have bounds := CAtomicScan.outcome_bounds outcome
  refine ⟨trace, slot, after, outcome, bounds.2.1, by simpa using bounds.2.2, ?_⟩
  intro behavior
  by_cases inside : slot < capacity
  · rw [if_pos inside]
    exact successful program tag model kind env types before after base flags capacity environment (some logger) true
      scope storage.instances bindings.boolean bindings.atomicPointer bindings.size bindings.constantSize
      typeBindings.pointer typeBindings.double typeBindings.handle bindings.namedHelper bindings.namedAtomic
      bindings.atomicBound bindings.defined storage.bounded outcome inside behavior
  · rw [if_neg inside]
    have same : slot = capacity := by omega
    subst slot
    exact exhausted_logged program tag model kind env types before after base flags capacity environment logger
      category message name foreign scope bindings storage.bounded outcome typeBindings.handle loggerBound
      nullBound errorBound categoryBound messageBound address external prototype converted behavior

end Rumoca.FMI3.StaticFactory
