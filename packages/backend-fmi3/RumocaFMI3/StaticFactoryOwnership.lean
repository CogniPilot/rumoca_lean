import RumocaFMI3.StaticFactoryCreation
import RumocaFMI3.StaticRelease

/-! Successful sequential creation establishes the same metadata and lease
used by the actual public release call. Both functions use one program, heap
and atomic interface. Public admission, intervening API calls, interleavings
and native/artifact correspondence remain separate composition obligations. -/
noncomputable section
namespace Rumoca.FMI3.StaticFactory
open CTree CMemory CBody
variable [interface : CInterface]

structure Created (heap : Heap) (base : Address) (block : Nat) (owners : SlotOwners.State capacity)
    (slot : Fin capacity) (owner : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) : Prop where
  storage : InstanceSlot.Storage heap (base.index slot.val)
  initialized : InstanceInitialization.Initialized heap (base.index slot.val) kind environment logger logging
  metadata : load heap ((base.index slot.val).member "slot") = some (.integer slot.val)
  represented : SlotOwners.Represents block heap owners
  owned : owners slot = some owner

theorem successful_owned (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (before after : Heap) (base : Address) (block capacity : Nat)
    (environment logger : Option Address) (logging : Bool)
    (scope : Scope env base ⟨block, [], 0⟩ capacity environment logger logging)
    (storage : CreationStorage before base ⟨block, [], 0⟩ capacity)
    (bindings : ReservationBindings program tag) (typeBindings : CreationTypes)
    (owners : SlotOwners.State capacity) (represented : SlotOwners.Represents block before owners)
    (owner : Nat) (slot : Fin capacity)
    (outcome : CAtomicScan.Outcome ⟨block, [], 0⟩ capacity 0 before trace slot.val after) :
    let heap := InstanceSlot.finalHeap after (base.index slot.val) slot.val kind environment logger logging
    SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) ∧
      Created heap base block (SlotOwners.update owners slot (some owner)) slot owner kind environment logger logging ∧
      CStorage.Preserves before heap ∧
      (∀ query, ¬ (base.index slot.val).InRecord query → query ≠ AtomicSlots.address block slot →
        heap query = before query) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.body (.running (code model kind) env types before) "fmi3Instance" .done) behavior ↔
      behavior = .terminates (trace.map tag) ⟨.pointer (some (base.index slot.val)), heap⟩ := by
  have effect := CAtomicScan.outcome_reserved outcome slot.isLt
  have exchanged : CAtomicBoolean.exchange before (AtomicSlots.address block slot) true = some (false, after) :=
    CAtomicBoolean.exchange_iff.mpr (by simpa [Address.index, AtomicSlots.address] using effect)
  have reserved := SlotOwners.exchange_reserves represented exchanged owner
  have ready := (storage.instances slot).preserved (CAtomicScan.outcome_storage outcome).1
  have bound := selected_bindings (reservedLocals env slot.val) (base.index slot.val) environment logger logging
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.environmentBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggerBound)
    (by simpa [reservedLocals, resolve, CBody.bind] using scope.loggingBound)
  have bounded : slot.val < 2^64 := Nat.lt_trans slot.isLt storage.bounded
  have owned := InstanceSlot.initialized_owners program model kind _
    (CLoops.bindType (reservedTypes types) "m" .pointer) after (base.index slot.val) slot.val
    environment logger logging ready bound
    bounded typeBindings.double typeBindings.handle
    (SlotOwners.update owners slot (some owner)) reserved.2
  have initializedPath := InstanceSlot.return_reaches program model kind _
    (CLoops.bindType (reservedTypes types) "m" .pointer) after (base.index slot.val) slot.val
    environment logger logging .done ready bound (by simp [reservedLocals, resolve, CBody.bind])
    bounded typeBindings.double typeBindings.handle
  have preserved := (CAtomicScan.outcome_storage outcome).1.trans
    (CStorage.internal_reaches program initializedPath)
  refine ⟨reserved.1, ⟨InstanceSlot.storage_ready _ _ _ _ _ _ _,
    InstanceSlot.initialized _ _ _ _ _ _ _, InstanceSlot.metadata _ _ _ _ _ _ _ bounded,
    owned, SlotOwners.reserved_owner reserved.1⟩, preserved, ?_, ?_⟩
  · intro query outside different
    rw [InstanceSlot.frame _ _ query _ _ _ _ _ outside]
    exact CAtomicScan.outcome_frame outcome (by simpa [AtomicSlots.address, Address.index] using different)
  · exact successful program tag model kind env types before after base ⟨block, [], 0⟩ capacity
      environment logger logging scope storage.instances bindings.boolean bindings.atomicPointer bindings.size
      bindings.constantSize typeBindings.pointer typeBindings.double typeBindings.handle bindings.namedHelper
      bindings.namedAtomic bindings.atomicBound bindings.defined storage.bounded outcome slot.isLt

/-- Release now gets its live-owner and metadata premises from the creation
postcondition, rather than requiring them as unrelated assumptions. -/
theorem Created.release (created : Created heap base block owners slot owner kind environment logger logging)
    (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (bindings : StaticRelease.Bindings program tag)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨block, [], 0⟩))) :
    let after := replace heap (AtomicSlots.address block slot) (CAtomicBoolean.cell false)
    SlotOwners.release owners slot owner = some (SlotOwners.update owners slot none) ∧
      SlotOwners.Represents block after (SlotOwners.update owners slot none) ∧
      CStorage.Preserves heap after ∧
      (∀ query, query ≠ AtomicSlots.address block slot → after query = heap query) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling StaticRelease.function.signature.name [.pointer (some (base.index slot.val))] heap .done) behavior ↔
      behavior = .terminates [tag (.write (AtomicSlots.address block slot) false)] ⟨.void, after⟩ :=
  StaticRelease.release_owned program tag heap base block owners slot owner bindings flagsBound
    created.represented created.owned created.metadata

/-- Creation followed by release restores the original slot ownership and
storage readiness for another creation. Object values remain initialized;
the theorem does not pretend release restores the old payloads. Both call
contracts use the exact created handle and heap in the same C program. -/
theorem create_release (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (model : Solve.Model source) (kind : Kind) (env : Locals) (types : CLoops.Types)
    (before after : Heap) (base : Address) (block capacity : Nat)
    (environment logger : Option Address) (logging : Bool)
    (scope : Scope env base ⟨block, [], 0⟩ capacity environment logger logging)
    (storage : CreationStorage before base ⟨block, [], 0⟩ capacity)
    (bindings : ReservationBindings program tag) (typeBindings : CreationTypes)
    (releaseBindings : StaticRelease.Bindings program tag)
    (flagsBound : interface.constants "rumoca_instance_flags" = some (.pointer (some ⟨block, [], 0⟩)))
    (owners : SlotOwners.State capacity) (represented : SlotOwners.Represents block before owners)
    (owner : Nat) (slot : Fin capacity)
    (outcome : CAtomicScan.Outcome ⟨block, [], 0⟩ capacity 0 before trace slot.val after) :
    ∃ live freed,
      Created live base block (SlotOwners.update owners slot (some owner)) slot owner kind environment logger logging ∧
      SlotOwners.Represents block freed owners ∧
      CreationStorage freed base ⟨block, [], 0⟩ capacity ∧ CStorage.Preserves before freed ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.body (.running (code model kind) env types before) "fmi3Instance" .done) behavior ↔
        behavior = .terminates (trace.map tag) ⟨.pointer (some (base.index slot.val)), live⟩) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling StaticRelease.function.signature.name [.pointer (some (base.index slot.val))] live .done) behavior ↔
        behavior = .terminates [tag (.write (AtomicSlots.address block slot) false)] ⟨.void, freed⟩) := by
  obtain ⟨reserved, created, preserved, framed, createdCall⟩ := successful_owned program tag model kind env types
    before after base block capacity environment logger logging scope storage bindings typeBindings owners
    represented owner slot outcome
  obtain ⟨released, ownedAfter, releaseStorage, releaseFrame, releaseCall⟩ :=
    created.release program tag releaseBindings flagsBound
  have vacant := (SlotOwners.reserve_iff.mp reserved).1
  have restored : SlotOwners.update (SlotOwners.update owners slot (some owner)) slot none = owners := by
    funext other
    by_cases same : other = slot
    · subst other
      simp [SlotOwners.update, vacant]
    · simp [SlotOwners.update, same]
  rw [restored] at ownedAfter
  have storageAfter := preserved.trans releaseStorage
  refine ⟨_, _, created, ownedAfter, ?_, storageAfter, createdCall, releaseCall⟩
  exact ⟨fun other => (storage.instances other).preserved storageAfter,
    AtomicSlots.scan_ready ownedAfter, storage.bounded⟩

end Rumoca.FMI3.StaticFactory
