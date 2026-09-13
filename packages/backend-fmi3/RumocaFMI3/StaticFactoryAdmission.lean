import RumocaFMI3.StaticFactoryEnvironment
import RumocaFMI3.StaticFactoryOwnership

/-! Public factory entry and static creation use the same C interface and heap.
Caller buffers carry independent byte predicates, not successful executions.
Native global storage and complete host histories remain artifact and lifetime
obligations. Solve owns all numerical initialization. -/
noncomputable section
namespace Rumoca.FMI3.StaticFactory
open CTree CMemory CBody CStringMemory

/-- Readable identity buffers and supported capabilities. The actual
validator must still be executed; this record contains no C execution premise.
The artifact layer must derive the expected bytes from its prepared literals. -/
structure IdentityRequest (literals : CLiteralAddresses) (model : Solve.FMI3Model source)
    (kind : Kind) (args : FactoryArguments.Raw) (heap : Heap) (valid : Bool) where
  name : Address
  suppliedToken : Address
  expected : Address
  whitespace : Address
  nameBytes : List UInt8
  tokenBytes : List UInt8
  expectedBytes : List UInt8
  whitespaceBytes : List UInt8
  supported : kind = .me ∨ FactoryEntry.unsupported args = false
  nameBound : args.name = some name
  tokenBound : args.token = some suppliedToken
  expectedBound : literals (token model) = some expected
  whitespaceBound : literals " \t\n\r\u000c\u000b" = some whitespace
  nameStored : Contents heap name nameBytes
  tokenStored : Contents heap suppliedToken tokenBytes
  expectedStored : Contents heap expected expectedBytes
  whitespaceStored : Contents heap whitespace whitespaceBytes
  fits : nameBytes.length < 2^64
  accepted : Identity.accepted nameBytes whitespaceBytes tokenBytes expectedBytes = valid

/-- Every observation of the public call is retained at its creation suffix.
Fresh locals and their global bindings are established by public entry. -/
theorem public_admission {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (_identity : Identity.Bindings program)
    (model : Solve.FMI3Model source) (kind : Kind) (args : FactoryArguments.Raw)
    (heap : Heap) (stack : CCalls.Typed.Continuation)
    (_request : IdentityRequest literals model kind args heap true)
    (_defined : program.internal.definitions (FactoryArguments.signature kind).name =
      some (.tree (function model kind)))
    (_helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function)),
    ∃ types,
      Scope (FactoryValidation.locals kind args true) objects.instances objects.flags objects.capacity
        args.environment args.logger args.logging ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) heap stack) behavior ↔
      (CCalls.Events.machine program).Behaves
        (.body (.running (code model.solve kind) (FactoryValidation.locals kind args true) types heap)
          "fmi3Instance" stack) behavior := by
  letI : CInterface := executionInterface objects literals
  intro program identity model kind args heap stack request defined helper
  obtain ⟨types, path⟩ := FactoryValidation.admission_equivalence program identity model kind (code model.solve kind)
    args heap stack request.name request.suppliedToken request.expected request.whitespace
    request.nameBytes request.tokenBytes request.expectedBytes request.whitespaceBytes
    defined helper (factory_types objects literals) rfl request.supported request.nameBound request.tokenBound
    request.expectedBound request.whitespaceBound request.nameStored request.tokenStored
    request.expectedStored request.whitespaceStored request.fits
  refine ⟨types, factory_scope objects literals kind args, ?_⟩
  intro behavior
  simpa only [request.accepted, FactoryValidation.remaining, ↓reduceIte, List.nil_append] using path behavior

/-- Accepted public calls either initialize an instance or return null on
exhaustion. The scan outcome and its work bound follow from typed storage. -/
theorem public_create_silent {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (_identity : Identity.Bindings program) (model : Solve.FMI3Model source)
    (kind : Kind) (args : FactoryArguments.Raw) (before : Heap)
    (_request : IdentityRequest literals model kind args before true)
    (_defined : program.internal.definitions (FactoryArguments.signature kind).name =
      some (.tree (function model kind)))
    (_helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (_storage : CreationStorage before objects.instances objects.flags objects.capacity)
    (_bindings : ReservationBindings program tag)
    (_quiet : (args.logger.isSome && args.logging) = false),
    ∃ trace slot after, CAtomicScan.Outcome objects.flags objects.capacity 0 before trace slot after ∧
      slot ≤ objects.capacity ∧ trace.length ≤ objects.capacity ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) before .done) behavior ↔
      if slot < objects.capacity then
        behavior = .terminates (trace.map tag) ⟨.pointer (some (objects.instances.index slot)),
          InstanceSlot.finalHeap after (objects.instances.index slot) slot kind args.environment args.logger args.logging⟩
      else behavior = .terminates (trace.map tag) ⟨.pointer none, before⟩ := by
  letI : CInterface := executionInterface objects literals
  intro program tag identity model kind args before request defined helper storage bindings quiet
  obtain ⟨types, scope, admission⟩ := public_admission objects literals program identity model kind args before .done
    request defined helper
  have argsScope := FactoryArguments.scope kind args
  obtain ⟨trace, slot, after, outcome, bounded, work, creation⟩ := create_silent program tag model.solve kind
    (FactoryValidation.locals kind args true) types before objects.instances objects.flags objects.capacity
    args.environment args.logger args.logging scope storage bindings ⟨rfl, rfl, rfl⟩
    (by simp [FactoryValidation.locals, CBody.bind, resolve, argsScope.null, constants]; rfl) quiet
  exact ⟨trace, slot, after, outcome, bounded, work, fun behavior => (admission behavior).trans (creation behavior)⟩

/-- Enabled exhaustion logging retains all represented host outcomes and their
effects, including absence of a represented callback outcome. Success never
calls the rejection logger. No callback success is assumed. -/
theorem public_create_logged {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (_identity : Identity.Bindings program) (model : Solve.FMI3Model source)
    (kind : Kind) (args : FactoryArguments.Raw) (before : Heap)
    (_request : IdentityRequest literals model kind args before true)
    (_defined : program.internal.definitions (FactoryArguments.signature kind).name =
      some (.tree (function model kind)))
    (_helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (_storage : CreationStorage before objects.instances objects.flags objects.capacity)
    (_bindings : ReservationBindings program tag)
    (logger category message : Address) (name : String) (foreign : CCalls.Events.External E)
    (_loggerBound : args.logger = some logger) (_logging : args.logging = true)
    (_categoryBound : literals "logStatus" = some category)
    (_messageBound : literals "Instance capacity exhausted" = some message)
    (_address : program.addresses logger = some name)
    (_external : program.externals name = some foreign)
    (_prototype : foreign.signature = Logging.signature name),
    ∃ trace slot after, CAtomicScan.Outcome objects.flags objects.capacity 0 before trace slot after ∧
      slot ≤ objects.capacity ∧ trace.length ≤ objects.capacity ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) before .done) behavior ↔
      if slot < objects.capacity then
        behavior = .terminates (trace.map tag) ⟨.pointer (some (objects.instances.index slot)),
          InstanceSlot.finalHeap after (objects.instances.index slot) slot kind args.environment (some logger) true⟩
      else
        (∃ events value heap, foreign.execute (Logging.arguments args.environment category message)
          before events value heap ∧ behavior = .terminates (trace.map tag ++ events) ⟨.pointer none, heap⟩) ∨
        ((∀ events value heap, ¬ foreign.execute (Logging.arguments args.environment category message)
          before events value heap) ∧ behavior = .wrong (trace.map tag)) := by
  letI : CInterface := executionInterface objects literals
  intro program tag identity model kind args before request defined helper storage bindings
    logger category message name foreign loggerBound logging categoryBound messageBound address external prototype
  obtain ⟨types, scope, admission⟩ := public_admission objects literals program identity model kind args before .done
    request defined helper
  rw [loggerBound, logging] at scope
  have argsScope := FactoryArguments.scope kind args
  have converted : CCalls.Events.convertedArguments (Logging.signature name).parameters
      (Logging.arguments args.environment category message) = some (Logging.arguments args.environment category message) := by
    rfl
  obtain ⟨trace, slot, after, outcome, bounded, work, creation⟩ := create_logged program tag model.solve kind
    (FactoryValidation.locals kind args true) types before objects.instances objects.flags objects.capacity
    args.environment logger category message name foreign scope storage bindings ⟨rfl, rfl, rfl⟩
    (by simp [FactoryValidation.locals, CBody.bind, argsScope.logger, loggerBound])
    (by simp [FactoryValidation.locals, CBody.bind, resolve, argsScope.null, constants]; rfl)
    (by simp [FactoryValidation.locals, CBody.bind, resolve, argsScope.error, constants]; rfl)
    categoryBound messageBound address external prototype converted
  exact ⟨trace, slot, after, outcome, bounded, work, fun behavior => (admission behavior).trans (creation behavior)⟩

/-- A public creation followed by public release returns the original logical
ownership and reusable storage. Availability is a property of the entry heap;
the actual scan outcome and successful C executions are derived. This theorem
is sequential and makes no claim about interleaved native invocation histories. -/
theorem public_create_release {E : Type} (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface objects literals
    ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (_identity : Identity.Bindings program) (model : Solve.FMI3Model source)
    (kind : Kind) (args : FactoryArguments.Raw) (before : Heap)
    (_request : IdentityRequest literals model kind args before true)
    (_defined : program.internal.definitions (FactoryArguments.signature kind).name =
      some (.tree (function model kind)))
    (_helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (_storage : CreationStorage before objects.instances objects.flags objects.capacity)
    (_bindings : ReservationBindings program tag) (_releaseBindings : StaticRelease.Bindings program tag)
    (owners : SlotOwners.State objects.capacity)
    (_represented : SlotOwners.Represents objects.flagsBlock before owners)
    (_available : ∃ slot, owners slot = none) (owner : Nat),
    ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin objects.capacity, ∃ live freed,
      trace.length ≤ objects.capacity ∧
      Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner))
        slot owner kind args.environment args.logger args.logging ∧
      SlotOwners.Represents objects.flagsBlock freed owners ∧
      CreationStorage freed objects.instances objects.flags objects.capacity ∧ CStorage.Preserves before freed ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) before .done) behavior ↔
        behavior = .terminates (trace.map tag) ⟨.pointer (some (objects.instances.index slot.val)), live⟩) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling StaticRelease.function.signature.name [.pointer (some (objects.instances.index slot.val))] live .done) behavior ↔
        behavior = .terminates [tag (.write (AtomicSlots.address objects.flagsBlock slot) false)] ⟨.void, freed⟩) := by
  letI : CInterface := executionInterface objects literals
  intro program tag identity model kind args before request defined helper storage bindings releaseBindings
    owners represented available owner
  obtain ⟨types, scope, admission⟩ := public_admission objects literals program identity model kind args before .done
    request defined helper
  obtain ⟨trace, index, after, outcome⟩ := CAtomicScan.outcome_exists storage.flagsReady (Nat.zero_le objects.capacity)
  have bounds := CAtomicScan.outcome_bounds outcome
  have selected : index < objects.capacity := by
    by_contra outside
    have exhausted : index = objects.capacity := by omega
    rw [exhausted] at outcome
    obtain ⟨slot, vacant⟩ := available
    have busy := (AtomicSlots.scan_exhausted represented outcome).2 slot
    simp [SlotOwners.occupied, vacant] at busy
  obtain ⟨live, freed, created, restored, ready, preserved, creation, released⟩ := create_release program tag
    model.solve kind (FactoryValidation.locals kind args true) types before after objects.instances
    objects.flagsBlock objects.capacity args.environment args.logger args.logging scope storage bindings
    ⟨rfl, rfl, rfl⟩ releaseBindings rfl owners represented owner ⟨index, selected⟩ outcome
  exact ⟨trace, ⟨index, selected⟩, live, freed, by simpa using bounds.2.2, created,
    restored, ready, preserved, fun behavior => (admission behavior).trans (creation behavior), released⟩

end Rumoca.FMI3.StaticFactory
