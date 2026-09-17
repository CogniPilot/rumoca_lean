import RumocaFMI3.RuntimeEnvironment
import RumocaFMI3.StaticFactoryAcquisition

noncomputable section
namespace Rumoca.FMI3.FactoryEnvironment
open CTree CMemory CBody StaticFactory CStringMemory

theorem types (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) :
    @FactoryArguments.Types (RuntimeEnvironment.interface header objects literals) := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem scope (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (kind : Kind) (args : FactoryArguments.Raw) :
    @Scope (RuntimeEnvironment.interface header objects literals) (FactoryValidation.locals kind args true)
      objects.instances objects.flags objects.capacity args.environment args.logger args.logging := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  cases kind <;> constructor <;>
    simp [FactoryValidation.locals,
      FactoryArguments.parameters, FactoryArguments.signature, FactoryArguments.arguments,
      CCalls.Signature.locals, List.lookup, CBody.resolve, CBody.constants, CBody.bind,
      CAtomicScan.function, Identity.factoryName]
  all_goals rfl

/-- Identity validation and the creation suffix share the header/object
environment used by numerical stepping. Only the factory's required bindings
are used; unrelated function bodies need not ignore the rounding macro. -/
theorem admission {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (_identity : Identity.Bindings program)
    (model : Solve.FMI3Model source) (kind : Kind) (args : FactoryArguments.Raw)
    (heap : Heap) (stack : CCalls.Typed.Continuation)
    (_request : IdentityRequest literals model kind args heap true)
    (_defined : program.internal.definitions (FactoryArguments.signature kind).name =
      some (.tree (function model kind)))
    (_helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function)),
    ∃ locals,
      Scope (FactoryValidation.locals kind args true) objects.instances objects.flags objects.capacity
        args.environment args.logger args.logging ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) heap stack) behavior ↔
      (CCalls.Events.machine program).Behaves
        (.body (.running (code model.solve kind) (FactoryValidation.locals kind args true) locals heap)
          "fmi3Instance" stack) behavior := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program identity model kind args heap stack request defined helper
  obtain ⟨locals, path⟩ := FactoryValidation.admission_equivalence program identity model (token model) kind (code model.solve kind)
    args heap stack request.name request.suppliedToken request.expected request.whitespace
    request.nameBytes request.tokenBytes request.expectedBytes request.whitespaceBytes
    defined helper (types header objects literals) rfl request.supported request.nameBound request.tokenBound
    request.expectedBound request.whitespaceBound request.nameStored request.tokenStored
    request.expectedStored request.whitespaceStored request.fits
  refine ⟨locals, scope header objects literals kind args, ?_⟩
  intro behavior
  simpa only [request.accepted, FactoryValidation.remaining, ↓reduceIte, List.nil_append] using path behavior

/-- Available storage and accepted source identity derive the complete public
factory call, initialized fields and lease in the same environment as CS. -/
theorem create_owned {E : Type} (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (_identity : Identity.Bindings program) (model : Solve.FMI3Model source)
    (kind : Kind) (args : FactoryArguments.Raw) (before : Heap)
    (_request : IdentityRequest literals model kind args before true)
    (_defined : program.internal.definitions (FactoryArguments.signature kind).name =
      some (.tree (function model kind)))
    (_helper : program.internal.definitions Identity.function.signature.name = some (.tree Identity.function))
    (_storage : CreationStorage before objects.instances objects.flags objects.capacity)
    (_bindings : ReservationBindings program tag)
    (owners : SlotOwners.State objects.capacity)
    (_represented : SlotOwners.Represents objects.flagsBlock before owners)
    (_available : ∃ slot, owners slot = none) (owner : Nat),
    ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin objects.capacity, ∃ live,
      trace.length ≤ objects.capacity ∧
      SlotOwners.reserve owners slot owner = some (SlotOwners.update owners slot (some owner)) ∧
      Created live objects.instances objects.flagsBlock (SlotOwners.update owners slot (some owner))
        slot owner kind args.environment args.logger args.logging ∧
      CStorage.Preserves before live ∧
      (∀ query, ¬ (objects.instances.index slot.val).InRecord query →
        query ≠ AtomicSlots.address objects.flagsBlock slot → live query = before query) ∧
      ∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args) before .done) behavior ↔
        behavior = .terminates (trace.map tag) ⟨.pointer (some (objects.instances.index slot.val)), live⟩ := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program tag identity model kind args before request defined helper storage bindings
    owners represented available owner
  obtain ⟨locals, scopedBindings, admitted⟩ := admission header objects literals program identity model kind args before .done
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
  obtain ⟨reserved, created, preserved, framed, creation⟩ :=
    successful_owned program tag model.solve kind (FactoryValidation.locals kind args true) locals
      before after objects.instances objects.flagsBlock objects.capacity args.environment args.logger args.logging
      scopedBindings storage bindings ⟨rfl, rfl, rfl⟩ owners represented owner ⟨index, selected⟩ outcome
  exact ⟨trace, ⟨index, selected⟩, _, by simpa using bounds.2.2,
    reserved, created, preserved, framed, fun behavior => (admitted behavior).trans (creation behavior)⟩

end Rumoca.FMI3.FactoryEnvironment
end
