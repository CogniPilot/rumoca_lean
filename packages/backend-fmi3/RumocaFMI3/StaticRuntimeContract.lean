import RumocaFMI3.StaticRuntimeLinkage
import RumocaFMI3.StaticFactoryPrinter

/-! Mandatory consequences of the actual static FMI runtime. Startup, public
creation and release use the same declaration product and function table.
This adds no source case. The statement remains about the authored C object/
call model; complete concurrent histories and native translation-unit/ABI
refinement are separate requirements. -/
noncomputable section
namespace Rumoca.FMI3.StaticRuntime
open CTree CMemory StaticFactory

/-- The represented foreign routines are explicit. All internal definitions,
including the reservation and release functions, must come from the actual
table rather than being supplied as independent successful-call premises. -/
def InitialExecution (model : Solve.FMI3Model source) (signatures : List Signature) : Prop :=
  ∀ (E : Type) (instances flags : Nat) (separate : instances ≠ flags) (literals : CLiteralAddresses),
    let storage := objects instances flags separate
    letI : CInterface := executionInterface storage literals
    ∀ (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E),
    program.internal = LiteralPreparation.program model signatures →
    Identity.Bindings program →
    program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag rfl) →
    program.externals "atomic_store" = some (CAtomicBoolean.Calls.writeExternal tag) →
    ∀ (kind : Kind) (args : FactoryArguments.Raw) (before : Heap),
    StaticStorage.Fresh storage before →
    IdentityRequest literals model kind args (StaticStorage.initial storage before) true →
    ∀ owner : Nat,
    ∃ trace : List CAtomicBoolean.Calls.Event, ∃ slot : Fin storage.capacity, ∃ live freed,
      trace.length ≤ storage.capacity ∧
      Created live storage.instances storage.flagsBlock
        (SlotOwners.update (fun _ => none) slot (some owner)) slot owner kind
        args.environment args.logger args.logging ∧
      SlotOwners.Represents storage.flagsBlock freed (fun _ : Fin storage.capacity => none) ∧
      CreationStorage freed storage.instances storage.flags storage.capacity ∧
      CStorage.Preserves (StaticStorage.initial storage before) freed ∧
      CReadOnly.Preserves before (StaticStorage.initial storage before) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling (FactoryArguments.signature kind).name (FactoryArguments.arguments kind args)
          (StaticStorage.initial storage before) .done) behavior ↔
        behavior = .terminates (trace.map tag) ⟨.pointer (some (storage.instances.index slot.val)), live⟩) ∧
      (∀ behavior, (CCalls.Events.machine program).Behaves
        (.calling StaticRelease.function.signature.name [.pointer (some (storage.instances.index slot.val))] live .done) behavior ↔
        behavior = .terminates [tag (.write (AtomicSlots.address storage.flagsBlock slot) false)] ⟨.void, freed⟩)

theorem initial_execution (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (factories : ∀ kind, FactoryArguments.signature kind ∈ signatures)
    (release : StaticRelease.function.signature ∈ signatures) : InitialExecution model signatures := by
  intro E instances flags separate literals
  let storage := objects instances flags separate
  letI : CInterface := executionInterface storage literals
  dsimp only
  intro program tag actual identity exchange write kind args before fresh request owner
  have reserveBindings : ReservationBindings program tag :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, exchange, by rw [actual]; exact reservation_bound model signatures⟩
  have releaseBindings : StaticRelease.Bindings program tag :=
    ⟨by rw [actual]; exact release_bound model signatures unique release, rfl, rfl, rfl, rfl, rfl, rfl, write⟩
  exact StaticStorage.initial_create_release storage literals program tag identity model kind args before fresh request
    (by rw [actual]; exact factory_bound model signatures unique kind (factories kind))
    (by rw [actual]; exact identity_bound model signatures) reserveBindings releaseBindings owner

/-- Existing proof-side routine contracts can all be satisfied in the actual
definition table. This is nonvacuity, not certification of native libc/atomics. -/
def BindingsExist (model : Solve.FMI3Model source) (signatures : List Signature) : Prop :=
  ∀ (E : Type) (instances flags : Nat) (separate : instances ≠ flags) (literals : CLiteralAddresses)
    (tag : CAtomicBoolean.Calls.Event → E),
    letI : CInterface := executionInterface (objects instances flags separate) literals
    ∃ program : CCalls.Events.Program E,
      program.internal = LiteralPreparation.program model signatures ∧
      Identity.Bindings program ∧ ReservationBindings program tag ∧ StaticRelease.Bindings program tag

structure FunctionContract (model : Solve.FMI3Model source) (signatures : List Signature) (text : String) : Prop where
  printed : text = StaticStorage.render StaticStorage.deploymentCapacity
  located : ∃ before after, Runtime.render model signatures = before ++ text ++ after
  declarationSyntax : ∃ modelTokens instanceTokens arrayTokens flagTokens countTokens,
    CObject.RecordPhrase StaticStorage.headerTypedefs modelTokens StaticStorage.modelRecord ∧
    CObject.RecordPhrase StaticStorage.modelTypedefs instanceTokens StaticStorage.instanceRecord ∧
    CObject.ArrayPhrase StaticStorage.typedefs arrayTokens (StaticStorage.instances StaticStorage.deploymentCapacity) ∧
    CObject.ArrayPhrase StaticStorage.typedefs flagTokens (StaticStorage.flags StaticStorage.deploymentCapacity) ∧
    CObject.ConstantPhrase StaticStorage.typedefs countTokens (StaticStorage.count StaticStorage.deploymentCapacity) ∧
    ∀ rest, CTokens.Prefix (text.toList ++ rest)
      (modelTokens ++ instanceTokens ++ arrayTokens ++ flagTokens ++ countTokens) rest
  records :
    (∃ fields, CObject.FieldsMean StaticStorage.headerTypes StaticStorage.modelRecord.fields fields ∧
      StaticStorage.modelShape = .record fields) ∧
    (∃ fields, CObject.FieldsMean StaticStorage.modelTypes StaticStorage.instanceRecord.fields fields ∧
      StaticStorage.instanceShape = .record fields)
  capacityPositive : 0 < StaticStorage.deploymentCapacity
  capacityLiteral : StaticStorage.deploymentCapacity < 2^31
  execution : InitialExecution model signatures
  bindings : BindingsExist model signatures

theorem rendered_contract (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (factories : ∀ kind, FactoryArguments.signature kind ∈ signatures)
    (release : StaticRelease.function.signature ∈ signatures)
    (fresh : ExternalNamesFresh signatures) :
    FunctionContract model signatures (StaticStorage.render StaticStorage.deploymentCapacity) := by
  refine ⟨rfl, declarations_located model signatures, StaticStorage.printed (by decide +kernel),
    StaticStorage.records_mean, by decide +kernel, by decide +kernel,
    initial_execution model signatures unique factories release, ?_⟩
  intro E instances flags separate literals tag
  exact bindings_exist (objects instances flags separate) literals model signatures unique release fresh tag

/-- Nonvacuity of the artifact's linked program already forces the actual
release definition. No execution of a release call is assumed here. -/
theorem FunctionContract.release_defined
    (contract : FunctionContract model signatures text) :
    (LiteralPreparation.program model signatures).definitions
      StaticRelease.function.signature.name = some (.tree StaticRelease.function) := by
  let literals : CLiteralAddresses := fun _ => none
  let storage := objects 0 1 (by decide)
  letI : CInterface := StaticFactory.executionInterface storage literals
  obtain ⟨program, actual, _, _, release⟩ := contract.bindings Unit 0 1 (by decide) literals (fun _ => ())
  have defined := release.defined
  rw [actual] at defined
  exact defined

end Rumoca.FMI3.StaticRuntime
