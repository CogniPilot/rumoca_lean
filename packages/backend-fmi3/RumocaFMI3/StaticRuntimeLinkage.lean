import RumocaFMI3.StaticStorageCalls
import RumocaFMI3.LiteralPreparation
import RumocaC.StringBindings

/-! The production runtime's exact definitions and selected external routines.
Creation/release are the already proved C trees. The linked program below uses
the actual rendered function table, with string and atomic contracts together.
Native libc, atomic macro expansion and ABI correspondence remain separate. -/
noncomputable section
namespace Rumoca.FMI3.StaticRuntime
open CTree CMemory StaticFactory

def objects (instances flags : Nat) (separate : instances ≠ flags) : Objects :=
  ⟨instances, flags, separate, StaticStorage.deploymentCapacity, by decide +kernel, by decide +kernel⟩

theorem factory_definition (model : Solve.FMI3Model source) (kind : Kind) :
    Runtime.function model (FactoryArguments.signature kind) = StaticFactory.function model kind := by
  cases kind <;> rfl

theorem release_definition (model : Solve.FMI3Model source) :
    Runtime.function model StaticRelease.function.signature = StaticRelease.function := rfl

theorem factory_bound (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (kind : Kind) (member : FactoryArguments.signature kind ∈ signatures) :
    (LiteralPreparation.program model signatures).definitions (FactoryArguments.signature kind).name =
      some (.tree (StaticFactory.function model kind)) := by
  have bound := LiteralPreparation.definition_bound model signatures unique
    (Runtime.function model (FactoryArguments.signature kind))
    (List.mem_append_right _ (List.mem_map.mpr ⟨_, member, rfl⟩))
  simpa only [factory_definition] using bound

theorem release_bound (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (member : StaticRelease.function.signature ∈ signatures) :
    (LiteralPreparation.program model signatures).definitions StaticRelease.function.signature.name =
      some (.tree StaticRelease.function) := by
  have bound := LiteralPreparation.definition_bound model signatures unique
    (Runtime.function model StaticRelease.function.signature)
    (List.mem_append_right _ (List.mem_map.mpr ⟨_, member, rfl⟩))
  simpa only [release_definition] using bound

theorem reservation_bound (model : Solve.FMI3Model source) (signatures : List Signature) :
    (LiteralPreparation.program model signatures).definitions CAtomicScan.function.signature.name =
      some (.tree CAtomicScan.function) :=
  LiteralPreparation.helpers_bound model signatures CAtomicScan.function (by simp [Runtime.helpers])

theorem identity_bound (model : Solve.FMI3Model source) (signatures : List Signature) :
    (LiteralPreparation.program model signatures).definitions Identity.function.signature.name =
      some (.tree Identity.function) :=
  LiteralPreparation.helpers_bound model signatures Identity.function (by simp [Runtime.helpers])

def routineNames : List String := ["atomic_exchange", "atomic_store"] ++ CStringCalls.routineNames
def ExternalNamesFresh (signatures : List Signature) : Prop :=
  ∀ sig ∈ signatures, sig.name ∉ routineNames

theorem external_undefined (model : Solve.FMI3Model source) (signatures : List Signature)
    (fresh : ExternalNamesFresh signatures) (name : String) (member : name ∈ routineNames) :
    (LiteralPreparation.program model signatures).definitions name = none := by
  have missing : (LiteralPreparation.functions model signatures).find?
      (fun fn => fn.signature.name == name) = none := by
    apply List.find?_eq_none.mpr
    intro fn belongs
    simp only [LiteralPreparation.functions, List.mem_append, List.mem_map] at belongs
    rcases belongs with helper | ⟨sig, belongs, rfl⟩
    · simp only [Runtime.helpers, List.mem_cons, List.not_mem_nil, or_false] at helper
      simp only [routineNames, CStringCalls.routineNames, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases helper with rfl | rfl | rfl | rfl | rfl <;>
        rcases member with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · have different : sig.name ≠ name := fun same => fresh sig belongs (same ▸ member)
      simpa only [Runtime.function, beq_iff_eq] using different
  simp only [LiteralPreparation.program, missing]
  simp only [routineNames, CStringCalls.routineNames, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

section
variable [interface : CInterface]

def library (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32) : String → Option (CCalls.Events.External E)
  | "atomic_exchange" => some (CAtomicBoolean.Calls.exchangeExternal tag boolean)
  | "atomic_store" => some (CAtomicBoolean.Calls.writeExternal tag)
  | name => CStringCalls.library size integer name

theorem library_names (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (found : library tag boolean size integer name = some fn) :
    name ∈ routineNames ∧ fn.signature.name = name := by
  unfold library at found
  split at found
  · cases Option.some.inj found; exact ⟨by simp [routineNames], rfl⟩
  · cases Option.some.inj found; exact ⟨by simp [routineNames], rfl⟩
  · have result := CStringCalls.library_name size integer name fn found
    exact ⟨List.mem_append_right _ result.1, result.2⟩

def linked (model : Solve.FMI3Model source) (signatures : List Signature)
    (fresh : ExternalNamesFresh signatures) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32) : CCalls.Events.Program E where
  internal := LiteralPreparation.program model signatures
  addresses := fun _ => none
  externals := library tag boolean size integer
  disjoint := fun name _fn found => external_undefined model signatures fresh name
    (library_names tag boolean size integer found).1
  names := fun _ _ found => (library_names tag boolean size integer found).2

end

/-- A nonvacuous program using the exact runtime table satisfies all three
families of bindings simultaneously, in the object environment. It does not
require a successful call, atomic outcome or implementation of a host logger. -/
theorem bindings_exist {E : Type} (storage : Objects) (literals : CLiteralAddresses) :
    letI : CInterface := executionInterface storage literals
    ∀ (model : Solve.FMI3Model source) (signatures : List Signature)
    (_unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (_release : StaticRelease.function.signature ∈ signatures)
    (_fresh : ExternalNamesFresh signatures) (tag : CAtomicBoolean.Calls.Event → E),
    ∃ program : CCalls.Events.Program E,
      program.internal = LiteralPreparation.program model signatures ∧
      Identity.Bindings program ∧ ReservationBindings program tag ∧ StaticRelease.Bindings program tag := by
  letI : CInterface := executionInterface storage literals
  intro model signatures unique release fresh tag
  let program := linked model signatures fresh tag rfl rfl rfl
  refine ⟨program, rfl, ?_, ?_, ?_⟩
  · constructor <;> rfl
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    exact reservation_bound model signatures
  · refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact release_bound model signatures unique release

theorem declarations_located (model : Solve.FMI3Model source) (signatures : List Signature) :
    ∃ before after, Runtime.render model signatures =
      before ++ StaticStorage.render StaticStorage.deploymentCapacity ++ after := by
  refine ⟨functionPrefix model.name ++ "#include \"model.c\"\n" ++ Runtime.declarationPrefix,
    "\n" ++ String.join (Runtime.helpers.map Function.render) ++
      String.join (signatures.map fun sig => (Runtime.function model sig).render), ?_⟩
  simp only [Runtime.render, Runtime.declarations, String.append_assoc]

end Rumoca.FMI3.StaticRuntime
