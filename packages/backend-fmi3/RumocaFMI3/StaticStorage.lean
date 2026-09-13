import RumocaFMI3.StaticStorageCode
import RumocaFMI3.StaticFactoryEnvironment
import RumocaFMI3.StaticFactoryCreation
import RumocaC.ObjectDeclarationSemantics

/-! Interpret the actual structured FMI storage declarations, and derive the
typed fields/clear flags required by static creation. Type spellings are
interpreted in the selected C/FMI profile. This is program-startup semantics;
it emits no initialization loop and performs no runtime allocation. Native
layout/header correspondence and the production emitter cutover remain open. -/
noncomputable section
namespace Rumoca.FMI3.StaticStorage
open CObject CMemory

/-- Meanings of the already-defined external scalar typedefs. These are the
same selected header meanings as execution, with the atomic object type added. -/
def headerTypes : CObject.Types
  | "atomic_bool" => some (.scalar .atomicBoolean)
  | name => Shape.scalar <$> StaticFactory.objectTypes name

def modelShape : Shape := (modelRecord.resolve headerTypes).get (by decide +kernel)

def modelTypes (name : String) : Option Shape :=
  if name = modelRecord.name then some modelShape else headerTypes name

def instanceShape : Shape := (instanceRecord.resolve modelTypes).get (by decide +kernel)

def types (name : String) : Option Shape :=
  if name = instanceRecord.name then some instanceShape else modelTypes name

theorem model_resolves : modelRecord.resolve headerTypes = some modelShape := rfl
theorem instance_resolves : instanceRecord.resolve modelTypes = some instanceShape := rfl

theorem records_mean :
    (∃ fields, FieldsMean headerTypes modelRecord.fields fields ∧ modelShape = .record fields) ∧
    (∃ fields, FieldsMean modelTypes instanceRecord.fields fields ∧ instanceShape = .record fields) :=
  ⟨(record_resolves _ _ _).mp model_resolves, (record_resolves _ _ _).mp instance_resolves⟩

def headerTypedefs : List String :=
  ["size_t", "fmi3Boolean", "fmi3InstanceEnvironment", "fmi3LogMessageCallback", "atomic_bool"]
def modelTypedefs : List String := modelRecord.name :: headerTypedefs
def typedefs : List String := instanceRecord.name :: modelTypedefs

private theorem named_type (name : String) (member : name ∈ names)
    (valid : CIdentifier.valid [] name = true) : CTree.Syntax.TypeSpelling names name :=
  .named (.typedefName member valid)

theorem model_printable : RecordPrintable headerTypedefs modelRecord := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro field member
  simp only [modelRecord, List.mem_cons, List.not_mem_nil, or_false] at member
  subst field
  exact ⟨.named (.primitive (by decide +kernel)), by decide +kernel⟩

theorem instance_printable : RecordPrintable modelTypedefs instanceRecord := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro field member
  simp only [instanceRecord, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    refine ⟨?_, by decide +kernel⟩
    first
    | exact .named (.primitive (by decide +kernel))
    | exact named_type _ (by decide +kernel) (by decide +kernel)

theorem instances_printable (positive : 0 < capacity) : ArrayPrintable typedefs (instances capacity) := by
  dsimp only [ArrayPrintable, instances]
  exact ⟨named_type _ (by decide +kernel) (by decide +kernel), by decide +kernel, positive⟩

theorem flags_printable (positive : 0 < capacity) : ArrayPrintable typedefs (flags capacity) := by
  dsimp only [ArrayPrintable, flags]
  exact ⟨named_type _ (by decide +kernel) (by decide +kernel), by decide +kernel, positive⟩

theorem count_printable (capacity : Nat) : ConstantPrintable typedefs (count capacity) := by
  dsimp only [ConstantPrintable, count]
  exact ⟨named_type _ (by decide +kernel) (by decide +kernel), by decide +kernel⟩

/-- Independent phrases use the typedef context at each declaration, and one
token witness consumes the entire rendered storage section in any continuation. -/
theorem printed (positive : 0 < capacity) :
    ∃ modelTokens instanceTokens arrayTokens flagTokens countTokens,
      RecordPhrase headerTypedefs modelTokens modelRecord ∧
      RecordPhrase modelTypedefs instanceTokens instanceRecord ∧
      ArrayPhrase typedefs arrayTokens (instances capacity) ∧
      ArrayPhrase typedefs flagTokens (flags capacity) ∧
      ConstantPhrase typedefs countTokens (count capacity) ∧
      ∀ rest, CTokens.Prefix ((render capacity).toList ++ rest)
        (modelTokens ++ instanceTokens ++ arrayTokens ++ flagTokens ++ countTokens) rest := by
  obtain ⟨mt, mp, ml⟩ := record_renders model_printable
  obtain ⟨it, ip, il⟩ := record_renders instance_printable
  obtain ⟨arrayTokens, ap, al⟩ := array_renders (instances_printable positive)
  obtain ⟨ft, fp, fl⟩ := array_renders (flags_printable positive)
  obtain ⟨ct, cp, cl⟩ := constant_renders (count_printable capacity)
  refine ⟨mt, it, arrayTokens, ft, ct, mp, ip, ap, fp, cp, ?_⟩
  intro rest
  simpa only [render, String.toList_append, List.append_assoc] using
    (ml _).append ((il _).append ((al _).append ((fl _).append (cl rest))))

def initialInstances (objects : StaticFactory.Objects) (before : Heap) : Heap :=
  CObject.initial before instanceShape objects.instancesBlock (instances objects.capacity).count

def initial (objects : StaticFactory.Objects) (before : Heap) : Heap :=
  CObject.initial (initialInstances objects before) (.scalar .atomicBoolean)
    objects.flagsBlock (flags objects.capacity).count

theorem initial_member (objects : StaticFactory.Objects) (before : Heap) (i : Fin objects.capacity)
    (typed : instanceShape.leaf ((0, name) :: rest) offset = some type) :
    initial objects before ⟨objects.instancesBlock, (i.val, name) :: rest, offset⟩ = some (zeroCell type) := by
  rw [initial, CObject.initial_other_block objects.separate]
  exact CObject.initial_member before instanceShape objects.instancesBlock objects.capacity i typed

theorem initial_fields (objects : StaticFactory.Objects) (before : Heap) (i : Fin objects.capacity) :
    InstanceSlot.Storage (initial objects before) (objects.instances.index i.val) := by
  have writable {p : Address} {type : CType} (found : initial objects before p = some (zeroCell type)) :
      Reset.Writable (initial objects before) p type := ⟨_, found⟩
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals
    apply writable
    simp only [StaticFactory.Objects.instances, Address.index, Address.member,
      StateProofs.stateAddress, List.nil_append, List.cons_append, Nat.zero_add]
    exact initial_member objects before i (by rfl)

theorem initial_flags (objects : StaticFactory.Objects) (before : Heap) (i : Fin objects.capacity) :
    initial objects before (objects.flags.index i.val) = some (CAtomicBoolean.cell false) := by
  simpa only [initial, flags, StaticFactory.Objects.flags, Address.index, Nat.zero_add] using
    CObject.initial_scalar (initialInstances objects before) .atomicBoolean objects.flagsBlock objects.capacity i

theorem initial_ready (objects : StaticFactory.Objects) (before : Heap) :
    StaticFactory.CreationStorage (initial objects before) objects.instances objects.flags objects.capacity :=
  ⟨initial_fields objects before, fun i inside => ⟨false, initial_flags objects before ⟨i, inside⟩⟩, objects.bounded⟩

theorem initial_owners (objects : StaticFactory.Objects) (before : Heap) :
    SlotOwners.Represents objects.flagsBlock (initial objects before) (fun _ : Fin objects.capacity => none) := by
  intro slot
  simpa only [StaticFactory.Objects.flags, Address.index, Nat.zero_add, AtomicSlots.address,
    SlotOwners.occupied] using initial_flags objects before slot

/-- The declaration product and execution environment agree on all three
global symbols, their array extents, and the immutable capacity value. Literal
integer representability in native C is a separate profile constraint. -/
theorem symbol_bindings (objects : StaticFactory.Objects) :
    StaticFactory.objectConstants objects (instances objects.capacity).name = some (.pointer (some objects.instances)) ∧
    StaticFactory.objectConstants objects (flags objects.capacity).name = some (.pointer (some objects.flags)) ∧
    StaticFactory.objectConstants objects (count objects.capacity).name = some (.integer (count objects.capacity).value) ∧
    (instances objects.capacity).count = objects.capacity ∧ (flags objects.capacity).count = objects.capacity ∧
    types (instances objects.capacity).type = some instanceShape ∧
    types (flags objects.capacity).type = some (.scalar .atomicBoolean) ∧
    types (count objects.capacity).type = some (.scalar .size) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem capacity_conversion (objects : StaticFactory.Objects) :
    convert .size (.integer (count objects.capacity).value) = some (.integer objects.capacity) :=
  CLoops.convert_size_nat objects.capacity objects.bounded

structure Fresh (objects : StaticFactory.Objects) (before : Heap) : Prop where
  instances : ∀ p, p.block = objects.instancesBlock → before p = none
  flags : ∀ p, p.block = objects.flagsBlock → before p = none

theorem instances_fresh (fresh : Fresh objects before)
    (typed : cellType instanceShape objects.instancesBlock objects.capacity p = some type) : before p = none :=
  fresh.instances p (cellType_block typed)

theorem flags_fresh (fresh : Fresh objects before)
    (typed : cellType (.scalar .atomicBoolean) objects.flagsBlock objects.capacity p = some type) :
    initialInstances objects before p = none := by
  have block := cellType_block typed
  have different : p.block ≠ objects.instancesBlock := by rw [block]; exact Ne.symm objects.separate
  rw [initialInstances, CObject.initial_other_block different, fresh.flags p block]

theorem initial_preserves (fresh : Fresh objects before) : CReadOnly.Preserves before (initial objects before) := by
  intro p entry found readonly
  have first := CObject.initial_readonly (fun p type typed => instances_fresh fresh typed) p entry found readonly
  exact CObject.initial_readonly (fun p type typed => flags_fresh fresh typed) p entry first readonly

/-- Both printed array declarations initialize their own fresh object domains;
the second preserves the first and every pre-existing read-only object. The
same resulting heap establishes factory readiness and vacant ownership. -/
theorem declarations_initialize (objects : StaticFactory.Objects) (before : Heap) (fresh : Fresh objects before) :
    Renders (RecordPhrase headerTypedefs) Record.render modelRecord ∧
    Renders (RecordPhrase modelTypedefs) Record.render instanceRecord ∧
    Renders (ArrayPhrase typedefs) StaticArray.render (instances objects.capacity) ∧
    Renders (ArrayPhrase typedefs) StaticArray.render (flags objects.capacity) ∧
    Renders (ConstantPhrase typedefs) Constant.render (count objects.capacity) ∧
    ArrayInitializes types (instances objects.capacity) objects.instancesBlock before (initialInstances objects before) ∧
    ArrayInitializes types (flags objects.capacity) objects.flagsBlock (initialInstances objects before) (initial objects before) ∧
    StaticFactory.CreationStorage (initial objects before) objects.instances objects.flags objects.capacity ∧
    SlotOwners.Represents objects.flagsBlock (initial objects before) (fun _ : Fin objects.capacity => none) ∧
    CReadOnly.Preserves before (initial objects before) := by
  have positive : 0 < objects.capacity := lt_of_lt_of_le (by decide +kernel : 0 < 2) objects.multiple
  exact ⟨record_renders model_printable, record_renders instance_printable,
    array_renders (instances_printable positive), array_renders (flags_printable positive),
    constant_renders (count_printable objects.capacity),
    array_initializes (by rfl) (fun _ _ typed => instances_fresh fresh typed),
    array_initializes (by rfl) (fun _ _ typed => flags_fresh fresh typed),
    initial_ready objects before, initial_owners objects before, initial_preserves fresh⟩

end Rumoca.FMI3.StaticStorage
