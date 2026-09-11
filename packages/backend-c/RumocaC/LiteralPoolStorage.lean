import RumocaC.LiteralPool

/-! Construct the immutable symbolic objects for a checked literal pool.
The frame theorem requires fresh blocks; this is not native allocation,
linkage, byte layout or a certificate for emitted global declarations. -/
namespace Rumoca.CLiteral
open CMemory
variable {reserved : List String}

def Pool.install (pool : Pool reserved) (before : Heap) (firstBlock : Nat)
    (signed : Bool) : Heap := fun address =>
  match lookup (fun entry => firstBlock + entry.slot) pool.entries address.block with
  | none => before address
  | some entry =>
      if address.members = [] then ((bytes entry.text)[address.offset]?).map (cell signed)
      else none

theorem Pool.blocks_unique (pool : Pool reserved) (firstBlock : Nat) :
    (pool.entries.map (fun entry => firstBlock + entry.slot)).Nodup := by
  have unique := List.Nodup.map (f := fun slot => firstBlock + slot)
    (fun _ _ same => Nat.add_left_cancel same) pool.valid.2.2.1
  simpa only [List.map_map, Function.comp_def] using unique

theorem Pool.installed (pool : Pool reserved) (before : Heap) (firstBlock : Nat)
    (signed : Bool) (member : entry ∈ pool.entries) :
    Stored signed (pool.install before firstBlock signed) (entry.address firstBlock) entry.text := by
  have found := lookup_of_mem (pool.blocks_unique firstBlock) member
  intro index byte atByte
  simp only [Pool.install, Entry.address, Address.index, found, Nat.zero_add,
    ↓reduceIte, atByte, Option.map_some]

theorem Pool.storage_valid (pool : Pool reserved) (before : Heap) (firstBlock : Nat)
    (signed : Bool) :
    Valid (pool.addresses firstBlock) signed (pool.install before firstBlock signed) := by
  intro source base bound
  simp only [Pool.addresses, Option.map_eq_some_iff] at bound
  obtain ⟨entry, found, rfl⟩ := bound
  have text := lookup_key found
  rw [← text]
  exact pool.installed before firstBlock signed (lookup_mem found)

theorem Pool.install_frame (pool : Pool reserved)
    (outside : ∀ entry ∈ pool.entries, address.block ≠ firstBlock + entry.slot) :
    pool.install before firstBlock signed address = before address := by
  unfold Pool.install
  cases found : lookup (fun entry => firstBlock + entry.slot) pool.entries address.block with
  | none => rfl
  | some entry => exact False.elim (outside entry (lookup_mem found) (lookup_key found).symm)

/-- Every pre-existing cell is retained, not only read-only cells. -/
theorem Pool.install_existing (pool : Pool reserved)
    (fresh : ∀ entry ∈ pool.entries, ∀ address,
      address.block = firstBlock + entry.slot → before address = none)
    (present : before address = some object) :
    pool.install before firstBlock signed address = some object := by
  rw [pool.install_frame, present]
  intro entry member same
  rw [fresh entry member address same] at present
  contradiction

theorem Pool.install_preserves (pool : Pool reserved)
    (fresh : ∀ entry ∈ pool.entries, ∀ address,
      address.block = firstBlock + entry.slot → before address = none) :
    CReadOnly.Preserves before (pool.install before firstBlock signed) := by
  intro address object present readonly
  exact pool.install_existing fresh present

/-- Both interfaces share the constructed literal-address map. The named
interface adds data bindings without changing header types or constants. -/
@[reducible] def Pool.interface (pool : Pool reserved) (header : CInterface)
    (firstBlock : Nat) : CInterface where
  constants := header.constants
  types := header.types
  literals := pool.addresses firstBlock

@[reducible] def Pool.namedInterface (pool : Pool reserved) (header : CInterface)
    (firstBlock : Nat) : CInterface :=
  Interface.extend (pool.interface header firstBlock) (pool.globals firstBlock)

def Pool.HeaderFresh (pool : Pool reserved) (header : CInterface) : Prop :=
  ∀ entry ∈ pool.entries, header.constants entry.name = none

theorem Pool.globalBindings (pool : Pool reserved) (header : CInterface) (firstBlock : Nat)
    (fresh : pool.HeaderFresh header) :
    @Lowering.GlobalBindings (pool.namedInterface header firstBlock) pool.symbols := by
  intro text name named
  have binding := pool.global_binding firstBlock named
  have absent : header.constants name = none := by
    simp only [Pool.symbols, Option.map_eq_some_iff] at named
    obtain ⟨entry, found, rfl⟩ := named
    exact fresh entry (lookup_mem found)
  change (header.constants name).orElse (fun _ => pool.globals firstBlock name) = _
  simpa only [absent, Option.orElse_none] using binding

theorem Pool.reserved_agreement (pool : Pool reserved) (header : CInterface) (firstBlock : Nat)
    (member : name ∈ reserved) :
    (pool.interface header firstBlock).constants name =
      (pool.namedInterface header firstBlock).constants name := by
  change header.constants name = (header.constants name).orElse (fun _ => pool.globals firstBlock name)
  rw [pool.globals_fresh firstBlock member]
  cases header.constants name <;> rfl

noncomputable section
/-- All pool objects retain their bytes after every finite execution prefix,
whether the full call will return, fail or diverge. -/
theorem Pool.storage_after_steps (pool : Pool reserved) (header : CInterface) (firstBlock : Nat)
    (before : Heap) (signed : Bool) (program : CCalls.Program)
    (steps : Transition.Reaches (@CCalls.Typed.machine (pool.namedInterface header firstBlock) program).step
      (.calling name args (pool.install before firstBlock signed) .done) state) :
    Valid (pool.addresses firstBlock) signed (CReadOnly.typedHeap state) := by
  have preserved := @CReadOnly.typed_reaches (pool.namedInterface header firstBlock) program _ _ steps
  exact (pool.storage_valid before firstBlock signed).preserved preserved

end
end Rumoca.CLiteral
