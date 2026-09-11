import RumocaC.LiteralInterfaceCalls
import RumocaC.Identifier

/-! Checked named string objects. Names and symbolic block slots are distinct;
the compiler validates candidates before any text is emitted. This module
does not allocate native storage or decide header/layout correspondence. -/
namespace Rumoca.CLiteral
open CMemory
variable {reserved : List String}

structure Entry where
  name : String
  text : String
  slot : Nat
  deriving Repr, DecidableEq

def Entry.address (entry : Entry) (firstBlock : Nat) : Address :=
  ⟨firstBlock + entry.slot, [], 0⟩

def lookup {α : Type} [BEq α] (key : Entry → α) (entries : List Entry) (value : α) : Option Entry :=
  entries.find? (fun entry => key entry == value)

section Lookup
variable {α : Type} [BEq α] [LawfulBEq α]
variable {key : Entry → α} {entries : List Entry} {value : α} {entry : Entry}

omit [LawfulBEq α] in
theorem lookup_mem (found : lookup key entries value = some entry) : entry ∈ entries :=
  List.mem_of_find?_eq_some found

theorem lookup_key (found : lookup key entries value = some entry) : key entry = value := by
  simpa only [beq_iff_eq] using List.find?_some found

theorem lookup_of_mem (unique : (entries.map key).Nodup) (member : entry ∈ entries) :
    lookup key entries (key entry) = some entry := by
  induction entries with
  | nil => contradiction
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with rfl | member
      · simp [lookup]
      · have different : key head ≠ key entry := by
          intro same
          exact unique.1 (List.mem_map.mpr ⟨entry, member, same.symm⟩)
        simpa [lookup, different] using ih unique.2 member

end Lookup

def PoolValid (reserved : List String) (entries : List Entry) : Prop :=
  (entries.map Entry.name).Nodup ∧ (entries.map Entry.text).Nodup ∧
  (entries.map Entry.slot).Nodup ∧
  entries.all (fun entry => CIdentifier.valid ("isfinite" :: reserved) entry.name &&
    decide (entry.name.length ≤ 63)) = true

instance (reserved : List String) (entries : List Entry) : Decidable (PoolValid reserved entries) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

structure Pool (reserved : List String) where
  entries : List Entry
  valid : PoolValid reserved entries

def Pool.check (reserved : List String) (entries : List Entry) : Option (Pool reserved) :=
  if valid : PoolValid reserved entries then some ⟨entries, valid⟩ else none

def candidates (texts : List String) : List Entry :=
  texts.eraseDups.mapIdx fun index text => ⟨"rumoca_literal_" ++ toString index, text, index⟩

def Pool.make (reserved texts : List String) : Option (Pool reserved) :=
  Pool.check reserved (candidates texts)

def Pool.symbols (pool : Pool reserved) : Lowering.Symbols :=
  fun text => (lookup Entry.text pool.entries text).map Entry.name

def Pool.addresses (pool : Pool reserved) (firstBlock : Nat) : CLiteralAddresses :=
  fun text => (lookup Entry.text pool.entries text).map (fun entry => entry.address firstBlock)

def Pool.globals (pool : Pool reserved) (firstBlock : Nat) : String → Option Value :=
  fun name => (lookup Entry.name pool.entries name).map (fun entry => .pointer (some (entry.address firstBlock)))

theorem Pool.entry_valid (pool : Pool reserved) (member : entry ∈ pool.entries) :
    CIdentifier.valid ("isfinite" :: reserved) entry.name = true ∧ entry.name.length ≤ 63 := by
  have checked := List.all_eq_true.mp pool.valid.2.2.2 entry member
  simpa only [Bool.and_eq_true, decide_eq_true_eq] using checked

theorem Pool.entry_fresh (pool : Pool reserved) (member : entry ∈ pool.entries) :
    entry.name ≠ "isfinite" ∧ entry.name ∉ reserved := by
  have checked := (pool.entry_valid member).1
  unfold CIdentifier.valid at checked
  split at checked
  · contradiction
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at checked
    have excluded : entry.name ∉ CIdentifier.keywords ++ "isfinite" :: reserved := by
      intro member
      have contained : (CIdentifier.keywords ++ "isfinite" :: reserved).contains entry.name = true :=
        List.contains_iff_mem.mpr member
      rw [checked.2] at contained
      contradiction
    simp only [List.mem_append, List.mem_cons, not_or] at excluded
    exact excluded.2

theorem Pool.noIntrinsic (pool : Pool reserved) : Lowering.NoIntrinsic pool.symbols := by
  intro text name named
  simp only [Pool.symbols, Option.map_eq_some_iff] at named
  obtain ⟨entry, found, rfl⟩ := named
  exact (pool.entry_fresh (lookup_mem found)).1

theorem Pool.global_binding (pool : Pool reserved) (firstBlock : Nat)
    (named : pool.symbols text = some name) :
    pool.globals firstBlock name =
      (pool.addresses firstBlock text).map (fun address => .pointer (some address)) := by
  simp only [Pool.symbols, Option.map_eq_some_iff] at named
  obtain ⟨entry, found, rfl⟩ := named
  have byName := lookup_of_mem pool.valid.1 (lookup_mem found)
  simp only [Pool.globals, Pool.addresses, byName, found, Option.map_some]

theorem Pool.symbol_of_mem (pool : Pool reserved) (member : entry ∈ pool.entries) :
    pool.symbols entry.text = some entry.name := by
  simp only [Pool.symbols, lookup_of_mem pool.valid.2.1 member, Option.map_some]

theorem Pool.address_of_mem (pool : Pool reserved) (firstBlock : Nat) (member : entry ∈ pool.entries) :
    pool.addresses firstBlock entry.text = some (entry.address firstBlock) := by
  simp only [Pool.addresses, lookup_of_mem pool.valid.2.1 member, Option.map_some]

theorem Pool.globals_fresh (pool : Pool reserved) (firstBlock : Nat) (member : name ∈ reserved) :
    pool.globals firstBlock name = none := by
  unfold Pool.globals
  cases found : lookup Entry.name pool.entries name with
  | none => rfl
  | some entry =>
      have same := lookup_key found
      have fresh := (pool.entry_fresh (lookup_mem found)).2
      exact False.elim (fresh (same ▸ member))

theorem Pool.check_entries {entries : List Entry} (checked : Pool.check reserved entries = some pool) :
    pool.entries = entries := by
  unfold Pool.check at checked
  split at checked
  · exact congrArg Pool.entries (Option.some.inj checked).symm
  · contradiction

theorem Pool.make_entries (made : Pool.make reserved texts = some pool) :
    pool.entries = candidates texts := Pool.check_entries made

theorem candidates_texts : (∃ entry ∈ candidates texts, entry.text = text) ↔ text ∈ texts := by
  constructor
  · rintro ⟨entry, member, same⟩
    obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp member
    simp only at same
    rw [← same]
    exact List.mem_eraseDups.mp (List.getElem_mem bound)
  · intro member
    obtain ⟨index, bound, same⟩ := List.mem_iff_getElem.mp (List.mem_eraseDups.mpr member)
    refine ⟨⟨"rumoca_literal_" ++ toString index, text, index⟩, ?_, rfl⟩
    exact List.mem_mapIdx.mpr ⟨index, bound, by simp [same]⟩

/-- A successful checked construction binds exactly the requested texts,
including duplicate requests. No totality of unchecked name generation or
absence of collisions with a caller's reserved names is assumed. -/
theorem Pool.make_coverage (made : Pool.make reserved texts = some pool) :
    (∃ name, pool.symbols text = some name) ↔ text ∈ texts := by
  have entries := Pool.make_entries made
  constructor
  · rintro ⟨name, named⟩
    simp only [Pool.symbols, Option.map_eq_some_iff] at named
    obtain ⟨entry, found, rfl⟩ := named
    exact candidates_texts.mp ⟨entry, entries ▸ lookup_mem found, lookup_key found⟩
  · intro member
    obtain ⟨entry, inEntries, same⟩ := candidates_texts.mpr member
    refine ⟨entry.name, ?_⟩
    rw [← same]
    exact pool.symbol_of_mem (entries ▸ inEntries)

end Rumoca.CLiteral
