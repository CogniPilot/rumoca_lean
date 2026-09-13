import RumocaC.TensorMemory
import RumocaC.Subobjects

/-! Initial object-memory regions for supplied tensor storage. This specifies
valid C call-entry memory; it does not execute a native allocator. -/
namespace Rumoca.CMemory.TensorRegion
open TensorView

def Contains (base : Address) (count : Nat) (q : Address) : Prop :=
  q.block = base.block ∧ q.members = base.members ∧ base.offset ≤ q.offset ∧
    q.offset < base.offset + count

instance (base : Address) (count : Nat) (q : Address) : Decidable (Contains base count q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def place (heap : Heap) (base : Address) (shape : Rumoca.Tensor.Shape)
    (writable : Bool) (initial : Option (Values shape)) : Heap := fun q =>
  if h : Contains base shape.volume q then
    some ⟨.float64, writable, initial.map (fun values => .finite (values[q.offset - base.offset]'(by
      obtain ⟨_, _, lower, upper⟩ := h
      omega)))⟩
  else heap q

theorem contains_index (base : Address) (count i : Nat) (bound : i < count) :
    Contains base count (base.index i) := by
  exact ⟨rfl, rfl, by simp [Address.index], by simpa only [Address.index, Nat.add_lt_add_iff_left] using bound⟩

theorem contains_iff (base q : Address) (count : Nat) :
    Contains base count q ↔ ∃ i < count, q = base.index i := by
  constructor
  · rintro ⟨block, members, lower, upper⟩
    refine ⟨q.offset - base.offset, by omega, ?_⟩
    have offset : q.offset = base.offset + (q.offset - base.offset) := by omega
    cases base
    cases q
    simp only [Address.index, Address.mk.injEq]
    exact ⟨block, members, offset⟩
  · rintro ⟨i, hi, rfl⟩
    exact contains_index base count i hi

theorem place_at (heap : Heap) (base : Address) (shape : Rumoca.Tensor.Shape)
    (writable : Bool) (initial : Option (Values shape)) (i : Fin shape.volume) :
    place heap base shape writable initial (base.index i.val) =
      some ⟨.float64, writable, initial.map (fun values => .finite values[i])⟩ := by
  rw [place, dif_pos (contains_index base shape.volume i.val i.isLt)]
  simp only [Address.index, Nat.add_sub_cancel_left, Fin.getElem_fin]

theorem place_frame (heap : Heap) (base : Address) (shape : Rumoca.Tensor.Shape)
    (writable : Bool) (initial : Option (Values shape)) (q : Address)
    (outside : ∀ i < shape.volume, q ≠ base.index i) :
    place heap base shape writable initial q = heap q := by
  unfold place
  apply dif_neg
  rw [contains_iff]
  rintro ⟨i, hi, eq⟩
  exact outside i hi eq

theorem place_writable (heap : Heap) (base : Address) (shape : Rumoca.Tensor.Shape)
    (initial : Option (Values shape)) : Writable (place heap base shape true initial) base shape.volume := by
  intro i hi
  exact ⟨_, place_at heap base shape true initial ⟨i, hi⟩⟩

theorem place_reads (heap : Heap) (base : Address) (values : Values shape) (writable : Bool) :
    Reads (place heap base shape writable (some values)) base values := by
  intro i
  simp only [load, place_at, Option.map_some, bind, Option.bind_some, convert, Value.finite,
    ↓reduceIte, pure]

theorem member_separate (base : Address) (a b : String) (different : a ≠ b) (i j : Nat) :
    (base.member a).index i ≠ (base.member b).index j :=
  base.fields_separate a b different i j

/-- Distinct fields remain separate for arbitrary ranks, counts and offsets. -/
theorem place_other_member (heap : Heap) (base : Address) (a b : String) (shape : Rumoca.Tensor.Shape)
    (writable : Bool) (initial : Option (Values shape)) (different : b ≠ a) (i : Nat) :
    place heap (base.member a) shape writable initial ((base.member b).index i) =
      heap ((base.member b).index i) :=
  place_frame heap (base.member a) shape writable initial _
    (fun j _ => member_separate base b a different i j)

/-- Preparing an instance's tensor storage preserves every member element of
another instance, even when both instances are in the same outer array. -/
theorem place_other_instance (heap : Heap) (base : Address) (i j : Nat) (a b : String)
    (shape : Rumoca.Tensor.Shape) (writable : Bool) (initial : Option (Values shape))
    (different : j ≠ i) (k : Nat) :
    place heap ((base.index i).member a) shape writable initial (((base.index j).member b).index k) =
      heap (((base.index j).member b).index k) :=
  place_frame heap ((base.index i).member a) shape writable initial _
    (fun l _ => base.instances_separate j i different b a k l)

theorem separate_instances (base : Address) (i j : Nat) (different : i ≠ j)
    (a b : String) (count : Nat) :
    Separate ((base.index i).member a) ((base.index j).member b) count :=
  fun k _ l _ => base.instances_separate i j different a b k l

def scratch (heap : Heap) (base : Address) (shape : Rumoca.Tensor.Shape) : List String → Heap
  | [] => heap
  | name :: names => place (scratch heap base shape names) (base.member name) shape true none

theorem scratch_other (heap : Heap) (base : Address) (shape : Rumoca.Tensor.Shape)
    (names : List String) (name : String) (outside : name ∉ names) (i : Nat) :
    scratch heap base shape names ((base.member name).index i) = heap ((base.member name).index i) := by
  induction names with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.mem_cons, not_or] at outside
    rw [scratch, place_other_member _ _ _ _ _ _ _ outside.1, ih outside.2]

theorem scratch_at (heap : Heap) (base : Address) (shape : Rumoca.Tensor.Shape)
    (names : List String) (name : String) (member : name ∈ names) (i : Fin shape.volume) :
    scratch heap base shape names ((base.member name).index i.val) = some ⟨.float64, true, none⟩ := by
  induction names with
  | nil => simp at member
  | cons head tail ih =>
    by_cases eq : name = head
    · subst name
      exact place_at _ _ _ true none i
    · rw [scratch, place_other_member _ _ _ _ _ _ _ eq]
      exact ih ((List.mem_cons.mp member).resolve_left eq)

theorem scratch_writable (heap : Heap) (base : Address) (shape : Rumoca.Tensor.Shape)
    (names : List String) (name : String) (member : name ∈ names) :
    Writable (scratch heap base shape names) (base.member name) shape.volume :=
  fun i hi => ⟨none, scratch_at heap base shape names name member ⟨i, hi⟩⟩

end Rumoca.CMemory.TensorRegion
