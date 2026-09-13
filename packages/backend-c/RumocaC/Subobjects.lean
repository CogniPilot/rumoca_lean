import RumocaC.Memory

/-! Structural separation of indexed C aggregate subobjects. These address
facts preserve both the enclosing array index and the index within a member
array. Valid native objects, bounds, layout and lifetimes remain premises of
the target profile; symbolic separation does not establish them. -/
namespace Rumoca.CMemory

variable {p q a b : Address}

/-- A strict member descendant of a record, at any nested member depth and
local array offset. Native leaf types and array bounds are separate. -/
def Address.InRecord (record cell : Address) : Prop :=
  cell.block = record.block ∧ ∃ name tail,
    cell.members = record.members ++ (record.offset, name) :: tail

theorem Address.member_in_record (p : Address) (name : String) : p.InRecord (p.member name) :=
  ⟨rfl, name, [], rfl⟩

theorem Address.InRecord.member (inside : p.InRecord q) (name : String) :
    p.InRecord (q.member name) := by
  obtain ⟨block, field, tail, path⟩ := inside
  refine ⟨block, field, tail ++ [(q.offset, name)], ?_⟩
  simp [Address.member, path, List.append_assoc]

theorem Address.InRecord.index (inside : p.InRecord q) (i : Nat) : p.InRecord (q.index i) :=
  inside

/-- Any member descendants of different enclosing array elements are separate,
including differently nested fields and tensor cells. -/
theorem Address.records_separate (base : Address) (i j : Nat) (different : i ≠ j)
    (left : (base.index i).InRecord a) (right : (base.index j).InRecord b) : a ≠ b := by
  intro same
  subst b
  obtain ⟨_, leftName, leftTail, leftPath⟩ := left
  obtain ⟨_, rightName, rightTail, rightPath⟩ := right
  have paths := List.append_cancel_left (leftPath.symm.trans rightPath)
  have offsets := congrArg Prod.fst (List.cons.inj paths).1
  exact different (Nat.add_left_cancel offsets)

/-- Both index levels and the member name are independently recoverable. -/
theorem Address.member_index_eq_iff (p : Address) (i j k l : Nat) (a b : String) :
    ((p.index i).member a).index j = ((p.index k).member b).index l ↔
      i = k ∧ a = b ∧ j = l := by
  cases p
  simp [Address.index, Address.member, Address.mk.injEq, and_assoc]

/-- Member arrays in distinct enclosing elements never share a cell. -/
theorem Address.instances_separate (p : Address) (i k : Nat) (different : i ≠ k)
    (a b : String) (j l : Nat) :
    ((p.index i).member a).index j ≠ ((p.index k).member b).index l := by
  intro same
  exact different ((member_index_eq_iff p i j k l a b).mp same).1

theorem Address.fields_separate (p : Address) (a b : String) (different : a ≠ b)
    (i j : Nat) : (p.member a).index i ≠ (p.member b).index j := by
  intro same
  have fields := congrArg Address.members same
  simp only [Address.index, Address.member] at fields
  exact different (congrArg Prod.snd (List.singleton_inj.mp (List.append_cancel_left fields)))

/-- A successful actual cell store in one record preserves all cells in another
record in the same array. This supplies the frame step for instance methods. -/
theorem store_other_record (stored : store before address value = some after)
    (base : Address) (i j : Nat) (different : i ≠ j)
    (destination : (base.index i).InRecord address)
    (other : (base.index j).InRecord query) : after query = before query :=
  store_frame before address value after stored query
    (Ne.symm (Address.records_separate base i j different destination other))

end Rumoca.CMemory
