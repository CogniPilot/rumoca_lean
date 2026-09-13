import RumocaC.LiteralStorage

/-! Null-terminated strings read from the existing C character-object memory.
Caller buffers may be writable; literal storage is a reusable special case.
The content excludes the terminating zero and cannot contain an earlier zero.
Native object validity, eight-bit character representation and library binding
remain explicit target-profile obligations. -/
namespace Rumoca.CStringMemory
open CMemory

inductive Contents (heap : Heap) : Address → List UInt8 → Prop where
  | nil {base : Address} (terminator : CLiteral.readByte heap base = some 0) : Contents heap base []
  | cons {base : Address} {byte : UInt8} {bytes : List UInt8}
      (nonzero : byte ≠ 0) (head : CLiteral.readByte heap base = some byte)
      (tail : Contents heap (base.index 1) bytes) : Contents heap base (byte :: bytes)

theorem Contents.unique (first : Contents heap base left) (second : Contents heap base right) : left = right := by
  induction first generalizing right with
  | nil zero =>
    cases second with
    | nil => rfl
    | cons nonzero head tail => exact False.elim (nonzero (Option.some.inj (head.symm.trans zero)))
  | cons nonzero head tail ih =>
    cases second with
    | nil zero => exact False.elim (nonzero (Option.some.inj (head.symm.trans zero)))
    | cons otherNonzero otherHead otherTail =>
      have same := Option.some.inj (head.symm.trans otherHead)
      exact congrArg₂ List.cons same (ih otherTail)

theorem Contents.nonzero (stored : Contents heap base bytes) : ∀ byte ∈ bytes, byte ≠ 0 := by
  induction stored with
  | nil => simp
  | cons nonzero head tail ih => simpa only [List.mem_cons, forall_eq_or_imp] using And.intro nonzero ih

private theorem index_successor (base : Address) (index : Nat) :
    (base.index 1).index index = base.index (index + 1) := by
  cases base
  simp [Address.index, Nat.add_comm, Nat.add_left_comm]

/-- An indexed byte/object contract constructs the terminating string relation;
it is not a premise that a C string routine has already executed successfully. -/
theorem of_indexed (nonzero : ∀ byte ∈ bytes, byte ≠ 0)
    (read : ∀ index byte, (bytes ++ [0])[index]? = some byte →
      CLiteral.readByte heap (base.index index) = some byte) : Contents heap base bytes := by
  induction bytes generalizing base with
  | nil => exact .nil (by simpa using read 0 0 (by simp))
  | cons byte bytes ih =>
    refine .cons (nonzero byte (by simp)) (by simpa using read 0 byte (by simp)) ?_
    apply ih (fun b member => nonzero b (by simp [member]))
    intro index b found
    rw [index_successor]
    exact read (index + 1) b (by simpa using found)

theorem of_literal (stored : CLiteral.Stored signed heap base source)
    (nonzero : ∀ byte ∈ source.toUTF8.data.toList, byte ≠ 0) :
    Contents heap base source.toUTF8.data.toList :=
  of_indexed nonzero (fun _ _ found => stored.read_byte found)

end Rumoca.CStringMemory
