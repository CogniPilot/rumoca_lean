import RumocaC.Memory

/-! Selected C11 sequentially consistent atomic Boolean operations. Each
transition is indivisible in this reference semantics. Connecting it to actual
standard-library bindings and concurrent C calls is a separate obligation.
Ordinary loads/stores cannot operate on these cells. Native lock freedom,
layout and static initialization require their own artifact/profile evidence. -/
namespace Rumoca.CAtomicBoolean
open CMemory

def value (b : Bool) : Value := .integer (if b then 1 else 0)

def decode : Value → Option Bool
  | .integer 0 => some false
  | .integer 1 => some true
  | _ => none

def cell (b : Bool) : Cell := ⟨.atomicBoolean, true, some (value b)⟩

def read (heap : Heap) (p : Address) : Option Bool := do
  let entry ← heap p
  if entry.type ≠ .atomicBoolean || !entry.writable then none
  else decode (← entry.value)

def exchange (heap : Heap) (p : Address) (next : Bool) : Option (Bool × Heap) := do
  let old ← read heap p
  return (old, replace heap p (cell next))

def write (heap : Heap) (p : Address) (next : Bool) : Option Heap := do
  let _ ← read heap p
  return replace heap p (cell next)

@[simp] theorem decode_value (b : Bool) : decode (value b) = some b := by
  cases b <;> rfl

theorem value_injective : Function.Injective value := by
  intro a b equal
  simpa only [decode_value, Option.some.injEq] using congrArg decode equal

theorem decode_iff : decode v = some b ↔ v = value b := by
  cases v <;> cases b <;> simp [decode, value]
  all_goals split <;> simp_all

theorem read_iff : read heap p = some b ↔ heap p = some (cell b) := by
  unfold read
  cases heap p with
  | none => simp
  | some entry =>
      cases entry with
      | mk type writable stored =>
          cases stored with
          | none => simp [cell]
          | some v =>
              cases writable <;> simp [cell, decode_iff]

theorem exchange_iff : exchange before p next = some (old, after) ↔
    before p = some (cell old) ∧ after = replace before p (cell next) := by
  simp only [exchange, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq, Prod.mk.injEq, read_iff]
  constructor
  · rintro ⟨old, found, rfl, rfl⟩
    exact ⟨found, rfl⟩
  · rintro ⟨found, rfl⟩
    exact ⟨old, found, rfl, rfl⟩

theorem write_iff : write before p next = some after ↔
    (∃ old, before p = some (cell old)) ∧ after = replace before p (cell next) := by
  simp only [write, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq, read_iff]
  constructor
  · rintro ⟨old, found, rfl⟩
    exact ⟨⟨old, found⟩, rfl⟩
  · rintro ⟨⟨old, found⟩, rfl⟩
    exact ⟨old, found, rfl⟩

theorem exchange_reads (step : exchange before p next = some (old, after)) :
    read after p = some next := by
  rw [read_iff, (exchange_iff.mp step).2]
  exact replace_at _ _ _

theorem exchange_frame (step : exchange before p next = some (old, after)) (different : q ≠ p) :
    after q = before q := by
  rw [(exchange_iff.mp step).2]
  exact replace_other _ _ _ _ different

/-- Replacing an atomic value with itself still emits an exchange operation,
but does not change any cell in the value-level memory projection. -/
theorem exchange_same (found : before p = some (cell next)) :
    exchange before p next = some (next, before) := by
  apply exchange_iff.mpr
  refine ⟨found, ?_⟩
  funext q
  by_cases same : q = p
  · subst q; simpa only [replace_at] using found
  · simp only [replace_other _ _ _ _ same]

theorem write_reads (step : write before p next = some after) : read after p = some next := by
  rw [read_iff, (write_iff.mp step).2]
  exact replace_at _ _ _

theorem write_frame (step : write before p next = some after) (different : q ≠ p) :
    after q = before q := by
  rw [(write_iff.mp step).2]
  exact replace_other _ _ _ _ different

theorem ordinary_load_unsupported (found : heap p = some (cell b)) : load heap p = none := by
  simp [load, found, cell, convert]

theorem ordinary_store_unsupported (found : heap p = some (cell b)) : store heap p v = none := by
  simp [store, found, cell, convert]

end Rumoca.CAtomicBoolean
