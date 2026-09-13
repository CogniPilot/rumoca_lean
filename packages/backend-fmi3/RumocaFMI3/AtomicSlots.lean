import RumocaC.AtomicStorage
import RumocaC.AtomicScanProofs
import RumocaFMI3.StaticSlots

/-! Refinement from typed atomic flag memory to the fixed-slot reference.
These lemmas describe individual indivisible operations. The bounded scan,
caller ownership, full C calls and native bindings remain separate. -/
namespace Rumoca.FMI3.AtomicSlots
open CMemory

variable {capacity : Nat} {state : StaticSlots.State capacity}

def address (block : Nat) (slot : Fin capacity) : Address := ⟨block, [], slot.val⟩

def Represents (block : Nat) (heap : Heap) (state : StaticSlots.State capacity) : Prop :=
  ∀ slot, heap (address block slot) = some (CAtomicBoolean.cell (state slot))

theorem address_injective (block : Nat) : Function.Injective (address (capacity := capacity) block) := by
  intro a b same
  exact Fin.ext (congrArg Address.offset same)

theorem initialized (heap : Heap) (block capacity : Nat) :
    Represents block (CAtomicBoolean.initial heap block capacity) (StaticSlots.vacant (capacity := capacity)) :=
  fun slot => CAtomicBoolean.initial_at heap block capacity slot

theorem exchanged (represented : Represents block before state)
    (step : CAtomicBoolean.exchange before (address block slot) next = some (old, after)) :
    old = state slot ∧ Represents block after (StaticSlots.update state slot next) := by
  have spec := CAtomicBoolean.exchange_iff.mp step
  have same := (represented slot).symm.trans spec.1
  have values := congrArg Cell.value (Option.some.inj same)
  have oldValue : old = state slot := by
    cases old <;> cases h : state slot <;> simp [CAtomicBoolean.cell, CAtomicBoolean.value, h] at values ⊢
  refine ⟨oldValue, ?_⟩
  intro other
  by_cases eq : other = slot
  · subst other
    rw [spec.2, replace_at]
    simp [StaticSlots.update]
  · rw [CAtomicBoolean.exchange_frame step (fun same => eq (address_injective block same))]
    simpa [StaticSlots.update, eq] using represented other

theorem exchange_exists (represented : Represents block before state) (slot : Fin capacity) (next : Bool) :
    ∃ after, CAtomicBoolean.exchange before (address block slot) next = some (state slot, after) ∧
      Represents block after (StaticSlots.update state slot next) ∧ CStorage.Preserves before after ∧
      CReadOnly.Preserves before after := by
  let after := replace before (address block slot) (CAtomicBoolean.cell next)
  have step : CAtomicBoolean.exchange before (address block slot) next = some (state slot, after) :=
    CAtomicBoolean.exchange_iff.mpr ⟨represented slot, rfl⟩
  exact ⟨after, step, (exchanged represented step).2,
    CAtomicBoolean.exchange_storage step, CAtomicBoolean.exchange_readonly step⟩

theorem reserve_corresponds (represented : Represents block before state)
    (step : CAtomicBoolean.exchange before (address block slot) true = some (old, after)) :
    (StaticSlots.reserve state slot = some (StaticSlots.update state slot true) ↔ old = false) ∧
      Represents block after (StaticSlots.update state slot true) := by
  have result := exchanged represented step
  refine ⟨?_, result.2⟩
  rw [StaticSlots.reserve_iff, result.1]
  simp

theorem release_exists (represented : Represents block before state)
    (released : StaticSlots.release state slot = some next) :
    ∃ after, CAtomicBoolean.write before (address block slot) false = some after ∧
      Represents block after next ∧ CStorage.Preserves before after ∧ CReadOnly.Preserves before after := by
  obtain ⟨after, step, memory, storage, readonly⟩ := exchange_exists represented slot false
  have written := CAtomicBoolean.write_as_exchange.mpr ⟨state slot, step⟩
  rw [(StaticSlots.release_iff.mp released).2]
  exact ⟨after, written, memory, storage, readonly⟩

theorem scan_ready (represented : Represents block heap state) :
    CAtomicScan.Ready ⟨block, [], 0⟩ capacity heap := by
  intro i inside
  exact ⟨state ⟨i, inside⟩, by simpa [Address.index, address] using represented ⟨i, inside⟩⟩

/-- A successful complete sequential scan refines the independent reservation
operation and preserves every other instance's availability. -/
theorem scan_reserves (represented : Represents block before state)
    (outcome : CAtomicScan.Outcome ⟨block, [], 0⟩ capacity 0 before trace index after)
    (inside : index < capacity) :
    StaticSlots.reserve state ⟨index, inside⟩ = some (StaticSlots.update state ⟨index, inside⟩ true) ∧
      Represents block after (StaticSlots.update state ⟨index, inside⟩ true) := by
  have spec := CAtomicScan.outcome_reserved outcome inside
  have operation : CAtomicBoolean.exchange before (address block ⟨index, inside⟩) true = some (false, after) :=
    CAtomicBoolean.exchange_iff.mpr (by simpa [Address.index, address] using spec)
  have correspondence := reserve_corresponds represented operation
  exact ⟨correspondence.1.mpr rfl, correspondence.2⟩

/-- Exhaustion characterizes the supplied sequential snapshot. It is not a
claim of simultaneous global fullness for overlapping native scans. -/
theorem scan_exhausted (represented : Represents block before state)
    (outcome : CAtomicScan.Outcome ⟨block, [], 0⟩ capacity 0 before trace capacity after) :
    after = before ∧ ∀ slot, state slot = true := by
  have spec := CAtomicScan.outcome_exhausted outcome rfl
  refine ⟨spec.1, ?_⟩
  intro slot
  have occupied : before (address block slot) = some (CAtomicBoolean.cell true) := by
    simpa [Address.index, address] using spec.2 slot.val (Nat.zero_le _) slot.isLt
  have same := (represented slot).symm.trans occupied
  have stored := congrArg Cell.value (Option.some.inj same)
  exact CAtomicBoolean.value_injective (Option.some.inj stored)

end Rumoca.FMI3.AtomicSlots
