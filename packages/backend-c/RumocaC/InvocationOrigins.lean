import RumocaC.InvocationLedger

namespace Rumoca.CCalls.Host.Recording
open CTree CMemory

def Started (thread : Nat) (call : Invocation) (tick : Tick E) : Prop :=
  tick.thread = thread ∧ tick.action = .invoke call.name call.args ∧ tick.origin = some call

theorem advance_origin (found : (advance ledger thread action).active tracked = some call) :
    ledger.active tracked = some call ∨ Started tracked call (stamp ledger thread action) := by
  cases action with
  | invoke name args =>
    by_cases same : tracked = thread
    · subst tracked
      simp only [advance, bind, ↓reduceIte, Option.some.injEq] at found
      subst call
      exact Or.inr ⟨rfl, rfl, rfl⟩
    · exact Or.inl (by simpa only [advance, bind, if_neg same] using found)
  | complete value =>
    by_cases same : tracked = thread
    · subst tracked
      simp [advance, bind] at found
    · exact Or.inl (by simpa only [advance, bind, if_neg same] using found)
  | execute | memory => exact Or.inl found

variable [CInterface] {E : Type} {program : Events.Program E}

/-- A retained descriptor belongs to the initial ledger or to an actual
earlier invocation on that same thread, including its exact name and arguments. -/
theorem history_origin (path : Transition.Events.Reaches (Step program policy) before ticks after)
    (found : after.ledger.active thread = some call) :
    before.ledger.active thread = some call ∨ ∃ tick ∈ ticks, Started thread call tick := by
  induction path with
  | refl => exact Or.inl found
  | next first rest ih =>
    rcases ih found with previous | ⟨tick, member, started⟩
    · cases first with
      | record actual =>
        rcases advance_origin previous with prior | started
        · exact Or.inl prior
        · exact Or.inr ⟨_, List.mem_append_left _ List.mem_cons_self, started⟩
    · exact Or.inr ⟨tick, List.mem_append_right _ member, started⟩

theorem history_unique_ids (path : Transition.Events.Reaches (Step program policy) before ticks after) :
    (issued ticks).Nodup := by
  rw [(history_issued path).2]
  exact List.nodup_range'

theorem history_ordered_ids (path : Transition.Events.Reaches (Step program policy) before ticks after) :
    (issued ticks).Pairwise (· < ·) := by
  rw [(history_issued path).2]
  exact List.pairwise_lt_range'

/-- A completion observation has an earlier matching invocation descriptor.
The recorded origin is derived from an actual host completion and its prefix;
it is not a handle, lease or successful-creation annotation supplied by a caller. -/
theorem completion_origin
    (path : Transition.Events.Reaches (Step program policy) ⟨⟨heap, fun _ => none⟩, initial⟩ ticks before)
    (actual : Host.Step program policy before.runtime thread (.complete value) after) :
    ∃ call, origin (E := E) before.ledger thread (.complete value) = some call ∧
      call.serial < before.ledger.next ∧ ∃ tick ∈ ticks, Started thread call tick := by
  obtain ⟨aligned, fresh⟩ := history_invariants path (initial_aligned heap) initial_fresh
  obtain ⟨⟨result, found, _⟩, _⟩ := Host.complete_iff.mp actual
  obtain ⟨call, active⟩ := aligned_active aligned found
  refine ⟨call, active, fresh thread call active, ?_⟩
  rcases history_origin path active with absent | started
  · contradiction
  · exact started

end Rumoca.CCalls.Host.Recording
