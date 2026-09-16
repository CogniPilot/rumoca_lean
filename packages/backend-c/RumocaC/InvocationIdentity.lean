import RumocaC.InvocationLedger

namespace Rumoca.CCalls.Host.Recording
open CTree CMemory

/-- An active serial identifies one original invocation on one thread. This
is stronger than freshness alone for an arbitrary supplied initial ledger. -/
def Unique (ledger : Ledger) : Prop :=
  ∀ left first right second, ledger.active left = some first → ledger.active right = some second →
    first.serial = second.serial → left = right ∧ first = second

theorem initial_unique : Unique initial := by
  intro left first right second found
  contradiction

/-- Computed invocation entry consumes the next fresh serial. Completion
removes its descriptor; no later reuse of a thread recycles that identity. -/
theorem advance_unique (unique : Unique ledger) (fresh : Fresh ledger)
    (thread : Nat) (action : Action E) : Unique (advance ledger thread action) := by
  intro left first right second firstActive secondActive serial
  cases action with
  | invoke name args =>
    by_cases leftNew : left = thread
    · subst left
      simp only [advance, bind, ↓reduceIte, Option.some.injEq] at firstActive
      subst first
      by_cases rightNew : right = thread
      · subst right
        simp only [advance, bind, ↓reduceIte, Option.some.injEq] at secondActive
        subst second
        exact ⟨rfl, rfl⟩
      · have old : ledger.active right = some second := by
          simpa only [advance, bind, if_neg rightNew] using secondActive
        have earlier := fresh right second old
        simp only at serial
        omega
    · have oldFirst : ledger.active left = some first := by
        simpa only [advance, bind, if_neg leftNew] using firstActive
      by_cases rightNew : right = thread
      · subst right
        simp only [advance, bind, ↓reduceIte, Option.some.injEq] at secondActive
        subst second
        have earlier := fresh left first oldFirst
        simp only at serial
        omega
      · exact unique left first right second oldFirst
          (by simpa only [advance, bind, if_neg rightNew] using secondActive) serial
  | complete value =>
    have leftOther : left ≠ thread := by
      intro same
      subst left
      simp [advance, bind] at firstActive
    have rightOther : right ≠ thread := by
      intro same
      subst right
      simp [advance, bind] at secondActive
    exact unique left first right second
      (by simpa only [advance, bind, if_neg leftOther] using firstActive)
      (by simpa only [advance, bind, if_neg rightOther] using secondActive) serial
  | execute | memory => exact unique left first right second firstActive secondActive serial

variable [CInterface] {E : Type}

/-- Active identity follows the same actual recorded history. Neither a
per-step unique-ID annotation nor a terminating public call is supplied. -/
theorem history_unique (path : Transition.Events.Reaches (Step program policy) before ticks after)
    (unique : Unique before.ledger) (fresh : Fresh before.ledger) : Unique after.ledger := by
  induction path with
  | refl => exact unique
  | next first rest ih =>
    cases first with
    | record actual => exact ih (advance_unique unique fresh _ _) (advance_fresh fresh _ _)

end Rumoca.CCalls.Host.Recording
