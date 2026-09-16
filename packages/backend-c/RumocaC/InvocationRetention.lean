import RumocaC.InvocationLedger

namespace Rumoca.CCalls.Host.Recording
open CTree CMemory

/-- A descriptor older than the next serial cannot have been newly issued by
this step. Thus a descriptor present afterwards was already active beforehand. -/
theorem advance_retained (found : (advance (E := E) ledger thread action).active tracked = some call)
    (earlier : call.serial < ledger.next) : ledger.active tracked = some call := by
  cases action with
  | invoke name args =>
    by_cases same : tracked = thread
    · subst tracked
      simp only [advance, bind, ↓reduceIte, Option.some.injEq] at found
      subst call
      exact False.elim (Nat.lt_irrefl _ earlier)
    · simpa only [advance, bind, if_neg same] using found
  | complete value =>
    by_cases same : tracked = thread
    · subst tracked
      simp [advance, bind] at found
    · simpa only [advance, bind, if_neg same] using found
  | execute | memory => exact found

variable [CInterface] {E : Type} {program : Events.Program E} {policy : Host.Policy}
  {before after : State}

/-- Serial monotonicity prevents a completed invocation from reappearing
later. A final old descriptor therefore belongs to every preceding suffix's
initial ledger, without a per-prefix retention annotation. -/
theorem history_retained (path : Transition.Events.Reaches (Step program policy) before ticks after)
    (earlier : call.serial < before.ledger.next)
    (found : after.ledger.active tracked = some call) : before.ledger.active tracked = some call := by
  induction path with
  | refl => exact found
  | next first rest ih =>
    cases first with
    | @record prior thread action target ledger actual =>
      have monotone : ledger.next ≤ (advance ledger thread action).next := by
        cases action <;> simp [advance]
      exact advance_retained (ih (Nat.lt_of_lt_of_le earlier monotone) found) earlier

end Rumoca.CCalls.Host.Recording
