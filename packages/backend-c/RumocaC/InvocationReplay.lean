import RumocaC.InvocationLedger

noncomputable section
namespace Rumoca.CCalls.Host.Recording
open CTree CMemory

/-- Invocation identities depend only on the actual public action sequence.
They do not depend on an arbitrarily selected recording witness. -/
def replay (ledger : Ledger) (actions : List (Nat × Host.Action E)) : Ledger :=
  actions.foldl (fun current action => advance current action.1 action.2) ledger

variable [CInterface] {E : Type}

theorem history_replay
    (path : Transition.Events.Reaches (Step program policy) before ticks after) :
    after.ledger = replay before.ledger (erase ticks) := by
  induction path with
  | refl => rfl
  | next first rest ih =>
    cases first with
    | record actual =>
      simpa [replay, erase, stamp, List.foldl_append] using ih

/-- Independent proofs over the same raw host actions necessarily use the
same final invocation ledger, including the active serial on each thread. -/
theorem history_same_ledger
    (left : Transition.Events.Reaches (Step (E := E) program policy) before leftTicks leftAfter)
    (right : Transition.Events.Reaches (Step program policy) before rightTicks rightAfter)
    (same : erase leftTicks = erase rightTicks) : leftAfter.ledger = rightAfter.ledger := by
  rw [history_replay left, history_replay right, same]

end Rumoca.CCalls.Host.Recording
