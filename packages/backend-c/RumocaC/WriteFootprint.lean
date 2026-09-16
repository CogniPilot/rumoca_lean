import RumocaC.CallEvents

noncomputable section
namespace Rumoca.CWriteFootprint
open CTree CMemory CCalls
variable [CInterface]

/-- The only memory destination of an ordinary assignment; identifier targets
are locals. Failed address evaluation licenses no memory write. -/
def target (env : CBody.Locals) (heap : Heap) : Expr → Option Address
  | .id _ => none
  | expr => CBody.lvalue env heap expr

/-- Compute the possible write of the current loop instruction without
evaluating its right-hand value or enumerating an aggregate. -/
def loop : CLoops.State → Option Address
  | .running (.assign expr _ :: _) env _ heap => target env heap expr
  | _ => none

omit [CInterface] in
theorem store_outside (stored : store before address value = some after)
    (outside : address ≠ query) : after query = before query :=
  store_frame before address value after stored query
    (Ne.symm outside)

/-- Every actual loop transition preserves cells outside its computed write
address. This includes branches, loops, locals and arbitrary supported RHSs. -/
theorem loop_frame (step : CLoops.next state = some following)
    (outside : loop state ≠ some query) :
    CReadOnly.loopHeap following query = CReadOnly.loopHeap state query := by
  unfold CLoops.next at step
  split at step
  all_goals
    aesop (add safe forward store_outside)
      (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        CReadOnly.loopHeap, loop, target])

end Rumoca.CWriteFootprint

namespace Rumoca.CWriteFootprint
open CTree CMemory CCalls
variable [CInterface]

/-- A call return may write through its saved destination. Use the current
heap to resolve it, just as the existing typed call machine does. -/
def saved (heap : Heap) : Typed.Continuation → Option Address
  | .caller (.assign expr) _ env _ _ _ => target env heap expr
  | _ => none

def current : Typed.State → Option Address
  | .body state _ _ => loop state
  | .returning _ heap stack => saved heap stack
  | _ => none

theorem resume_frame (step : Typed.resume value heap stack = some following)
    (outside : saved heap stack ≠ some query) :
    CReadOnly.typedHeap following query = heap query := by
  cases stack with
  | done => cases Option.some.inj step; rfl
  | caller destination rest env types resultType outer =>
    cases destination with
    | assign expr =>
      by_cases localTarget : ∃ name, expr = Expr.id name
      · obtain ⟨name, rfl⟩ := localTarget
        simp only [Typed.resume, Option.bind_eq_bind, Option.pure_def,
          Option.bind_eq_some_iff] at step
        aesop (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
          CReadOnly.typedHeap, CReadOnly.loopHeap])
      · have notLocal : ∀ name, expr ≠ Expr.id name :=
          fun name same => localTarget ⟨name, same⟩
        have reduction : Typed.resume value heap
            (.caller (.assign expr) rest env types resultType outer) =
            (do
              let address ← CBody.lvalue env heap expr
              let after ← store heap address value
              return .body (.running rest env types after) resultType outer) := by
          cases expr <;> try rfl
          exact False.elim (notLocal _ rfl)
        rw [reduction] at step
        simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at step
        obtain ⟨address, selected, after, stored, returned⟩ := step
        cases Option.some.inj returned
        have selectedWrite : saved heap
            (.caller (.assign expr) rest env types resultType outer) = some address := by
          change target env heap expr = some address
          cases expr <;> exact selected
        exact store_outside stored (fun same => outside (selectedWrite.trans (congrArg some same)))
    | declare | discard | ret =>
      simp only [Typed.resume, Option.bind_eq_bind, Option.pure_def,
        Option.bind_eq_some_iff] at step
      aesop (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
          CReadOnly.typedHeap, CReadOnly.loopHeap])

theorem enter_frame (step : Events.enterCall program state resultType stack = some following) :
    CReadOnly.typedHeap following = CReadOnly.loopHeap state := by
  unfold Events.enterCall at step
  split at step
  all_goals
    aesop (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
      CReadOnly.typedHeap, CReadOnly.loopHeap])

/-- All internal typed transitions, including indirect-call entry and saved
return assignments, preserve every cell outside their computed write address.
Foreign effects remain separate obligations. -/
theorem internal_frame (step : Events.internalNext program state = some following)
    (outside : current state ≠ some query) :
    CReadOnly.typedHeap following query = CReadOnly.typedHeap state query := by
  cases state with
  | halted => simp [Events.internalNext, Typed.nextWith] at step
  | returning value heap stack => exact resume_frame step outside
  | body body resultType stack =>
    cases body with
    | returned result =>
      simp only [Events.internalNext, Typed.nextWith, Option.bind_eq_bind,
        Option.pure_def, Option.bind_eq_some_iff] at step
      aesop (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
          CReadOnly.typedHeap, CReadOnly.loopHeap])
    | running code env types heap =>
      cases next : CLoops.next (.running code env types heap) with
      | none =>
        simp only [Events.internalNext, Typed.nextWith, next] at step
        exact congrFun (enter_frame step) query
      | some body =>
        simp only [Events.internalNext, Typed.nextWith, next] at step
        cases Option.some.inj step
        exact loop_frame next outside
  | calling name args heap stack =>
    simp only [Events.internalNext, Typed.nextWith, Option.bind_eq_bind,
      Option.pure_def, Option.bind_eq_some_iff] at step
    obtain ⟨definition, found, entered⟩ := step
    cases definition <;>
      aesop (add simp [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        CReadOnly.typedHeap, CReadOnly.loopHeap])
  | kernel body heap stack =>
    cases body <;>
      simp only [Events.internalNext, Typed.nextWith, Option.bind_eq_bind,
        Option.pure_def, Option.bind_eq_some_iff] at step <;>
      aesop (add simp [CReadOnly.typedHeap])

end Rumoca.CWriteFootprint
