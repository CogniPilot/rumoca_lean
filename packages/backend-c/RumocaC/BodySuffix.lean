import RumocaC.Body

noncomputable section
namespace Rumoca.CBody
open CTree CMemory
variable [CInterface]

/-- A finite step that remains running is unchanged by appending a suffix. -/
theorem next_running_suffix (code rest tail : List Stmt) (env later : Locals)
    (heap after : Heap)
    (ran : next (.running code env heap) = some (.running rest later after)) :
    next (.running (code ++ tail) env heap) =
      some (.running (rest ++ tail) later after) := by
  cases code with
  | nil => simp [next, nextWith] at ran
  | cons stmt code =>
    cases stmt <;>
      simp only [next, nextWith, List.cons_append, Option.bind_eq_bind, Option.pure_def,
        Option.bind_eq_some_iff, Option.some.injEq,
        State.running.injEq] at ran ⊢ <;>
      aesop (add simp [List.append_assoc, List.cons_append, Option.bind_eq_bind,
        Option.pure_def, Option.bind_eq_some_iff])

/-- This is deliberately a running-prefix result, not append equivalence for
returned or divergent executions. -/
theorem run_running_suffix (steps : Nat) (code rest tail : List Stmt)
    (env later : Locals) (heap after : Heap)
    (ran : run steps (.running code env heap) = some (.running rest later after)) :
    run steps (.running (code ++ tail) env heap) =
      some (.running (rest ++ tail) later after) := by
  induction steps generalizing code env heap with
  | zero =>
    cases Option.some.inj ran
    rfl
  | succ n ih =>
    cases hn : next (.running code env heap) with
    | none => simp [run, hn] at ran
    | some state =>
      cases state with
      | returned result =>
        simp only [run, hn] at ran
        cases n <;> simp [run, next, nextWith] at ran
      | running mid env' heap' =>
        have restRun := ih mid env' heap' (by simpa [run, hn] using ran)
        simpa only [run, next_running_suffix code mid tail env env' heap heap' hn,
          Option.bind_some] using restRun

end Rumoca.CBody
