import RumocaC.HostCalls

namespace Rumoca.CCalls.Host
open CTree CMemory Concurrent
noncomputable section
variable [CInterface] {E : Type}

def installed (threads : Nat → Option Typed.State) (thread : Nat) (state : Typed.State) : Concurrent.State :=
  ⟨CReadOnly.typedHeap state, update threads thread state⟩

omit [CInterface] in
theorem update_twice (threads : Nat → Option Typed.State) (thread : Nat) (first second : Typed.State) :
    update (update threads thread first) thread second = update threads thread second := by
  funext other
  by_cases same : other = thread <;> simp [update, same]

/-- Embedding a typed C step uses the very same shared scheduler transition. -/
theorem execute_installed (step : Events.Step program before events after)
    (policy : Policy) (threads : Nat → Option Typed.State) (thread : Nat) :
    Step program policy (installed threads thread before) thread (.execute events)
      (installed threads thread after) := by
  have executed : Concurrent.Step program (installed threads thread before) thread events
      ⟨CReadOnly.typedHeap after, update (update threads thread before) thread after⟩ :=
    .run (show (installed threads thread before).threads thread = some (control before) from by
        simp [installed, update])
      (by simpa only [installed, control_resume, withHeap_original] using step)
  exact .execute (by simpa only [update_twice, installed] using executed)

/-- Every existing finite C execution embeds, with its exact event chunks.
This requires no new outcome or host execution axiom. -/
theorem execution_history (program : Events.Program E) (policy : Policy)
    (threads : Nat → Option Typed.State) (thread : Nat)
    (path : Transition.Events.Reaches (Events.machine program).step before events after) :
    ∃ chunks : List (List E), chunks.flatten = events ∧
      History program policy (installed threads thread before)
        (chunks.map fun chunk => (thread, Action.execute chunk)) (installed threads thread after) := by
  induction path with
  | refl => exact ⟨[], rfl, .refl _⟩
  | @next before first middle rest after head tail ih =>
    obtain ⟨chunks, flattened, history⟩ := ih
    refine ⟨first :: chunks, by simp only [List.flatten_cons, flattened], ?_⟩
    exact .next ⟨thread, .execute first, rfl, execute_installed head policy threads thread⟩ history

/-- A proved C call can be bracketed by host invocation and observation. The
thread becomes idle again, the result and shared output heap are exact, and
every other saved invocation retains its control. A host may then choose its
next admitted call based on that result and heap. -/
theorem call_history (program : Events.Program E) (policy : Policy)
    (idle : before.threads thread = none)
    (admitted : policy.admit before thread name args)
    (path : Transition.Events.Reaches (Events.machine program).step
      (.calling name args before.heap .done) events (.halted result)) :
    ∃ chunks : List (List E), chunks.flatten = events ∧
      History program policy before
        ([(thread, Action.invoke name args)] ++
          (chunks.map fun chunk => (thread, Action.execute chunk)) ++ [(thread, Action.complete result.value)])
        ⟨result.heap, before.threads⟩ := by
  obtain ⟨chunks, flattened, history⟩ := execution_history program policy before.threads thread path
  have entered : History program policy before [(thread, Action.invoke name args)]
      (installed before.threads thread (.calling name args before.heap .done)) := by
    have emitted : emits program policy before [(thread, Action.invoke name args)]
        (installed before.threads thread (.calling name args before.heap .done)) :=
      ⟨thread, .invoke name args, rfl, .invoke idle admitted⟩
    exact .next emitted (.refl _)
  have retired : retire (update before.threads thread (.halted result)) thread = before.threads := by
    funext other
    by_cases same : other = thread
    · subst other
      simp [retire, idle]
    · simp [retire, update, same]
  have completed : History program policy (installed before.threads thread (.halted result))
      [(thread, Action.complete result.value)] ⟨result.heap, before.threads⟩ := by
    have step : Step program policy (installed before.threads thread (.halted result)) thread
        (.complete result.value)
        ⟨result.heap, retire (update before.threads thread (.halted result)) thread⟩ :=
      .complete (result := ⟨result.value, fun _ => none⟩) (by simp [installed, update, Concurrent.control, withHeap])
    rw [retired] at step
    have emitted : emits program policy (installed before.threads thread (.halted result))
        [(thread, Action.complete result.value)] ⟨result.heap, before.threads⟩ :=
      ⟨thread, .complete result.value, rfl, step⟩
    exact .next emitted (.refl _)
  exact ⟨chunks, flattened, (entered.trans history).trans completed⟩

end
end Rumoca.CCalls.Host
