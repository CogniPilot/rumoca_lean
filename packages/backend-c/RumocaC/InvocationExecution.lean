import RumocaC.InvocationLedger
import RumocaC.HostExecution

namespace Rumoca.CCalls.Host.Recording
open CTree CMemory Concurrent
noncomputable section

def callTrace (ledger : Ledger) (thread : Nat) (name : String) (args : List Value)
    (chunks : List (List E)) (value : Value) : List (Tick E) :=
  let during := advance ledger thread (Action.invoke name args : Action E)
  [stamp ledger thread (.invoke name args)] ++
    chunks.map (fun chunk => stamp during thread (.execute chunk)) ++
    [stamp during thread (.complete value)]

theorem callTrace_issued (ledger : Ledger) (thread : Nat) (name : String) (args : List Value)
    (chunks : List (List E)) (value : Value) :
    issued (callTrace ledger thread name args chunks value) = [ledger.next] := by
  simp [callTrace, issued, stamp, origin, List.flatMap_map]

variable [CInterface] {E : Type}

theorem execution_recorded (program : Events.Program E) (policy : Policy)
    (threads : Nat → Option Typed.State) (thread : Nat) (ledger : Ledger)
    (path : Transition.Events.Reaches (Events.machine program).step before events after) :
    ∃ chunks : List (List E), chunks.flatten = events ∧
      Transition.Events.Reaches (Step program policy) ⟨installed threads thread before, ledger⟩
        (chunks.map fun chunk => stamp ledger thread (.execute chunk))
        ⟨installed threads thread after, ledger⟩ := by
  induction path with
  | refl => exact ⟨[], rfl, .refl _⟩
  | @next before first middle rest after head tail ih =>
    obtain ⟨chunks, flattened, history⟩ := ih
    exact ⟨first :: chunks, by simp only [List.flatten_cons, flattened],
      .next (.record (execute_installed head policy threads thread)) history⟩

/-- Record an actual C call with one descriptor at the current counter,
matching its exact completion. Its identifier is issued once in this call's
trace and the counter advances while the caller thread and all other active
records are restored after completion. Separation from previously active
identifiers requires the separate freshness invariant; alignment alone does
not provide it. -/
theorem call_recorded (program : Events.Program E) (policy : Policy)
    (ledger : Ledger) (aligned : Aligned before ledger)
    (idle : before.threads thread = none)
    (admitted : policy.admit before thread name args)
    (path : Transition.Events.Reaches (Events.machine program).step
      (.calling name args before.heap .done) events (.halted result)) :
    ∃ chunks : List (List E), chunks.flatten = events ∧
      Transition.Events.Reaches (Step program policy) ⟨before, ledger⟩
        (callTrace ledger thread name args chunks result.value)
        ⟨⟨result.heap, before.threads⟩, ⟨ledger.next + 1, ledger.active⟩⟩ := by
  let during := advance ledger thread (Action.invoke name args : Action E)
  have ledgerIdle := (aligned thread).mp idle
  obtain ⟨chunks, flattened, history⟩ := execution_recorded program policy before.threads thread during path
  have entered : Transition.Events.Reaches (Step program policy) ⟨before, ledger⟩
      [stamp ledger thread (Action.invoke name args)]
      ⟨installed before.threads thread (.calling name args before.heap .done), during⟩ :=
    .next (Step.record (Host.Step.invoke idle admitted)) (.refl _)
  have retired : retire (update before.threads thread (.halted result)) thread = before.threads := by
    funext other
    by_cases same : other = thread
    · subst other
      simp [retire, idle]
    · simp [retire, update, same]
  have removed : bind during.active thread none = ledger.active := by
    funext other
    by_cases same : other = thread
    · subst other
      simp [bind, ledgerIdle]
    · simp [during, advance, bind, same]
  have completed : Transition.Events.Reaches (Step program policy)
      ⟨installed before.threads thread (.halted result), during⟩
      [stamp during thread (Action.complete result.value)]
      ⟨⟨result.heap, before.threads⟩, ⟨ledger.next + 1, ledger.active⟩⟩ := by
    have actual : Host.Step program policy (installed before.threads thread (.halted result)) thread
        (.complete result.value) ⟨result.heap, retire (update before.threads thread (.halted result)) thread⟩ :=
      .complete (result := ⟨result.value, fun _ => none⟩)
        (by simp [installed, update, Concurrent.control, withHeap])
    rw [retired] at actual
    have recorded : Step program policy ⟨installed before.threads thread (.halted result), during⟩
        [stamp during thread (Action.complete result.value)]
        ⟨⟨result.heap, before.threads⟩, advance during thread (Action.complete result.value : Action E)⟩ :=
      .record actual
    simp only [advance, removed] at recorded
    exact .next recorded (.refl _)
  exact ⟨chunks, flattened, (entered.trans history).trans completed⟩

end
end Rumoca.CCalls.Host.Recording


namespace Rumoca.CCalls.Events
variable [CInterface] {E : Type} {program : Program E}

theorem terminating_path (behavior : (machine program).Behaves before (.terminates events result)) :
    Transition.Events.Reaches (machine program).step before events (.halted result) := by
  cases behavior with
  | terminates path done =>
    rename_i last
    cases last <;> simp only [machine, machineWith] at done
    all_goals try contradiction
    cases Option.some.inj done
    exact path

end Rumoca.CCalls.Events
