import RumocaC.ConcurrentCalls

/-! A reusable host boundary around the existing shared C transition. A host
may invoke on an idle thread, observe its actual halted result, and reuse that
thread. Host memory effects are explicit and separately constrained by policy;
this layer does not claim that arbitrary host effects respect private storage.
Neither an invocation nor an observation executes a replacement C body. -/
noncomputable section
namespace Rumoca.CCalls.Host
open CTree CMemory Concurrent

structure Policy where
  admit : Concurrent.State → Nat → String → List Value → Prop
  memory : Concurrent.State → Nat → Heap → Prop

/-- Restrict host entry to the exact public signature table. The supplied
domain describes additional observable state/buffer/argument conditions;
evolving ghost leases are carried by a separate annotated history. -/
def publicPolicy (sigs : List Signature)
    (domain : Concurrent.State → Nat → Signature → List Value → Prop)
    (memory : Concurrent.State → Nat → Heap → Prop) : Policy where
  admit state thread name args := ∃ sig ∈ sigs, sig.name = name ∧ domain state thread sig args
  memory := memory

inductive Action (E : Type) where
  | invoke (name : String) (args : List Value)
  | execute (events : List E)
  | complete (value : Value)
  | memory

def retire (threads : Nat → Option Typed.State) (thread : Nat) : Nat → Option Typed.State :=
  fun other => if other = thread then none else threads other

variable [CInterface] {E : Type}

inductive Step (program : Events.Program E) (policy : Policy) :
    Concurrent.State → Nat → Action E → Concurrent.State → Prop where
  | invoke (idle : before.threads thread = none)
      (admitted : policy.admit before thread name args) :
      Step program policy before thread (.invoke name args)
        ⟨before.heap, update before.threads thread (.calling name args before.heap .done)⟩
  | execute (executed : Concurrent.Step program before thread events after) :
      Step program policy before thread (.execute events) after
  | complete (halted : before.threads thread = some (.halted result)) :
      Step program policy before thread (.complete result.value)
        ⟨before.heap, retire before.threads thread⟩
  | memory (idle : before.threads thread = none)
      (allowed : policy.memory before thread heap) :
      Step program policy before thread .memory ⟨heap, before.threads⟩

/-- One host or actual C action is observable, including its chosen thread. -/
def emits (program : Events.Program E) (policy : Policy)
    (before : Concurrent.State) (events : List (Nat × Action E)) (after : Concurrent.State) : Prop :=
  ∃ thread action, events = [(thread, action)] ∧ Step program policy before thread action after

abbrev History (program : Events.Program E) (policy : Policy) :=
  Transition.Events.Reaches (emits program policy)

theorem invoke_iff : Step program policy before thread (.invoke name args) after ↔
    before.threads thread = none ∧ policy.admit before thread name args ∧
    after = ⟨before.heap, update before.threads thread (.calling name args before.heap .done)⟩ := by
  constructor
  · intro step
    cases step with | invoke idle admitted => exact ⟨idle, admitted, rfl⟩
  · rintro ⟨idle, admitted, rfl⟩
    exact .invoke idle admitted

theorem complete_iff : Step program policy before thread (.complete value) after ↔
    (∃ result, before.threads thread = some (.halted result) ∧ result.value = value) ∧
    after = ⟨before.heap, retire before.threads thread⟩ := by
  constructor
  · intro step
    cases step with | complete halted => exact ⟨⟨_, halted, rfl⟩, rfl⟩
  · rintro ⟨⟨result, halted, rfl⟩, rfl⟩
    exact .complete halted

theorem execute_iff : Step program policy before thread (.execute events) after ↔
    Concurrent.Step program before thread events after := by
  constructor
  · intro step
    cases step with | execute executed => exact executed
  · exact Step.execute

theorem other_thread (step : Step program policy before thread action after)
    (different : other ≠ thread) : after.threads other = before.threads other := by
  cases step with
  | invoke => simp [update, different]
  | execute executed => exact Concurrent.other_thread executed different
  | complete => simp [retire, different]
  | memory => rfl

/-- Heap-stable control invariants are independent of the host's memory policy.
Memory-dependent ownership/frame invariants require additional obligations. -/
def Threads (P : Typed.State → Prop) (state : Concurrent.State) : Prop :=
  ∀ thread saved, state.threads thread = some saved → P saved

theorem step_threads (program : Events.Program E) (policy : Policy)
    (P : Typed.State → Prop)
    (heapStable : ∀ state, P state → ∀ heap, P (withHeap state heap))
    (entry : ∀ state thread name args, policy.admit state thread name args →
      P (.calling name args state.heap .done))
    (preserves : ∀ before events after, P before → Events.Step program before events after → P after)
    (ready : Threads P before) (step : Step program policy before chosen action after) : Threads P after := by
  cases step with
  | invoke idle admitted =>
    intro other saved found
    by_cases same : other = chosen
    · subst other
      simp only [update, ↓reduceIte, Option.some.injEq] at found
      subst saved
      exact heapStable _ (entry _ _ _ _ admitted) _
    · exact ready _ _ (by simpa only [update, if_neg same] using found)
  | execute executed =>
    cases executed with
    | run found executed =>
      have following := preserves _ _ _ (heapStable _ (ready _ _ found) _) executed
      intro other saved selected
      by_cases same : other = chosen
      · subst other
        simp only [update, ↓reduceIte, Option.some.injEq] at selected
        subst saved
        exact heapStable _ following _
      · exact ready _ _ (by simpa only [update, if_neg same] using selected)
  | complete halted =>
    intro other saved found
    by_cases same : other = chosen
    · subst other
      simp [retire] at found
    · exact ready _ _ (by simpa only [retire, if_neg same] using found)
  | memory => exact ready

theorem history_threads (program : Events.Program E) (policy : Policy)
    (P : Typed.State → Prop)
    (heapStable : ∀ state, P state → ∀ heap, P (withHeap state heap))
    (entry : ∀ state thread name args, policy.admit state thread name args →
      P (.calling name args state.heap .done))
    (preserves : ∀ before events after, P before → Events.Step program before events after → P after)
    (ready : Threads P before) (path : History program policy before trace after) : Threads P after := by
  induction path with
  | refl => exact ready
  | next first rest ih =>
    obtain ⟨thread, action, _, step⟩ := first
    exact ih (step_threads program policy P heapStable entry preserves ready step)

end Rumoca.CCalls.Host
