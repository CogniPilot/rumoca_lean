import RumocaC.HostCalls

namespace Rumoca.CCalls.Host.Recording
open CTree CMemory
noncomputable section

/-- Proof-side invocation provenance. This is neither an ABI argument nor
storage allocated by the generated C program. -/
structure Invocation where
  serial : Nat
  name : String
  args : List Value

structure Ledger where
  next : Nat
  active : Nat → Option Invocation

def initial : Ledger := ⟨0, fun _ => none⟩

def bind (records : Nat → Option Invocation) (thread : Nat) (record : Option Invocation) : Nat → Option Invocation :=
  fun other => if other = thread then record else records other

def advance (ledger : Ledger) (thread : Nat) : Action E → Ledger
  | .invoke name args => ⟨ledger.next + 1, bind ledger.active thread (some ⟨ledger.next, name, args⟩)⟩
  | .complete _ => ⟨ledger.next, bind ledger.active thread none⟩
  | .execute _ | .memory => ledger

def origin (ledger : Ledger) (thread : Nat) : Action E → Option Invocation
  | .invoke name args => some ⟨ledger.next, name, args⟩
  | .execute _ | .complete _ => ledger.active thread
  | .memory => none

structure Tick (E : Type) where
  thread : Nat
  action : Action E
  origin : Option Invocation

def stamp (ledger : Ledger) (thread : Nat) (action : Action E) : Tick E :=
  ⟨thread, action, origin ledger thread action⟩

def erase (ticks : List (Tick E)) : List (Nat × Action E) :=
  ticks.map fun tick => (tick.thread, tick.action)

def issued (ticks : List (Tick E)) : List Nat :=
  ticks.flatMap fun tick => match tick.action with
    | .invoke _ _ => tick.origin.toList.map Invocation.serial
    | _ => []

structure State where
  runtime : Concurrent.State
  ledger : Ledger

def Aligned (runtime : Concurrent.State) (ledger : Ledger) : Prop :=
  ∀ thread, runtime.threads thread = none ↔ ledger.active thread = none

def Fresh (ledger : Ledger) : Prop :=
  ∀ thread call, ledger.active thread = some call → call.serial < ledger.next

theorem initial_aligned (heap : Heap) : Aligned ⟨heap, fun _ => none⟩ initial := by
  intro thread
  simp [initial]

theorem initial_fresh : Fresh initial := by
  intro thread call found
  contradiction

/-- The counter and descriptors are computed from host actions, rather than
being supplied as unconstrained annotations. -/
inductive Step [CInterface] (program : Events.Program E) (policy : Policy) :
    State → List (Tick E) → State → Prop where
  | record (actual : Host.Step program policy before thread action after) :
      Step program policy ⟨before, ledger⟩ [stamp ledger thread action]
        ⟨after, advance ledger thread action⟩

variable [CInterface] {E : Type}

omit [CInterface] in
theorem aligned_active (aligned : Aligned runtime ledger)
    (found : runtime.threads thread = some saved) : ∃ call, ledger.active thread = some call := by
  cases present : ledger.active thread with
  | none =>
    have absent := (aligned thread).mpr present
    rw [found] at absent
    contradiction
  | some call => exact ⟨call, rfl⟩

theorem step_aligned (aligned : Aligned before ledger)
    (actual : Host.Step program policy before thread action after) :
    Aligned after (advance ledger thread action) := by
  cases actual with
  | invoke idle admitted =>
    intro other
    by_cases same : other = thread
    · subst other
      simp [advance, Concurrent.update, bind]
    · simpa only [advance, Concurrent.update, bind, if_neg same] using aligned other
  | execute executed =>
    cases executed with
    | run found executed =>
      obtain ⟨call, active⟩ := aligned_active aligned found
      intro other
      by_cases same : other = thread
      · subst other
        simp [advance, Concurrent.update, active]
      · simpa only [advance, Concurrent.update, if_neg same] using aligned other
  | complete halted =>
    intro other
    by_cases same : other = thread
    · subst other
      simp [advance, retire, bind]
    · simpa only [advance, retire, bind, if_neg same] using aligned other
  | memory => exact aligned

omit [CInterface] in
theorem advance_fresh (fresh : Fresh ledger) (thread : Nat) (action : Action E) :
    Fresh (advance ledger thread action) := by
  cases action with
  | invoke name args =>
    intro other call found
    by_cases same : other = thread
    · subst other
      simp only [advance, bind, ↓reduceIte, Option.some.injEq] at found
      subst call
      exact Nat.lt_succ_self _
    · have old := fresh other call (by simpa only [advance, bind, if_neg same] using found)
      exact Nat.lt_trans old (Nat.lt_succ_self _)
  | complete value =>
    intro other call found
    by_cases same : other = thread
    · subst other
      simp [advance, bind] at found
    · exact fresh other call (by simpa only [advance, bind, if_neg same] using found)
  | execute | memory => exact fresh

/-- Every actual host history has a computed recording, including arbitrary
interleavings and repeated invocations. No fresh-ID or call-origin annotation
is assumed on later host actions. -/
theorem history_lift (program : Events.Program E) (policy : Policy)
    (path : Host.History program policy before labels after) (ledger : Ledger) :
    ∃ following ticks, erase ticks = labels ∧
      Transition.Events.Reaches (Step program policy) ⟨before, ledger⟩ ticks ⟨after, following⟩ := by
  induction path generalizing ledger with
  | refl => exact ⟨ledger, [], rfl, .refl _⟩
  | next first rest ih =>
    obtain ⟨thread, action, rfl, actual⟩ := first
    obtain ⟨following, ticks, erased, history⟩ := ih (advance ledger thread action)
    exact ⟨following, stamp ledger thread action :: ticks, by change (thread, action) :: erase ticks = (thread, action) :: _; rw [erased]; rfl,
      .next (.record actual) history⟩

theorem history_erases (path : Transition.Events.Reaches (Step program policy) before ticks after) :
    Host.History program policy before.runtime (erase ticks) after.runtime := by
  induction path with
  | refl => exact .refl _
  | next first rest ih =>
    cases first with
    | record actual =>
      simpa only [erase, List.map_append, List.map_cons, List.map_nil, stamp] using
        Transition.Events.Reaches.next
          (show emits program policy _ [(_, _)] _ from ⟨_, _, rfl, actual⟩) ih

theorem history_invariants (path : Transition.Events.Reaches (Step program policy) before ticks after)
    (aligned : Aligned before.runtime before.ledger) (fresh : Fresh before.ledger) :
    Aligned after.runtime after.ledger ∧ Fresh after.ledger := by
  induction path with
  | refl => exact ⟨aligned, fresh⟩
  | next first rest ih =>
    cases first with
    | record actual => exact ih (step_aligned aligned actual) (advance_fresh fresh _ _)

/-- Issued identifiers form a contiguous, strictly increasing interval.
Completion never recycles an identifier, even when the thread is reused. -/
theorem history_issued (path : Transition.Events.Reaches (Step program policy) before ticks after) :
    before.ledger.next ≤ after.ledger.next ∧
      issued ticks = List.range' before.ledger.next (after.ledger.next - before.ledger.next) := by
  induction path with
  | refl => simp [issued]
  | @next start first middle rest after head tail ih =>
    cases head with
    | @record before thread action middle ledger actual =>
      cases action with
      | invoke name args =>
        have bound : ledger.next + 1 ≤ after.ledger.next := ih.1
        have delta : after.ledger.next - ledger.next = (after.ledger.next - (ledger.next + 1)) + 1 := by omega
        refine ⟨show ledger.next ≤ after.ledger.next from (Nat.le_succ _).trans bound, ?_⟩
        simpa [issued, stamp, origin, advance, delta, List.range'_succ] using
          congrArg (List.cons ledger.next) ih.2
      | execute events | complete value | memory =>
        simpa [issued, stamp, origin, advance] using ih

end
end Rumoca.CCalls.Host.Recording
