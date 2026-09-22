import RumocaC.AtomicScanCalls
import RumocaC.CallIntervals

/-! Original flag-array pointer and bounded indices throughout the actual generated scan loop. -/
namespace Rumoca.CAtomicScan.ConcurrentInvariant
open CTree CMemory CCalls
open CCalls.Concurrent (Exit BeforeReturn exit_withHeap saved_predicate_step)
variable {count : Nat}

def tail : List Stmt := [selected, advance, scan, .ret (some (.id "count"))]

/-- Exact control states of the generated loop, retaining its original array
and extent. Each exchange index is strictly below the original extent. Heap
contents are unrestricted; progress and ownership need separate contracts. -/
inductive Ready (flags : Address) (count : Nat) (stack : Typed.Continuation) : Typed.State → Prop where
  | scan (k : Nat) (bounded : k ≤ count) (busy : Bool) (heap : Heap) :
      Ready flags count stack (.body (.running [CAtomicScan.scan, .ret (some (.id "count"))]
        (locals flags count k busy) types heap) "size_t" stack)
  | attempt (k : Nat) (bounded : k < count) (busy : Bool) (heap : Heap) :
      Ready flags count stack (.body (.running (CAtomicScan.attempt :: tail)
        (locals flags count k busy) types heap) "size_t" stack)
  | atomic (k : Nat) (bounded : k < count) (busy : Bool) (heap : Heap) :
      Ready flags count stack (.calling "atomic_exchange"
        [.pointer (some (flags.index k)), CAtomicBoolean.value true] heap
        (.caller (.assign (.id "busy")) tail (locals flags count k busy) types "size_t" stack))
  | resume (k : Nat) (bounded : k < count) (previous observed : Bool) (heap : Heap) :
      Ready flags count stack (.returning (CAtomicBoolean.value observed) heap
        (.caller (.assign (.id "busy")) tail (locals flags count k previous) types "size_t" stack))
  | selected (k : Nat) (bounded : k < count) (busy : Bool) (heap : Heap) :
      Ready flags count stack (.body (.running tail (locals flags count k busy) types heap) "size_t" stack)
  | advance (k : Nat) (bounded : k < count) (heap : Heap) :
      Ready flags count stack (.body (.running [CAtomicScan.advance, CAtomicScan.scan, .ret (some (.id "count"))]
        (locals flags count k true) types heap) "size_t" stack)
  | returnIndex (k : Nat) (bounded : k < count) (heap : Heap) :
      Ready flags count stack (.body (.running
        [.ret (some (.id "k")), CAtomicScan.advance, CAtomicScan.scan, .ret (some (.id "count"))]
        (locals flags count k false) types heap) "size_t" stack)
  | returnCount (busy : Bool) (heap : Heap) :
      Ready flags count stack (.body (.running [.ret (some (.id "count"))]
        (locals flags count count busy) types heap) "size_t" stack)
  | returned (k : Nat) (bounded : k ≤ count) (heap : Heap) :
      Ready flags count stack (.body (.returned ⟨.integer k, heap⟩) "size_t" stack)
  | done (k : Nat) (bounded : k ≤ count) (heap : Heap) :
      Ready flags count stack (.returning (.integer k) heap stack)

theorem Ready.withHeap (ready : Ready flags count stack state) (heap : Heap) :
    Ready flags count stack (Concurrent.withHeap state heap) := by
  cases ready with
  | scan k bounded busy => exact .scan k bounded busy heap
  | attempt k bounded busy => exact .attempt k bounded busy heap
  | atomic k bounded busy => exact .atomic k bounded busy heap
  | resume k bounded previous observed => exact .resume k bounded previous observed heap
  | selected k bounded busy => exact .selected k bounded busy heap
  | advance k bounded => exact .advance k bounded heap
  | returnIndex k bounded => exact .returnIndex k bounded heap
  | returnCount busy => exact .returnCount busy heap
  | returned k bounded => exact .returned k bounded heap
  | done k bounded => exact .done k bounded heap

/-- The invariant itself supplies the original pointer and strict range;
these are not assumptions about an already selected atomic argument. -/
theorem Ready.call_origin (ready : Ready flags count stack (.calling name args heap later)) :
    name = "atomic_exchange" ∧ ∃ k, k < count ∧
      args = [.pointer (some (flags.index k)), CAtomicBoolean.value true] := by
  cases ready with
  | atomic k bounded busy => exact ⟨rfl, k, bounded, rfl⟩

theorem Ready.exit_value (ready : Ready flags count stack (.returning value heap stack)) :
    ∃ k : Nat, k ≤ count ∧ value = .integer k := by
  cases ready with
  | done k bounded => exact ⟨k, bounded, rfl⟩

variable [interface : CInterface] {E : Type}

private theorem known_step (program : Events.Program E)
    (known : Events.internalNext program before = some target)
    (ready : Ready flags count stack target)
    (step : Events.Step program before events after) : Ready flags count stack after := by
  obtain ⟨_, rfl⟩ := Events.internal_unique program known _ _ step
  exact ready

/-- Every actual loop step before return preserves pointer origin and index
bounds. Other threads may change the heap between any two of these steps. -/
theorem step_ready (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (range : count < 2 ^ 64)
    (ready : Ready flags count stack before) (active : ¬ Exit stack before)
    (step : Events.Step program before events after) : Ready flags count stack after := by
  cases ready with
  | scan k bounded busy heap =>
    by_cases below : k < count
    · exact known_step program (Events.body_step program
        (scan_enter flags count k busy heap _ below) "size_t" stack) (.attempt k below busy heap) step
    · have same : k = count := by omega
      subst k
      exact known_step program (Events.body_step program
        (scan_stop flags count busy heap _) "size_t" stack) (.returnCount busy heap) step
  | attempt k bounded busy heap =>
    exact known_step program (attempt_enter program flags count k busy heap tail "size_t" stack boolean named)
      (.atomic k bounded busy heap) step
  | atomic k bounded busy heap =>
    cases step with
    | internal moved =>
      change Events.internalNext program _ = _ at moved
      rw [Events.external_entry_exclusive program bound] at moved
      contradiction
    | external found converted executed =>
      cases Option.some.inj (found.symm.trans bound)
      have exactArguments := CAtomicBoolean.Calls.arguments_converted boolean pointer (flags.index k) true
      cases Option.some.inj (converted.symm.trans exactArguments)
      obtain ⟨address, observed, desired, arguments, operation, trace, rfl⟩ := executed
      have desiredSame : true = desired := CAtomicBoolean.value_injective
        (List.cons.inj (List.cons.inj arguments).2).1
      subst desired
      exact .resume k bounded busy observed _
  | resume k bounded previous observed heap =>
    exact known_step program (attempt_resume program flags count k previous observed heap tail "size_t" stack)
      (.selected k bounded observed heap) step
  | selected k bounded busy heap =>
    cases busy with
    | false =>
      exact known_step program (Events.body_step program
        (selected_step flags count k false heap _) "size_t" stack) (.returnIndex k bounded heap) step
    | true =>
      exact known_step program (Events.body_step program
        (selected_step flags count k true heap _) "size_t" stack) (.advance k bounded heap) step
  | advance k bounded heap =>
    exact known_step program (Events.body_step program
      (advance_step flags count k true heap _ (by omega)) "size_t" stack)
      (.scan (k + 1) (by omega) true heap) step
  | returnIndex k bounded heap =>
    exact known_step program (Events.body_step program
      (return_body (locals flags count k false) heap "k" k _ (by simp [locals, CBody.bind]))
      "size_t" stack) (.returned k (by omega) heap) step
  | returnCount busy heap =>
    exact known_step program (Events.body_step program
      (return_body (locals flags count count busy) heap "count" count _ (by simp [locals, CBody.bind]))
      "size_t" stack) (.returned count (by omega) heap) step
  | returned k bounded heap =>
    exact known_step program (size_returned program heap k stack size (by omega)) (.done k bounded heap) step
  | done k bounded heap => exact False.elim (active ⟨_, _, rfl⟩)

end Rumoca.CAtomicScan.ConcurrentInvariant


namespace Rumoca.CAtomicScan.ConcurrentInvariant
open CTree CMemory CCalls
open CCalls.Concurrent (Exit BeforeReturn exit_withHeap saved_predicate_step)
variable {count : Nat}

def ThreadReady (flags : Address) (count : Nat) (stack : Typed.Continuation)
    (thread : Nat) (state : Concurrent.State) : Prop :=
  ∃ saved, state.threads thread = some saved ∧ Ready flags count stack saved

variable [interface : CInterface] {E : Type}

theorem thread_step (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (range : count < 2 ^ 64)
    (ready : ThreadReady flags count stack tracked before)
    (active : BeforeReturn tracked stack before chosen)
    (step : Concurrent.Step program before chosen events after) :
    ThreadReady flags count stack tracked after := by
  exact saved_predicate_step program (Ready flags count stack)
    (fun _ ready heap => ready.withHeap heap)
    (fun _ _ _ ready active step => step_ready program tag boolean pointer size named bound range ready active step)
    ready active step

theorem thread_reaches (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (range : count < 2 ^ 64)
    (ready : ThreadReady flags count stack tracked before)
    (path : Transition.Reaches (fun a b => ∃ chosen events,
      Concurrent.Step program a chosen events b ∧ BeforeReturn tracked stack a chosen) before after) :
    ThreadReady flags count stack tracked after := by
  induction path with
  | refl => exact ready
  | next first rest ih =>
    obtain ⟨chosen, events, step, active⟩ := first
    exact ih (thread_step program tag boolean pointer size named bound range ready active step)

/-- A finite interleaving from the actual initialized loop preserves each
scheduled exchange's original array and strict index bound. The same theorem
bounds any return observed before the original caller resumes. -/
theorem loop_prefix_bounds (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (range : count < 2 ^ 64)
    (entry : before.threads tracked = some (.body
      (.running [CAtomicScan.scan, .ret (some (.id "count"))]
        (locals flags count 0 false) types savedHeap) "size_t" stack))
    (path : Transition.Reaches (fun a b => ∃ chosen events,
      Concurrent.Step program a chosen events b ∧ BeforeReturn tracked stack a chosen) before after) :
    (∀ name args heap later, after.threads tracked = some (.calling name args heap later) →
      name = "atomic_exchange" ∧ ∃ k, k < count ∧
        args = [.pointer (some (flags.index k)), CAtomicBoolean.value true]) ∧
    (∀ value heap, after.threads tracked = some (.returning value heap stack) →
      ∃ k : Nat, k ≤ count ∧ value = .integer k) := by
  obtain ⟨saved, found, ready⟩ := thread_reaches program tag boolean pointer size named bound range
    (show ThreadReady flags count stack tracked before from ⟨_, entry, .scan 0 (Nat.zero_le _) false _⟩) path
  constructor
  · intro name args heap later calling
    cases Option.some.inj (found.symm.trans calling)
    exact ready.call_origin
  · intro value heap returning
    cases Option.some.inj (found.symm.trans returning)
    exact ready.exit_value

end Rumoca.CAtomicScan.ConcurrentInvariant
