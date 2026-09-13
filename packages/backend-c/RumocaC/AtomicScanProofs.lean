import RumocaC.AtomicScan

/-! Complete single-invocation behavior of the emitted fixed-storage scan.
This is a sequential execution lemma for composition; it does not assume that
the eventual FMI factory serializes concurrent invocations. A separate shared
memory history must connect overlapping invocations to ownership. -/
noncomputable section
namespace Rumoca.CAtomicScan
open CTree CMemory

def Ready (flags : Address) (count : Nat) (heap : Heap) : Prop :=
  ∀ i < count, ∃ busy, heap (flags.index i) = some (CAtomicBoolean.cell busy)

/-- Inspecting a busy slot leaves its value unchanged, while a successful
exchange reserves exactly the first vacancy observed in this sequential run. -/
inductive Outcome (flags : Address) (count : Nat) :
    Nat → Heap → List CAtomicBoolean.Calls.Event → Nat → Heap → Prop where
  | exhausted (heap) : Outcome flags count count heap [] count heap
  | reserved (inside : i < count) (vacant : heap (flags.index i) = some (CAtomicBoolean.cell false)) :
      Outcome flags count i heap [.exchange (flags.index i) false true] i
        (replace heap (flags.index i) (CAtomicBoolean.cell true))
  | busy (inside : i < count) (occupied : heap (flags.index i) = some (CAtomicBoolean.cell true))
      (rest : Outcome flags count (i + 1) heap trace result after) :
      Outcome flags count i heap (.exchange (flags.index i) true true :: trace) result after

theorem outcome_exists (ready : Ready flags count heap) (lower : i ≤ count) :
    ∃ trace result after, Outcome flags count i heap trace result after := by
  suffices ∀ remaining i, remaining + i = count →
      ∃ trace result after, Outcome flags count i heap trace result after from
    this (count - i) i (by omega)
  intro remaining
  induction remaining with
  | zero =>
    intro i total
    have equal : i = count := by omega
    subst i
    exact ⟨[], count, heap, .exhausted heap⟩
  | succ remaining ih =>
    intro i total
    have inside : i < count := by omega
    obtain ⟨busy, found⟩ := ready i inside
    cases busy with
    | false => exact ⟨_, _, _, .reserved inside found⟩
    | true =>
      obtain ⟨trace, result, after, rest⟩ := ih (i + 1) (by omega)
      exact ⟨_, result, after, .busy inside found rest⟩

/-- Bound both the returned index/sentinel and the number of atomic exchanges.
The recursion is in the proof relation; generated C contains one bounded loop. -/
theorem outcome_bounds (outcome : Outcome flags count i before trace result after) :
    i ≤ result ∧ result ≤ count ∧ trace.length ≤ count - i := by
  induction outcome with
  | exhausted => simp
  | reserved inside => simp; omega
  | busy inside occupied rest ih => simp only [List.length_cons]; omega

theorem outcome_reserved (outcome : Outcome flags count i before trace result after)
    (selected : result < count) :
    before (flags.index result) = some (CAtomicBoolean.cell false) ∧
      after = replace before (flags.index result) (CAtomicBoolean.cell true) := by
  induction outcome with
  | exhausted => omega
  | reserved inside vacant => exact ⟨vacant, rfl⟩
  | busy inside occupied rest ih => exact ih selected

theorem outcome_exhausted (outcome : Outcome flags count i before trace result after)
    (exhausted : result = count) :
    after = before ∧ ∀ k, i ≤ k → k < count → before (flags.index k) = some (CAtomicBoolean.cell true) := by
  induction outcome with
  | exhausted => exact ⟨rfl, fun _ lower upper => by omega⟩
  | reserved inside => omega
  | @busy i heap trace result after inside occupied rest ih =>
    have restSpec := ih exhausted
    refine ⟨restSpec.1, ?_⟩
    intro k lower upper
    by_cases first : k = i
    · simpa only [first] using occupied
    · exact restSpec.2 k (by omega) upper

theorem outcome_frame (outcome : Outcome flags count i before trace result after)
    (different : query ≠ flags.index result) : after query = before query := by
  induction outcome with
  | exhausted => rfl
  | reserved => exact replace_other _ _ _ _ different
  | busy inside occupied rest ih => exact ih different

theorem outcome_storage (outcome : Outcome flags count i before trace result after) :
    CStorage.Preserves before after ∧ CReadOnly.Preserves before after := by
  induction outcome with
  | exhausted => exact ⟨.refl _, .refl _⟩
  | @reserved i heap inside vacant =>
    have operation : CAtomicBoolean.exchange heap (flags.index i) true =
        some (false, replace heap (flags.index i) (CAtomicBoolean.cell true)) :=
      CAtomicBoolean.exchange_iff.mpr ⟨vacant, rfl⟩
    exact ⟨CAtomicBoolean.exchange_storage operation, CAtomicBoolean.exchange_readonly operation⟩
  | busy inside occupied rest ih => exact ih

variable [interface : CInterface]
set_option maxRecDepth 10000

theorem scan_path (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (bounded : count < 2 ^ 64)
    (outcome : Outcome flags count i before trace result after) (previous : Bool)
    (stack : CCalls.Typed.Continuation) :
    Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running [scan, .ret (some (.id "count"))] (locals flags count i previous) types before)
        "size_t" stack) (trace.map tag) (.returning (.integer result) after stack) := by
  induction outcome generalizing previous with
  | exhausted heap =>
    apply (CCalls.Events.internal_path program
      (.next (CCalls.Events.body_step program (scan_stop flags count previous heap _) "size_t" stack) (.refl _))).trans
    exact return_path program _ heap "count" count [] stack size
      (by simp [locals, CBody.bind]) bounded
  | @reserved i heap inside vacant =>
    apply (CCalls.Events.internal_path program
      (.next (CCalls.Events.body_step program (scan_enter flags count i previous heap _ inside) "size_t" stack) (.refl _))).trans
    change Transition.Events.Prefix _ _ ([tag (.exchange (flags.index i) false true)] ++ []) _
    apply (attempt_path program tag boolean pointer named bound
      (CAtomicBoolean.exchange_iff.mpr ⟨vacant, rfl⟩)).trans
    apply (CCalls.Events.internal_path program
      (.next (CCalls.Events.body_step program (selected_step flags count i false _ _) "size_t" stack) (.refl _))).trans
    exact return_path program _ _ "k" i _ stack size (by simp [locals, CBody.bind]) (by omega)
  | @busy i heap trace result after inside occupied rest ih =>
    apply (CCalls.Events.internal_path program
      (.next (CCalls.Events.body_step program (scan_enter flags count i previous heap _ inside) "size_t" stack) (.refl _))).trans
    change Transition.Events.Prefix _ _ ([tag (.exchange (flags.index i) true true)] ++ trace.map tag) _
    apply (attempt_path program tag boolean pointer named bound (CAtomicBoolean.exchange_same occupied)).trans
    apply (CCalls.Events.internal_path program
      (.next (CCalls.Events.body_step program (selected_step flags count i true heap _) "size_t" stack)
        (.next (CCalls.Events.body_step program (advance_step flags count i true heap _ (by omega)) "size_t" stack)
          (.refl _)))).trans
    exact ih true

theorem scan_prefix (program : CCalls.Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (bounded : count < 2 ^ 64)
    (outcome : Outcome flags count i before trace result after) (previous : Bool)
    (stack : CCalls.Typed.Continuation)
    (continued : Transition.Events.Forced (CCalls.Events.machine program)
      (.returning (.integer result) after stack) continuationTrace final) :
    Transition.Events.Forced (CCalls.Events.machine program)
      (.body (.running [scan, .ret (some (.id "count"))] (locals flags count i previous) types before)
        "size_t" stack) (trace.map tag ++ continuationTrace) final :=
  (scan_path program tag boolean pointer size named bound bounded outcome previous stack).forced continued

end Rumoca.CAtomicScan
