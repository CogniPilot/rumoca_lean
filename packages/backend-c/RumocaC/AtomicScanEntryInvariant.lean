import RumocaC.AtomicScanInvariant

/-! Extend the scan invariant through actual helper entry and local initialization. -/
namespace Rumoca.CAtomicScan.ConcurrentInvariant
open CTree CMemory CCalls
open CCalls.Concurrent (Exit BeforeReturn exit_withHeap saved_predicate_step)
variable {count : Nat}

def afterK (flags : Address) (count : Nat) : CBody.Locals :=
  CBody.bind (parameterLocals flags count) "k" (.integer 0)
def typesAfterK : CLoops.Types := CLoops.bindType parameterTypes "k" .size

def afterOne (flags : Address) (count : Nat) : CBody.Locals :=
  CBody.bind (afterK flags count) "one" (.integer 1)
def typesAfterOne : CLoops.Types := CLoops.bindType typesAfterK "one" .size

/-- Include the actual helper call and its three local declarations. -/
inductive FullReady (flags : Address) (count : Nat) (stack : Typed.Continuation) : Typed.State → Prop where
  | entry (heap : Heap) : FullReady flags count stack
      (.calling function.signature.name [.pointer (some flags), .integer count] heap stack)
  | parameters (heap : Heap) : FullReady flags count stack
      (.body (.running function.body (parameterLocals flags count) parameterTypes heap) "size_t" stack)
  | counter (heap : Heap) : FullReady flags count stack
      (.body (.running function.body.tail (afterK flags count) typesAfterK heap) "size_t" stack)
  | stride (heap : Heap) : FullReady flags count stack
      (.body (.running (function.body.drop 2) (afterOne flags count) typesAfterOne heap) "size_t" stack)
  | loop (ready : Ready flags count stack state) : FullReady flags count stack state

theorem FullReady.withHeap (ready : FullReady flags count stack state) (heap : Heap) :
    FullReady flags count stack (Concurrent.withHeap state heap) := by
  cases ready with
  | entry => exact .entry heap
  | parameters => exact .parameters heap
  | counter => exact .counter heap
  | stride => exact .stride heap
  | loop ready => exact .loop (ready.withHeap heap)

theorem FullReady.atomic_origin
    (ready : FullReady flags count stack (.calling name args heap later))
    (atomic : name = "atomic_exchange") :
    ∃ k : Nat, k < count ∧ args = [.pointer (some (flags.index k)), CAtomicBoolean.value true] := by
  cases ready with
  | entry heap => simp [function] at atomic
  | loop ready => exact ready.call_origin.2

theorem FullReady.exit_value (ready : FullReady flags count stack (.returning value heap stack)) :
    ∃ k : Nat, k ≤ count ∧ value = .integer k := by
  cases ready with
  | loop ready => exact ready.exit_value

variable [interface : CInterface] {E : Type}

private theorem known_full_step (program : Events.Program E)
    (known : Events.internalNext program before = some target)
    (ready : FullReady flags count stack target)
    (step : Events.Step program before events after) : FullReady flags count stack after := by
  obtain ⟨_, rfl⟩ := Events.internal_unique program known _ _ step
  exact ready

theorem full_step_ready (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (constantSize : interface.types "const size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (range : count < 2 ^ 64)
    (ready : FullReady flags count stack before) (active : ¬ Exit stack before)
    (step : Events.Step program before events after) : FullReady flags count stack after := by
  cases ready with
  | entry heap =>
    exact known_full_step program (Events.tree_entry program _ _ heap stack function _ _ defined
      (parameters_bound flags count pointer size range) (parameter_types pointer size)) (.parameters heap) step
  | parameters heap =>
    exact known_full_step program (Events.body_step program
      (CLoops.declare_local (parameterLocals flags count) parameterTypes heap "size_t" "k" (.nat 0)
        function.body.tail .size (.integer 0) (.integer 0) size
        (by simp [parameterLocals, CBody.bind]) rfl (CLoops.convert_size_nat 0 (by decide +kernel)))
      "size_t" stack) (.counter heap) step
  | counter heap =>
    exact known_full_step program (Events.body_step program
      (CLoops.declare_local (afterK flags count) typesAfterK heap "const size_t" "one" (.nat 1)
        (function.body.drop 2) .size (.integer 1) (.integer 1) constantSize
        (by simp [afterK, parameterLocals, CBody.bind]) rfl (CLoops.convert_size_nat 1 (by decide +kernel)))
      "size_t" stack) (.stride heap) step
  | stride heap =>
    exact known_full_step program (Events.body_step program
      (CLoops.declare_local (afterOne flags count) typesAfterOne heap "_Bool" "busy" (.cast "_Bool" (.nat 0))
        [CAtomicScan.scan, .ret (some (.id "count"))] .boolean (.integer 0) (.integer 0) boolean
        (by simp [afterOne, afterK, parameterLocals, CBody.bind])
        (by simp [CLoops.eval, CBody.eval, CBody.expressionCast, CBody.cast, CBody.zeroLiteral,
          boolean, convert, Value.truth]) rfl)
      "size_t" stack) (.loop (.scan 0 (Nat.zero_le _) false heap)) step
  | loop ready => exact .loop (step_ready program tag boolean pointer size named bound range ready active step)

theorem full_thread_reaches (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (constantSize : interface.types "const size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (range : count < 2 ^ 64)
    (ready : ∃ saved, before.threads tracked = some saved ∧ FullReady flags count stack saved)
    (path : Transition.Reaches (fun a b => ∃ chosen events,
      Concurrent.Step program a chosen events b ∧ BeforeReturn tracked stack a chosen) before after) :
    ∃ saved, after.threads tracked = some saved ∧ FullReady flags count stack saved := by
  induction path with
  | refl => exact ready
  | next first rest ih =>
    obtain ⟨chosen, events, step, active⟩ := first
    exact ih (saved_predicate_step program (FullReady flags count stack)
      (fun _ ready heap => ready.withHeap heap)
      (fun _ _ _ ready active step => full_step_ready program tag boolean pointer size constantSize
        named bound defined range ready active step) ready active step)

theorem call_prefix_bounds (program : Events.Program E) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (pointer : interface.types "volatile atomic_bool *" = some .pointer)
    (size : interface.types "size_t" = some .size)
    (constantSize : interface.types "const size_t" = some .size)
    (named : interface.constants "atomic_exchange" = none)
    (bound : program.externals "atomic_exchange" = some (CAtomicBoolean.Calls.exchangeExternal tag boolean))
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (range : count < 2 ^ 64)
    (entry : before.threads tracked = some
      (.calling function.signature.name [.pointer (some flags), .integer count] savedHeap stack))
    (path : Transition.Reaches (fun a b => ∃ chosen events,
      Concurrent.Step program a chosen events b ∧ BeforeReturn tracked stack a chosen) before after) :
    (∀ args heap later, after.threads tracked = some (.calling "atomic_exchange" args heap later) →
      ∃ k : Nat, k < count ∧ args = [.pointer (some (flags.index k)), CAtomicBoolean.value true]) ∧
    (∀ value heap, after.threads tracked = some (.returning value heap stack) →
      ∃ k : Nat, k ≤ count ∧ value = .integer k) := by
  obtain ⟨saved, found, ready⟩ := full_thread_reaches program tag boolean pointer size constantSize named
    bound defined range (show ∃ saved, before.threads tracked = some saved ∧ FullReady flags count stack saved from
      ⟨_, entry, .entry savedHeap⟩) path
  constructor
  · intro args heap later calling
    cases Option.some.inj (found.symm.trans calling)
    exact ready.atomic_origin rfl
  · intro value heap returning
    cases Option.some.inj (found.symm.trans returning)
    exact ready.exit_value

end Rumoca.CAtomicScan.ConcurrentInvariant
