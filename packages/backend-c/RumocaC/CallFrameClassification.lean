import RumocaC.CallStoreInvariant

/-! Classify frame-preserving steps and explicitly exceptional foreign calls. -/
noncomputable section
namespace Rumoca.CStoreInvariant
open CTree CMemory CCalls CCalls.Events
variable [CInterface] {E : Type} {R : Heap → Heap → Prop}

/-- Only named exceptional foreign routines may fail a store-stable heap frame.
This allows effectful operations to be handled by their own refinement proofs. -/
def ExceptPreserves (R : Heap → Heap → Prop) (special : String → Prop)
    (program : Events.Program E) : Prop :=
  ∀ name fn, program.externals name = some fn → ¬ special name → ExternalPreserves R fn

theorem linked_except (program : Events.Program E) (fn : External E)
    (internalFree : program.internal.definitions fn.signature.name = none)
    (externalFree : program.externals fn.signature.name = none)
    (previous : ExceptPreserves R special program)
    (added : ¬ special fn.signature.name → ExternalPreserves R fn) :
    ExceptPreserves R special (Linkage.withExternal program fn internalFree externalFree) := by
  intro name target found ordinary
  by_cases same : name = fn.signature.name
  · simp only [Linkage.withExternal, if_pos same, Option.some.injEq] at found
    subst target
    exact added (by simpa only [same] using ordinary)
  · exact previous name target (by simpa only [Linkage.withExternal, if_neg same] using found) ordinary

/-- A real step either preserves the frame or starts at an exceptional foreign
call. No classification of the actual execution is supplied by the caller. -/
theorem event_classifies (stable : Stable R)
    (foreign : ExceptPreserves R special program)
    (step : Events.Step program s events t) :
    R (CReadOnly.typedHeap s) (CReadOnly.typedHeap t) ∨
      ∃ name args heap stack, s = .calling name args heap stack ∧ special name := by
  cases step with
  | internal next => exact .inl (internal_next stable _ next)
  | @external name fn args values heap events result after stack found converted executed =>
    by_cases exceptional : special name
    · exact .inr ⟨name, args, heap, stack, rfl, exceptional⟩
    · exact .inl (foreign name fn found exceptional values heap events result after executed)

/-- The same classification uses the current shared heap and the selected
thread's saved control, including arbitrary interleavings. -/
theorem concurrent_classifies (stable : Stable R)
    (foreign : ExceptPreserves R special program)
    (step : Concurrent.Step program before thread events after) :
    R before.heap after.heap ∨
      ∃ saved name args stack,
        before.threads thread = some saved ∧
        Concurrent.withHeap saved before.heap = .calling name args before.heap stack ∧
        special name := by
  cases step with
  | run found executed =>
    obtain preserved | ⟨name, args, heap, stack, source, exceptional⟩ :=
      event_classifies stable foreign executed
    · exact .inl (by simpa only [Concurrent.heap_withHeap] using preserved)
    · have heapSame : before.heap = heap := by
        simpa only [Concurrent.heap_withHeap] using congrArg CReadOnly.typedHeap source
      cases heapSame
      exact .inr ⟨_, name, args, stack, found, source, exceptional⟩

end Rumoca.CStoreInvariant
namespace Rumoca.CStoreInvariant
open CCalls
variable [CInterface]

/-- Widening the exceptional names retains all ordinary-call frame obligations. -/
theorem ExceptPreserves.mono (previous : ExceptPreserves R special (program : Events.Program E))
    (includes : ∀ name, special name → wider name) : ExceptPreserves R wider program :=
  fun name fn found ordinary => previous name fn found (fun exceptional => ordinary (includes name exceptional))
end Rumoca.CStoreInvariant
