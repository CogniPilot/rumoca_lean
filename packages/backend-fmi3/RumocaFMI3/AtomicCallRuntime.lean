import RumocaFMI3.AtomicCallPolicy
import RumocaFMI3.RuntimeLinkage

/-! Generated public invocations retain atomic-call values through actual shared-heap interleavings. -/
namespace Rumoca.FMI3.AtomicCallPolicy
open CTree CMemory CCalls CCallSites CCalls.Events RuntimeLinkage
variable [interface : CInterface]

theorem logged_named_only (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName))
    (selected : desired name = some busy) :
    NamedOnly (logged model sigs covered tag boolean size integer double observed range logger effect) name := by
  intro address found
  change (if address = logger then some hostName else none) = some name at found
  split at found
  · cases Option.some.inj found
    simp [desired, hostName] at selected
  · contradiction

omit interface in
theorem ranked_entry (ranked : CallPolicy.functionRank name = some rank) : desired name = none := by
  by_cases exchange : name = "atomic_exchange"
  · subst name
    have absent : CallPolicy.functionRank "atomic_exchange" = none := by decide +kernel
    rw [absent] at ranked
    contradiction
  · by_cases release : name = "atomic_store"
    · subst name
      have absent : CallPolicy.functionRank "atomic_store" = none := by decide +kernel
      rw [absent] at ranked
      contradiction
    · simp [desired, exchange, release]

omit interface in
theorem entry_valid (unrestricted : desired entry = none) (args : List Value) : ValidCall entry args := by
  intro busy selected
  rw [unrestricted] at selected
  contradiction

/-- Every finite path from a generated public entry respects atomic call
values. The heap and every returning foreign choice are unrestricted here;
address validity, flag frames and lease ownership are separate properties. -/
theorem logged_reaches (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName)) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ (sig : Signature), sig ∈ sigs → ∀ args heap events after,
      Transition.Events.Reaches (Events.machine program).step
        (.calling sig.name args heap .done) events after → Ready Permitted ValidCall after := by
  intro program sig member args heap events after path
  apply reaches_ready program (program_policy model sigs)
    (operand_sound program boolean (fun _ _ selected =>
      logged_named_only model sigs covered tag boolean size integer double observed range logger effect selected))
    (show Ready Permitted ValidCall (.calling sig.name args heap .done) from ?_) path
  exact ⟨entry_valid (ranked_entry (CallPolicy.covered_ranks covered sig member)) args, True.intro⟩

/-- Arbitrary shared-heap interleavings preserve the same call-value rule.
The initial threads are ordinary generated public invocations; no annotation
of later reservation/release calls or completed-call outcome is a premise. -/
theorem logged_concurrent_reaches (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName)) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ (before after : Concurrent.State),
      (∀ thread saved, before.threads thread = some saved →
        ∃ sig ∈ sigs, ∃ args heap, saved = .calling sig.name args heap .done) →
      Transition.Reaches (fun a b => ∃ thread events, Concurrent.Step program a thread events b) before after →
      ThreadsReady Permitted ValidCall after := by
  intro program before after entries path
  apply concurrent_reaches program (program_policy model sigs)
    (operand_sound program boolean (fun _ _ selected =>
      logged_named_only model sigs covered tag boolean size integer double observed range logger effect selected))
    (show ThreadsReady Permitted ValidCall before from ?_) path
  intro thread saved found
  obtain ⟨sig, member, args, heap, rfl⟩ := entries thread saved found
  exact ⟨entry_valid (ranked_entry (CallPolicy.covered_ranks covered sig member)) args, True.intro⟩

omit interface in
theorem exchange_value (ready : ThreadsReady Permitted ValidCall state)
    (calling : state.threads thread = some (.calling "atomic_exchange" args heap stack)) :
    ∃ pointer, args = [pointer, CAtomicBoolean.value true] :=
  (ready thread _ calling).1 true rfl

omit interface in
theorem release_value (ready : ThreadsReady Permitted ValidCall state)
    (calling : state.threads thread = some (.calling "atomic_store" args heap stack)) :
    ∃ pointer, args = [pointer, CAtomicBoolean.value false] :=
  (ready thread _ calling).1 false rfl

end Rumoca.FMI3.AtomicCallPolicy
