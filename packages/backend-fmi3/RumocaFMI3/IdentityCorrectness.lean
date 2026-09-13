import RumocaFMI3.IdentityCalls

/-! Complete private-validator calls. The independent acceptance condition
requires a non-whitespace byte in the name and equality with the prepared
token. The proof includes the actual body, parameter binding and library calls;
valid caller buffers and selected native/library bindings remain explicit. -/
noncomputable section
namespace Rumoca.FMI3.Identity
open CTree CMemory CStringMemory CStringOperations

def accepted (name whitespace token expected : List UInt8) : Bool :=
  name.any (fun byte => !whitespace.contains byte) && token == expected

theorem accepted_iff (name whitespace token expected : List UInt8) :
    accepted name whitespace token expected = true ↔
      (∃ byte ∈ name, byte ∉ whitespace) ∧ token = expected := by
  simp [accepted]

theorem accepted_span (name whitespace token expected : List UInt8) :
    accepted name whitespace token expected =
      ((!decide (span name whitespace = name.length)) && decide (token = expected)) := by
  apply Bool.eq_iff_iff.mpr
  simp [accepted, span_eq_length, not_forall]

variable [interface : CInterface]

theorem body_equivalence (program : CCalls.Events.Program E) (bindings : Bindings program)
    (name token expected whitespace : Address) (nameBytes tokenBytes expectedBytes whitespaceBytes : List UInt8)
    (heap : Heap) (nameStored : Contents heap name nameBytes) (tokenStored : Contents heap token tokenBytes)
    (expectedStored : Contents heap expected expectedBytes) (whitespaceStored : Contents heap whitespace whitespaceBytes)
    (fits : nameBytes.length < 2^64) (stack : CCalls.Typed.Continuation) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running body (locals ⟨some name, some token, some expected, some whitespace⟩ 0 0 0) types heap)
        "fmi3Boolean" stack) behavior ↔
    (CCalls.Events.machine program).Behaves
      (.returning (CBody.boolean (accepted nameBytes whitespaceBytes tokenBytes expectedBytes)) heap stack) behavior := by
  let args : Arguments := ⟨some name, some token, some expected, some whitespace⟩
  change (CCalls.Events.machine program).Behaves
    (.body (.running body (locals args 0 0 0) types heap) "fmi3Boolean" stack) behavior ↔ _
  unfold body
  rw [measure_equivalence program bindings args name rfl nameBytes heap nameStored fits]
  rw [prefix_equivalence program bindings args name whitespace rfl rfl nameBytes whitespaceBytes heap
    nameStored whitespaceStored fits]
  apply (CCalls.Events.internal_prefix_behaviors program
    (.next (CCalls.Events.body_step program
      (blank_step args nameBytes.length (span nameBytes whitespaceBytes) 0 heap [compareToken, comparisonReturn])
      "fmi3Boolean" stack) (.refl _)) behavior).trans
  by_cases blankName : span nameBytes whitespaceBytes = nameBytes.length
  · simp only [blankName, if_true, List.cons_append, List.nil_append]
    have returned := false_return program (locals args nameBytes.length (span nameBytes whitespaceBytes) 0)
      types heap [compareToken, comparisonReturn] stack bindings.boolean
    have refused : accepted nameBytes whitespaceBytes tokenBytes expectedBytes = false := by
      simp [accepted_span, blankName]
    rw [refused]
    simpa only [blankName] using CCalls.Events.internal_prefix_behaviors program returned behavior
  · simp only [blankName, if_false, List.nil_append]
    have acceptedToken : accepted nameBytes whitespaceBytes tokenBytes expectedBytes = decide (tokenBytes = expectedBytes) := by
      simp [accepted_span, blankName]
    rw [acceptedToken]
    exact comparison_equivalence program bindings args token expected rfl rfl tokenBytes expectedBytes heap
      tokenStored expectedStored nameBytes.length (span nameBytes whitespaceBytes) 0 stack behavior

/-- The helper preserves arbitrary caller observations, including later
errors and divergence. No successful helper execution is assumed. -/
theorem call_equivalence (program : CCalls.Events.Program E) (bindings : Bindings program)
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (name token expected whitespace : Address) (nameBytes tokenBytes expectedBytes whitespaceBytes : List UInt8)
    (heap : Heap) (nameStored : Contents heap name nameBytes) (tokenStored : Contents heap token tokenBytes)
    (expectedStored : Contents heap expected expectedBytes) (whitespaceStored : Contents heap whitespace whitespaceBytes)
    (fits : nameBytes.length < 2^64) (stack : CCalls.Typed.Continuation) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling function.signature.name
        (Arguments.values ⟨some name, some token, some expected, some whitespace⟩) heap stack) behavior ↔
    (CCalls.Events.machine program).Behaves
      (.returning (CBody.boolean (accepted nameBytes whitespaceBytes tokenBytes expectedBytes)) heap stack) behavior := by
  let args : Arguments := ⟨some name, some token, some expected, some whitespace⟩
  apply (CCalls.Events.internal_prefix_behaviors program
    (.next (CCalls.Events.tree_entry program _ args.values heap stack function _ _ defined
      (parameters_bound args bindings.pointer) (parameter_types bindings.pointer)) (.refl _)) behavior).trans
  apply (CCalls.Events.internal_prefix_behaviors program
    (CCalls.Events.body_reaches program (CLoops.run_reaches (initialization args heap bindings.size bindings.integer))
      "fmi3Boolean" stack) behavior).trans
  apply (CCalls.Events.internal_prefix_behaviors program
    (CCalls.Events.body_reaches program (CLoops.run_reaches
      (checks_pass name token expected whitespace heap bindings.voidPointer)) "fmi3Boolean" stack) behavior).trans
  exact body_equivalence program bindings name token expected whitespace nameBytes tokenBytes expectedBytes whitespaceBytes
    heap nameStored tokenStored expectedStored whitespaceStored fits stack behavior

theorem call_correct (program : CCalls.Events.Program E) (bindings : Bindings program)
    (defined : program.internal.definitions function.signature.name = some (.tree function))
    (name token expected whitespace : Address) (nameBytes tokenBytes expectedBytes whitespaceBytes : List UInt8)
    (heap : Heap) (nameStored : Contents heap name nameBytes) (tokenStored : Contents heap token tokenBytes)
    (expectedStored : Contents heap expected expectedBytes) (whitespaceStored : Contents heap whitespace whitespaceBytes)
    (fits : nameBytes.length < 2^64) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling function.signature.name
        (Arguments.values ⟨some name, some token, some expected, some whitespace⟩) heap .done) behavior ↔
      behavior = .terminates [] ⟨CBody.boolean (accepted nameBytes whitespaceBytes tokenBytes expectedBytes), heap⟩ := by
  rw [call_equivalence program bindings defined name token expected whitespace nameBytes tokenBytes expectedBytes whitespaceBytes
    heap nameStored tokenStored expectedStored whitespaceStored fits]
  exact (CCalls.Events.return_forced program _ heap).behaviors behavior

end Rumoca.FMI3.Identity
