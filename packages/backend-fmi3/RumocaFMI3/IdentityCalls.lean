import RumocaFMI3.IdentitySteps
import RumocaC.StringCalls
import RumocaC.SilentCallChoices

/-! Compose actual library calls and their local results inside the identity
validator. Every legal strcmp result is retained, and arbitrary later caller
observations are preserved. Native library/ABI correspondence is separate. -/
noncomputable section
namespace Rumoca.FMI3.Identity
open CTree CMemory CStringMemory CStringOperations
variable [interface : CInterface]

structure Bindings (program : CCalls.Events.Program E) : Prop where
  pointer : interface.types "const char *" = some .pointer
  voidPointer : interface.types "void *" = some .pointer
  size : interface.types "size_t" = some .size
  integer : interface.types "int" = some .int32
  boolean : interface.types "fmi3Boolean" = some .boolean
  lengthName : interface.constants "strlen" = none
  spanName : interface.constants "strspn" = none
  compareName : interface.constants "strcmp" = none
  lengthBinding : program.externals "strlen" = some (CStringCalls.lengthExternal size)
  spanBinding : program.externals "strspn" = some (CStringCalls.spanExternal size)
  compareBinding : program.externals "strcmp" = some (CStringCalls.compareExternal integer)

theorem measure_equivalence (program : CCalls.Events.Program E) (bindings : Bindings program)
    (args : Arguments) (name : Address) (hasName : args.name = some name)
    (bytes : List UInt8) (heap : Heap) (stored : Contents heap name bytes) (fits : bytes.length < 2^64)
    (length prefixLength : Nat) (difference : Int) (rest : List Stmt) (stack : CCalls.Typed.Continuation) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (measure :: rest) (locals args length prefixLength difference) types heap) "fmi3Boolean" stack) behavior ↔
    (CCalls.Events.machine program).Behaves
      (.body (.running rest (locals args bytes.length prefixLength difference) types heap) "fmi3Boolean" stack) behavior := by
  apply (CCalls.Events.internal_prefix_behaviors program
    (.next (measure_enter program args length prefixLength difference heap rest stack bindings.lengthName) (.refl _)) behavior).trans
  rw [hasName]
  apply CCalls.Events.external_silent_equivalence program bindings.lengthBinding
    (CStringCalls.single_arguments bindings.pointer name)
  · exact ⟨.integer bytes.length, heap, (CStringCalls.length_effect bindings.size stored).mpr ⟨fits, rfl, rfl, rfl⟩⟩
  · intro events value after executed
    exact ((CStringCalls.length_effect bindings.size stored).mp executed).2.1
  · intro value after executed observed
    obtain ⟨_, _, rfl, unchanged⟩ := (CStringCalls.length_effect bindings.size stored).mp executed
    subst after
    exact CCalls.Events.internal_prefix_behaviors program
      (.next (length_resume program args length prefixLength bytes.length difference heap rest stack fits) (.refl _)) observed

theorem prefix_equivalence (program : CCalls.Events.Program E) (bindings : Bindings program)
    (args : Arguments) (name whitespace : Address)
    (hasName : args.name = some name) (hasWhitespace : args.whitespace = some whitespace)
    (bytes accepted : List UInt8) (heap : Heap)
    (stored : Contents heap name bytes) (allowed : Contents heap whitespace accepted) (fits : bytes.length < 2^64)
    (length prefixLength : Nat) (difference : Int) (rest : List Stmt) (stack : CCalls.Typed.Continuation) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (measurePrefix :: rest) (locals args length prefixLength difference) types heap) "fmi3Boolean" stack) behavior ↔
    (CCalls.Events.machine program).Behaves
      (.body (.running rest (locals args length (span bytes accepted) difference) types heap) "fmi3Boolean" stack) behavior := by
  apply (CCalls.Events.internal_prefix_behaviors program
    (.next (prefix_enter program args length prefixLength difference heap rest stack bindings.spanName) (.refl _)) behavior).trans
  rw [hasName, hasWhitespace]
  apply CCalls.Events.external_silent_equivalence program bindings.spanBinding
    (CStringCalls.pair_arguments bindings.pointer name whitespace)
  · exact ⟨.integer (span bytes accepted), heap,
      (CStringCalls.span_effect bindings.size stored allowed).mpr ⟨fits, rfl, rfl, rfl⟩⟩
  · intro events value after executed
    exact ((CStringCalls.span_effect bindings.size stored allowed).mp executed).2.1
  · intro value after executed observed
    obtain ⟨_, _, rfl, unchanged⟩ := (CStringCalls.span_effect bindings.size stored allowed).mp executed
    subst after
    exact CCalls.Events.internal_prefix_behaviors program
      (.next (prefix_resume program args length prefixLength (span bytes accepted) difference heap rest stack
        (lt_of_le_of_lt (span_le_length bytes accepted) fits)) (.refl _)) observed

theorem comparison_equivalence (program : CCalls.Events.Program E) (bindings : Bindings program)
    (args : Arguments) (token expected : Address)
    (hasToken : args.token = some token) (hasExpected : args.expected = some expected)
    (tokenBytes expectedBytes : List UInt8) (heap : Heap)
    (tokenStored : Contents heap token tokenBytes) (expectedStored : Contents heap expected expectedBytes)
    (length prefixLength : Nat) (old : Int) (stack : CCalls.Typed.Continuation) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running [compareToken, comparisonReturn] (locals args length prefixLength old) types heap) "fmi3Boolean" stack) behavior ↔
    (CCalls.Events.machine program).Behaves
      (.returning (CBody.boolean (decide (tokenBytes = expectedBytes))) heap stack) behavior := by
  apply (CCalls.Events.internal_prefix_behaviors program
    (.next (compare_enter program args length prefixLength old heap [comparisonReturn] stack bindings.compareName) (.refl _)) behavior).trans
  rw [hasToken, hasExpected]
  apply CCalls.Events.external_silent_equivalence program bindings.compareBinding
    (CStringCalls.pair_arguments bindings.pointer token expected)
  · obtain ⟨n, range, compared⟩ := comparison_exists tokenBytes expectedBytes
    exact ⟨.integer n, heap,
      (CStringCalls.compare_effect bindings.integer tokenStored expectedStored).mpr ⟨n, range, compared, rfl, rfl, rfl⟩⟩
  · intro events value after executed
    obtain ⟨n, range, compared, noEvents, _, _⟩ :=
      (CStringCalls.compare_effect bindings.integer tokenStored expectedStored).mp executed
    exact noEvents
  · intro value after executed observed
    obtain ⟨n, range, compared, _, rfl, unchanged⟩ :=
      (CStringCalls.compare_effect bindings.integer tokenStored expectedStored).mp executed
    subst after
    have same : decide (n = 0) = decide (tokenBytes = expectedBytes) := by
      simp only [comparison_zero compared]
    have returned := comparison_return program args length prefixLength n heap [] stack bindings.boolean
    rw [same] at returned
    exact CCalls.Events.internal_prefix_behaviors program
      (.next (compare_resume program args length prefixLength old n heap [comparisonReturn] stack range) returned) observed

end Rumoca.FMI3.Identity
