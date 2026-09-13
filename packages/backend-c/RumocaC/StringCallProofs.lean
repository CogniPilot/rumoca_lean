import RumocaC.StringCalls

/-! Complete call behavior for the selected string bindings, from valid
null-terminated input memory. No successful foreign execution is supplied as
a premise. The native library remains an explicit binding boundary. -/
noncomputable section
namespace Rumoca.CStringCalls
open CMemory CStringMemory CStringOperations
variable [interface : CInterface]

theorem length_behaviors (program : CCalls.Events.Program E)
    (size : interface.types "size_t" = some .size) (pointer : interface.types "const char *" = some .pointer)
    (bound : program.externals "strlen" = some (lengthExternal size))
    (stored : Contents heap p bytes) (fits : bytes.length < 2^64) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling "strlen" [.pointer (some p)] heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer bytes.length, heap⟩ := by
  exact CCalls.Events.external_behaviors program bound (single_arguments pointer p)
    ((length_effect size stored).mpr ⟨fits, rfl, rfl, rfl⟩)
    (fun _ _ _ executed => ((length_effect size stored).mp executed).2) behavior

theorem span_behaviors (program : CCalls.Events.Program E)
    (size : interface.types "size_t" = some .size) (pointer : interface.types "const char *" = some .pointer)
    (bound : program.externals "strspn" = some (spanExternal size))
    (stored : Contents heap p bytes) (allowed : Contents heap q accepted) (fits : bytes.length < 2^64) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling "strspn" [.pointer (some p), .pointer (some q)] heap .done)
      behavior ↔ behavior = .terminates [] ⟨.integer (span bytes accepted), heap⟩ := by
  exact CCalls.Events.external_behaviors program bound (pair_arguments pointer p q)
    ((span_effect size stored allowed).mpr ⟨fits, rfl, rfl, rfl⟩)
    (fun _ _ _ executed => ((span_effect size stored allowed).mp executed).2) behavior

/-- All legal strcmp results are covered, including implementations returning
larger positive or negative magnitudes. Valid strings provide a terminating
outcome; neither wrong nor divergent behaviors occur in this binding model. -/
theorem compare_behaviors (program : CCalls.Events.Program E)
    (integer : interface.types "int" = some .int32) (pointer : interface.types "const char *" = some .pointer)
    (bound : program.externals "strcmp" = some (compareExternal integer))
    (leftStored : Contents heap p left) (rightStored : Contents heap q right) (behavior) :
    (CCalls.Events.machine program).Behaves (.calling "strcmp" [.pointer (some p), .pointer (some q)] heap .done)
      behavior ↔ ∃ n : Int, (-(2^31) ≤ n ∧ n < 2^31) ∧ Comparison left right n ∧
        behavior = .terminates [] ⟨.integer n, heap⟩ := by
  rw [CCalls.Events.external_choices_behaviors program bound (pair_arguments pointer p q)
    (fun value after => ⟨value, after⟩)
    (fun _ value after _ => CCalls.Events.return_forced program value after)]
  constructor
  · rintro (⟨events, result, after, executed, observed⟩ | ⟨missing, wrong⟩)
    · obtain ⟨n, range, compared, rfl, rfl, rfl⟩ := (compare_effect integer leftStored rightStored).mp executed
      exact ⟨n, range, compared, observed⟩
    · obtain ⟨n, range, compared⟩ := comparison_exists left right
      exact False.elim (missing [] (.integer n) heap
        ((compare_effect integer leftStored rightStored).mpr ⟨n, range, compared, rfl, rfl, rfl⟩))
  · rintro ⟨n, range, compared, observed⟩
    exact Or.inl ⟨[], .integer n, heap,
      (compare_effect integer leftStored rightStored).mpr ⟨n, range, compared, rfl, rfl, rfl⟩, observed⟩

/-- The equality observation used by identity validation is independent of
the allowed implementation-dependent nonzero comparison magnitude. -/
theorem compare_zero (integer : interface.types "int" = some .int32)
    (leftStored : Contents heap p left) (rightStored : Contents heap q right)
    (executed : (compareExternal (E := E) integer).execute [.pointer (some p), .pointer (some q)]
      heap events (.integer n) after) : (n = 0 ↔ left = right) ∧ events = [] ∧ after = heap := by
  obtain ⟨result, range, compared, rfl, same, rfl⟩ := (compare_effect integer leftStored rightStored).mp executed
  have values := Value.integer.inj same
  subst result
  exact ⟨comparison_zero compared, rfl, rfl⟩

end Rumoca.CStringCalls
