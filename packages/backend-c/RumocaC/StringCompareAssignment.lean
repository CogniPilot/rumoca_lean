import RumocaC.StringCalls
import RumocaC.NamedCallSites
import RumocaC.SilentCallChoices

/-! Compose a real strcmp call into an ordinary typed local assignment. The
continuation must account for every representable result with the specified
sign. Character contents, argument evaluation and external linkage are explicit;
no native string-library implementation is certified by this theorem. -/
noncomputable section
namespace Rumoca.CStringCalls
open CTree CMemory CStringMemory CStringOperations
variable [interface : CInterface]

theorem compare_assignment_equivalence (program : CCalls.Events.Program E)
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (destination : String) (args : List Expr) (rest : List Stmt)
    (resultType : String) (stack : CCalls.Typed.Continuation)
    (old : Value) (left right : Address) (leftBytes rightBytes : List UInt8)
    (pointer : interface.types "const char *" = some .pointer)
    (integer : interface.types "int" = some .int32)
    (present : env destination = some old) (typed : types destination = some .int32)
    (unshadowed : env "strcmp" = none) (named : interface.constants "strcmp" = none)
    (bound : program.externals "strcmp" = some (compareExternal integer))
    (evaluated : CCalls.arguments env heap args =
      some [.pointer (some left), .pointer (some right)])
    (leftStored : Contents heap left leftBytes) (rightStored : Contents heap right rightBytes)
    (target : CCalls.Typed.State)
    (continuation : ∀ value : Int, (-(2^31) ≤ value ∧ value < 2^31) →
      Comparison leftBytes rightBytes value → ∀ behavior,
      (CCalls.Events.machine program).Behaves
        (.body (.running rest (CBody.bind env destination (.integer value)) types heap)
          resultType stack) behavior ↔
      (CCalls.Events.machine program).Behaves target behavior)
    (behavior) :
    (CCalls.Events.machine program).Behaves
      (.body (.running (.assign (.id destination) (.call (.id "strcmp") args) :: rest)
        env types heap) resultType stack) behavior ↔
      (CCalls.Events.machine program).Behaves target behavior := by
  apply (CCalls.Events.internal_prefix_behaviors program
    (.next (CCalls.Events.named_assign_entry program env types heap destination "strcmp" args
      _ rest resultType stack old .int32 present typed unshadowed named (by decide) evaluated)
      (.refl _)) behavior).trans
  apply CCalls.Events.external_silent_equivalence program bound (pair_arguments pointer left right)
  · obtain ⟨value, range, compared⟩ := comparison_exists leftBytes rightBytes
    exact ⟨.integer value, heap,
      (compare_effect integer leftStored rightStored).mpr ⟨value, range, compared, rfl, rfl, rfl⟩⟩
  · intro events value after executed
    obtain ⟨_, _, _, silent, _, _⟩ := (compare_effect integer leftStored rightStored).mp executed
    exact silent
  · intro value after executed observed
    obtain ⟨value, range, compared, _, rfl, unchanged⟩ :=
      (compare_effect integer leftStored rightStored).mp executed
    subst after
    apply (CCalls.Events.internal_prefix_behaviors program
      (.next (CCalls.Events.assign_result program env types heap destination rest resultType stack
        old (.integer value) (.integer value) .int32 present typed
        (by simp only [convert, if_pos range])) (.refl _)) observed).trans
    exact continuation value range compared observed

end Rumoca.CStringCalls
end
