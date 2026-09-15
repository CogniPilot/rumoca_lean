import RumocaC.CallFrameClassification
import RumocaC.AtomicFrame
import RumocaFMI3.RuntimeLinkage

/-! Ordinary flag frames, explicit logger contracts and attribution of changes. -/
noncomputable section
namespace Rumoca.FMI3.AtomicFlagFrame
open CTree CMemory CCalls CCalls.Events CStoreInvariant RuntimeLinkage
open CAtomicBoolean (Preserves)
variable [interface : CInterface]

def AtomicRoutine (name : String) : Prop :=
  name = "atomic_exchange" ∨ name = "atomic_store"

theorem static_library (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (found : StaticRuntime.library tag boolean size integer name = some fn)
    (ordinary : ¬ AtomicRoutine name) : ExternalPreserves Preserves fn := by
  have exchange : name ≠ "atomic_exchange" := fun h => ordinary (.inl h)
  have write : name ≠ "atomic_store" := fun h => ordinary (.inr h)
  have strings : CStringCalls.library size integer name = some fn := by
    simpa only [StaticRuntime.library, exchange, write] using found
  unfold CStringCalls.library at strings
  split at strings
  · cases Option.some.inj strings
    rintro args before events result after ⟨p, bytes, values, stored, bound, trace, value, rfl⟩
    exact .refl _
  · cases Option.some.inj strings
    rintro args before events result after ⟨p, q, bytes, accepted, values, stored, allowed, bound, trace, value, rfl⟩
    exact .refl _
  · cases Option.some.inj strings
    rintro args before events result after ⟨p, q, left, right, n, values, ls, rs, bound, compared, trace, value, rfl⟩
    exact .refl _
  · contradiction

theorem linked_flags (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → E)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31) :
    ExceptPreserves Preserves AtomicRoutine
      (linked model sigs covered tag boolean size integer double observed range) := by
  refine linked_except _ _
    (unranked_undefined model sigs covered (by change CallPolicy.functionRank "fegetround" = none; decide +kernel)) rfl ?_ ?_
  · refine linked_except _ _
      (unranked_undefined model sigs covered (by change CallPolicy.functionRank "floor" = none; decide +kernel)) rfl ?_ ?_
    · exact fun _ _ found ordinary => static_library tag boolean size integer found ordinary
    · intro ordinary
      rintro args before events result after ⟨x, values, trace, value, rfl⟩
      exact .refl _
  · intro ordinary
    rintro args before events result after ⟨values, trace, value, rfl⟩
    exact .refl _

/-- Atomic flag stability is a separate callback obligation from preservation
of object descriptors. It is stated only for the actual importer effect. -/
theorem logged_flags (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName))
    (callback : ∀ args before result after, effect.execute args before result after → Preserves before after) :
    ExceptPreserves Preserves AtomicRoutine
      (logged model sigs covered tag boolean size integer double observed range logger effect) := by
  exact linked_except _ _
    (unranked_undefined model sigs covered (by change CallPolicy.functionRank hostName = none; decide +kernel)) rfl
    (linked_flags model sigs covered tag boolean size integer double observed range)
    (fun _ args before _ result after executed => callback args before result after executed.2)

/-- Every actual shared step is either framed ordinary work or an actual atomic
call. No per-step annotation or ordinary-effect frame is an extra premise. -/
theorem logged_step (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName))
    (callback : ∀ args before result after, effect.execute args before result after → Preserves before after) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ before thread events after, Concurrent.Step program before thread events after →
      Preserves before.heap after.heap ∨
        ∃ saved name args stack, before.threads thread = some saved ∧
          Concurrent.withHeap saved before.heap = .calling name args before.heap stack ∧
          AtomicRoutine name := by
  intro program before thread events after step
  exact concurrent_classifies CAtomicBoolean.ordinary_stable
    (logged_flags model sigs covered tag boolean size integer double observed range logger effect callback) step

end Rumoca.FMI3.AtomicFlagFrame
noncomputable section
namespace Rumoca.FMI3.AtomicFlagFrame
open CTree CMemory CCalls CCalls.Events CStoreInvariant RuntimeLinkage
open CAtomicBoolean (Preserves)
variable [interface : CInterface]

theorem logged_exceptions (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName)) :
    ExceptPreserves Preserves (fun name => AtomicRoutine name ∨ name = hostName)
      (logged model sigs covered tag boolean size integer double observed range logger effect) := by
  exact linked_except _ _
    (unranked_undefined model sigs covered (by change CallPolicy.functionRank hostName = none; decide +kernel)) rfl
    ((linked_flags model sigs covered tag boolean size integer double observed range).mono
      (fun _ exceptional => .inl exceptional))
    (fun ordinary => False.elim (ordinary (.inr rfl)))

/-- Without any callback restriction, a flag-changing shared step is attributed
to an actual atomic routine or the concrete importer logger call. -/
theorem logged_changed_origin (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName)) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ before thread events after, Concurrent.Step program before thread events after →
      ¬ Preserves before.heap after.heap →
        ∃ saved name args stack, before.threads thread = some saved ∧
          Concurrent.withHeap saved before.heap = .calling name args before.heap stack ∧
          (AtomicRoutine name ∨ name = hostName) := by
  intro program before thread events after step changed
  exact (concurrent_classifies CAtomicBoolean.ordinary_stable
    (logged_exceptions model sigs covered tag boolean size integer double observed range logger effect) step).resolve_left changed

end Rumoca.FMI3.AtomicFlagFrame
