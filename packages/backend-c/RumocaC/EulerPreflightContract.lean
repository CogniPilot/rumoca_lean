import RumocaC.EulerPreflightCalls
import RumocaC.EulerPreflightSyntax

/-! Actual-source contract for the scalar interval preflight.
Exact bytes, independently specified tokens, canonical contextual execution,
and independent finite-prefix/real-overflow semantics are mandatory together.
File I/O, producer integration, native ABI and public time policy are outside
this proposition. No caller preservation premise substitutes for execution. -/
noncomputable section
namespace Rumoca.CEulerPreflight
open CMemory

theorem acceptance_iff_prefix (initial rate : Binary64.Value) (count : Nat) :
    (Solve.FiniteEuler.run initial rate count).isSome = true ↔
      ∃ after, Solve.FiniteEuler.Prefix initial rate count after := by
  constructor
  · intro accepted
    cases h : Solve.FiniteEuler.run initial rate count with
    | none => simp [h] at accepted
    | some after => exact ⟨after, (Solve.FiniteEuler.success_iff _ _ _ _).mp h⟩
  · rintro ⟨after, executed⟩
    rw [(Solve.FiniteEuler.success_iff _ _ _ _).mpr executed]
    rfl

/-- Rejection supplies an actually reachable finite prefix before a signed
real overflow, including either threshold tie; no post-overflow trajectory. -/
theorem rejection_iff_overflow (initial rate : Binary64.Value) (count : Nat) :
    (Solve.FiniteEuler.run initial rate count).isSome = false ↔
      ∃ k < count, ∃ before, Solve.FiniteEuler.Prefix initial rate k before ∧
        (Binary64.value before + Binary64.value rate ≤ -Binary64.overflowValue ∨
          Binary64.overflowValue ≤ Binary64.value before + Binary64.value rate) := by
  have rejected : (Solve.FiniteEuler.run initial rate count).isSome = false ↔
      Solve.FiniteEuler.run initial rate count = none := by
    cases Solve.FiniteEuler.run initial rate count <;> simp
  rw [rejected, Solve.FiniteEuler.failure_iff]
  rfl

def ArtifactContract (actual : String) : Prop :=
  actual = function.render ∧ Syntax.Denotes actual ∧
  (∀ (interface : CInterface) (declarations : CDeclaredMembers.Declarations)
    (objects : CDeclaredMembers.Objects) (p : CCalls.Program)
    (initial rate : Binary64.Value) (count : Nat) (heap : Heap),
    HeaderTypes interface → p.definitions function.signature.name = some (.tree function) →
    count < 2 ^ 64 →
    (∀ stack, Transition.Reaches
      (@CContextMachine.machine interface (@CContextMachine.declared interface declarations objects) p).step
      (.calling function.signature.name (argumentValues initial rate count) heap stack)
      (.returning (CBody.boolean (Solve.FiniteEuler.run initial rate count).isSome) heap stack)) ∧
    (∀ behavior,
      (@CContextMachine.machine interface (@CContextMachine.declared interface declarations objects) p).Behaves
        (.calling function.signature.name (argumentValues initial rate count) heap .done) behavior ↔
      behavior = .terminates ⟨CBody.boolean (Solve.FiniteEuler.run initial rate count).isSome, heap⟩)) ∧
  (∀ (initial rate : Binary64.Value) (count : Nat),
    ((Solve.FiniteEuler.run initial rate count).isSome = true ↔
      ∃ after, Solve.FiniteEuler.Prefix initial rate count after) ∧
    ((Solve.FiniteEuler.run initial rate count).isSome = false ↔
      ∃ k < count, ∃ before, Solve.FiniteEuler.Prefix initial rate k before ∧
        (Binary64.value before + Binary64.value rate ≤ -Binary64.overflowValue ∨
          Binary64.overflowValue ≤ Binary64.value before + Binary64.value rate)))

theorem artifact_correct (actual : String) (emitted : actual = function.render) :
    ArtifactContract actual := by
  refine ⟨emitted, emitted ▸ Syntax.render_denotes, ?_, ?_⟩
  · intro interface declarations objects p initial rate count heap header found bounded
    letI : CInterface := interface
    exact ⟨fun stack => call_reaches declarations objects p initial rate count heap stack
        found header bounded,
      call_correct declarations objects p initial rate count heap found header bounded⟩
  · intro initial rate count
    exact ⟨acceptance_iff_prefix initial rate count, rejection_iff_overflow initial rate count⟩

end Rumoca.CEulerPreflight
