import RumocaCore.Solve.Tensor

/-! Typed mutable tensor bindings. This uses the existing Solve reference
and environment types; no second untyped register map is introduced. -/
namespace Rumoca.Solve.Tensor
open Rumoca.Tensor Rumoca.Solve.Tensor

def Ref.position : Ref context shape → Nat
  | .here => 0
  | .there ref => Ref.position ref + 1

def Env.update (env : Env α context) (ref : Ref context shape) (value : Value α shape) :
    Env α context := match ref with
  | .here => Env.push value (fun r => env (.there r))
  | .there earlier => Env.push (env .here) (Env.update (fun r => env (.there r)) earlier value)

theorem Env.update_same (env : Env α context) (ref : Ref context shape) (value : Value α shape) :
    Env.update env ref value ref = value := by
  induction ref with
  | here => rfl
  | there ref ih => exact ih (fun r => env (.there r)) value

theorem Env.update_other (env : Env α context) (ref : Ref context shape) (value : Value α shape)
    (other : Ref context otherShape) (different : Ref.position other ≠ Ref.position ref) :
    Env.update env ref value other = env other := by
  induction ref with
  | here =>
    cases other with
    | here => exact False.elim (different rfl)
    | there other => rfl
  | there ref ih =>
    cases other with
    | here => rfl
    | there other =>
      exact ih (fun r => env (.there r)) value other
        (fun same => different (congrArg (· + 1) same))

/-- Equal binding positions recover dependent reference equality, not merely
equal tensor volumes. This is used only to prove the frame specification. -/
theorem Ref.position_agrees (ref : Ref context shape) (other : Ref context otherShape)
    (same : Ref.position other = Ref.position ref) :
    ∃ sameShape : otherShape = shape, sameShape ▸ other = ref := by
  induction ref with
  | here =>
    cases other with
    | here => exact ⟨rfl, rfl⟩
    | there other => simp [Ref.position] at same
  | there ref ih =>
    cases other with
    | here => simp [Ref.position] at same
    | there other =>
      obtain ⟨sameShape, sameRef⟩ := ih other (Nat.add_right_cancel same)
      cases sameShape
      cases sameRef
      exact ⟨rfl, rfl⟩

/-- Independent whole-environment assignment: exact addressed value, with a
frame for every other binding even when it has a different nominal shape. -/
def Env.Updates (before : Env α context) (ref : Ref context shape) (value : Value α shape)
    (after : Env α context) : Prop :=
  after ref = value ∧ ∀ {otherShape} (other : Ref context otherShape),
    Ref.position other ≠ Ref.position ref → after other = before other

theorem Env.update_correct (before : Env α context) (ref : Ref context shape) (value : Value α shape)
    (after : Env α context) : Env.Updates before ref value after ↔ @after = @Env.update α context shape before ref value := by
  constructor
  · rintro ⟨same, frame⟩
    funext otherShape other
    by_cases atTarget : Ref.position other = Ref.position ref
    · obtain ⟨sameShape, sameRef⟩ := Ref.position_agrees ref other atTarget
      cases sameShape
      cases sameRef
      exact same.trans (Env.update_same before other value).symm
    · exact (frame other atTarget).trans (Env.update_other before ref value other atTarget).symm
  · rintro rfl
    exact ⟨Env.update_same before ref value, fun other different => Env.update_other before ref value other different⟩

theorem Env.update_self (env : Env α context) (ref : Ref context shape) :
    @Env.update α context shape env ref (env ref) = @env :=
  ((Env.update_correct env ref (env ref) env).mp ⟨rfl, fun _ _ => rfl⟩).symm

theorem Env.update_twice (env : Env α context) (ref : Ref context shape)
    (first second : Value α shape) :
    @Env.update α context shape (Env.update env ref first) ref second =
      @Env.update α context shape env ref second := by
  apply ((Env.update_correct (Env.update env ref first) ref second (Env.update env ref second)).mp ?_).symm
  exact ⟨Env.update_same env ref second, fun other different =>
    (Env.update_other env ref second other different).trans
      (Env.update_other env ref first other different).symm⟩

end Rumoca.Solve.Tensor
