import RumocaCore.Solve.Tensor.Forward

/-! Reverse execution with saved primal values. The forward sweep constructs
a pullback closure at each instruction. Applying it visits that saved tape
backwards; it never re-evaluates the primal program. Contributions accumulate
at typed references, including when both operands name the same register.
This is an executable reverse evaluator, not yet a static Solve-to-Solve
reverse transformation or a mutable target register allocation. -/
namespace Rumoca.Solve.Tensor
open Rumoca.Tensor

def Env.tail (env : Env α (s :: Γ)) : Env α Γ := fun r => env (.there r)

def Env.zeros (zero : α) : Env α Γ := fun {s} _ => Value.fill s zero

/-- Add one cotangent without replacing contributions from earlier uses. -/
def Env.addAt (ops : ScalarOps α) : Ref Γ s → Value α s → Env α Γ → Env α Γ
  | .here, value, env => Env.push (BinaryOp.eval ops .add (env .here) value) env.tail
  | .there r, value, env => Env.push (env .here) (Env.addAt ops r value env.tail)

structure ReverseResult (α : Type) (Γ : List Shape) (s : Shape) where
  value : Value α s
  pullback : Value α s → Env α Γ

def Program.reverse (ops : ScalarOps α) (zero one : α) :
    Program Γ s → Env α Γ → ReverseResult α Γ s
  | .ret r, env => ⟨env r, fun seed => Env.addAt ops r seed (Env.zeros zero)⟩
  | .fill shape value next, env =>
      let result := next.reverse ops zero one (env.push (Value.fill shape (value.eval zero one)))
      ⟨result.value, fun seed => Env.tail (result.pullback seed)⟩
  | .binary op left right next, env =>
      let x := env left
      let y := env right
      let result := next.reverse ops zero one (env.push (op.eval ops x y))
      ⟨result.value, fun seed =>
        let bars : Env α (_ :: Γ) := result.pullback seed
        let contributions := op.vjp ops x y (bars .here)
        Env.addAt ops right contributions.2 (Env.addAt ops left contributions.1 bars.tail)⟩

theorem Program.reverse_primal (p : Program Γ s) (ops : ScalarOps α) (zero one : α)
    (env : Env α Γ) : (p.reverse ops zero one env).value = p.eval ops zero one env := by
  induction p with
  | ret => rfl
  | fill shape value next ih => exact ih _
  | binary op left right next ih => exact ih _

end Rumoca.Solve.Tensor
