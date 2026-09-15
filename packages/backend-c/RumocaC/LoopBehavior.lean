import RumocaC.LoopEvents

/-! Counted-loop composition for bodies whose actual external calls are silent.
Behavior equivalence retains all legal call outcomes and arbitrary subsequent
observations. It does not assume an internal-only path through a library call. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CTree CMemory CLoops
variable {E : Type} [interface : CInterface]

theorem loop_prefix_equivalence (program : Program E) (counter : String) (count : Expr)
    (body rest : List Stmt) (locals : Nat → CBody.Locals) (types : Types)
    (heaps : Nat → Heap) (n start stop : Nat) (resultType : String) (stack : Typed.Continuation)
    (range : start ≤ stop) (limit : stop ≤ n)
    (typed : types counter = some .size) (bounded : n < 2^64)
    (safe : body.all noDeclarations = true)
    (count_value : ∀ i ≤ n, CBody.eval (counterEnv (locals i) counter i) (heaps i) count = some (.integer n))
    (body_equivalent : ∀ i, start ≤ i → i < stop → ∀ behavior,
      (machine program).Behaves
        (.body (.running (body ++ counterStep counter :: loop counter count body :: rest)
          (counterEnv (locals i) counter i) types (heaps i)) resultType stack) behavior ↔
      (machine program).Behaves
        (.body (.running (counterStep counter :: loop counter count body :: rest)
          (counterEnv (locals (i + 1)) counter i) types (heaps (i + 1))) resultType stack) behavior)
    (behavior) :
    (machine program).Behaves
      (.body (.running (loop counter count body :: rest)
        (counterEnv (locals start) counter start) types (heaps start)) resultType stack) behavior ↔
    (machine program).Behaves
      (.body (.running (loop counter count body :: rest)
        (counterEnv (locals stop) counter stop) types (heaps stop)) resultType stack) behavior := by
  suffices ∀ remaining i, remaining + i = stop → start ≤ i →
    ((machine program).Behaves
      (.body (.running (loop counter count body :: rest)
        (counterEnv (locals i) counter i) types (heaps i)) resultType stack) behavior ↔
    (machine program).Behaves
      (.body (.running (loop counter count body :: rest)
        (counterEnv (locals stop) counter stop) types (heaps stop)) resultType stack) behavior) from
    this (stop - start) start (by omega) (by omega)
  intro remaining
  induction remaining with
  | zero =>
    intro i total lower
    have same : i = stop := by omega
    subst i
    exact Iff.rfl
  | succ remaining ih =>
    intro i total lower
    have less : i < n := by omega
    apply (internal_prefix_behaviors program
      (.next (body_step program (CLoops.loop_enter _ _ _ counter count body rest i n
        (by simp [counterEnv, CBody.bind]) (count_value i (by omega)) safe less) resultType stack)
        (.refl _)) behavior).trans
    apply (body_equivalent i lower (by omega) behavior).trans
    apply (internal_prefix_behaviors program
      (.next (body_step program (counter_step _ types _ counter i _ typed (by omega)) resultType stack)
        (.refl _)) behavior).trans
    exact ih (i + 1) (by omega) (by omega)

end Rumoca.CCalls.Events
end
