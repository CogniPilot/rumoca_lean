import RumocaC.CallEventChoices
import RumocaC.LoopProofs

/-! Counted-loop composition in the actual call scheduler. A loop body may call
other internal functions; its proof is not restricted to the expression-only
loop machine. These lemmas preserve arbitrary caller continuations. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CTree CMemory CLoops
variable {E : Type} [interface : CInterface]

/-- Run any prefix ending at a loop condition, for example immediately before
the first invalid reference. Every increment fits the declared size_t bound. -/
theorem loop_prefix (program : Program E) (counter : String) (count : Expr)
    (body rest : List Stmt) (locals : Nat → CBody.Locals) (types : Types)
    (heaps : Nat → Heap) (n start stop : Nat) (resultType : String) (stack : Typed.Continuation)
    (range : start ≤ stop) (limit : stop ≤ n)
    (typed : types counter = some .size) (bounded : n < 2 ^ 64)
    (safe : body.all noDeclarations = true)
    (count_value : ∀ i ≤ n, CBody.eval (counterEnv (locals i) counter i) (heaps i) count = some (.integer n))
    (body_run : ∀ i, start ≤ i → i < stop →
      Transition.Reaches (fun s t => internalNext program s = some t)
        (.body (.running (body ++ counterStep counter :: loop counter count body :: rest)
          (counterEnv (locals i) counter i) types (heaps i)) resultType stack)
        (.body (.running (counterStep counter :: loop counter count body :: rest)
          (counterEnv (locals (i + 1)) counter i) types (heaps (i + 1))) resultType stack)) :
    Transition.Reaches (fun s t => internalNext program s = some t)
      (.body (.running (loop counter count body :: rest)
        (counterEnv (locals start) counter start) types (heaps start)) resultType stack)
      (.body (.running (loop counter count body :: rest)
        (counterEnv (locals stop) counter stop) types (heaps stop)) resultType stack) := by
  suffices ∀ remaining i, remaining + i = stop → start ≤ i →
    Transition.Reaches (fun s t => internalNext program s = some t)
      (.body (.running (loop counter count body :: rest)
        (counterEnv (locals i) counter i) types (heaps i)) resultType stack)
      (.body (.running (loop counter count body :: rest)
        (counterEnv (locals stop) counter stop) types (heaps stop)) resultType stack) from
    this (stop - start) start (by omega) (by omega)
  intro remaining
  induction remaining with
  | zero =>
      intro i total lower
      have same : i = stop := by omega
      subst i
      exact .refl _
  | succ remaining ih =>
      intro i total lower
      have less : i < n := by omega
      refine .next (body_step program (CLoops.loop_enter _ _ _ counter count body rest i n
        (by simp [counterEnv, CBody.bind]) (count_value i (by omega)) safe less) resultType stack) ?_
      exact (body_run i lower (by omega)).trans (.next
        (body_step program (counter_step _ types _ counter i _ typed (by omega)) resultType stack)
        (ih (i + 1) (by omega) (by omega)))

/-- Complete the loop, including its final false condition. Internal calls in
each proved body are executed in this same function table and scheduler. -/
theorem loop_reaches (program : Program E) (counter : String) (count : Expr)
    (body rest : List Stmt) (locals : Nat → CBody.Locals) (types : Types)
    (heaps : Nat → Heap) (n : Nat) (resultType : String) (stack : Typed.Continuation)
    (typed : types counter = some .size) (bounded : n < 2 ^ 64)
    (safe : body.all noDeclarations = true)
    (count_value : ∀ i ≤ n, CBody.eval (counterEnv (locals i) counter i) (heaps i) count = some (.integer n))
    (body_run : ∀ i < n,
      Transition.Reaches (fun s t => internalNext program s = some t)
        (.body (.running (body ++ counterStep counter :: loop counter count body :: rest)
          (counterEnv (locals i) counter i) types (heaps i)) resultType stack)
        (.body (.running (counterStep counter :: loop counter count body :: rest)
          (counterEnv (locals (i + 1)) counter i) types (heaps (i + 1))) resultType stack)) :
    Transition.Reaches (fun s t => internalNext program s = some t)
      (.body (.running (loop counter count body :: rest)
        (counterEnv (locals 0) counter 0) types (heaps 0)) resultType stack)
      (.body (.running rest (counterEnv (locals n) counter n) types (heaps n)) resultType stack) := by
  exact (loop_prefix program counter count body rest locals types heaps n 0 n resultType stack
    (by omega) (by omega) typed bounded safe count_value (fun i _ less => body_run i less)).trans
      (.next (body_step program (CLoops.loop_stop _ _ _ counter count body rest n
        (by simp [counterEnv, CBody.bind]) (count_value n (by omega)) safe) resultType stack) (.refl _))

end Rumoca.CCalls.Events

noncomputable section
namespace Rumoca.CLoops
open CTree CMemory
variable [interface : CInterface]

theorem counter_reset (env : CBody.Locals) (types : Types) (heap : Heap) (counter : String)
    (n : Nat) (rest : List Stmt) (typed : types counter = some .size) :
    next (.running (.assign (.id counter) (.nat 0) :: rest) (counterEnv env counter n) types heap) =
      some (.running rest (counterEnv env counter 0) types heap) := by
  have shadow : CBody.bind (counterEnv env counter n) counter (.integer 0) = counterEnv env counter 0 := by
    funext name
    by_cases equal : name = counter <;> simp [counterEnv, CBody.bind, equal]
  have executed := assign_local (counterEnv env counter n) types heap counter (.nat 0) rest
    (.integer n) (.integer 0) (.integer 0) .size
    (by simp [counterEnv, CBody.bind]) typed rfl (convert_size_nat 0 (by decide +kernel))
  simpa only [shadow] using executed

end Rumoca.CLoops
