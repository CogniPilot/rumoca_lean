import RumocaC.LiteralInterfaceCalls

/-! Changing unused global bindings preserves the body machine, including
failure and divergence. This local theorem can reuse body proofs when other
functions in the enclosing program intentionally use the added globals. -/
namespace Rumoca.CLiteral.Interface
open CTree CMemory

def BodyAgrees (before after : CInterface) : CBody.State → Prop
  | .running code _ _ => CodeAgrees before after code
  | .returned _ => True

theorem body_next_agrees (valid : BodyAgrees before after s)
    (step : @CBody.next before s = some t) : BodyAgrees before after t := by
  unfold CBody.next CBody.nextWith at step
  split at step
  all_goals aesop (add simp [BodyAgrees, CodeAgrees, StmtAgrees,
    Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff])

theorem body_next_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (s : CBody.State) (valid : BodyAgrees before after s) :
    @CBody.next before s = @CBody.next after s := by
  cases s with
  | returned result => rfl
  | running code env heap =>
      cases code with
      | nil => rfl
      | cons stmt rest =>
          have head := valid stmt (by simp)
          cases stmt with
          | declare type name value =>
              simp only [StmtAgrees] at head
              have ev := (expression_agreement before after types literals env heap value head).1
              simp [CBody.next, CBody.nextWith, CBody.legacyExpressions, ev, cast_agreement before after types]
          | assign target value =>
              simp only [StmtAgrees] at head
              have ev := (expression_agreement before after types literals env heap value head.2).1
              have lv := (expression_agreement before after types literals env heap target head.1).2
              simp [CBody.next, CBody.nextWith, CBody.legacyExpressions, ev, lv]
          | eval value =>
              simp only [StmtAgrees] at head
              have ev := (expression_agreement before after types literals env heap value head).1
              simp [CBody.next, CBody.nextWith, CBody.legacyExpressions, ev]
          | ret value =>
              cases value with
              | none => rfl
              | some value =>
                  simp only [StmtAgrees] at head
                  have ev := (expression_agreement before after types literals env heap value head).1
                  simp [CBody.next, CBody.nextWith, CBody.legacyExpressions, ev]
          | branch condition yes no =>
              simp only [StmtAgrees] at head
              have ev := (expression_agreement before after types literals env heap condition head.1).1
              simp [CBody.next, CBody.nextWith, CBody.legacyExpressions, ev]
          | whileLoop condition body =>
              simp only [StmtAgrees] at head
              have ev := (expression_agreement before after types literals env heap condition head.1).1
              simp [CBody.next, CBody.nextWith, CBody.legacyExpressions, ev]

/-- Every bounded execution attempt agrees, including attempts that get stuck.
This equality does not require a successful original execution. -/
theorem body_run_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (n : Nat) (s : CBody.State) (valid : BodyAgrees before after s) :
    @CBody.run before n s = @CBody.run after n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      have same := body_next_agreement before after types literals s valid
      cases step : @CBody.next before s with
      | none => simp [CBody.run, ← same, step]
      | some t =>
          simpa only [CBody.run, ← same, step, Option.bind_some] using
            ih t (body_next_agrees valid step)

def body_bisimulation (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals) :
    Transition.FunctionalBisimulation (@CBody.machine before) (@CBody.machine after) where
  map := id
  Valid := BodyAgrees before after
  step valid step := ⟨body_next_agrees valid step,
    (body_next_agreement before after types literals _ valid).symm.trans step⟩
  reflect valid step := ⟨_, (body_next_agreement before after types literals _ valid).trans step, rfl⟩
  final := by intro s valid; cases s <;> rfl

/-- Exact returned values/heaps, stuck behavior and divergence survive the
interface change. Only bindings used by this body's syntax must agree. -/
theorem body_behaviors (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (valid : BodyAgrees before after s) (behavior) :
    (@CBody.machine after).Behaves s behavior ↔ (@CBody.machine before).Behaves s behavior :=
  (body_bisimulation before after types literals).behaviors valid behavior

end Rumoca.CLiteral.Interface
