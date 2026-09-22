import RumocaC.CallEventChoices
import RumocaC.Statements

/-! Numerical public-call composition through the shared event scheduler. The event scheduler
executes the existing numerical statement semantics without host observations
or memory effects; all caller continuations are retained. -/
noncomputable section
namespace Rumoca.CCalls.Events
variable {E : Type} [interface : CInterface]
open CMemory

theorem kernel_step (program : Program E)
    (step : CStatements.next program.internal.kernel s = some t) (heap stack) :
    internalNext program (.kernel s heap stack) = some (.kernel t heap stack) := by
  cases s <;> simp_all [CStatements.next, internalNext, internalNextWith, Typed.nextWithExpressions]

theorem kernel_reaches (program : Program E)
    (path : CStatements.Reaches program.internal.kernel s t) (heap stack) :
    Transition.Reaches (fun a b => internalNext program a = some b)
      (.kernel s heap stack) (.kernel t heap stack) := by
  induction path with
  | refl => exact .refl _
  | next step _ ih => exact .next (kernel_step program step heap stack) ih

/-- This uses the existing proved C statements for the stored Solve program,
not an assumed derivative callback or a selected numerical result. -/
theorem kernel_correct (program : Program E) (model : Solve.Model source)
    (same : program.internal.kernel = Rumoca.CExecution.program model) (fn x n heap stack) :
    Transition.Reaches (fun a b => internalNext program a = some b)
      (.kernel (.entry fn x n) heap stack)
      (.returning (.finite (CStatements.result model fn x n)) heap stack) := by
  have path := CStatements.call_reaches model fn x n
  rw [← same] at path
  exact (kernel_reaches program path heap stack).trans (.next rfl (.refl _))

theorem kernel_behaviors (program : Program E) (model : Solve.Model source)
    (same : program.internal.kernel = Rumoca.CExecution.program model) (fn x n heap stack behavior) :
    (machine program).Behaves (.kernel (.entry fn x n) heap stack) behavior ↔
      (machine program).Behaves
        (.returning (.finite (CStatements.result model fn x n)) heap stack) behavior :=
  internal_prefix_behaviors program (kernel_correct program model same fn x n heap stack) behavior

end Rumoca.CCalls.Events
