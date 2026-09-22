import RumocaC.LiteralEventInterface

/-! Reuse a proved internal call prefix in a larger program and interface.
Only the definitions reachable in the original prefix need binding agreement.
No behavior of the target's other functions or foreign callbacks is assumed. -/
noncomputable section
namespace Rumoca.CCalls.Events
open CTree CMemory CLiteral.Interface

/-- A proof fragment with no external outcomes. Use it only for internal
prefixes; this constructor does not restrict the actual runtime callbacks. -/
def Program.internalOnly [CInterface] (internal : CCalls.Program)
    (addresses : Address → Option String) : Program E where
  internal := internal
  addresses := addresses
  externals _ := none
  disjoint := by simp
  names := by simp

theorem internalNext_extends [CInterface] (original target : Program E)
    (definitions : ∀ name fn, original.internal.definitions name = some fn →
      target.internal.definitions name = some fn)
    (kernel : original.internal.kernel = target.internal.kernel)
    (addresses : original.addresses = target.addresses)
    (step : internalNext original s = some t) : internalNext target s = some t := by
  have entered (body : CLoops.State) (resultType : String) (stack : Typed.Continuation) :
      enterCall original body resultType stack = enterCall target body resultType stack := by
    cases body with
    | returned => rfl
    | running code env types heap =>
      cases code <;> simp [enterCall, enterCallWith, resolveWith, addresses]
  simp only [enterCall] at entered
  cases s with
  | calling name args heap stack =>
    cases found : original.internal.definitions name with
    | none => simp [internalNext, internalNextWith, Typed.nextWithExpressions, found] at step
    | some fn =>
      have actual := definitions name fn found
      cases fn <;> simp only [internalNext, internalNextWith, Typed.nextWithExpressions, actual]
        <;> simpa [internalNext, internalNextWith, Typed.nextWithExpressions, found] using step
  | body body resultType stack =>
    cases body <;> simpa only [internalNext, internalNextWith, Typed.nextWithExpressions, entered] using step
  | kernel body heap stack =>
    cases body <;> simpa only [internalNext, internalNextWith, Typed.nextWithExpressions, kernel] using step
  | returning value heap stack => exact step
  | halted result => exact step

/-- Transfer every silent transition, including loops and nested kernel calls,
from a checked program fragment to the actual larger runtime. Missing source
definitions cannot supply steps, and no target success trace is a premise. -/
theorem internal_reaches_interface (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (original : @Program before E) (target : @Program after E)
    (definitions : ∀ name fn, (@Program.internal before E original).definitions name = some fn →
      (@Program.internal after E target).definitions name = some fn)
    (kernel : (@Program.internal before E original).kernel = (@Program.internal after E target).kernel)
    (addresses : @Program.addresses before E original = @Program.addresses after E target)
    (checked : ProgramAgrees before after (@Program.internal before E original))
    (valid : StateAgrees before after s)
    (run : Transition.Reaches (fun s t => @internalNext E before original s = some t) s t) :
    Transition.Reaches (fun s t => @internalNext E after target s = some t) s t := by
  induction run with
  | refl => exact .refl _
  | next first rest ih =>
    have transported := (CLiteral.Interface.Events.internal_agreement before after types literals
      original _ valid).symm.trans first
    exact .next
      (internalNext_extends (CLiteral.Interface.Events.program types original) target
        definitions kernel addresses transported)
      (ih (CLiteral.Interface.Events.internal_agrees original checked valid first))

end Rumoca.CCalls.Events
end
