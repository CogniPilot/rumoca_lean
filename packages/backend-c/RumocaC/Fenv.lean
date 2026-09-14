import RumocaC.MathCalls
import RumocaC.LiteralInterfaceBody

/-! Explicit fenv header values for the selected signed-32-bit C int profile.
No numeric macro value, native header identity, mode stability or restoration
of floating exception flags is assumed by constructing this interface. -/
namespace Rumoca.CFenv
open CMemory CTree

structure Header where
  nearest : Int
  nonnegative : 0 ≤ nearest
  bounded : nearest < 2 ^ 31

abbrev Header.interface (header : Header) (base : CInterface) : CInterface :=
  { base with constants := fun name =>
      if name = "FE_TONEAREST" then some (.integer header.nearest) else base.constants name }

@[simp] theorem Header.nearest_binding (header : Header) (base : CInterface) :
    (header.interface base).constants "FE_TONEAREST" = some (.integer header.nearest) := by
  rfl

theorem Header.other_binding (header : Header) (base : CInterface) (name : String)
    (other : name ≠ "FE_TONEAREST") :
    (header.interface base).constants name = base.constants name := by
  exact if_neg other

theorem Header.nearest_typed (header : Header) :
    convert .int32 (.integer header.nearest) = some (.integer header.nearest) := by
  have range : -(2 ^ 31 : Int) ≤ header.nearest ∧ header.nearest < 2 ^ 31 := by
    have positive := header.nonnegative
    exact ⟨by omega, header.bounded⟩
  simp only [convert, if_pos range]

theorem Header.failure_distinct (header : Header) (observed : Int) (failure : observed < 0) :
    observed ≠ header.nearest := by
  have positive := header.nonnegative
  omega

theorem Header.expression_agrees (header : Header) (base : CInterface) (expr : Expr)
    (unused : "FE_TONEAREST" ∉ CLiteral.Interface.names expr) :
    CLiteral.Interface.ExprAgrees base (header.interface base) expr := by
  intro name member
  exact (header.other_binding base name (fun same => unused (same ▸ member))).symm

noncomputable section
variable [interface : CInterface]

/-- Observe rounding and choose the ordinary branch for every int32 result,
including negative failure. The rejected continuation retains its behavior. -/
theorem rounding_branch_path (header : Header) (program : CCalls.Events.Program E)
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (rejected rest : List Stmt) (resultType : String) (stack : CCalls.Typed.Continuation)
    (closed : rejected.all CLoops.noDeclarations = true)
    (integer : interface.types "int" = some .int32)
    (fresh : env "rounding" = none) (unshadowed : env "fegetround" = none)
    (macroUnshadowed : env "FE_TONEAREST" = none)
    (ordinary : interface.constants "fegetround" = none)
    (macroBound : interface.constants "FE_TONEAREST" = some (.integer header.nearest))
    (found : program.externals "fegetround" =
      some (CMathCalls.roundingExternal integer observed range)) :
    Transition.Events.Prefix (CCalls.Events.machine program)
      (.body (.running
        (.declare "int" "rounding" (.call (.id "fegetround") []) ::
         .branch (.bin .ne (.id "rounding") (.id "FE_TONEAREST")) rejected [] :: rest)
        env types heap) resultType stack)
      []
      (.body (.running ((if observed = header.nearest then [] else rejected) ++ rest)
        (CBody.bind env "rounding" (.integer observed))
        (CLoops.bindType types "rounding" .int32) heap) resultType stack) := by
  have entered := CMathCalls.rounding_declaration_path program env types heap "rounding"
    observed range
    (.branch (.bin .ne (.id "rounding") (.id "FE_TONEAREST")) rejected [] :: rest)
    resultType stack integer fresh unshadowed ordinary found
  have branchStep : CCalls.Events.internalNext program
      (.body (.running
        (.branch (.bin .ne (.id "rounding") (.id "FE_TONEAREST")) rejected [] :: rest)
        (CBody.bind env "rounding" (.integer observed))
        (CLoops.bindType types "rounding" .int32) heap) resultType stack) =
      some (.body (.running ((if observed = header.nearest then [] else rejected) ++ rest)
        (CBody.bind env "rounding" (.integer observed))
        (CLoops.bindType types "rounding" .int32) heap) resultType stack) := by
    apply CCalls.Events.body_step
    by_cases same : observed = header.nearest <;>
      simp [CLoops.next, CLoops.eval, CBody.eval, CBody.resolve, CBody.bind,
        CBody.constants, CBody.comparison, CBody.boolean, Value.truth,
        macroUnshadowed, macroBound, same, closed]
  simpa only [List.append_nil] using entered.trans
    (CCalls.Events.internal_path program (.next branchStep (.refl _)))

end
end Rumoca.CFenv
