import RumocaC.LiteralCallLowering

/-! Interface extension must preserve lookups in the original program before
literal lowering can use the additional data symbols. These expression facts
keep that obligation separate from the same-interface lowering theorem. -/
namespace Rumoca.CLiteral.Interface
open CTree CMemory

def names : Expr → List String
  | .id name => [name]
  | .bin _ a b | .index a b => names a ++ names b
  | .not a | .deref a | .address a | .field a _ _ | .cast _ a => names a
  | .call fn args => names fn ++ args.flatMap names
  | .nat _ | .decimal _ _ _ | .str _ | .sizeof _ => []

private theorem other_call (interface : CInterface) (env : CBody.Locals) (heap : Heap)
    (fn a : Expr) (other : fn ≠ .id "isfinite") :
    @CBody.eval interface env heap (.call fn [a]) = none := by
  cases fn <;> simp_all [CBody.eval]

theorem expression_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (env : CBody.Locals) (heap : Heap) (e : Expr)
    (agree : ∀ name ∈ names e, before.constants name = after.constants name) :
    @CBody.eval before env heap e = @CBody.eval after env heap e ∧
      @CBody.lvalue before env heap e = @CBody.lvalue after env heap e := by
  revert agree
  induction e using Expr.rec (motive_2 := fun args => ∀ a ∈ args,
      (∀ name ∈ names a, before.constants name = after.constants name) →
        @CBody.eval before env heap a = @CBody.eval after env heap a ∧
        @CBody.lvalue before env heap a = @CBody.lvalue after env heap a) with
  | id name =>
      intro agree
      simp [CBody.eval, CBody.lvalue, CBody.resolve, CBody.constants,
        agree name (by simp [names])]
  | nat | decimal | sizeof => intro agree; simp [CBody.eval, CBody.lvalue]
  | str text => intro agree; simp [CBody.eval, CBody.lvalue, literals]
  | bin op a b ha hb =>
      intro agree
      have left := ha (fun name member => agree name (by simp [names, member]))
      have right := hb (fun name member => agree name (by simp [names, member]))
      cases op <;> simp [CBody.eval, CBody.lvalue, left.1, right.1]
  | index a b ha hb =>
      intro agree
      have left := ha (fun name member => agree name (by simp [names, member]))
      have right := hb (fun name member => agree name (by simp [names, member]))
      simp [CBody.eval, CBody.lvalue, left.1, left.2, right.1]
  | not a ha | deref a ha | address a ha | field a name pointer ha =>
      intro agree
      have same := ha (by simpa only [names] using agree)
      simp [CBody.eval, CBody.lvalue, same.1, same.2]
  | cast type a ha =>
      intro agree
      have same := ha (by simpa only [names] using agree)
      have casts (value : Value) :
          @CBody.expressionCast before type a value = @CBody.expressionCast after type a value := by
        unfold CBody.expressionCast CBody.cast
        rw [types]
      simp only [CBody.eval, CBody.lvalue, same.1, casts, and_self]
  | call fn args hfn hargs =>
      intro agree
      refine ⟨?_, by simp [CBody.lvalue]⟩
      cases args with
      | nil => cases fn <;> simp [CBody.eval]
      | cons a rest =>
          cases rest with
          | cons b rest => cases fn <;> simp [CBody.eval]
          | nil =>
              have same := (hargs a (by simp))
                (fun name member => agree name (by simp [names, member]))
              by_cases intrinsic : fn = .id "isfinite"
              · subst fn; simp [CBody.eval, same.1]
              · rw [other_call before env heap fn a intrinsic, other_call after env heap fn a intrinsic]
  | nil => simp_all
  | cons a rest ha hr =>
      rename_i value member agree
      rcases List.mem_cons.mp member with rfl | member
      · exact ha agree
      · exact hr value member agree

theorem loop_expression_agreement (before after : CInterface)
    (types : before.types = after.types) (literals : before.literals = after.literals)
    (env : CBody.Locals) (locals : CLoops.Types) (heap : Heap) (e : Expr)
    (agree : ∀ name ∈ names e, before.constants name = after.constants name) :
    @CLoops.eval before env locals heap e = @CLoops.eval after env locals heap e := by
  have whole := (expression_agreement before after types literals env heap e agree).1
  cases e with
  | bin op a b =>
      have left := (expression_agreement before after types literals env heap a
        (fun name member => agree name (by simp [names, member]))).1
      have right := (expression_agreement before after types literals env heap b
        (fun name member => agree name (by simp [names, member]))).1
      cases op
      case add =>
        cases a <;> cases b <;> simp [CLoops.eval, left, right]
        rename_i name value
        by_cases unit : value = 1 <;> simp_all
      case mul => simp [CLoops.eval, left, right]
      case sub => simp [CLoops.eval, left, right]
      case div => simp [CLoops.eval, left, right]
      all_goals simpa only [CLoops.eval] using whole
  | _ => simpa only [CLoops.eval] using whole

/-- Preserve the supplied header dictionary, using the additional data
bindings only for names absent from it. Declaration legality is separate. -/
@[reducible] def extend (before : CInterface) (globals : String → Option Value) : CInterface where
  constants name := (before.constants name).orElse (fun _ => globals name)
  types := before.types
  literals := before.literals

theorem extend_existing (before : CInterface) (globals : String → Option Value)
    (known : before.constants name = some value) :
    (extend before globals).constants name = some value := by
  change (before.constants name).orElse (fun _ => globals name) = some value
  simp [known]

/-- Adding fresh global data bindings cannot repair or alter an identifier
lookup in the original expression. Missing bindings and failures are retained. -/
theorem expression_extended (before : CInterface) (globals : String → Option Value)
    (env : CBody.Locals) (heap : Heap) (e : Expr)
    (fresh : ∀ name ∈ names e, globals name = none) :
    @CBody.eval (extend before globals) env heap e = @CBody.eval before env heap e ∧
      @CBody.lvalue (extend before globals) env heap e = @CBody.lvalue before env heap e := by
  apply expression_agreement (extend before globals) before rfl rfl env heap e
  intro name member
  change (before.constants name).orElse (fun _ => globals name) = before.constants name
  rw [fresh name member]
  cases before.constants name <;> rfl

end Rumoca.CLiteral.Interface
