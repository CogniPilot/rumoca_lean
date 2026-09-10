import RumocaCore.Driven.IR
import Mathlib.Data.Real.Basic

/-! Equation equivalence at each declarative lowering, followed by the
executable tensor derivative, initialization and observation contracts. -/
namespace Rumoca.Driven
open Rumoca.Tensor Solve.Tensor

def Model.Equation (m : Model) (values derivatives : String → ℝ) : Prop :=
  derivatives m.derivativeName = values m.rhsName

def Model.Initial (m : Model) (values : String → ℝ) : Prop := values m.state = 0

def Flat.Model.Equation (m : Flat.Model source) (state input derivative : Value ℝ scalar) : Prop :=
  m.lhs.eval 0 state input derivative = m.rhs.eval 0 state input derivative

def Flat.Model.Initial (m : Flat.Model source) (state input derivative : Value ℝ scalar) : Prop :=
  m.initialLhs.eval 0 state input derivative = m.initialRhs.eval 0 state input derivative

def singleton (x : α) : Value α scalar := Value.fill scalar x

theorem singleton_injective : Function.Injective (singleton (α := α)) := by
  intro x y h
  have h := congrArg (fun (v : Value α scalar) => v[0]) h
  simpa [singleton] using h

theorem Flat.lower_correct (m : Driven.Model) (h : Resolved m)
    (values derivatives : String → ℝ) :
    m.Equation values derivatives ↔
      (lower m h).Equation (singleton (values m.state))
        (singleton (values m.input)) (singleton (derivatives m.state)) := by
  simp only [Model.Equation, lower, Expr.eval, Driven.Model.Equation, h.2.1, h.2.2.1]
  exact singleton_injective.eq_iff.symm

/-- Residual denotation is coordinatewise real subtraction; neither the IR
nor its lowering expands it into a list of scalar equations. -/
def DAE.Expr.eval (state input derivative : Value ℝ shape) : DAE.Expr shape → Denotation ℝ shape
  | .derivative => fun i => derivative[i]
  | .input => fun i => input[i]
  | .state => fun i => state[i]
  | .zero => fun _ => 0
  | .sub a b => fun i => a.eval state input derivative i - b.eval state input derivative i

def DAE.Model.Equation (m : DAE.Model source) (state input derivative : Value ℝ scalar) : Prop :=
  ∀ i, m.residual.eval state input derivative i = 0

def DAE.Model.Initial (m : DAE.Model source) (state input derivative : Value ℝ scalar) : Prop :=
  ∀ i, m.initialResidual.eval state input derivative i = 0

theorem DAE.lower_correct (m : Flat.Model source) (state input derivative : Value ℝ scalar) :
    m.Equation state input derivative ↔ (lower m).Equation state input derivative := by
  simp only [Flat.Model.Equation, m.lhs_source, m.rhs_source, Flat.Expr.eval,
    Model.Equation, lower, lowerExpr, Expr.eval, sub_eq_zero]
  exact ⟨fun h i => congrArg (fun v : Value ℝ scalar => v[i]) h,
    fun h => Value.ext fun i hi => h ⟨i, hi⟩⟩

theorem Solved.lower_correct (m : DAE.Model source) (state input derivative : Value ℝ scalar) :
    m.Equation state input derivative ↔ derivative = (lower m).ivp.rhs (0 : ℝ) 1 state input := by
  simp only [DAE.Model.Equation, m.residual_source, m.flat.lhs_source,
    m.flat.rhs_source, DAE.lowerExpr, DAE.Expr.eval, sub_eq_zero,
    lower, Solve.driven_rhs]
  exact ⟨fun h => Value.ext fun i hi => h ⟨i, hi⟩,
    fun h i => congrArg (fun v : Value ℝ scalar => v[i]) h⟩

theorem lowering_chain_correct (m : Model) (h : Resolved m)
    (values derivatives : String → ℝ) :
    m.Equation values derivatives ↔
      singleton (derivatives m.state) =
        (Solved.lower (DAE.lower (Flat.lower m h))).ivp.rhs (0 : ℝ) 1 (singleton (values m.state))
          (singleton (values m.input)) :=
  (Flat.lower_correct m h values derivatives).trans
    ((DAE.lower_correct _ _ _ _).trans (Solved.lower_correct _ _ _ _))

theorem Flat.lower_initial (m : Driven.Model) (h : Resolved m)
    (values derivatives : String → ℝ) :
    m.Initial values ↔ (lower m h).Initial (singleton (values m.state))
      (singleton (values m.input)) (singleton (derivatives m.state)) := by
  change values m.state = 0 ↔ singleton (values m.state) = singleton 0
  exact singleton_injective.eq_iff.symm

theorem DAE.lower_initial (m : Flat.Model source) (state input derivative : Value ℝ scalar) :
    m.Initial state input derivative ↔ (lower m).Initial state input derivative := by
  simp only [Flat.Model.Initial, m.initialLhs_source, m.initialRhs_source, Flat.Expr.eval,
    Model.Initial, lower, lowerExpr, Expr.eval, sub_zero]
  constructor
  · intro h i
    have h := congrArg (fun v : Value ℝ scalar => v[i]) h
    simpa using h
  · intro h
    apply Value.ext
    intro i hi
    simpa using h ⟨i, hi⟩

theorem Solved.lower_initial (m : DAE.Model source) (state input derivative : Value ℝ scalar) :
    m.Initial state input derivative ↔ state = (lower m).ivp.initial (0 : ℝ) 1 := by
  simp only [DAE.Model.Initial, m.initialResidual_source, m.flat.initialLhs_source,
    m.flat.initialRhs_source, DAE.lowerExpr, DAE.Expr.eval, sub_zero,
    lower, Solve.driven_initial]
  constructor
  · intro h
    apply Value.ext
    intro i hi
    simpa using h ⟨i, hi⟩
  · intro h i
    have h := congrArg (fun v : Value ℝ scalar => v[i]) h
    simpa using h

theorem initialization_chain_correct (m : Model) (h : Resolved m)
    (values derivatives : String → ℝ) :
    m.Initial values ↔ singleton (values m.state) =
      (Solved.lower (DAE.lower (Flat.lower m h))).ivp.initial (0 : ℝ) 1 :=
  (Flat.lower_initial m h values derivatives).trans
    ((DAE.lower_initial _ _ _ _).trans (Solved.lower_initial _ _ _ _))

theorem initialization_correct (m : DAE.Model source) :
    (Solved.lower m).ivp.initial (0 : ℝ) 1 = singleton 0 := rfl

theorem output_correct (m : DAE.Model source) (state input : Value α scalar) (zero one : α) :
    (Solved.lower m).ivp.outputs zero one state input = state := rfl

end Rumoca.Driven
