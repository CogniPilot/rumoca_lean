import RumocaCore.Modelica.Array
import RumocaCore.Solve.Interface

/-! The declared interface of an array-profile source, produced from its
resolved AST: the `input` tensor, the `output` state tensor and, for a Jacobian
body, the `output` dense Jacobian, each with its declared extents. The state's
derivative reads the operands of its right-hand side and the Jacobian reads
the operands of the differentiated expression. -/
namespace Rumoca.ArrayProfile
open Rumoca.Solve

/-- The names the derivative right-hand side reads. -/
def Body.derivativeReads : Body → List String
  | .jacobian _ _ rhs _ _ => [rhs.left, rhs.right].eraseDups

/-- The declared Jacobian output of a Jacobian body. -/
def Body.outputs (dimensions : List Nat) : Body → List Declaration
  | .jacobian output _ _ _ call =>
      [⟨output, .output, .algebraic, ⟨dimensions⟩, none,
        [call.expression.left, call.expression.right].eraseDups⟩]

/-- The resolved declarations in source order. The input has no start
modifier and uses the Real fallback `0`; the state declares `each start=0`. -/
def Model.interface (m : Model) : Interface :=
  ⟨[⟨m.header.input, .input, .input, ⟨m.stateDimensions⟩, some 0, []⟩,
    ⟨m.header.state, .output, .state, ⟨m.stateDimensions⟩, some 0, m.body.derivativeReads⟩] ++
    m.body.outputs m.jacobianDimensions⟩

/-- Soundness of the declared interface: the declarations read back from the
parsed source tokens, with the causality of their prefixes and their written
subscripts, are exactly the resolved declarations. -/
theorem Model.interface_sound (m : Model) :
    declaredIn m.tokens = m.interface.declarations.map Declaration.signature := by
  cases hb : m.body
  simp [Model.tokens, Model.interface, hb, Header.tokens, Body.tokens,
    Body.outputs, Product.tokens, Call.tokens, declaredIn, declaredAfter, causalityBefore,
    subscriptAt, closeSubscript, subscriptTokens, Declaration.signature, Model.stateDimensions,
    Model.jacobianDimensions]
  decide


/-- A resolved array source declares distinct names. -/
theorem Model.interface_names (m : Model) (resolved : m.Resolved) :
    (m.interface.declarations.map Declaration.name).Nodup := by
  obtain ⟨_, distinct, _, _, body⟩ := resolved
  cases hb : m.body with
  | jacobian output derivative rhs assigned call =>
    rw [hb] at body
    obtain ⟨ne_input, ne_state, _⟩ := body
    simp [Model.interface, hb, Body.outputs, distinct, Ne.symm ne_input, Ne.symm ne_state]

/-- Every name a resolved array equation reads is declared: the operands of the
square and of the differentiated expression are the input. -/
theorem Model.interface_closed (m : Model) (resolved : m.Resolved) : m.interface.Closed := by
  obtain ⟨_, _, _, _, body⟩ := resolved
  intro d member name read
  cases hb : m.body with
  | jacobian output derivative rhs assigned call =>
    rw [hb] at body
    obtain ⟨_, _, _, left, right, _, _, expression_left, expression_right, _⟩ := body
    simp only [Model.interface, hb, Body.outputs, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · cases read
    · simp only [Body.derivativeReads, List.mem_eraseDups, List.mem_cons, List.not_mem_nil,
        or_false] at read
      rcases read with rfl | rfl <;> simp [Model.interface, hb, Body.outputs, left, right]
    · simp only [List.mem_eraseDups, List.mem_cons, List.not_mem_nil, or_false] at read
      rcases read with rfl | rfl <;>
        simp [Model.interface, hb, Body.outputs, expression_left, expression_right]

end Rumoca.ArrayProfile
