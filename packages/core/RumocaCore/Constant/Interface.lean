import RumocaCore.Constant.Semantics
import RumocaCore.Solve.Interface

/-! The declared interface of a constant-rate source, produced from its resolved
AST: one prefix-free scalar `Real` state per source declaration, in source
order, each starting from its completed initialization plan. A constant
derivative reads no variable. -/
namespace Rumoca.ConstantProfile
open Rumoca.Solve _root_.Parser

/-- The resolved declaration of one source state. -/
def Model.declaration (m : Model) (state : String) : Declaration :=
  ⟨state, .local, .state, Tensor.scalar, some (m.plan state).initial, []⟩

/-- The resolved declarations in source order. -/
def Model.interface (m : Model) : Interface := ⟨m.states.map m.declaration⟩

/-- A token that does not begin a `Real` declaration only becomes the preceding
token of the rest of the stream. -/
private theorem declared_skip (previous : Option Token) (t : Token) (rest : List Token)
    (other : t ≠ .literal "Real") :
    declaredAfter previous (t :: rest) = declaredAfter (some t) rest := by
  rw [declaredAfter.eq_def]
  split
  · rename_i h; cases h
  · rename_i h; cases h; exact absurd rfl other
  · rename_i h; cases h; rfl

private theorem declared_states (previous : Option Token) (ss : List String) (rest : List Token)
    (prefixFree : causalityBefore previous = .local) :
    declaredAfter previous (ss.flatMap declTokens ++ rest) =
      ss.map (fun s => (s, Causality.local, ([] : List Token))) ++
        declaredAfter (if ss = [] then previous else some (.literal ";")) rest := by
  induction ss generalizing previous with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.flatMap_cons, declTokens, List.cons_append, List.nil_append,
      List.map_cons, reduceCtorEq, if_false]
    rw [declaredAfter.eq_def]
    simp only [prefixFree, subscriptAt]
    rw [declared_skip _ _ _ (by decide), ih _ rfl]
    cases ss <;> simp

private theorem declared_equations (previous : Option Token) (es : List Equation) (rest : List Token) :
    declaredAfter previous (es.flatMap equationTokens ++ rest) =
      declaredAfter (if es = [] then previous else some (.literal ";")) rest := by
  induction es generalizing previous with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons, equationTokens, List.cons_append, List.nil_append,
      reduceCtorEq, if_false]
    rw [declared_skip _ _ _ (by decide), declared_skip _ _ _ (by decide),
      declared_skip _ _ _ (by simp), declared_skip _ _ _ (by decide),
      declared_skip _ _ _ (by decide), declared_skip _ _ _ (by simp),
      declared_skip _ _ _ (by decide), ih]
    cases es <;> simp

/-- Soundness of the declared interface: the declarations read back from the
parsed source tokens are the resolved declarations, one prefix-free scalar per
source state in source order. -/
theorem Model.interface_sound (m : Model) :
    declaredIn m.tokens = m.interface.declarations.map Declaration.signature := by
  simp only [declaredIn, Model.tokens, List.cons_append, List.nil_append, List.append_assoc]
  rw [declared_skip _ _ _ (by decide), declared_skip _ _ _ (by simp),
    declared_states _ _ _ rfl, declared_skip _ _ _ (by decide), declared_equations]
  simp only [Model.interface, List.map_map]
  rw [declared_skip _ _ _ (by decide), declared_skip _ _ _ (by simp),
    declared_skip _ _ _ (by decide)]
  simp [declaredAfter, Function.comp_def, Model.declaration, Declaration.signature, subscriptTokens,
    Tensor.scalar]


/-- A resolved constant-rate source declares distinct names. -/
theorem Model.interface_names (m : Model) (resolved : m.Resolved) :
    (m.interface.declarations.map Declaration.name).Nodup := by
  simpa [Model.interface, Model.declaration, List.map_map, Function.comp_def] using resolved.2.1

/-- A constant derivative reads no variable. -/
theorem Model.interface_closed (m : Model) : m.interface.Closed := by
  intro d member name read
  simp only [Model.interface, List.mem_map] at member
  obtain ⟨_, _, rfl⟩ := member
  cases read

end Rumoca.ConstantProfile
