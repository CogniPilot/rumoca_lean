import RumocaCore.Constant.Semantics

/-! The equation order is immaterial. Because resolution makes the derivative
names distinct, the equation naming a given state is unique, so a `find?` over a
permuted equation list returns the same equation, and every state keeps its
rate. The prepared IVP is therefore invariant under reordering the equations. -/
noncomputable section
namespace Rumoca.ConstantProfile
open Rumoca.Binary64

/-- A `find?` over permuted lists agrees when at most one element satisfies the
predicate. -/
theorem find?_perm_unique {α : Type*} {p : α → Bool} {l₁ l₂ : List α}
    (hperm : l₁.Perm l₂)
    (huniq : ∀ a ∈ l₁, ∀ b ∈ l₁, p a = true → p b = true → a = b) :
    l₁.find? p = l₂.find? p := by
  cases hf₁ : l₁.find? p with
  | none =>
    refine (List.find?_eq_none.mpr ?_).symm
    exact fun a ha => (List.find?_eq_none.mp hf₁) a (hperm.mem_iff.mpr ha)
  | some e =>
    have hpe : p e = true := List.find?_some hf₁
    have hme₁ : e ∈ l₁ := List.mem_of_find?_eq_some hf₁
    have hme₂ : e ∈ l₂ := hperm.mem_iff.mp hme₁
    cases hf₂ : l₂.find? p with
    | none =>
      rw [List.find?_eq_none] at hf₂
      exact absurd hpe (by simpa using hf₂ e hme₂)
    | some e' =>
      have hpe' : p e' = true := List.find?_some hf₂
      have hme₁' : e' ∈ l₁ := hperm.mem_iff.mpr (List.mem_of_find?_eq_some hf₂)
      rw [huniq e hme₁ e' hme₁' hpe hpe']

/-- Resolution makes the equation naming a state unique. -/
theorem Model.equation_unique (m : Model) (h : m.Resolved) (name : String)
    (a : Equation) (ha : a ∈ m.equations) (b : Equation) (hb : b ∈ m.equations)
    (hpa : (a.derivative == name) = true) (hpb : (b.derivative == name) = true) : a = b := by
  have hnd : (m.equations.map Equation.derivative).Nodup :=
    (List.Perm.nodup_iff h.2.2.1).mpr h.2.1
  have hda : a.derivative = name := by simpa using hpa
  have hdb : b.derivative = name := by simpa using hpb
  exact List.inj_on_of_nodup_map hnd ha hb (hda.trans hdb.symm)

/-- Reordering the equations preserves the rate of every state, and therefore
the whole prepared IVP is unchanged by the equation order. -/
theorem Model.decimalOf_perm {m₁ m₂ : Model} (hperm : m₁.equations.Perm m₂.equations)
    (h₁ : m₁.Resolved) (name : String) : m₁.decimalOf name = m₂.decimalOf name := by
  unfold Model.decimalOf Model.equationFor
  rw [find?_perm_unique hperm (m₁.equation_unique h₁ name)]

theorem Model.rateOf_perm {m₁ m₂ : Model} (hperm : m₁.equations.Perm m₂.equations)
    (h₁ : m₁.Resolved) (name : String) : m₁.rateOf name = m₂.rateOf name := by
  unfold Model.rateOf; rw [m₁.decimalOf_perm hperm h₁]

/-- With the same states, permuting the equations preserves the prepared IVP
rate at each index: the rate vector, hence the whole IVP, is independent of the
equation order. -/
theorem Model.lower_rates_perm {m₁ m₂ : Model} (hstates : m₁.states = m₂.states)
    (hperm : m₁.equations.Perm m₂.equations) (h₁ : m₁.Resolved)
    (i : Fin m₁.states.length) (j : Fin m₂.states.length) (hij : i.val = j.val) :
    (m₁.lower).rateValues i = (m₂.lower).rateValues j := by
  rw [Model.lower_rate, Model.lower_rate, m₁.rateOf_perm hperm h₁]
  congr 1
  rw [List.get_eq_getElem, List.get_eq_getElem]
  exact getElem_congr hstates hij _

end Rumoca.ConstantProfile
