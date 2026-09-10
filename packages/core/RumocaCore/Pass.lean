/-! Reusable semantic pass contracts. Observations can include results, errors,
traces or divergence; the framework does not select a solver or target. -/
namespace Rumoca.Pass

/-- Every successful output has exactly its input's observable behaviors.
Rejection/completeness is a separate property, so this statement never claims
that all inputs compile merely because successful compilations are correct. -/
def Preserves (compile : A → Except E B) (source : A → O → Prop)
    (target : B → O → Prop) : Prop :=
  ∀ a b, compile a = .ok b → ∀ o, target b o ↔ source a o

def compose (first : A → Except E B) (second : B → Except E C) : A → Except E C :=
  fun a => (first a).bind second

theorem preserves_compose
    (h₁ : Preserves first source middle) (h₂ : Preserves second middle target) :
    Preserves (compose first second) source target := by
  intro a c hc o
  unfold compose at hc
  cases hb : first a with
  | error e => simp [hb, Except.bind] at hc
  | ok b =>
    have hs : second b = .ok c := by simpa [hb, Except.bind] using hc
    exact (h₂ b c hs o).trans (h₁ a b hb o)

/-- Target correctness transfers every property of source observations. -/
theorem preserves_property {compile : A → Except E B}
    {source : A → O → Prop} {target : B → O → Prop}
    (h : Preserves compile source target)
    (hc : compile a = .ok b) (property : O → Prop) (safe : ∀ o, source a o → property o) :
    ∀ o, target b o → property o := fun o ho => safe o ((h a b hc o).mp ho)

end Rumoca.Pass
