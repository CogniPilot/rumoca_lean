import RumocaC.LoopCalls

/-! Parameter binding checks the adjusted header types before body entry.
Successful binding has exact arity and a matching type environment; all stored
values are stable under their declared conversion. Unknown types are rejected.
This is the authored object-level C profile, not a native ABI theorem. -/
noncomputable section
namespace Rumoca.CCalls.Parameters
open CTree CMemory
open CLoops.Calls (parameterTypes)
variable [interface : CInterface]

omit interface in
theorem convert_stable (type : CType) (value result : Value)
    (h : convert type value = some result) : convert type result = some result := by
  cases type with
  | float64 =>
    cases value <;> simp [convert] at h
    · split at h
      · rw [← Option.some.inj h]; rfl
      · split at h
        · rw [← Option.some.inj h]; rfl
        · contradiction
    · cases h; rfl
  | int32 =>
    cases value <;> simp [convert] at h
    rcases h with ⟨bounds, rfl⟩
    simpa [convert] using bounds
  | size =>
    cases value <;> simp [convert] at h
    rcases h with ⟨bounds, rfl⟩
    simpa [convert] using bounds
  | character signed =>
    cases value <;> simp [convert] at h
    rcases h with ⟨bounds, rfl⟩
    simpa [convert] using bounds
  | unsigned width =>
    cases value <;> simp [convert] at h
    subst result
    simp [convert, CUnsigned.value_idempotent]
  | pointer => cases value <;> simp [convert] at h; cases h; rfl
  | boolean | atomicBoolean =>
    cases ht : value.truth <;> simp [convert, ht] at h
    rename_i b
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
    · rw [← h]; rfl
    · rw [← h]; rfl

def Coherent (env : CBody.Locals) (types : CLoops.Types) : Prop :=
  ∀ name, (env name = none ∧ types name = none) ∨
    ∃ value type, env name = some value ∧ types name = some type ∧
      convert type value = some value

omit interface in
theorem coherent_domain (env : CBody.Locals) (types : CLoops.Types)
    (h : Coherent env types) (name : String) :
    (env name).isSome = (types name).isSome := by
  rcases h name with ⟨he, ht⟩ | ⟨v, t, he, ht, _⟩ <;> simp [he, ht]

omit interface in
theorem coherent_bind (env : CBody.Locals) (types : CLoops.Types)
    (name : String) (value : Value) (type : CType)
    (h : Coherent env types) (hv : convert type value = some value) :
    Coherent (CBody.bind env name value) (CLoops.bindType types name type) := by
  intro key
  by_cases he : key = name
  · exact Or.inr ⟨value, type, by simp [CBody.bind, he], by simp [CLoops.bindType, he], hv⟩
  · simpa [CBody.bind, CLoops.bindType, he] using h key

theorem parameters_typed (ps : List Parameter) (vs : List Value) (env : CBody.Locals)
    (h : parameters ps vs = some env) :
    ∃ types, parameterTypes ps = some types ∧ Coherent env types := by
  induction ps generalizing vs env with
  | nil =>
    cases vs with
    | nil =>
      simp only [parameters, Option.some.injEq] at h
      cases h
      exact ⟨_, rfl, fun _ => Or.inl ⟨rfl, rfl⟩⟩
    | cons => simp [parameters] at h
  | cons p ps ih =>
    cases vs with
    | nil => simp [parameters] at h
    | cons v vs =>
      cases hb : parameters ps vs with
      | none => simp [parameters, hb] at h
      | some tail =>
        rcases ih vs tail hb with ⟨types, ht, coherent⟩
        by_cases fresh : (tail p.name).isSome = true
        · simp [parameters, hb, fresh] at h
        · have tfresh : (types p.name).isSome ≠ true := by
            rwa [← coherent_domain tail types coherent p.name]
          cases hc : interface.types (CCalls.parameterType p) with
          | none => simp [parameters, hb, CBody.cast, hc] at h
          | some type =>
            cases hv : convert type v with
            | none => simp [parameters, hb, CBody.cast, hc, hv] at h
            | some value =>
              have he : CBody.bind tail p.name value = env := by
                simpa [parameters, hb, fresh, CBody.cast, hc, hv] using h
              subst env
              refine ⟨CLoops.bindType types p.name type, ?_, ?_⟩
              · simp [parameterTypes, ht, tfresh, hc]
              · exact coherent_bind tail types p.name value type coherent (convert_stable type v value hv)

theorem parameters_length (ps : List Parameter) (vs : List Value) (env : CBody.Locals)
    (h : parameters ps vs = some env) : ps.length = vs.length := by
  induction ps generalizing vs env with
  | nil => cases vs <;> simp_all [parameters]
  | cons p ps ih =>
    cases vs with
    | nil => simp [parameters] at h
    | cons v vs =>
      cases ht : parameters ps vs with
      | none => simp [parameters, ht] at h
      | some tail => simpa using ih vs tail ht

theorem parameters_unknown (p : Parameter) (ps : List Parameter) (vs : List Value)
    (unknown : interface.types (CCalls.parameterType p) = none) :
    parameters (p :: ps) vs = none := by
  cases vs with
  | nil => rfl
  | cons v vs =>
    cases ht : parameters ps vs <;> simp [parameters, ht, CBody.cast, unknown]

end Rumoca.CCalls.Parameters
