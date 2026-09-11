import Std

/-! Initialization preparation for the scalar unit-derivative profile.
A binding constrains the state throughout simulation. A start attribute is
an initial constraint only when fixed; completing an unfixed start records
the required diagnostic. The data is independent of either FMI backend. -/
namespace Rumoca.Initialization

structure Settings (α : Type) where
  binding : Option α := none
  start : Option α := none
  fixed : Bool := false
  deriving Repr

inductive Notice where
  | fallbackUsed
  | unfixedStartSelected
  deriving Repr, BEq, DecidableEq

inductive Error where
  | constantStateBinding
  deriving Repr, BEq, DecidableEq

structure Plan (α : Type) where
  initial : α
  notices : List Notice
  deriving Repr

def Settings.startValue (settings : Settings α) (fallback : α) : α :=
  settings.start.getD fallback

/-- The profile has `der(x) = 1`; a constant binding for x is inconsistent.
The default is supplied by the predefined Real type, not by a C backend. -/
def prepare (settings : Settings α) (fallback : α) : Except Error (Plan α) :=
  match settings.binding with
  | some _ => .error .constantStateBinding
  | none => .ok ⟨settings.startValue fallback,
      (if settings.start.isNone then [.fallbackUsed] else []) ++
      (if settings.fixed then [] else [.unfixedStartSelected])⟩

def Settings.map (f : α → β) (settings : Settings α) : Settings β :=
  ⟨settings.binding.map f, settings.start.map f, settings.fixed⟩

def Plan.map (f : α → β) (plan : Plan α) : Plan β :=
  ⟨f plan.initial, plan.notices⟩

/-- Interpreting finite constants cannot change the initialization decision
or its diagnostics. -/
theorem prepare_map (f : α → β) (settings : Settings α) (fallback : α) :
    prepare (settings.map f) (f fallback) = (prepare settings fallback).map (Plan.map f) := by
  cases settings with
  | mk binding start fixed =>
      cases binding <;> cases start <;> cases fixed <;> rfl

theorem prepare_initial (accepted : prepare settings fallback = .ok plan) :
    plan.initial = settings.startValue fallback := by
  unfold prepare at accepted
  split at accepted
  · contradiction
  · cases accepted
    rfl

theorem prepare_no_binding (accepted : prepare settings fallback = .ok plan) :
    settings.binding = none := by
  unfold prepare at accepted
  split at accepted
  · contradiction
  · assumption

theorem prepare_fallback_notice (accepted : prepare settings fallback = .ok plan) :
    Notice.fallbackUsed ∈ plan.notices ↔ settings.start = none := by
  cases settings with
  | mk binding start fixed =>
      cases binding <;> cases start <;> cases fixed <;>
        simp_all [prepare, Settings.startValue]
      all_goals cases accepted; simp

theorem prepare_selection_notice (accepted : prepare settings fallback = .ok plan) :
    Notice.unfixedStartSelected ∈ plan.notices ↔ settings.fixed = false := by
  cases settings with
  | mk binding start fixed =>
      cases binding <;> cases start <;> cases fixed <;>
        simp_all [prepare, Settings.startValue]
      all_goals cases accepted; simp

theorem prepare_default (fallback : α) :
    prepare (⟨none, none, false⟩ : Settings α) fallback =
      .ok ⟨fallback, [.fallbackUsed, .unfixedStartSelected]⟩ := rfl

/-- Extract a checked plan; an impossible failure is eliminated by the
success proof, rather than replaced by an executable fallback. -/
def checked (settings : Settings α) (fallback : α)
    (success : ∃ plan, prepare settings fallback = .ok plan) :
    {plan : Plan α // prepare settings fallback = .ok plan} :=
  match result : prepare settings fallback with
  | .ok plan => ⟨plan, rfl⟩
  | .error error => False.elim (by
      obtain ⟨plan, accepted⟩ := success
      rw [result] at accepted
      contradiction)

end Rumoca.Initialization
