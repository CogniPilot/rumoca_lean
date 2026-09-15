import Std

/-! The continuous, event-free FMI 3 profile. This table is shared with code
generation; Reference.Allowed separately records the reference lifecycle
rules for the implemented commands (FMI 3.0.2 §§2.3, 3.2, 4.2).
Errors enter Terminated (FMI 3.0.2 §2.3.1); final-value queries remain
available there (§2.3.8). This does not model pointers, argument validity,
callbacks or native execution. -/
namespace Rumoca.FMI3

inductive Kind where | me | cs
  deriving Repr, BEq, DecidableEq
inductive Mode where | instantiated | initialization | event | continuous | step | terminated
  deriving Repr, BEq, DecidableEq
inductive Command where
  | enterInitialization | exitInitialization | enterEvent | enterContinuous
  | updateDiscrete | evaluateDiscrete | terminate | reset | get | setStart | setVariables
  | setTime | setStates | getStates | getDerivatives | getNominals | getCounts
  | completedStep | doStep | logging
  deriving Repr, BEq, DecidableEq

def Mode.code : Mode → Nat
  | .instantiated => 0 | .initialization => 1 | .event => 2 | .continuous => 3
  | .step => 4 | .terminated => 5

def permittedModes : Command → Kind → List Mode
  | .enterInitialization, _ => [.instantiated]
  | .exitInitialization, _ => [.initialization]
  | .enterEvent, .me => [.continuous]
  | .enterContinuous, .me => [.event]
  | .updateDiscrete, .me => [.event]
  | .evaluateDiscrete, .me => [.event]
  | .terminate, .me => [.event, .continuous]
  | .terminate, .cs => [.step]
  | .reset, _ => [.instantiated, .initialization, .event, .continuous, .step, .terminated]
  | .get, _ | .logging, _ => [.instantiated, .initialization, .event, .continuous, .step, .terminated]
  | .setStart, .me => [.instantiated, .initialization, .event, .continuous]
  | .setStart, .cs => [.instantiated, .initialization]
  | .setVariables, .me => [.instantiated, .initialization, .event, .continuous]
  | .setVariables, .cs => [.instantiated, .initialization, .step]
  | .setTime, .me => [.continuous]
  | .setStates, .me => [.continuous]
  | .getStates, .me => [.initialization, .event, .continuous, .terminated]
  | .getDerivatives, .me => [.initialization, .event, .continuous, .terminated]
  | .getNominals, .me => [.initialization, .event, .continuous, .terminated]
  | .getCounts, .me => [.instantiated, .event]
  | .completedStep, .me => [.continuous]
  | .doStep, .cs => [.step]
  | _, _ => []

def allowed (c : Command) (k : Kind) (m : Mode) : Bool := (permittedModes c k).contains m

namespace Reference
def Allowed (c : Command) (k : Kind) (m : Mode) : Prop :=
  match c with
  | .enterInitialization => m = .instantiated
  | .exitInitialization => m = .initialization
  | .enterEvent => k = .me ∧ m = .continuous
  | .enterContinuous | .updateDiscrete => k = .me ∧ m = .event
  | .evaluateDiscrete => k = .me ∧ m = .event
  | .terminate => (k = .me ∧ (m = .event ∨ m = .continuous)) ∨ (k = .cs ∧ m = .step)
  | .reset => True
  | .get | .logging => True
  | .setStart => m = .instantiated ∨ m = .initialization ∨
      (k = .me ∧ (m = .event ∨ m = .continuous))
  | .setVariables => m = .instantiated ∨ m = .initialization ∨
      (k = .me ∧ (m = .event ∨ m = .continuous)) ∨ (k = .cs ∧ m = .step)
  | .getStates | .getDerivatives | .getNominals => k = .me ∧
      (m = .initialization ∨ m = .event ∨ m = .continuous ∨ m = .terminated)
  | .setTime | .setStates | .completedStep => k = .me ∧ m = .continuous
  | .getCounts => k = .me ∧ (m = .instantiated ∨ m = .event)
  | .doStep => k = .cs ∧ m = .step
end Reference

theorem allowed_correct (c : Command) (k : Kind) (m : Mode) :
    allowed c k m = true ↔ Reference.Allowed c k m := by
  cases c <;> cases k <;> cases m <;>
    simp [Reference.Allowed, allowed, permittedModes] <;> decide +kernel

/-- General setter endpoints for the implemented interface modes. Per-variable
selection, pointer validity and CS getter/setter ordering are separate. Empty
selections do not license a setter after Terminated (FMI 3.0.2 §2.3.8). -/
theorem variable_setter_allowed_iff (k : Kind) (m : Mode) :
    allowed .setVariables k m = true ↔
      m = .instantiated ∨ m = .initialization ∨
        (k = .me ∧ (m = .event ∨ m = .continuous)) ∨ (k = .cs ∧ m = .step) :=
  allowed_correct .setVariables k m

theorem variable_setter_terminated (k : Kind) :
    allowed .setVariables k .terminated = false := by
  cases k <;> rfl

/-- Preservation of the existing raw state-assignment domain does not by
itself establish that domain's full correspondence to legal FMI issuance. -/
theorem state_assignment_endpoint (valid : Reference.Allowed .setStart k m) :
    Reference.Allowed .setVariables k m := by
  rcases valid with first | second | state
  · exact Or.inl first
  · exact Or.inr (Or.inl second)
  · exact Or.inr (Or.inr (Or.inl state))

theorem cs_empty_setter_endpoint :
    allowed .setVariables .cs .step = true ∧ allowed .setStart .cs .step = false := by
  decide +kernel

/-- Event-only evaluation for the current ME profile. CS event handling is
not enabled. FMI 3.0.2 §2.3.5 lists this call; Initialization (§2.3.3) does not.
The omitted capability makes evaluation an ignored operation in Event Mode,
not a replacement for the required discrete-state update. -/
theorem evaluation_allowed_iff (k : Kind) (m : Mode) :
    allowed .evaluateDiscrete k m = true ↔ k = .me ∧ m = .event :=
  allowed_correct .evaluateDiscrete k m

theorem evaluation_rejects_initialization (k : Kind) :
    ¬ Reference.Allowed .evaluateDiscrete k .initialization := by
  simp [Reference.Allowed]

/-- FMI 3.0.2 §2.3.2 excludes the nominal query from Instantiated; §§2.3.3,
2.3.4 and 2.3.8 allow it in Initialization, Initialized and Terminated.
The prose-to-predicate correspondence still requires standards review. -/
theorem nominals_reject_instantiated (k : Kind) :
    ¬ Reference.Allowed .getNominals k .instantiated := by
  simp [Reference.Allowed]

/-- FMI 3.0.2 lists count queries in Instantiated (§2.3.2) and Event Mode
(§2.3.5), not Initialization, Continuous-Time or Terminated. They are distinct
from the final-value accessors allowed by §2.3.8. -/
theorem counts_reject_computation_and_termination (k : Kind) (m : Mode)
    (outside : m ∈ [.initialization, .continuous, .terminated]) :
    ¬ Reference.Allowed .getCounts k m := by
  cases k <;> cases m <;> simp_all [Reference.Allowed]

def nextMode (c : Command) (k : Kind) (m : Mode) : Mode :=
  if allowed c k m then
    match c with
    | .enterInitialization => .initialization
    | .exitInitialization => if k = .me then .event else .step
    | .enterEvent => .event
    | .enterContinuous => .continuous
    | .terminate => .terminated
    | .reset => .instantiated
    | _ => m
  else .terminated

theorem invalid_call_error (h : ¬ Reference.Allowed c k m) : nextMode c k m = .terminated := by
  have ha : allowed c k m ≠ true := fun he => h ((allowed_correct c k m).mp he)
  simp [nextMode, ha]

/-- Error ends simulation, but the final variables remain observable. -/
theorem invalid_call_final_values (h : ¬ Reference.Allowed c k m) :
    allowed .get k (nextMode c k m) = true ∧
    allowed .setStart k (nextMode c k m) = false ∧
    allowed .doStep k (nextMode c k m) = false := by
  rw [invalid_call_error h]
  cases k <;> decide

/-- ME final-state value queries remain available after normal or erroneous
termination. Count queries are only allowed in Instantiated and Event Mode. -/
theorem terminated_me_queries (c : Command)
    (h : c ∈ [.getStates, .getDerivatives, .getNominals]) :
    allowed c .me .terminated = true := by
  cases c <;> simp_all [allowed, permittedModes] <;> decide

theorem reset_recovers (k : Kind) (m : Mode) : nextMode .reset k m = .instantiated := by
  cases k <;> cases m <;> decide

theorem me_initialization : nextMode .exitInitialization .me .initialization = .event := rfl
theorem cs_initialization : nextMode .exitInitialization .cs .initialization = .step := rfl
theorem cs_cannot_use_me_set_time (m : Mode) : allowed .setTime .cs m = false := rfl

end Rumoca.FMI3
