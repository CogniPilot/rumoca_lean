import Std

/-! The continuous, event-free FMI 3 profile. This table is shared with code
generation; Reference.Allowed separately records the reference lifecycle
rules for the implemented commands (FMI 3.0.2 §§2.3, 3.2, 4.2).
It does not model pointers, argument validity, callbacks or native execution. -/
namespace Rumoca.FMI3

inductive Kind where | me | cs
  deriving Repr, BEq, DecidableEq
inductive Mode where | instantiated | initialization | event | continuous | step | terminated | error
  deriving Repr, BEq, DecidableEq
inductive Command where
  | enterInitialization | exitInitialization | enterEvent | enterContinuous
  | updateDiscrete | evaluateDiscrete | terminate | reset | get | setStart
  | setTime | setStates | getStates | getDerivatives | getNominals | getCounts
  | completedStep | doStep | logging
  deriving Repr, BEq, DecidableEq

def Mode.code : Mode → Nat
  | .instantiated => 0 | .initialization => 1 | .event => 2 | .continuous => 3
  | .step => 4 | .terminated => 5 | .error => 6

def permittedModes : Command → Kind → List Mode
  | .enterInitialization, _ => [.instantiated]
  | .exitInitialization, _ => [.initialization]
  | .enterEvent, .me => [.continuous]
  | .enterContinuous, .me => [.event]
  | .updateDiscrete, .me => [.event]
  | .evaluateDiscrete, .me => [.initialization, .event]
  | .terminate, .me => [.event, .continuous]
  | .terminate, .cs => [.step]
  | .reset, _ => [.instantiated, .initialization, .event, .continuous, .step, .terminated, .error]
  | .get, _ | .logging, _ => [.instantiated, .initialization, .event, .continuous, .step, .terminated]
  | .setStart, .me => [.instantiated, .initialization, .event, .continuous]
  | .setStart, .cs => [.instantiated, .initialization]
  | .setTime, .me => [.continuous]
  | .setStates, .me => [.continuous]
  | .getStates, .me => [.initialization, .event, .continuous]
  | .getDerivatives, .me => [.initialization, .event, .continuous]
  | .getNominals, .me => [.instantiated, .initialization, .event, .continuous]
  | .getCounts, .me => [.instantiated, .initialization, .event, .continuous]
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
  | .evaluateDiscrete => k = .me ∧ (m = .initialization ∨ m = .event)
  | .terminate => (k = .me ∧ (m = .event ∨ m = .continuous)) ∨ (k = .cs ∧ m = .step)
  | .reset => True
  | .get | .logging => m ≠ .error
  | .setStart => m = .instantiated ∨ m = .initialization ∨
      (k = .me ∧ (m = .event ∨ m = .continuous))
  | .getStates | .getDerivatives => k = .me ∧ (m = .initialization ∨ m = .event ∨ m = .continuous)
  | .setTime | .setStates | .completedStep => k = .me ∧ m = .continuous
  | .getNominals | .getCounts => k = .me ∧
      (m = .instantiated ∨ m = .initialization ∨ m = .event ∨ m = .continuous)
  | .doStep => k = .cs ∧ m = .step
end Reference

theorem allowed_correct (c : Command) (k : Kind) (m : Mode) :
    allowed c k m = true ↔ Reference.Allowed c k m := by
  cases c <;> cases k <;> cases m <;>
    simp [Reference.Allowed, allowed, permittedModes] <;> decide +kernel

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
  else .error

theorem invalid_call_error (h : ¬ Reference.Allowed c k m) : nextMode c k m = .error := by
  have ha : allowed c k m ≠ true := fun he => h ((allowed_correct c k m).mp he)
  simp [nextMode, ha]

theorem reset_recovers (k : Kind) (m : Mode) : nextMode .reset k m = .instantiated := by
  cases k <;> cases m <;> decide

theorem me_initialization : nextMode .exitInitialization .me .initialization = .event := rfl
theorem cs_initialization : nextMode .exitInitialization .cs .initialization = .step := rfl
theorem cs_cannot_use_me_set_time (m : Mode) : allowed .setTime .cs m = false := rfl

end Rumoca.FMI3
