import RumocaFMI3.EventIndicatorFunction

noncomputable section
namespace Rumoca.FMI3.EventIndicatorAccess
open CMemory

/-- History requests retain the caller's pointer and count. Expected status
is derived from a separate lifecycle/count classification. No event element
exists in this profile, so no future output-storage premise is introduced. -/
inductive Request where
  | get (buffer : Option Address)
  | reject (access : Bool) (buffer : Option Address) (count : UInt64)

def Request.call (request : Request) (p : Address) : String × List Value :=
  match request with
  | .get buffer => (EventIndicatorCalls.signature.name, EventIndicatorCalls.values (some p) buffer 0)
  | .reject _ buffer count => (EventIndicatorCalls.signature.name, EventIndicatorCalls.values (some p) buffer count)

def Request.Allowed (request : Request) (kind : Kind) (mode : Mode) : Prop :=
  match request with
  | .get _ => EventIndicatorCalls.Allowed kind mode
  | .reject access _ count => EventIndicatorCalls.FailureCondition access kind mode count

def Request.failed : Request → Bool
  | .get _ => false
  | .reject _ _ _ => true

theorem request_coverage (p : Address) (buffer : Option Address) (count : UInt64) (kind : Kind) (mode : Mode) :
    (count = 0 ∧ (Request.get buffer).Allowed kind mode) ∨
    (∃ access, (Request.reject access buffer count).Allowed kind mode) := by
  rcases EventIndicatorCalls.query_cases kind mode (some p) count with impossible | ⟨_, same, result⟩
  · cases impossible
  · cases same
    exact result

end Rumoca.FMI3.EventIndicatorAccess
end
