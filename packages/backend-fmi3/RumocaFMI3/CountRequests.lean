import RumocaFMI3.CountEntry
import RumocaFMI3.Float64Access
import RumocaC.StorageRegion

/-! Count-call requests for the existing protocol histories. Expected outcomes
are reference postconditions; raw C observations remain unrestricted. -/
noncomputable section
namespace Rumoca.FMI3.CountAccess
open CMemory

inductive Request where
  | get (events : Bool) (buffer : Address)
  | reject (events missing : Bool) (buffer : Option Address)

def Request.call (request : Request) (p : Address) : String × List Value :=
  match request with
  | .get events buffer => ((CountQueries.signature events).name,
      CountQueries.arguments (some p) (some buffer))
  | .reject events _ buffer => ((CountQueries.signature events).name,
      CountQueries.arguments (some p) buffer)

def Request.Allowed (request : Request) (kind : Kind) (mode : Mode) : Prop :=
  match request with
  | .get _ _ => Reference.Allowed .getCounts kind mode
  | .reject _ missing buffer => CountQueries.FailureCondition missing kind mode buffer

def Request.failed : Request → Bool
  | .get _ _ => false
  | .reject _ _ _ => true

def Request.OutputStorage (request : Request) (heap : Heap) : Prop :=
  match request with
  | .get _ buffer => ∃ old, heap buffer = some ⟨.size, true, old⟩
  | .reject _ _ _ => True

def Request.Guarded (request : Request) (region : Address → Prop) : Prop :=
  match request with
  | .get _ buffer => region buffer
  | .reject _ _ _ => True

theorem Request.OutputStorage.preserved (request : Request)
    (stored : request.OutputStorage before)
    (preserved : CStorage.PreservesOn region before after)
    (guarded : request.Guarded region) : request.OutputStorage after := by
  cases request with
  | get events buffer =>
    obtain ⟨old, found⟩ := stored
    exact preserved.cell guarded found
  | reject _ _ _ => trivial

def Request.Outside (request : Request) (q : Address) : Prop :=
  match request with
  | .get _ buffer => q ≠ buffer
  | .reject _ _ _ => True

def Request.readback (request : Request) (heap : Heap) : Nat → Option Value :=
  match request with
  | .get _ buffer => fun i => if i = 0 then load heap buffer else none
  | .reject _ _ _ => fun _ => none

def Request.expected (request : Request) (model : Solve.FMI3Model source) : Nat → Option Value :=
  match request with
  | .get events _ => fun i => if i = 0 then
      some (.integer (if events then 0 else model.problem.stateShape.volume)) else none
  | .reject _ _ _ => fun _ => none

/-- Every represented call has either a legal non-null output or one of the
existing rejection reasons. Lifecycle rejection precedes pointer rejection. -/
theorem request_coverage (events : Bool) (buffer : Option Address) (kind : Kind) (mode : Mode) :
    (∃ output, buffer = some output ∧ (Request.get events output).Allowed kind mode) ∨
    (∃ missing, (Request.reject events missing buffer).Allowed kind mode) := by
  classical
  by_cases permitted : Reference.Allowed .getCounts kind mode
  · cases buffer with
    | none => exact Or.inr ⟨true, rfl, permitted⟩
    | some output => exact Or.inl ⟨output, rfl, permitted⟩
  · exact Or.inr ⟨false, permitted⟩

end Rumoca.FMI3.CountAccess
end
