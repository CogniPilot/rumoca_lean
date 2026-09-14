import RumocaFMI3.NominalEntry
import RumocaFMI3.Float64Access
import RumocaC.StorageRegion

/-! Nominal requests for protocol histories. Expected outputs are indexed by
the prepared Solve state volume; raw call observations are unrestricted. -/
noncomputable section
namespace Rumoca.FMI3.NominalAccess
open CMemory

inductive Request where
  | get (buffer : Address)
  | reject (access : Bool) (buffer : Option Address) (count : UInt64)

def Request.call (request : Request) (p : Address) : String × List Value :=
  match request with
  | .get buffer => (ErrorCalls.nominalSignature.name, ErrorCalls.nominalArguments p (some buffer) 1)
  | .reject _ buffer count => (ErrorCalls.nominalSignature.name, ErrorCalls.nominalArguments p buffer count)

def Request.Allowed (request : Request) (kind : Kind) (mode : Mode) : Prop :=
  match request with
  | .get _ => Reference.Allowed .getNominals kind mode
  | .reject access buffer count => Nominals.FailureCondition access kind mode buffer count

def Request.failed : Request → Bool
  | .get _ => false
  | .reject _ _ _ => true

def Request.OutputStorage (request : Request) (heap : Heap) : Prop :=
  match request with
  | .get buffer => ∃ old, heap buffer = some ⟨.float64, true, old⟩
  | .reject _ _ _ => True

def Request.Guarded (request : Request) (region : Address → Prop) : Prop :=
  match request with
  | .get buffer => region buffer
  | .reject _ _ _ => True

theorem Request.OutputStorage.preserved (request : Request)
    (stored : request.OutputStorage before)
    (preserved : CStorage.PreservesOn region before after)
    (guarded : request.Guarded region) : request.OutputStorage after := by
  cases request with
  | get buffer =>
    obtain ⟨old, found⟩ := stored
    exact preserved.cell guarded found
  | reject _ _ _ => trivial

def Request.Outside (request : Request) (q : Address) : Prop :=
  match request with
  | .get buffer => q ≠ buffer
  | .reject _ _ _ => True

def Request.readback (request : Request) (heap : Heap) : Nat → Option Value :=
  match request with
  | .get buffer => fun i => if i = 0 then load heap buffer else none
  | .reject _ _ _ => fun _ => none

def Request.expected (request : Request) (model : Solve.FMI3Model source) : Nat → Option Value :=
  match request with
  | .get _ => fun i => if i < model.problem.stateShape.volume then some (.finite Binary64.one) else none
  | .reject _ _ _ => fun _ => none

theorem Request.get_observed (model : Solve.FMI3Model source)
    (stored : load heap buffer = some (.finite Binary64.one)) :
    (Request.get buffer).readback heap = (Request.get buffer).expected model := by
  funext i
  change (if i = 0 then load heap buffer else none) = (if i < 1 then some (.finite Binary64.one) else none)
  simp only [stored, Nat.lt_one_iff]

/-- Lifecycle rejection has priority over the size/pointer check. This covers
every represented size and pointer, without requiring a successful output. -/
theorem request_coverage (buffer : Option Address) (count : UInt64) (kind : Kind) (mode : Mode) :
    (∃ output, buffer = some output ∧ count.toNat = 1 ∧ (Request.get output).Allowed kind mode) ∨
    (∃ access, (Request.reject access buffer count).Allowed kind mode) := by
  classical
  by_cases permitted : Reference.Allowed .getNominals kind mode
  · by_cases one : count.toNat = 1
    · cases buffer with
      | none => exact Or.inr ⟨true, permitted, Or.inr rfl⟩
      | some output => exact Or.inl ⟨output, rfl, one, permitted⟩
    · exact Or.inr ⟨true, permitted, Or.inl one⟩
  · exact Or.inr ⟨false, permitted⟩

end Rumoca.FMI3.NominalAccess
end
