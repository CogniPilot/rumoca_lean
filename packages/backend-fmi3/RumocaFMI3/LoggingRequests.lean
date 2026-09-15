import RumocaFMI3.DebugLoggingMetadata
import RumocaFMI3.DebugLoggingInputFrame
import RumocaFMI3.DebugLoggingEntry

/-! Importer requests retain their actual pointer array and string contents.
FMI legality is separate from defensive C acceptance. The logging flag is
runtime control state; its transition does not alter the prepared Solve IVP. -/
noncomputable section
namespace Rumoca.FMI3.DebugLogging
open CMemory CStringMemory
open scoped Classical

structure Request where
  enabled : Bool
  count : UInt64
  pointer : Option Address
  selected : Nat → Option Address
  bytes : Nat → List UInt8

def Request.Inputs (request : Request) (heap : Heap) : Prop :=
  request.pointer.isSome = true →
    Entries heap request.pointer request.count.toNat request.selected request.bytes

def Request.Region (request : Request) (q : Address) : Prop :=
  InputRegion request.pointer request.count.toNat request.selected request.bytes q

def Request.Legal (request : Request) : Prop :=
  LegalRequest request.pointer request.count.toNat request.selected request.bytes ["logStatus"]

/-- This includes the defensive zero-length/non-null case. Such a request
has a C behavior but is not thereby a legal FMI request. -/
def Request.Accepted (request : Request) : Prop :=
  (request.count.toNat = 0 ∨ request.pointer.isSome = true) ∧
    ∀ i < request.count.toNat,
      DebugLogging.Accepted (request.selected i) (request.bytes i) (content "logStatus")

def Request.failed (request : Request) : Bool := decide (¬ request.Accepted)

def Request.nextLogging (request : Request) (before : Bool) : Bool :=
  if request.Accepted then request.enabled else before

def Request.loggingUpdate (request : Request) : Option Bool :=
  if request.Accepted then some request.enabled else none

theorem Request.logging_update (request : Request) :
    request.loggingUpdate.getD before = request.nextLogging before := by
  by_cases accepted : request.Accepted <;> simp [Request.loggingUpdate, Request.nextLogging, accepted]

def Request.call (request : Request) (p : Address) : String × List Value :=
  (signature.name, arguments (some p) request.enabled request.count request.pointer)

theorem Request.legal_accepted {request : Request} (legal : request.Legal) : request.Accepted := by
  refine ⟨?_, legal_single_accepted legal⟩
  by_cases zero : request.count.toNat = 0
  · exact Or.inl zero
  · exact Or.inr (legal.2.1 (Nat.pos_of_ne_zero zero))

theorem Request.legal_logging {request : Request} (legal : request.Legal) :
    request.failed = false ∧ request.nextLogging before = request.enabled := by
  simp [Request.failed, Request.nextLogging, legal_accepted legal]

theorem Request.Inputs.framed {request : Request} (inputs : request.Inputs before)
    (frame : ∀ q, request.Region q → after q = before q) : request.Inputs after :=
  fun present => (inputs present).framed frame

theorem Request.Inputs.load_ne_none {request : Request} (inputs : request.Inputs heap)
    (inside : request.Region q) : load heap q ≠ none := by
  have present : request.pointer.isSome = true := by
    obtain ⟨base, _, same, _⟩ := inside
    simp [same]
  exact (inputs present).load_ne_none inside

end Rumoca.FMI3.DebugLogging
end
