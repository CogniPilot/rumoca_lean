import RumocaFMI3.Logging
import RumocaFMI3.DebugLoggingCalls
import RumocaC.ObservedCalls

/-! Persistent callback information is independent of whether logging is
currently enabled. A disabled non-null pointer does not establish a callback
binding or a memory policy; those facts are retained from the original host. -/
noncomputable section
namespace Rumoca.FMI3.Logging
open CTree CMemory CBody CCalls.Events
variable [interface : CInterface]

inductive Capability where
  | absent (environment : Option Address)
  | present (logger : Address) (environment : Option Address) (name : String)
      (effect : ReturningEffect (signature name))

def Capability.logger : Capability → Option Address
  | .absent _ => none
  | .present logger _ _ _ => some logger

def Capability.environment : Capability → Option Address
  | .absent environment | .present _ environment _ _ => environment

def Capability.Stored (capability : Capability) (heap : Heap) (p : Address) : Prop :=
  load heap (p.member "logger") = some (.pointer capability.logger) ∧
  load heap (p.member "environment") = some (.pointer capability.environment)

def Capability.Configured (capability : Capability) (heap : Heap) (p : Address) (enabled : Bool) : Prop :=
  capability.Stored heap p ∧ load heap (p.member "logging") = some (boolean enabled)

def Capability.Bound (capability : Capability) (program : Program Invocation) : Prop :=
  match capability with
  | .absent _ => True
  | .present logger _ name effect => program.addresses logger = some name ∧
      program.externals name = some (External.observed (signature name) effect)

/-- A host obligation on every possible callback outcome remains in force
even when the current flag suppresses invocation. -/
def Capability.Requires (capability : Capability)
    (policy : ∀ name, ReturningEffect (signature name) → Prop) : Prop :=
  match capability with
  | .absent _ => True
  | .present _ _ name effect => policy name effect

theorem Capability.requires_mono {capability : Capability}
    (required : capability.Requires policy)
    (implies : ∀ name effect, policy name effect → nextPolicy name effect) :
    capability.Requires nextPolicy := by
  cases capability with
  | absent _ => trivial
  | present _ _ name effect => exact implies name effect required

theorem Capability.requires_and (capability : Capability) (left right) :
    capability.Requires (fun name effect => left name effect ∧ right name effect) ↔
    capability.Requires left ∧ capability.Requires right := by
  cases capability <;> simp [Capability.Requires]

theorem Capability.Stored.framed {capability : Capability}
    (stored : capability.Stored heap p)
    (frame : ∀ name ∈ ["logger", "environment"], after (p.member name) = heap (p.member name)) :
    capability.Stored after p := by
  constructor
  · simpa only [load, frame "logger" (by simp)] using stored.1
  · simpa only [load, frame "environment" (by simp)] using stored.2

theorem Capability.Stored.logging_written {capability : Capability}
    (stored : capability.Stored heap p) (enabled : Bool) :
    capability.Stored (DebugLogging.written heap p enabled) p := by
  apply stored.framed
  intro name member
  apply DebugLogging.written_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp

theorem Capability.Stored.mode_written {capability : Capability}
    (stored : capability.Stored heap p) (mode : Mode) :
    capability.Stored (LifecycleBodies.writeMode heap p mode) p := by
  apply stored.framed
  intro name member
  apply LifecycleBodies.write_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp

theorem Capability.Configured.logging_written {capability : Capability}
    (stored : capability.Stored heap p) (enabled : Bool) :
    capability.Configured (DebugLogging.written heap p enabled) p enabled :=
  ⟨stored.logging_written enabled, DebugLogging.written_flag heap p enabled⟩

theorem Capability.Configured.framed {capability : Capability}
    (configured : capability.Configured heap p enabled)
    (frame : ∀ name ∈ ["logger", "environment", "logging"], after (p.member name) = heap (p.member name)) :
    capability.Configured after p enabled := by
  constructor
  · apply configured.1.framed
    intro name member
    apply frame
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    tauto
  · simpa only [load, frame "logging" (by simp)] using configured.2

end Rumoca.FMI3.Logging
end
