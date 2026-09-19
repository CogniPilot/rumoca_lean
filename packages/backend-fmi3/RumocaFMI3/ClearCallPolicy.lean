import RumocaFMI3.AtomicCallPolicy
import RumocaFMI3.RuntimeLinkage
import RumocaC.HostCallSites

namespace Rumoca.FMI3.ClearCallPolicy
open CTree CMemory CCalls CCallSites

/-- Every emitted atomic store is a clear. Its address is retained as an
expression here and is derived from actual argument evaluation separately. -/
def Permitted (operand : Indirect.Operand) : Prop :=
  operand.callee = .id "atomic_store" →
    ∃ address, operand.args = [address, .cast "_Bool" (.nat 0)]

def Arguments (name : String) (args : List Value) : Prop :=
  name = "atomic_store" → ∃ address, args = [address, CAtomicBoolean.value false]

/-- The clear-store policy is the atomic reservation policy restricted to the
store direction: an atomically stored `false` is exactly a released reservation.
Every operand the atomic policy admits is therefore admitted here, so the clear
policy instantiates the shared body and helper classification instead of
re-classifying every emitted call site. -/
theorem permitted_of_atomic (operand : Indirect.Operand)
    (atomic : AtomicCallPolicy.Permitted operand) : Permitted operand := by
  intro store
  simp only [AtomicCallPolicy.Permitted, store, AtomicCallPolicy.desired,
    AtomicCallPolicy.DesiredArguments, AtomicCallPolicy.DesiredValue,
    String.reduceEq, reduceIte] at atomic
  split at atomic
  · rename_i head value _
    split at atomic
    · rename_i type k _
      obtain ⟨rfl, rfl⟩ := atomic
      exact ⟨head, by assumption⟩
    · exact atomic.elim
  · exact atomic.elim

set_option maxHeartbeats 1000000 in
theorem body_policy (model : Solve.FMI3Model source) (sig : Signature) :
    ∀ stmt ∈ Runtime.body model sig, Admits Permitted stmt := fun stmt member =>
  AtomicCallPolicy.admits_mono permitted_of_atomic stmt
    (AtomicCallPolicy.body_policy model sig stmt member)

theorem helpers_policy (fn : Function) (member : fn ∈ Runtime.helpers) :
    ∀ stmt ∈ fn.body, Admits Permitted stmt := fun stmt smember =>
  AtomicCallPolicy.admits_mono permitted_of_atomic stmt
    (AtomicCallPolicy.helpers_policy fn member stmt smember)

theorem program_policy (model : Solve.FMI3Model source) (sigs : List Signature) :
    ProgramAdmits Permitted (LiteralPreparation.program model sigs) := by
  intro name fn found
  have member := LiteralPreparation.program_covered model sigs name fn found
  rcases List.mem_append.mp member with helper | exported
  · exact helpers_policy fn helper
  · obtain ⟨sig, _, rfl⟩ := List.mem_map.mp exported
    exact body_policy model sig

variable [interface : CInterface] {E : Type}

/-- Named resolution and the actual argument evaluator supply the zero value;
no already-converted argument list is assumed. -/
theorem operand_sound (program : Events.Program E)
    (boolean : interface.types "_Bool" = some .boolean)
    (named : NamedOnly program "atomic_store") : OperandSound program Permitted Arguments := by
  intro operand permitted env heap name values resolved evaluated same
  subst name
  have callee := CCallPolicy.named_origin env heap operand.callee
    (named_resolution program named resolved)
  obtain ⟨address, args⟩ := permitted callee
  rw [args] at evaluated
  cases location : CBody.eval env heap address with
  | none => simp [CCalls.arguments, location] at evaluated
  | some value =>
    refine ⟨value, ?_⟩
    simpa [CCalls.arguments, location, CBody.eval, CBody.expressionCast, CBody.cast,
      CBody.zeroLiteral, boolean, convert, Value.truth, CAtomicBoolean.value] using evaluated.symm

omit interface in
theorem public_entry (sigs : List Signature) (covered : PublicAPI.Covered sigs)
    (member : sig ∈ sigs) : Arguments sig.name args := by
  intro stored
  have ranked := CallPolicy.covered_ranks covered sig member
  rw [stored] at ranked
  have missing : CallPolicy.functionRank "atomic_store" = none := by decide +kernel
  rw [missing] at ranked
  contradiction

end Rumoca.FMI3.ClearCallPolicy

namespace Rumoca.FMI3.ClearCallPolicy
open CTree CMemory CCalls CCalls.Events CCallSites RuntimeLinkage
variable [interface : CInterface]

/-- The actual logged program exposes no indirect alias for atomic store. -/
theorem logged_named_only (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName)) :
    NamedOnly (logged model sigs covered tag boolean size integer double observed range logger effect) "atomic_store" := by
  intro address found
  change (if address = logger then some hostName else none) = some "atomic_store" at found
  split at found <;> simp [hostName] at found

/-- Every actual host history supplies the raw false argument of each reached
atomic store. Neither argument conversion nor a completed release is assumed. -/
theorem logged_history (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName)) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ (domain : Concurrent.State → Nat → Signature → List Value → Prop)
      (memory : Concurrent.State → Nat → Heap → Prop) heap trace current,
      Host.History program (Host.publicPolicy sigs domain memory) ⟨heap, fun _ => none⟩ trace current →
      ∀ thread args oldHeap stack,
        current.threads thread = some (.calling "atomic_store" args oldHeap stack) →
        ∃ address, args = [address, CAtomicBoolean.value false] := by
  intro program domain memory heap trace current path
  have control := CCallSites.host_history program (Host.publicPolicy sigs domain memory)
    (program_policy model sigs)
    (operand_sound program boolean (logged_named_only model sigs covered tag boolean size integer double observed range logger effect))
    (fun _ _ _ _ admitted => by
      obtain ⟨sig, member, rfl, _⟩ := admitted
      exact public_entry sigs covered member)
    (by intro thread saved found; contradiction) path
  intro thread args oldHeap stack calling
  exact (control thread _ calling).1 rfl

end Rumoca.FMI3.ClearCallPolicy
