import RumocaFMI3.AtomicCallRuntime
import RumocaC.HostCallSites

namespace Rumoca.FMI3.AtomicCallPolicy
open CTree CMemory CCalls CCallSites CCalls.Events RuntimeLinkage
variable [interface : CInterface]

/-- The policy may further restrict the current heap, buffers and arguments;
every admitted entry must come from this exact public header. Host memory
effects remain explicit, and need not be restricted for this control property.
Evolving ghost leases belong to a separate annotated history relation. -/
theorem logged_host_history (model : Solve.FMI3Model source) (sigs : List Signature)
    (covered : PublicAPI.Covered sigs) (tag : CAtomicBoolean.Calls.Event → Invocation)
    (boolean : interface.types "_Bool" = some .boolean)
    (size : interface.types "size_t" = some .size)
    (integer : interface.types "int" = some .int32)
    (double : interface.types "double" = some .float64)
    (observed : Int) (range : -(2^31) ≤ observed ∧ observed < 2^31)
    (logger : Address) (effect : ReturningEffect (Logging.signature hostName))
    (domain : Concurrent.State → Nat → Signature → List Value → Prop)
    (memory : Concurrent.State → Nat → Heap → Prop) :
    let program := logged model sigs covered tag boolean size integer double observed range logger effect
    ∀ heap trace after, Host.History program (Host.publicPolicy sigs domain memory) ⟨heap, fun _ => none⟩ trace after →
      ThreadsReady Permitted ValidCall after := by
  intro program heap trace after path
  let policy := Host.publicPolicy sigs domain memory
  have entries : ∀ state thread name args, policy.admit state thread name args → ValidCall name args := by
    intro state thread name args admitted
    obtain ⟨sig, member, rfl, _⟩ := admitted
    exact entry_valid (ranked_entry (CallPolicy.covered_ranks covered sig member)) args
  have idle : ThreadsReady Permitted ValidCall ⟨heap, fun _ => none⟩ := by
    intro thread saved found
    contradiction
  exact host_history program policy (program_policy model sigs)
    (operand_sound program boolean (fun _ _ selected =>
      logged_named_only model sigs covered tag boolean size integer double observed range logger effect selected))
    entries idle path

end Rumoca.FMI3.AtomicCallPolicy
