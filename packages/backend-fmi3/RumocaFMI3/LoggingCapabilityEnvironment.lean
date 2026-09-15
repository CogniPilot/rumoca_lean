import RumocaFMI3.LoggingCapabilityCalls
import RumocaFMI3.DebugLoggingPrepared

/-! Construct capability-aware public calls from the same prepared definition
table and immutable literal pool as the actual adapter. The shared runtime
interface is explicit, including the fenv header and static object bindings. -/
noncomputable section
namespace Rumoca.FMI3.Logging
open CTree CMemory CBody CCalls.Events StaticFactory CLiteral

theorem Capability.prepared_request (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++ (LiteralPreparation.functions model sigs).flatMap functionNames))
    (contract : DebugLogging.PreparedContract model sigs pool)
    (header : CFenv.Header) (objects : Objects) (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation), program.internal = LiteralPreparation.program model sigs →
      program.externals "strcmp" = some (CStringCalls.compareExternal (by rfl)) →
      ∀ (capability : Capability) (enabled : Bool) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode),
        CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
        capability.Configured heap p enabled → capability.Bound program →
        heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩ →
        ∃ (category : Address) (messages : Bool → Address),
          pool.addresses firstBlock "logStatus" = some category ∧
          (∀ unknown, pool.addresses firstBlock (DebugLogging.failureMessage unknown) = some (messages unknown)) ∧
          CStringMemory.Contents heap category (CStringMemory.content "logStatus") ∧
          (∀ unknown, CLiteral.Stored signed heap (messages unknown) (DebugLogging.failureMessage unknown)) ∧
          DebugLogging.RequestContract program heap p kind mode
            (capability.Failure enabled heap p category messages) := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual compare capability enabled heap p kind mode readonly configured bound hm
  obtain ⟨category, messages, literal, addresses, content, stored, execute⟩ :=
    contract.execution header baseHeap firstBlock signed objects heap readonly
  obtain ⟨quiet, logged⟩ := execute Invocation program actual compare
  exact ⟨category, messages, literal, addresses, content, stored,
    capability.request_contract enabled program heap p category messages kind mode configured bound hm quiet logged⟩

end Rumoca.FMI3.Logging
end
