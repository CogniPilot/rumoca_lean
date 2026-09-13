import RumocaC.BodyEmbedding
import RumocaFMI3.LifecycleBodies

/-! Reuse checked lifecycle body runs in the typed tensor-call machine.
These results start at body entry, with supplied locals and memory. They do
not establish public argument binding, callback execution or printed bytes.
Every emitted body satisfies the nested-declaration restriction. -/
namespace Rumoca.FMI3.BodyEmbedding
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory

omit static in
theorem body_closed (m : Solve.FMI3Model source) (sig : Signature) :
    (Runtime.body m sig).all CBodyEmbedding.closedBlocks = true := by
  unfold Runtime.body
  split <;> simp_all [CBodyEmbedding.closedBlocks, CLoops.noDeclarations,
    FactoryPrefix.validation, FactoryPrefix.identityGuard, FactoryPrefix.capabilityGuard,
    FactoryRejection.code, FactoryRejection.logCall,
    StaticFactory.code, StaticFactory.reserve, StaticFactory.guard, StaticFactory.exhausted,
    StaticFactory.initializeInstance, StaticFactory.selectInstance,
    StaticRelease.function, StaticRelease.guard, StaticRelease.clear,
    InstanceSlot.code, InstanceSlot.statement, InstanceInitialization.code,
    InstanceInitialization.put, InstanceInitialization.field, InstanceInitialization.state,
    InstanceInitialization.returnHandle, CAtomicScan.function,
    CAtomicScan.scan, CAtomicScan.attempt, CAtomicScan.selected, CAtomicScan.advance,
    Runtime.makeInstance, Runtime.require, Runtime.instancePrefix, Runtime.countLoop,
    Runtime.getFloat64, Runtime.setFloat64, Runtime.setFloat64Values,
    Runtime.scalarAccessCheck, Runtime.pointerCheck,
    Runtime.doStep, Runtime.initialTime, Runtime.eventTime, Runtime.completedTime,
    CInitialization.Emission.statement,
    Runtime.raiseField, Runtime.reject, Runtime.branch, Runtime.fail, Runtime.ret,
    Runtime.put, Runtime.out, Runtime.ok, Runtime.setMode, Runtime.log]
  split <;> simp [CLoops.noDeclarations]

omit static in
theorem helpers_closed (fn : CTree.Function) (h : fn ∈ Runtime.helpers) :
    fn.body.all CBodyEmbedding.closedBlocks = true := by
  simp only [Runtime.helpers, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    simp [CBodyEmbedding.closedBlocks, CLoops.noDeclarations, Runtime.setMode,
      Runtime.put, Runtime.log, Runtime.branch, Runtime.ret, Identity.function,
      Identity.nullCheck, Identity.falseReturn, Identity.measure, Identity.measurePrefix,
      Identity.blank, Identity.compareToken, Identity.comparisonReturn,
      CAtomicScan.function, CAtomicScan.scan, CAtomicScan.attempt, CAtomicScan.selected, CAtomicScan.advance]

noncomputable section
/-- Any terminating run of an admitted runtime body has exactly the same
result and heap in the typed machine. This reuses, rather than restates, the
memory-body execution proof; return conversion remains an explicit premise. -/
theorem runtime_behaviors (m : Solve.FMI3Model source) (sig : Signature)
    (program : CCalls.Program)
    (env : CBody.Locals) (types : CLoops.Types) (heap : Heap) (result : CBody.Result)
    (returned : Value) (n : Nat)
    (run : CBody.run n (.running (Runtime.body m sig) env heap) = some (.returned result))
    (cast : CCalls.returnCast sig.result result.value = some returned) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.body (.running (Runtime.body m sig) env types heap) sig.result .done) behavior ↔
      behavior = .terminates ⟨returned, result.heap⟩ :=
  CBodyEmbedding.typed_body_behaviors program (.running (Runtime.body m sig) env heap)
    types result sig.result returned n
    (body_closed m sig) run cast behavior

/-- Apply the bridge to the complete, previously proved termination body. -/
theorem terminate_behaviors (m : Solve.FMI3Model source) (sig : Signature)
    (hsig : sig.name = "fmi3Terminate") (program : CCalls.Program)
    (types : CLoops.Types) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : heap (p.member "mode") = some ⟨.int32, true, some (.integer mode.code)⟩)
    (ha : Reference.Allowed .terminate kind mode) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.body (.running (Runtime.body m sig) (HistoryBodies.parameters p) types heap)
        "fmi3Status" .done) behavior ↔
      behavior = .terminates ⟨.integer 0, LifecycleBodies.writeMode heap p .terminated⟩ :=
  CBodyEmbedding.typed_body_behaviors program
    (.running (Runtime.body m sig) (HistoryBodies.parameters p) heap)
    types ⟨.integer 0, LifecycleBodies.writeMode heap p .terminated⟩ "fmi3Status" (.integer 0) 5
    (body_closed m sig)
    (LifecycleBodies.terminate_run m sig hsig heap p kind mode hk hm ha)
    (by simp [CCalls.returnCast, CBody.cast, convert]) behavior
end
end Rumoca.FMI3.BodyEmbedding
