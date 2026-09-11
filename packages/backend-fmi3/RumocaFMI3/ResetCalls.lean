import RumocaFMI3.Reset

/-! Complete typed reset calls use the emitted function, including its actual
parameter conversion and fresh scope. Definition-table binding and allocated
instance storage are explicit; later native linkage is not modeled here. -/
noncomputable section
namespace Rumoca.FMI3.Reset
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CTree CMemory

def signature : Signature := ⟨"fmi3Status", "fmi3Reset", [⟨"fmi3Instance", "instance", false⟩]⟩

theorem parameters_bound (p : Address) :
    CCalls.parameters signature.parameters [.pointer (some p)] = some (HistoryBodies.parameters p) := by
  rfl

theorem call_reaches (m : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode) (stack : CCalls.Typed.Continuation)
    (defined : program.definitions "fmi3Reset" = some (.tree (Runtime.function m signature)))
    (storage : Storage heap p)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling "fmi3Reset" [.pointer (some p)] heap stack)
      (.returning (.integer 0) (finalHeap heap p) stack) :=
  CBodyEmbedding.typed_call_reaches program (Runtime.function m signature)
    [.pointer (some p)] (HistoryBodies.parameters p) heap
    ⟨.integer 0, finalHeap heap p⟩ (.integer 0) stack 12
    defined (parameters_bound p) (BodyEmbedding.body_closed m signature)
    (body_run m signature rfl heap p kind mode storage hk hm)
    (by simp [Runtime.function, signature, CCalls.returnCast, CBody.cast, convert])

theorem call_behaviors (m : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (defined : program.definitions "fmi3Reset" = some (.tree (Runtime.function m signature)))
    (storage : Storage heap p)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.calling "fmi3Reset" [.pointer (some p)] heap .done) behavior ↔
      behavior = .terminates ⟨.integer 0, finalHeap heap p⟩ :=
  (CCalls.Typed.machine program).behavior_iff
    ((call_reaches m program heap p kind mode .done defined storage hk hm).trans
      (.next rfl (.refl _))) rfl

/-- Null instances return Error and preserve every heap cell. -/
theorem null_reaches (m : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (stack : CCalls.Typed.Continuation)
    (defined : program.definitions "fmi3Reset" = some (.tree (Runtime.function m signature))) :
    Transition.Reaches (CCalls.Typed.machine program).step
      (.calling "fmi3Reset" [.pointer none] heap stack)
      (.returning (.integer 3) heap stack) := by
  apply CBodyEmbedding.typed_call_reaches program (Runtime.function m signature)
    [.pointer none] StateProofs.nullParameters heap ⟨.integer 3, heap⟩ (.integer 3) stack 3
    defined rfl (BodyEmbedding.body_closed m signature) ?_
    (by simp [Runtime.function, signature, CCalls.returnCast, CBody.cast, convert])
  change CBody.run 3 (.running (Runtime.instancePrefix ++
      (Runtime.modeGuard .reset :: (CInitialization.emit m.solve Runtime.x).statement :: tail))
      StateProofs.nullParameters heap) = _
  exact StateProofs.null_instance_run heap _

theorem null_behaviors (m : Solve.FMI3Model source) (program : CCalls.Program) (heap : Heap)
    (defined : program.definitions "fmi3Reset" = some (.tree (Runtime.function m signature))) (behavior) :
    (CCalls.Typed.machine program).Behaves
      (.calling "fmi3Reset" [.pointer none] heap .done) behavior ↔
      behavior = .terminates ⟨.integer 3, heap⟩ :=
  (CCalls.Typed.machine program).behavior_iff
    ((null_reaches m program heap .done defined).trans (.next rfl (.refl _))) rfl

/-- Successful reset composes the actual call with the model, history and
lifecycle postconditions; no assumption is made about old model/time values. -/
theorem correct (m : Solve.FMI3Model source) (program : CCalls.Program)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
    (defined : program.definitions "fmi3Reset" = some (.tree (Runtime.function m signature)))
    (storage : Storage heap p)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    (∀ behavior, (CCalls.Typed.machine program).Behaves
      (.calling "fmi3Reset" [.pointer (some p)] heap .done) behavior ↔
      behavior = .terminates ⟨.integer 0, finalHeap heap p⟩) ∧
    StateProofs.Represents (finalHeap heap p) p ⟨Binary64.positiveZero⟩ ∧
    HistoryProofs.Stored (finalHeap heap p) p (Time.Clock.initial Binary64.positiveZero) ∧
    load (finalHeap heap p) (p.member "mode") = some (.integer (nextMode .reset kind mode).code) ∧
    load (finalHeap heap p) (p.member "stopDefined") = some (CBody.boolean false) ∧
    (∀ q, q.block ≠ p.block → finalHeap heap p q = heap q) :=
  ⟨call_behaviors m program heap p kind mode defined storage hk hm, state heap p,
    history heap p, lifecycle heap p kind mode, (stop heap p).2, other_instance heap p⟩

end Rumoca.FMI3.Reset
