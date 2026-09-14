import RumocaFMI3.InitializationAccess
import RumocaFMI3.ResetStorage
import RumocaFMI3.StaticReset

noncomputable section
namespace Rumoca.FMI3.Float64Access
open CMemory

theorem Instance.reset {kind : Kind} {mode : Mode} {state : ModelExchange.State} {time : Binary64.Value}
    (stored : Instance heap p kind mode state time) :
    Instance (Reset.finalHeap heap p) p kind .instantiated ⟨Binary64.positiveZero⟩ Binary64.positiveZero := by
  refine ⟨(StaticReset.kind_value heap p).trans stored.kind, ?_, ?_, ?_⟩
  · simp [Reset.finalHeap, LifecycleBodies.writeMode]
  · have different (name : String) : (p.member "model").member "x" ≠ p.member name :=
      HistoryBodies.state_ne_field p name
    simp [Reset.finalHeap, CInitialization.written, HistoryProofs.initialHeap,
      HistoryProofs.write, LifecycleBodies.writeMode, StateProofs.stateAddress, replace, different]
  · simp [load, (Reset.history heap p).time, convert, Value.finite, Time.Clock.initial, HistoryProofs.cell]

end Rumoca.FMI3.Float64Access

namespace Rumoca.FMI3.InitializationAccess
open CMemory Float64Buffers Float64Access

/-- Reset and a new initialization script are one reusable recovery primitive.
The before/during access lists may contain finite state overrides and batched
queries. Its selected source IVP is determined at the actual exit heap. -/
structure Recovery [CInterface] (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (buffers : Layout) (kind : Kind) (args : Initialization.Arguments)
    (before during : List Request) (beforeEntry atExit : Heap) : Prop where
  resetCall : ∀ behavior, (CCalls.Events.machine program).Behaves
    (.calling Reset.signature.name [.pointer (some p)] heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 0, Reset.finalHeap heap p⟩
  initialized : Certificate model program p buffers args kind ⟨Binary64.positiveZero⟩ Binary64.positiveZero
    (Reset.finalHeap heap p) before during beforeEntry atExit
  storage : CStorage.Preserves heap (InitializationBodies.exitHeap atExit p kind)
  atomic : CAtomicBoolean.Preserves heap (InitializationBodies.exitHeap atExit p kind)
  readonly : CReadOnly.Preserves heap (InitializationBodies.exitHeap atExit p kind)
  frame : ∀ q, ¬ p.InRecord q → Float64Access.Outside buffers q →
    InitializationBodies.exitHeap atExit p kind q = heap q

theorem Recovery.correct [CInterface] (program : CCalls.Events.Program E)
    (reset : StaticReset.ExecutionContract program)
    (initialization : InitializationCalls.QuietExecutionContract program)
    (get : ∀ heap, Float64Calls.QuietExecutionContract model program heap)
    (set : ∀ heap, Float64Set.QuietExecutionContract program heap)
    (stored : Instance heap p kind mode state time) (storage : Reset.Storage heap p)
    (outputs : Stored heap buffers) (separate : buffers.Separate p)
    (args : Initialization.Arguments) (admissible : args.Admissible)
    (before during : List Request)
    (beforeFits : ∀ request ∈ before, request.Fits buffers)
    (beforeAllowed : ∀ request ∈ before, request.StartQuery)
    (duringFits : ∀ request ∈ during, request.Fits buffers)
    (duringAllowed : ∀ request ∈ during, request.Allowed kind .initialization) :
    ∃ beforeEntry atExit, Recovery model program heap p buffers kind args before during beforeEntry atExit := by
  have resetCall := reset.successful heap p kind mode storage stored.kind stored.mode_loaded
  have retained := Reset.preserves model heap p kind mode storage stored.kind stored.mode_loaded
  obtain ⟨beforeEntry, atExit, initialized⟩ := initialization_history program initialization get set
    stored.reset (StaticReset.entry_storage heap p) (outputs.preserved retained.1) separate args admissible
    before during beforeFits beforeAllowed duringFits duringAllowed
  refine ⟨beforeEntry, atExit, resetCall, initialized, retained.1.trans initialized.storage,
    retained.2.trans initialized.atomic,
    (CCalls.Events.termination_preserves ((resetCall _).mpr rfl)).trans initialized.readonly, ?_⟩
  intro q notRecord outside
  have field (name : String) : q ≠ p.member name := fun same => notRecord (same ▸ p.member_in_record name)
  have notState : q ≠ StateProofs.stateAddress p :=
    fun same => notRecord (same ▸ (p.member_in_record "model").member "x")
  exact (initialized.frame q ⟨outside, notState, fun name _ => field name⟩).trans
    (StaticReset.record_frame heap p q notRecord)

/-- The raw relation records the real reset status and events, followed by the
existing raw initialization-access relation. No expected result is a premise. -/
def Recovered [CInterface] (program : CCalls.Events.Program E) (heap : Heap) (p : Address) (buffers : Layout)
    (args : Initialization.Arguments) (before during : List Request) (resetEvents : List E) (resetStatus : Value)
    (observation : Observation E) (after : Heap) : Prop :=
  ∃ resetHeap,
    (CCalls.Events.machine program).Behaves (.calling Reset.signature.name [.pointer (some p)] heap .done)
      (.terminates resetEvents ⟨resetStatus, resetHeap⟩) ∧
    Executed program p buffers args resetHeap before during observation after

theorem Recovery.executes [CInterface] {program : CCalls.Events.Program E}
    (certified : Recovery model program heap p buffers kind args before during beforeEntry atExit) :
    Recovered program heap p buffers args before during [] (.integer 0)
      (expectedObservation model ⟨Binary64.positiveZero⟩ Binary64.positiveZero args before during)
      (InitializationBodies.exitHeap atExit p kind) :=
  ⟨Reset.finalHeap heap p, (certified.resetCall _).mpr rfl, certified.initialized.executes⟩

theorem Recovery.determines [CInterface] {program : CCalls.Events.Program E}
    (certified : Recovery model program heap p buffers kind args before during beforeEntry atExit)
    (executed : Recovered program heap p buffers args before during events status observation after) :
    events = [] ∧ status = .integer 0 ∧
    observation = expectedObservation model ⟨Binary64.positiveZero⟩ Binary64.positiveZero args before during ∧
    after = InitializationBodies.exitHeap atExit p kind := by
  obtain ⟨resetHeap, resetCall, initialized⟩ := executed
  have result := (certified.resetCall _).mp resetCall
  have equal : events = [] ∧ status = .integer 0 ∧ resetHeap = Reset.finalHeap heap p := by
    simpa only [Transition.Events.Observation.terminates.injEq, CBody.Result.mk.injEq] using result
  obtain ⟨events, status, same⟩ := equal
  subst resetHeap
  obtain ⟨observed, memory⟩ := certified.initialized.determines initialized
  exact ⟨events, status, observed, memory⟩

theorem Recovery.execution_iff [CInterface] {program : CCalls.Events.Program E}
    (certified : Recovery model program heap p buffers kind args before during beforeEntry atExit) :
    Recovered program heap p buffers args before during events status observation after ↔
      events = [] ∧ status = .integer 0 ∧
      observation = expectedObservation model ⟨Binary64.positiveZero⟩ Binary64.positiveZero args before during ∧
      after = InitializationBodies.exitHeap atExit p kind := by
  constructor
  · exact certified.determines
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact certified.executes

end Rumoca.FMI3.InitializationAccess
end
