import RumocaFMI3.Float64RejectionMemory
import RumocaFMI3.InitializationAccessReset

noncomputable section
namespace Rumoca.FMI3.Float64Rejection
open CTree CMemory CBody CLiteral CCalls.Events StaticFactory

/-- Caller transfers followed by the actual accessor machine. The observed
behavior may return any raw status/heap or take the existing blocked branch. -/
def Request.Behaves [CInterface] (request : Request) (program : Program E) (heap : Heap) (p : Address)
    (behavior : Transition.Events.Observation E CBody.Result) : Prop :=
  ∃ ready, request.hostRun heap = some ready ∧
    (machine program).Behaves (.calling (request.call p).1 (request.call p).2 ready .done) behavior

theorem Request.behaves_iff [CInterface] (request : Request) (program : Program E)
    (stored : request.TransferStorage heap) :
    request.Behaves program heap p behavior ↔
    (machine program).Behaves (.calling (request.call p).1 (request.call p).2 (request.prepare heap) .done) behavior := by
  have run := (request.prepare_correct heap stored).1
  constructor
  · rintro ⟨ready, actual, called⟩
    rw [run] at actual
    cases Option.some.inj actual
    exact called
  · exact fun called => ⟨request.prepare heap, run, called⟩

structure Returned (objects : Objects) (retained : Address → Prop) (owners : SlotOwners.State objects.capacity)
    (request : Request) (heap : Heap) (p : Address) (kind : Kind) (state : ModelExchange.State)
    (time : Binary64.Value) (after : Heap) : Prop where
  stored : Float64Access.Instance after p kind .terminated state time
  resetStorage : Reset.Storage after p
  ownership : SlotOwners.Represents objects.flagsBlock after owners
  readonly : CReadOnly.Preserves heap after
  writable : ∀ (base : Address) (type : CType) (count : Nat),
    ArrayStore.Writable heap base type count →
    (∀ i < count, Protected objects retained (base.index i)) → ArrayStore.Writable after base type count
  frame : ∀ q, Protected objects retained q → request.Outside q → q ≠ p.member "mode" → after q = heap q

theorem Request.returned (request : Request) (objects : Objects) (retained : Address → Prop)
    (owners : SlotOwners.State objects.capacity) (heap : Heap) (p : Address)
    (stored : Float64Access.Instance heap p kind mode state time) (storage : Reset.Storage heap p)
    (inputs : request.TransferStorage heap) (separate : ∀ q, p.InRecord q → request.Outside q)
    (inPool : p.block = objects.instances.block) (represented : SlotOwners.Represents objects.flagsBlock heap owners)
    (callbackFrame : Frame objects retained (LifecycleBodies.writeMode (request.prepare heap) p .terminated) after)
    (callbackReadonly : CReadOnly.Preserves (LifecycleBodies.writeMode (request.prepare heap) p .terminated) after) :
    Returned objects retained owners request heap p kind state time after := by
  obtain ⟨_, _, preparedStorage, preparedReadonly, preparedAtomic⟩ := request.prepare_correct heap inputs
  have ready := request.prepared_instance stored separate
  have modeFrame := LifecycleBodies.write_storage (request.prepare heap) p _ .terminated ready.mode
  have preserved := preparedStorage.trans modeFrame.1
  refine ⟨ready.failed.record_preserved (callbackFrame.record inPool),
    (storage.preserved preserved).record_preserved (callbackFrame.record inPool),
    callbackFrame.owners (SlotOwners.ordinary_preserves represented (preparedAtomic.trans modeFrame.2.2)),
    preparedReadonly.trans (modeFrame.2.1.trans callbackReadonly), ?_, ?_⟩
  · intro base type count writable guarded
    apply callbackFrame.writable _ guarded
    intro i inside
    obtain ⟨old, cell⟩ := writable i inside
    exact preserved.cell cell
  · intro q guarded outside different
    exact (callbackFrame q guarded).trans
      ((LifecycleBodies.write_frame _ p q .terminated different).trans (request.prepare_frame heap q outside))

theorem Returned.buffers {buffers : Float64Buffers.Layout}
    (returned : Returned objects retained owners request heap p kind state time after)
    (stored : Float64Buffers.Stored heap buffers)
    (references : ∀ i < buffers.capacity.toNat, Protected objects retained (buffers.references.index i))
    (values : ∀ i < buffers.capacity.toNat, Protected objects retained (buffers.values.index i)) :
    Float64Buffers.Stored after buffers :=
  ⟨returned.writable _ _ _ stored.references references, returned.writable _ _ _ stored.values values⟩

theorem Returned.recover [CInterface] {buffers : Float64Buffers.Layout} (program : Program E)
    (reset : StaticReset.ExecutionContract program) (initialization : InitializationCalls.QuietExecutionContract program)
    (get : ∀ heap, Float64Calls.QuietExecutionContract model program heap)
    (set : ∀ heap, Float64Set.QuietExecutionContract program heap)
    (returned : Returned objects retained owners request heap p kind state time after)
    (stored : Float64Buffers.Stored heap buffers) (separate : buffers.Separate p)
    (references : ∀ i < buffers.capacity.toNat, Protected objects retained (buffers.references.index i))
    (values : ∀ i < buffers.capacity.toNat, Protected objects retained (buffers.values.index i))
    (args : Initialization.Arguments) (admissible : args.Admissible)
    (before during : List Float64Access.Request)
    (beforeFits : ∀ access ∈ before, access.Fits buffers)
    (beforeAllowed : ∀ access ∈ before, access.StartQuery)
    (duringFits : ∀ access ∈ during, access.Fits buffers)
    (duringAllowed : ∀ access ∈ during, access.Allowed kind .initialization) :
    ∃ beforeEntry atExit,
      InitializationAccess.Recovery model program after p buffers kind args before during beforeEntry atExit :=
  InitializationAccess.Recovery.correct program reset initialization get set returned.stored returned.resetStorage
    (returned.buffers stored references values) separate args admissible before during
    beforeFits beforeAllowed duringFits duringAllowed

def Request.RuntimeContract (request : Request) (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames))
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) : Prop :=
    letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
    ∀ (program : Program Invocation), program.internal = LiteralPreparation.program model sigs →
    ∀ (heap : Heap) (p : Address) (kind : Kind) (mode : Mode) (state : ModelExchange.State) (time : Binary64.Value)
      (owners : SlotOwners.State objects.capacity) (retained : Address → Prop),
    CReadOnly.Preserves (pool.install baseHeap firstBlock signed) heap →
    Float64Access.Instance heap p kind mode state time → Reset.Storage heap p →
    request.TransferStorage heap → (∀ q, p.InRecord q → request.Outside q) → request.Condition kind mode →
    p.block = objects.instances.block → SlotOwners.Represents objects.flagsBlock heap owners →
    ∃ category message,
      pool.addresses firstBlock "logStatus" = some category ∧
      pool.addresses firstBlock request.message = some message ∧
      request.hostRun heap = some (request.prepare heap) ∧
      (∀ (logger : Option Address) (logging : Bool),
        load heap (p.member "logger") = some (.pointer logger) →
        load heap (p.member "logging") = some (boolean logging) → (logger = none ∨ logging = false) →
        (∀ behavior, request.Behaves program heap p behavior ↔
          behavior = .terminates [] ⟨.integer 3, LifecycleBodies.writeMode (request.prepare heap) p .terminated⟩) ∧
        Returned objects retained owners request heap p kind state time
          (LifecycleBodies.writeMode (request.prepare heap) p .terminated)) ∧
      (∀ (logger : Address) (environment : Option Address) (name : String) (effect : ReturningEffect (Logging.signature name)),
        load heap (p.member "logger") = some (.pointer (some logger)) →
        load heap (p.member "logging") = some (.integer 1) →
        load heap (p.member "environment") = some (.pointer environment) →
        program.addresses logger = some name → program.externals name = some (External.observed (Logging.signature name) effect) →
        Respects effect objects retained →
        (∀ behavior, request.Behaves program heap p behavior ↔
          (∃ value after, effect.execute (Logging.arguments environment category message)
            (LifecycleBodies.writeMode (request.prepare heap) p .terminated) value after ∧
            behavior = .terminates [⟨name, Logging.arguments environment category message⟩] ⟨.integer 3, after⟩) ∨
          ((∀ value after, ¬ effect.execute (Logging.arguments environment category message)
            (LifecycleBodies.writeMode (request.prepare heap) p .terminated) value after) ∧ behavior = .wrong [])) ∧
        ∀ events status after, request.Behaves program heap p (.terminates events ⟨status, after⟩) →
          events = [⟨name, Logging.arguments environment category message⟩] ∧ status = .integer 3 ∧
          Returned objects retained owners request heap p kind state time after)

/-- Source-prepared accessor contracts govern the actual host-transfer/call
composition. Suppressed logging has a unique result. Enabled logging retains
every modeled return and no-return branch, and derives the recovery invariant
from every completed raw call rather than assuming its expected status. -/
theorem Request.execution (request : Request) (header : CFenv.Header) (objects : Objects)
    (model : Solve.FMI3Model source) (sigs : List Signature)
    (pool : Pool (LiteralPreparation.excluded ++
      (LiteralPreparation.functions model sigs).flatMap functionNames))
    (getter : Float64Environment.PreparedContract model sigs pool)
    (setter : Float64SetEnvironment.PreparedContract model sigs pool)
    (baseHeap : Heap) (firstBlock : Nat) (signed : Bool) :
    request.RuntimeContract header objects model sigs pool baseHeap firstBlock signed := by
  letI : CInterface := RuntimeEnvironment.interface header objects (pool.addresses firstBlock)
  intro program actual heap p kind mode state time owners retained literals stored storage inputs separate condition inPool represented
  obtain ⟨host, readable, _, readonly, _⟩ := request.prepare_correct heap inputs
  have ready := request.prepared_instance stored separate
  have fields (field : String) : load (request.prepare heap) (p.member field) = load heap (p.member field) := by
    simp only [load, request.prepare_frame heap (p.member field) (separate _ (p.member_in_record field))]
  obtain ⟨category, message, categoryBound, messageBound, _, _, quiet, logged⟩ :=
    request.prepared getter setter header baseHeap firstBlock signed objects (request.prepare heap) (literals.trans readonly)
  refine ⟨category, message, categoryBound, messageBound, host, ?_, ?_⟩
  · intro logger logging loggerValue loggingValue suppressed
    have called := quiet Invocation program actual p kind mode logger logging ready.kind ready.mode condition readable
      ((fields "logger").trans loggerValue) ((fields "logging").trans loggingValue) suppressed
    exact ⟨fun behavior => (request.behaves_iff program inputs).trans (called behavior),
      request.returned objects retained owners heap p stored storage inputs separate inPool represented
        (fun _ _ => rfl) (.refl _)⟩
  · intro logger environment name effect loggerValue loggingValue environmentValue address external policy
    obtain ⟨called, _⟩ := logged program actual p logger environment kind mode name effect address external ready.kind ready.mode
      condition readable ((fields "logger").trans loggerValue) ((fields "logging").trans loggingValue)
      ((fields "environment").trans environmentValue)
    have behavior : ∀ observed, request.Behaves program heap p observed ↔ _ :=
      fun observed => (request.behaves_iff program inputs).trans (called observed)
    refine ⟨behavior, ?_⟩
    intro events status after executed
    rcases (behavior _).mp executed with ⟨value, actualAfter, callback, same⟩ | ⟨_, impossible⟩
    · have equal : events = [⟨name, Logging.arguments environment category message⟩] ∧
          status = .integer 3 ∧ after = actualAfter := by
        simpa only [Transition.Events.Observation.terminates.injEq, CBody.Result.mk.injEq] using same
      obtain ⟨events, status, sameAfter⟩ := equal
      subst actualAfter
      exact ⟨events, status, request.returned objects retained owners heap p stored storage inputs separate inPool represented
        (policy _ _ _ _ callback) (effect.readonly _ _ _ _ callback)⟩
    · cases impossible

end Rumoca.FMI3.Float64Rejection
end
