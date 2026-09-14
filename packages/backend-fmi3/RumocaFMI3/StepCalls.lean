import RumocaFMI3.StepRejectionCalls

/-! Complete raw public CS call contracts under the prepared static/header
interface, with explicit caller storage and foreign effects. -/
noncomputable section
namespace Rumoca.FMI3.StepCalls
open CTree CMemory CBody CCalls StaticFactory CLiteral
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 4096

/-- Original instance cells used by a successful CS call. The query supplies
the finite source state/clock interpretation; no executed C state is assumed. -/
structure State (heap : Heap) (p : Address) (query : StepCases.Query) (x : Binary64.Value) : Prop where
  kind : load heap (p.member "kind") = some (.integer query.kind.code)
  mode : load heap (p.member "mode") = some (.integer query.mode.code)
  clock : heap (p.member "time") = some ⟨.float64, true, some (.finite query.time)⟩
  stopDefined : load heap (p.member "stopDefined") = some (boolean query.stop.isSome)
  stopValue : ∀ stop, query.stop = some stop → load heap (p.member "stop") = some (.finite stop)
  state : heap (StateProofs.stateAddress p) = some ⟨.float64, true, some (.finite x)⟩

structure Storage (query : StepCases.Query) (heap : Heap) (x : Binary64.Value) : Prop where
  modelState : ∀ p, query.handle = some p → State heap p query x
  outputs : ∀ (p : Address) (buffers : StepEntry.Buffers), query.handle = some p → query.outputs = buffers.outputs →
    StepArguments.Storage heap p buffers

/-- Every accepted raw request executes the actual prepared function table
and numerical kernel in the shared static-object/header interface. -/
theorem accepted_call {E : Type} (query : StepCases.Query) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (fresh : LiteralPreparation.KernelNamesFresh signatures) (member : StepEntry.signature ∈ signatures) :
    letI : CInterface := RuntimeEnvironment.interface query.header objects literals
    ∀ (program : Events.Program E) (heap : Heap) (x : Binary64.Value) (flag : Bool)
      (range : -(2^31) ≤ query.observed ∧ query.observed < 2^31),
      program.internal = LiteralPreparation.program model signatures →
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl query.observed range) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      Storage query heap x → StepCases.Condition query .accepted →
      ∃ (p : Address) (buffers : StepEntry.Buffers) (duration : Binary64.Value) (count : CStatements.Counter),
        query.handle = some p ∧ query.outputs = buffers.outputs ∧
        query.step = (Binary64.toBits duration).val ∧
        0 < count.val ∧ count.val ≤ 1000000 ∧ Binary64.value duration = (count.val : ℝ) ∧
        ∀ behavior, (Events.machine program).Behaves
          (.calling StepEntry.signature.name
            (StepEntry.arguments query.handle query.point query.step flag query.outputs) heap .done) behavior ↔
          behavior = .terminates [] ⟨.integer 0,
            StepAdvance.written (StepEntry.outputHeap heap buffers query.time) p buffers.last
              (model.solve.run x count.val) (Binary64.roundedAdd query.time duration)⟩ := by
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  intro program heap x flag range actual rounding floorBound stored admitted
  obtain ⟨p, buffers, current, duration, handle, outputs, kind, mode, point, step, same,
    accepted, nearest, progress, stop⟩ := StepCases.accepted_values query admitted
  have fields := stored.modelState p handle
  have cells := stored.outputs p buffers handle outputs
  obtain ⟨oldOutput, last⟩ := cells.last
  have roundingBound : program.externals "fegetround" = some
      (CMathCalls.roundingExternal rfl query.header.nearest
        ⟨by have positive := query.header.nonnegative; omega, query.header.bounded⟩) := by
    simpa only [nearest] using rounding
  let context := ErrorContext.withRounding (ErrorContext.static objects literals) query.header
  have types : StepEntry.Types := StepErrors.types context
  have helperTypes : ModelAdvance.Types := ⟨rfl, rfl, rfl⟩
  have defined : program.internal.definitions StepEntry.signature.name =
      some (.tree (Runtime.function model StepEntry.signature)) := by
    rw [actual]
    exact LiteralPreparation.function_bound model signatures unique StepEntry.signature member
  have helper : program.internal.definitions "model_advance" = some (.tree Runtime.helpers[2]) := by
    rw [actual]
    exact LiteralPreparation.helpers_bound model signatures Runtime.helpers[2] (by simp [Runtime.helpers])
  have sample : program.internal.definitions "rumoca_sample" = some (.kernel .sample) := by
    rw [actual]
    exact LiteralPreparation.numerical_bound model signatures fresh .sample
  have clock : load heap (p.member "time") = some (.finite query.time) := by
    simp [load, fields.clock, Value.finite, convert]
  obtain ⟨count, positive, bounded, durationValue, executed⟩ := StepEntry.accepted_call types program model
    query.header heap p buffers x current query.time duration flag query.stop (some (.finite query.time)) oldOutput
    rfl rfl rfl helperTypes
    (by intro name member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> rfl)
    rfl rfl roundingBound floorBound defined
    (by simpa only [kind, Kind.code] using fields.kind)
    (by simpa only [mode, Mode.code] using fields.mode)
    clock same fields.stopDefined fields.stopValue accepted progress stop
    (by rw [actual]; rfl) helper sample fields.state fields.clock
    cells.event cells.terminate cells.early last cells.outsideEvent cells.outsideTerminate cells.outsideEarly cells.outsideLast
  refine ⟨p, buffers, duration, count, handle, outputs, step, positive, bounded, durationValue, ?_⟩
  intro behavior
  simpa only [handle, outputs, point, step] using executed behavior


def Success [CInterface] (query : StepCases.Query) (model : Solve.FMI3Model source)
    (program : Events.Program E) (heap : Heap) (x : Binary64.Value) (flag : Bool) : Prop :=
  ∃ (p : Address) (buffers : StepEntry.Buffers) (duration : Binary64.Value) (count : CStatements.Counter),
    query.handle = some p ∧ query.outputs = buffers.outputs ∧ query.step = (Binary64.toBits duration).val ∧
    0 < count.val ∧ count.val ≤ 1000000 ∧ Binary64.value duration = (count.val : ℝ) ∧
    ∀ behavior, (Events.machine program).Behaves (StepRejections.start query heap flag) behavior ↔
      behavior = .terminates [] ⟨.integer 0,
        StepAdvance.written (StepEntry.outputHeap heap buffers query.time) p buffers.last
          (model.solve.run x count.val) (Binary64.roundedAdd query.time duration)⟩

def AcceptedContract (query : StepCases.Query) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (signatures : List Signature) : Prop :=
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  ∀ (E : Type) (program : Events.Program E) (heap : Heap) (x : Binary64.Value) (flag : Bool)
    (range : -(2^31) ≤ query.observed ∧ query.observed < 2^31),
    program.internal = LiteralPreparation.program model signatures →
    program.externals "fegetround" = some (CMathCalls.roundingExternal rfl query.observed range) →
    program.externals "floor" = some (CMathCalls.floorExternal rfl) →
    Storage query heap x → StepCases.Condition query .accepted → Success query model program heap x flag

def NullContract (query : StepCases.Query) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (signatures : List Signature) : Prop :=
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  ∀ (E : Type) (program : Events.Program E) (heap : Heap) (flag : Bool),
    program.internal = LiteralPreparation.program model signatures → StepCases.Condition query .null →
    ∀ behavior, (Events.machine program).Behaves (StepRejections.start query heap flag) behavior ↔
      behavior = .terminates [] ⟨.integer 3, heap⟩

theorem accepted_correct (query : StepCases.Query) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (fresh : LiteralPreparation.KernelNamesFresh signatures) (member : StepEntry.signature ∈ signatures) :
    AcceptedContract query objects literals model signatures := by
  intro E
  exact accepted_call query objects literals model signatures unique fresh member

theorem null_correct (query : StepCases.Query) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (member : StepEntry.signature ∈ signatures) : NullContract query objects literals model signatures := by
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  intro E program heap flag actual isNull behavior
  have defined : program.internal.definitions StepEntry.signature.name =
      some (.tree (Runtime.function model StepEntry.signature)) := by
    rw [actual]
    exact LiteralPreparation.function_bound model signatures unique StepEntry.signature member
  let context := ErrorContext.withRounding (ErrorContext.static objects literals) query.header
  have call := StepEntry.null_call (StepErrors.types context) program model heap query.point query.step flag
    query.outputs rfl rfl defined behavior
  simpa only [StepRejections.start, show query.handle = none from isNull] using call

def SuppressedContract (query : StepCases.Query) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (signatures : List Signature) (heap : Heap) : Prop :=
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  ∀ (E : Type) (program : Events.Program E) (reason : StepRejections.Reason) (p : Address) (flag : Bool)
    (range : -(2^31) ≤ query.observed ∧ query.observed < 2^31) (logger : Option Address) (logging : Bool),
    program.internal = LiteralPreparation.program model signatures →
    (reason.observesRounding = true → program.externals "fegetround" =
      some (CMathCalls.roundingExternal rfl query.observed range)) →
    (reason = .discard → StepGuards.Progress query.time (StepCases.nextTime query) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl)) →
    query.handle = some p → StepRejections.Reads reason query heap p →
    StepCases.Condition query reason.outcome →
    (reason ≠ .discard → ∃ old, heap (p.member "mode") = some ⟨.int32, true, old⟩) →
    load heap (p.member "logger") = some (.pointer logger) →
    load heap (p.member "logging") = some (boolean logging) →
    (logger = none ∨ logging = false) → ∀ behavior,
    (Events.machine program).Behaves (StepRejections.start query heap flag) behavior ↔
      behavior = .terminates [] ⟨.integer (StepRejections.status reason), StepRejections.afterHeap reason query heap p⟩

def LoggedContract (query : StepCases.Query) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (signatures : List Signature) (heap : Heap) (signed : Bool)
    (category : Address) (messages : StepRejections.Reason → Address) : Prop :=
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  ∀ (program : Events.Program Events.Invocation) (reason : StepRejections.Reason) (p logger : Address) (flag : Bool)
    (range : -(2^31) ≤ query.observed ∧ query.observed < 2^31) (environment : Option Address)
    (name : String) (effect : Events.ReturningEffect (Logging.signature name)),
    program.internal = LiteralPreparation.program model signatures →
    (reason.observesRounding = true → program.externals "fegetround" =
      some (CMathCalls.roundingExternal rfl query.observed range)) →
    (reason = .discard → StepGuards.Progress query.time (StepCases.nextTime query) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl)) →
    program.addresses logger = some name →
    program.externals name = some (Events.External.observed (Logging.signature name) effect) →
    query.handle = some p → StepRejections.Reads reason query heap p →
    StepCases.Condition query reason.outcome →
    (reason ≠ .discard → ∃ old, heap (p.member "mode") = some ⟨.int32, true, old⟩) →
    load heap (p.member "logger") = some (.pointer (some logger)) →
    load heap (p.member "logging") = some (.integer 1) →
    load heap (p.member "environment") = some (.pointer environment) →
    (∀ behavior, (Events.machine program).Behaves (StepRejections.start query heap flag) behavior ↔
      (∃ value after, effect.execute (StepRejections.arguments reason environment category (messages reason))
        (StepRejections.afterHeap reason query heap p) value after ∧
        behavior = .terminates [⟨name, StepRejections.arguments reason environment category (messages reason)⟩]
          ⟨.integer (StepRejections.status reason), after⟩) ∨
      ((∀ value after, ¬ effect.execute (StepRejections.arguments reason environment category (messages reason))
        (StepRejections.afterHeap reason query heap p) value after) ∧ behavior = .wrong [])) ∧
    (∀ value after, effect.execute (StepRejections.arguments reason environment category (messages reason))
      (StepRejections.afterHeap reason query heap p) value after →
      Stored signed after category "logStatus" ∧ ∀ other, Stored signed after (messages other) other.message)

theorem suppressed_correct (query : StepCases.Query) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (member : StepEntry.signature ∈ signatures) (heap : Heap) (messages : StepRejections.Reason → Address)
    (bound : ∀ reason, literals reason.message = some (messages reason)) :
    SuppressedContract query objects literals model signatures heap := by
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  intro E program reason p flag range logger logging actual rounding floorBound handle reads selected
    writable loggerValue loggingValue suppressed behavior
  exact StepRejections.suppressed_call reason query objects literals model signatures unique member
    program heap p (messages reason) flag range logger logging actual rounding floorBound (fun _ => bound reason)
    handle reads selected writable loggerValue loggingValue suppressed behavior

theorem logged_correct (query : StepCases.Query) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (member : StepEntry.signature ∈ signatures) (heap : Heap) (signed : Bool)
    (category : Address) (messages : StepRejections.Reason → Address)
    (categoryBound : literals "logStatus" = some category)
    (bound : ∀ reason, literals reason.message = some (messages reason))
    (categoryStored : Stored signed heap category "logStatus")
    (messageStored : ∀ reason, Stored signed heap (messages reason) reason.message) :
    LoggedContract query objects literals model signatures heap signed category messages := by
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  intro program reason p logger flag range environment name effect actual rounding floorBound address external
    handle reads selected writable loggerValue loggingValue environmentValue
  have all := StepRejections.logged_call reason query objects literals model signatures unique member
    program heap p (messages reason) category logger flag range environment name
    (Events.External.observed (Logging.signature name) effect) actual rounding floorBound (bound reason) categoryBound
    address external rfl handle reads selected writable loggerValue loggingValue environmentValue
  constructor
  · intro behavior
    exact (all behavior).trans (Events.observed_choices effect _ _
      (fun _ after => ⟨.integer (StepRejections.status reason), after⟩) behavior)
  · intro value after executed
    have successful := (all (.terminates [⟨name, StepRejections.arguments reason environment category (messages reason)⟩]
      ⟨.integer (StepRejections.status reason), after⟩)).mpr (Or.inl ⟨_, value, after, ⟨rfl, executed⟩, rfl⟩)
    have preserved := Events.termination_preserves successful
    exact ⟨categoryStored.preserved preserved, fun other => (messageStored other).preserved preserved⟩

theorem outcome_cases (query : StepCases.Query) :
    StepCases.Condition query .null ∨ StepCases.Condition query .accepted ∨
      ∃ reason : StepRejections.Reason, StepCases.Condition query reason.outcome := by
  obtain ⟨outcome, selected⟩ := StepCases.complete query
  cases outcome with
  | null => exact Or.inl selected
  | accepted => exact Or.inr (Or.inl selected)
  | lifecycle => exact Or.inr (Or.inr ⟨.lifecycle, selected⟩)
  | outputs => exact Or.inr (Or.inr ⟨.outputs, selected⟩)
  | input => exact Or.inr (Or.inr ⟨.input, selected⟩)
  | rounding => exact Or.inr (Or.inr ⟨.rounding, selected⟩)
  | stop => exact Or.inr (Or.inr ⟨.stop, selected⟩)
  | discard => exact Or.inr (Or.inr ⟨.discard, selected⟩)

end Rumoca.FMI3.StepCalls
end
