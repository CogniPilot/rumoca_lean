import RumocaFMI3.StepContract
import RumocaCore.Solve.Run

/-! Finite admitted CS histories, with raw request bits and an unbounded
mathematical solver duration distinct from the rounded communication clock.
Only initial caller/instance storage is assumed; subsequent storage is derived.
Foreign environment and ownership premises remain explicit. -/
noncomputable section
namespace Rumoca.FMI3.CSHistory
open CTree CMemory CBody CCalls StaticFactory
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 4096

structure Request where
  point : BitVec 64
  step : BitVec 64
  flag : Bool

structure ReferenceState where
  time : Binary64.Value
  elapsed : Nat

def Request.query (request : Request) (header : CFenv.Header) (p : Address)
    (buffers : StepEntry.Buffers) (reference : ReferenceState)
    (stop : Option Binary64.Value) : StepCases.Query :=
  ⟨some p, .cs, .step, buffers.outputs, request.point, request.step,
    reference.time, stop, header.nearest, header⟩

/-- The reference relation states the admitted mathematical duration and
rounded time progression independently of any C execution. -/
def Accepted (stop : Option Binary64.Value) (before : ReferenceState)
    (request : Request) (after : ReferenceState) : Prop :=
  ∃ (point duration : Binary64.Value) (count : Nat),
    request.point = (Binary64.toBits point).val ∧
    request.step = (Binary64.toBits duration).val ∧
    Binary64.value point = Binary64.value before.time ∧
    0 < count ∧ count ≤ 1000000 ∧ Binary64.value duration = (count : ℝ) ∧
    after.time = Binary64.roundedAdd before.time duration ∧
    Binary64.value before.time < Binary64.value after.time ∧
    (∀ limit, stop = some limit → Binary64.value after.time ≤ Binary64.value limit) ∧
    after.elapsed = before.elapsed + count

theorem accepted_case (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers)
    (accepted : Accepted stop before request after) :
    StepCases.Condition (request.query header p buffers before stop) .accepted := by
  obtain ⟨point, duration, count, pointBits, stepBits, same, positive, bounded,
    durationValue, clock, progress, limit, _⟩ := accepted
  let counter : CStatements.Counter := ⟨count, by omega⟩
  have admitted := StepAdmission.duration_of_count duration counter positive bounded durationValue
  have sum := StepAdmission.duration_sum before.time duration admitted
  refine ⟨⟨by simp [Request.query], ⟨rfl, rfl⟩, ?_, ?_⟩, rfl, ?_, ?_, ?_⟩
  · simp [Request.query, StepArguments.MissingOutput, StepEntry.Buffers.outputs]
  · simp only [Request.query, StepEntry.InputsValid, pointBits, stepBits, Float64.decode_finite]
    exact ⟨same, admitted.1⟩
  · simp only [StepCases.nextTime, Request.query, stepBits, Float64.decode_finite, sum]
    cases chosen : stop with
    | none => simp [StepGuards.AboveStop]
    | some value =>
      simpa only [StepGuards.AboveStop, not_lt, ← clock] using limit value chosen
  · simpa only [StepCases.nextTime, Request.query, stepBits, Float64.decode_finite,
      sum, StepGuards.Progress, ← clock] using progress
  · simpa only [StepCases.Duration, Request.query, stepBits, Float64.decode_finite] using admitted

structure Stored (model : Solve.Model source) (seed : Binary64.Value) (heap : Heap)
    (p : Address) (buffers : StepEntry.Buffers) (reference : ReferenceState)
    (stop : Option Binary64.Value) : Prop where
  kind : load heap (p.member "kind") = some (.integer 1)
  mode : load heap (p.member "mode") = some (.integer 4)
  clock : heap (p.member "time") = some ⟨.float64, true, some (.finite reference.time)⟩
  state : heap (StateProofs.stateAddress p) =
    some ⟨.float64, true, some (.finite (model.run seed reference.elapsed))⟩
  stopDefined : load heap (p.member "stopDefined") = some (boolean stop.isSome)
  stopValue : ∀ limit, stop = some limit → load heap (p.member "stop") = some (.finite limit)
  buffers : StepArguments.Storage heap p buffers

def written (model : Solve.Model source) (seed : Binary64.Value) (heap : Heap)
    (p : Address) (buffers : StepEntry.Buffers) (before after : ReferenceState) : Heap :=
  StepAdvance.written (StepEntry.outputHeap heap buffers before.time) p buffers.last
    (model.run seed after.elapsed) after.time

def Outputs (heap : Heap) (buffers : StepEntry.Buffers) (time : Binary64.Value) : Prop :=
  heap buffers.event = some ⟨.boolean, true, some (.integer 0)⟩ ∧
  heap buffers.terminate = some ⟨.boolean, true, some (.integer 0)⟩ ∧
  heap buffers.early = some ⟨.boolean, true, some (.integer 0)⟩ ∧
  heap buffers.last = some ⟨.float64, true, some (.finite time)⟩

def Outside (p : Address) (buffers : StepEntry.Buffers) (query : Address) : Prop :=
  query ≠ StateProofs.stateAddress p ∧ query ≠ p.member "time" ∧
  query ≠ buffers.event ∧ query ≠ buffers.terminate ∧
  query ≠ buffers.early ∧ query ≠ buffers.last

theorem written_frame (model : Solve.Model source) (seed : Binary64.Value) (heap : Heap)
    (p : Address) (buffers : StepEntry.Buffers) (before after : ReferenceState)
    (query : Address) (outside : Outside p buffers query) :
    written model seed heap p buffers before after query = heap query :=
  StepEntry.call_frame heap p buffers _ _ _ query outside.1 outside.2.1
    outside.2.2.1 outside.2.2.2.1 outside.2.2.2.2.1 outside.2.2.2.2.2

theorem field_outside (stored : StepArguments.Storage heap p buffers)
    (name : String) (other : name ≠ "time") : Outside p buffers (p.member name) := by
  have separated (address : Address) (outside : address.block ≠ p.block) : p.member name ≠ address := by
    intro same
    exact outside (congrArg Address.block same).symm
  refine ⟨?_, by simpa using other, separated _ stored.outsideEvent,
    separated _ stored.outsideTerminate, separated _ stored.outsideEarly, separated _ stored.outsideLast⟩
  intro same
  have lengths := congrArg (fun address : Address => address.members.length) same
  simp [StateProofs.stateAddress, Address.member] at lengths

theorem written_stored (stored : Stored model seed heap p buffers before stop)
    (after : ReferenceState) :
    Stored model seed (written model seed heap p buffers before after) p buffers after stop ∧
    Outputs (written model seed heap p buffers before after) buffers after.time := by
  obtain ⟨old, last⟩ := stored.buffers.last
  obtain ⟨event, terminate, early, state, clock, output⟩ := StepEntry.final_values
    heap p buffers before.time (model.run seed after.elapsed) after.time old
    stored.buffers.event stored.buffers.terminate stored.buffers.early last
    stored.buffers.outsideEvent stored.buffers.outsideTerminate
    stored.buffers.outsideEarly stored.buffers.outsideLast
  have fields (name : String) (other : name ≠ "time") :
      load (written model seed heap p buffers before after) (p.member name) = load heap (p.member name) := by
    simp only [load, written_frame model seed heap p buffers before after _
      (field_outside stored.buffers name other)]
  refine ⟨⟨(fields "kind" (by decide)).trans stored.kind,
    (fields "mode" (by decide)).trans stored.mode, clock, state,
    (fields "stopDefined" (by decide)).trans stored.stopDefined,
    fun value chosen => (fields "stop" (by decide)).trans (stored.stopValue value chosen), ?_⟩,
    event, terminate, early, output⟩
  exact ⟨⟨_, event⟩, ⟨_, terminate⟩, ⟨_, early⟩, ⟨_, output⟩,
    stored.buffers.outsideEvent, stored.buffers.outsideTerminate,
    stored.buffers.outsideEarly, stored.buffers.outsideLast⟩

theorem stored_call (stored : Stored model seed heap p buffers reference stop)
    (header : CFenv.Header) (request : Request) :
    StepCalls.Storage (request.query header p buffers reference stop) heap
      (model.run seed reference.elapsed) := by
  constructor
  · intro address handle
    have same : p = address := Option.some.inj handle
    subst address
    exact ⟨stored.kind, stored.mode, stored.clock, stored.stopDefined, stored.stopValue, stored.state⟩
  · intro address outputs handle sameOutputs
    have same : p = address := Option.some.inj handle
    subst address
    have buffersSame : buffers = outputs := by
      cases buffers
      cases outputs
      simpa [Request.query, StepEntry.Buffers.outputs] using sameOutputs
    subst outputs
    exact stored.buffers

theorem accepted_of_case (header : CFenv.Header) (p : Address) (buffers : StepEntry.Buffers)
    (admitted : StepCases.Condition (request.query header p buffers before stop) .accepted) :
    ∃ after, Accepted stop before request after := by
  obtain ⟨_, _, point, duration, _, _, _, _, pointBits, stepBits, same,
    durationAccepted, _, progress, limit⟩ :=
    StepCases.accepted_values (request.query header p buffers before stop) admitted
  obtain ⟨count, positive, bounded, durationValue, _⟩ := StepAdmission.duration_count duration durationAccepted
  exact ⟨⟨Binary64.roundedAdd before.time duration, before.elapsed + count.val⟩,
    point, duration, count.val, pointBits, stepBits, same, positive, bounded,
    durationValue, rfl, progress, limit, rfl⟩

theorem step (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (signatures : List Signature)
    (seed : Binary64.Value) (p : Address) (buffers : StepEntry.Buffers)
    (before after : ReferenceState) (stop : Option Binary64.Value) (request : Request)
    (contract : StepCalls.AcceptedContract (request.query header p buffers before stop)
      objects literals model signatures) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Events.Program E) (heap : Heap)
      (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
      program.internal = LiteralPreparation.program model signatures →
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      Stored model.solve seed heap p buffers before stop → Accepted stop before request after →
      (∀ behavior, (Events.machine program).Behaves
        (.calling StepEntry.signature.name
          (StepEntry.arguments (some p) request.point request.step request.flag buffers.outputs) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, written model.solve seed heap p buffers before after⟩) ∧
      Stored model.solve seed (written model.solve seed heap p buffers before after) p buffers after stop ∧
      Outputs (written model.solve seed heap p buffers before after) buffers after.time := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap range actual rounding floorBound stored accepted
  have admitted := accepted_case header p buffers accepted
  obtain ⟨point, duration, n, _, stepBits, _, _, _, durationValue, clock, _, _, elapsed⟩ := accepted
  obtain ⟨address, outputs, computedDuration, count, handle, outputAddresses, computedBits,
    _, _, computedValue, executed⟩ := contract E program heap (model.solve.run seed before.elapsed)
      request.flag range actual rounding floorBound (stored_call stored header request)
        admitted
  have sameAddress : p = address := Option.some.inj handle
  subst address
  have sameOutputs : buffers = outputs := by
    cases buffers
    cases outputs
    simpa [Request.query, StepEntry.Buffers.outputs] using outputAddresses
  subst outputs
  have encoded : (Binary64.toBits computedDuration).val = (Binary64.toBits duration).val :=
    computedBits.symm.trans stepBits
  have sameDuration : computedDuration = duration := by
    have decoded := congrArg Float64.decode encoded
    simpa only [Float64.decode_finite, Float64.Number.finite.injEq] using decoded
  subst computedDuration
  have sameCount : count.val = n := by exact_mod_cast computedValue.symm.trans durationValue
  refine ⟨?_, written_stored stored after⟩
  intro behavior
  simpa only [StepRejections.start, Request.query, ← model.solve.run_add,
    sameCount, ← elapsed, ← clock, written] using executed behavior

inductive ReferenceTrace (stop : Option Binary64.Value) :
    ReferenceState → List Request → ReferenceState → Prop where
  | nil : ReferenceTrace stop reference [] reference
  | cons {before following final : ReferenceState} {request : Request} {rest : List Request} :
      Accepted stop before request following → ReferenceTrace stop following rest final →
      ReferenceTrace stop before (request :: rest) final

/-- This relation retains every intermediate call and output, with an
all-behavior contract for each actual public invocation. -/
inductive Calls [CInterface] (program : Events.Program E) (p : Address)
    (buffers : StepEntry.Buffers) :
    Heap → ReferenceState → List Request → Heap → ReferenceState → Prop where
  | nil : Calls program p buffers heap reference [] heap reference
  | cons {heap after finalHeap : Heap} {before following final : ReferenceState}
      {request : Request} {rest : List Request} : (∀ behavior, (Events.machine program).Behaves
        (.calling StepEntry.signature.name
          (StepEntry.arguments (some p) request.point request.step request.flag buffers.outputs) heap .done) behavior ↔
        behavior = .terminates [] ⟨.integer 0, after⟩) →
      Outputs after buffers following.time → Calls program p buffers after following rest finalHeap final →
      Calls program p buffers heap before (request :: rest) finalHeap final

theorem trace_frame (header : CFenv.Header) (objects : Objects) (literals : CLiteralAddresses)
    (model : Solve.FMI3Model source) (signatures : List Signature)
    (seed : Binary64.Value) (p : Address) (buffers : StepEntry.Buffers) (stop : Option Binary64.Value)
    (contracts : ∀ (reference : ReferenceState) (request : Request), StepCalls.AcceptedContract
      (request.query header p buffers reference stop) objects literals model signatures) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : Events.Program E)
      (range : -(2^31) ≤ header.nearest ∧ header.nearest < 2^31),
      program.internal = LiteralPreparation.program model signatures →
      program.externals "fegetround" = some (CMathCalls.roundingExternal rfl header.nearest range) →
      program.externals "floor" = some (CMathCalls.floorExternal rfl) →
      ∀ (heap : Heap) (before final : ReferenceState) (requests : List Request),
      Stored model.solve seed heap p buffers before stop → ReferenceTrace stop before requests final →
      ∃ after, Calls program p buffers heap before requests after final ∧
        Stored model.solve seed after p buffers final stop ∧
        ∀ query, Outside p buffers query → after query = heap query := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program range actual rounding floorBound heap before final requests stored admitted
  induction admitted generalizing heap with
  | nil => exact ⟨heap, .nil, stored, fun _ _ => rfl⟩
  | cons accepted _ ih =>
    obtain ⟨called, storedAfter, outputs⟩ := step header objects literals model signatures seed p buffers
      _ _ stop _ (contracts _ _) program heap range actual rounding floorBound stored accepted
    obtain ⟨after, calls, finalStored, frame⟩ := ih _ storedAfter
    refine ⟨after, .cons called outputs calls, finalStored, ?_⟩
    intro query outside
    exact (frame query outside).trans (written_frame model.solve seed heap p buffers _ _ query outside)

theorem ReferenceTrace.clock_monotone (trace : ReferenceTrace stop before requests final) :
    Binary64.value before.time ≤ Binary64.value final.time := by
  induction trace with
  | nil => exact le_rfl
  | cons accepted _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, progress, _, _⟩ := accepted
    exact progress.le.trans ih

theorem ReferenceTrace.duration_monotone (trace : ReferenceTrace stop before requests final) :
    before.elapsed ≤ final.elapsed := by
  induction trace with
  | nil => exact le_rfl
  | cons accepted _ ih =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, elapsed⟩ := accepted
    omega

end Rumoca.FMI3.CSHistory
end
