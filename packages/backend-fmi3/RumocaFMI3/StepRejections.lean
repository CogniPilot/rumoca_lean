import RumocaFMI3.FailurePaths
import RumocaFMI3.StepCases
import RumocaFMI3.RuntimeEnvironment

/-! Classified raw rejections reach the actual prepared error or discard block.
Memory and ordinary-library premises follow the reads of each selected path. -/
noncomputable section
namespace Rumoca.FMI3.StepRejections
open CTree CMemory CBody CCalls StaticFactory
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 4096

inductive Reason where
  | lifecycle | outputs | input | rounding | stop | discard
  deriving DecidableEq

def Reason.outcome : Reason → StepCases.Outcome
  | .lifecycle => .lifecycle | .outputs => .outputs | .input => .input
  | .rounding => .rounding | .stop => .stop | .discard => .discard

def Reason.message : Reason → String
  | .lifecycle => ErrorCalls.rejectionMessage
  | .outputs => "Missing output pointer"
  | .input => StepArguments.inputMessage
  | .rounding => StepFailures.roundingMessage
  | .stop => StepFailures.stopMessage
  | .discard => StepDiscard.message

def Reason.writesOutputs : Reason → Bool
  | .lifecycle | .outputs => false
  | _ => true

def Reason.observesRounding : Reason → Bool
  | .rounding | .stop | .discard => true
  | _ => false

def outputHeap (query : StepCases.Query) (heap : Heap) : Heap :=
  match query.outputs.event, query.outputs.terminate, query.outputs.early, query.outputs.last with
  | some event, some terminate, some early, some last =>
      StepEntry.outputHeap heap ⟨event, terminate, early, last⟩ query.time
  | _, _, _, _ => heap

theorem outputHeap_of_buffers (query : StepCases.Query) (heap : Heap) (buffers : StepEntry.Buffers)
    (outputs : query.outputs = buffers.outputs) :
    outputHeap query heap = StepEntry.outputHeap heap buffers query.time := by
  cases buffers
  simp [outputHeap, outputs, StepEntry.Buffers.outputs]

def beforeHeap (reason : Reason) (query : StepCases.Query) (heap : Heap) : Heap :=
  if reason.writesOutputs then outputHeap query heap else heap

def start (query : StepCases.Query) (heap : Heap) (flag : Bool) : Typed.State :=
  .calling StepEntry.signature.name
    (StepEntry.arguments query.handle query.point query.step flag query.outputs) heap .done

/-- Only cells read by the selected rejection prefix are required. -/
structure Reads (reason : Reason) (query : StepCases.Query) (heap : Heap) (p : Address) : Prop where
  kind : load heap (p.member "kind") = some (.integer query.kind.code)
  mode : load heap (p.member "mode") = some (.integer query.mode.code)
  clock : reason.writesOutputs = true → load heap (p.member "time") = some (.finite query.time)
  outputs : reason.writesOutputs = true → ∀ buffers : StepEntry.Buffers,
    query.outputs = buffers.outputs → StepArguments.Storage heap p buffers
  stopDefined : reason = .stop ∨ reason = .discard →
    load heap (p.member "stopDefined") = some (boolean query.stop.isSome)
  stopValue : reason = .stop ∨ reason = .discard →
    ∀ value, query.stop = some value → load heap (p.member "stop") = some (.finite value)

def Path [CInterface] (program : Events.Program E) (reason : Reason)
    (query : StepCases.Query) (heap : Heap) (p : Address) (flag : Bool) : Prop :=
  if reason = .discard then
    StepDiscard.Path program (start query heap flag) (beforeHeap reason query heap) p
  else StaticErrors.FailurePath program (start query heap flag) (beforeHeap reason query heap) p reason.message

/-- Every classified rejection reaches its actual error/discard block under
the same prepared definitions and explicit ordinary-library bindings. -/
theorem public_path {E : Type} (reason : Reason) (query : StepCases.Query) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (member : StepEntry.signature ∈ signatures) :
    letI : CInterface := RuntimeEnvironment.interface query.header objects literals
    ∀ (program : Events.Program E) (heap : Heap) (p : Address) (flag : Bool)
      (range : -(2^31) ≤ query.observed ∧ query.observed < 2^31),
      program.internal = LiteralPreparation.program model signatures →
      (reason.observesRounding = true → program.externals "fegetround" =
        some (CMathCalls.roundingExternal rfl query.observed range)) →
      (reason = .discard → StepGuards.Progress query.time (StepCases.nextTime query) →
        program.externals "floor" = some (CMathCalls.floorExternal rfl)) →
      query.handle = some p → Reads reason query heap p → StepCases.Condition query reason.outcome →
      Path program reason query heap p flag := by
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  intro program heap p flag range actual rounding floorBound handle reads selected
  let context := ErrorContext.withRounding (ErrorContext.static objects literals) query.header
  have defined : program.internal.definitions StepEntry.signature.name =
      some (.tree (Runtime.function model StepEntry.signature)) := by
    rw [actual]
    exact LiteralPreparation.function_bound model signatures unique StepEntry.signature member
  cases reason with
  | lifecycle =>
    have denied := selected.2
    have pure := StepErrors.lifecycle_prefix context model heap p query.point query.step flag query.outputs
      query.kind query.mode reads.kind reads.mode denied
    have reached := StaticErrors.prefix_path program _ _ _ _ _ _ pure defined
    simpa only [Path, Reason.message, Reason.writesOutputs, beforeHeap, start, handle,
      Bool.false_eq_true, ↓reduceIte] using reached
  | outputs =>
    obtain ⟨_, allowed, missing⟩ := selected
    have pure := StepArguments.outputs_prefix context model heap p query.point query.step flag query.outputs
      (by simpa only [allowed.1, Kind.code] using reads.kind)
      (by simpa only [allowed.2, Mode.code] using reads.mode) missing
    have reached := StaticErrors.prefix_path program _ _ _ _ _ _ pure defined
    simpa only [Path, Reason.message, Reason.writesOutputs, beforeHeap, start, handle,
      Bool.false_eq_true, ↓reduceIte] using reached
  | input =>
    obtain ⟨_, allowed, present, invalid⟩ := selected
    obtain ⟨buffers, outputs⟩ := (StepArguments.output_cases query.outputs).resolve_left present
    have pure := StepArguments.input_prefix context model heap p buffers query.point query.step query.time flag
      (by simpa only [allowed.1, Kind.code] using reads.kind)
      (by simpa only [allowed.2, Mode.code] using reads.mode)
      (reads.clock rfl) (reads.outputs rfl buffers outputs) invalid
    have reached := StaticErrors.prefix_path program _ _ _ _ _ _ pure defined
    simpa only [Path, Reason.message, Reason.writesOutputs, beforeHeap, start, handle, outputs,
      outputHeap_of_buffers query heap buffers outputs, ↓reduceIte] using reached
  | rounding =>
    obtain ⟨ready, rejected⟩ := selected
    obtain ⟨_, allowed, present, valid⟩ := ready
    obtain ⟨buffers, outputs⟩ := (StepArguments.output_cases query.outputs).resolve_left present
    have reached := StepFailures.rounding_prefix context model query.header program heap p buffers
      query.point query.step query.time flag query.observed range rfl rfl rfl (rounding rfl) defined
      (by simpa only [allowed.1, Kind.code] using reads.kind)
      (by simpa only [allowed.2, Mode.code] using reads.mode)
      (reads.clock rfl) (reads.outputs rfl buffers outputs) valid rejected
    simpa only [Path, Reason.message, Reason.writesOutputs, beforeHeap, start, handle, outputs,
      outputHeap_of_buffers query heap buffers outputs, ↓reduceIte] using reached
  | stop =>
    obtain ⟨ready, nearest, beyond⟩ := selected
    obtain ⟨_, allowed, present, valid⟩ := ready
    obtain ⟨buffers, outputs⟩ := (StepArguments.output_cases query.outputs).resolve_left present
    obtain ⟨current, duration, point, step, same, positive⟩ := StepCases.input_values query.point query.step query.time valid
    have observed : program.externals "fegetround" = some
        (CMathCalls.roundingExternal rfl query.header.nearest
          ⟨by have positive := query.header.nonnegative; omega, query.header.bounded⟩) := by
      simpa only [nearest] using rounding rfl
    have reached := StepFailures.stop_prefix context model query.header program heap p buffers query.point duration
      query.time flag query.stop rfl rfl rfl observed defined
      (by simpa only [allowed.1, Kind.code] using reads.kind)
      (by simpa only [allowed.2, Mode.code] using reads.mode)
      (reads.clock rfl) (reads.outputs rfl buffers outputs) (by simpa only [step] using valid)
      (reads.stopDefined (Or.inl rfl)) (reads.stopValue (Or.inl rfl))
      (by simpa only [StepCases.nextTime, step, Float64.decode_finite] using beyond)
    simpa only [Path, Reason.message, Reason.writesOutputs, beforeHeap, start, handle, outputs, step,
      outputHeap_of_buffers query heap buffers outputs, ↓reduceIte] using reached
  | discard =>
    obtain ⟨ready, nearest, noStop, rejected⟩ := selected
    obtain ⟨_, allowed, present, valid⟩ := ready
    obtain ⟨buffers, outputs⟩ := (StepArguments.output_cases query.outputs).resolve_left present
    obtain ⟨current, duration, point, step, same, positive⟩ := StepCases.input_values query.point query.step query.time valid
    have observed : program.externals "fegetround" = some
        (CMathCalls.roundingExternal rfl query.header.nearest
          ⟨by have positive := query.header.nonnegative; omega, query.header.bounded⟩) := by
      simpa only [nearest] using rounding rfl
    have reached := StepDiscard.public_prefix context model query.header program heap p buffers query.point duration
      query.time flag query.stop rfl rfl rfl rfl rfl rfl observed
      (by intro progress; apply floorBound rfl
          simpa only [StepCases.nextTime, step, Float64.decode_finite] using progress)
      defined (by simpa only [allowed.1, Kind.code] using reads.kind)
      (by simpa only [allowed.2, Mode.code] using reads.mode)
      (reads.clock rfl) (reads.outputs rfl buffers outputs) (by simpa only [step] using valid)
      (reads.stopDefined (Or.inr rfl)) (reads.stopValue (Or.inr rfl))
      (by simpa only [StepCases.nextTime, step, Float64.decode_finite] using noStop)
      (by simpa only [StepDiscard.Rejected, StepCases.nextTime, StepCases.Duration, step, Float64.decode_finite] using rejected)
    simpa only [Path, Reason.writesOutputs, beforeHeap, start, handle, outputs, step,
      outputHeap_of_buffers query heap buffers outputs, ↓reduceIte] using reached

end Rumoca.FMI3.StepRejections
end
