import RumocaFMI3.StepRejections

/-! Complete prepared CS rejection calls with shared frames and all represented
callback outcomes. Discard preserves the instance until any foreign callback. -/
noncomputable section
namespace Rumoca.FMI3.StepRejections
open CTree CMemory CBody CCalls StaticFactory
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option exponentiation.threshold 4096

def status (reason : Reason) : Int := if reason = .discard then 2 else 3

def arguments (reason : Reason) (environment : Option Address) (category message : Address) : List Value :=
  [.pointer environment, .integer (status reason), .pointer (some category), .pointer (some message)]

def afterHeap (reason : Reason) (query : StepCases.Query) (heap : Heap) (p : Address) : Heap :=
  if reason = .discard then beforeHeap reason query heap
  else LifecycleBodies.writeMode (beforeHeap reason query heap) p .terminated

theorem buffers_present (reason : Reason) (query : StepCases.Query)
    (selected : StepCases.Condition query reason.outcome) (writes : reason.writesOutputs = true) :
    ∃ buffers : StepEntry.Buffers, query.outputs = buffers.outputs := by
  apply (StepArguments.output_cases query.outputs).resolve_left
  cases reason <;> simp only [Reason.writesOutputs, Bool.false_eq_true] at writes
  · exact selected.2.2.1
  · exact selected.1.2.2.1
  · exact selected.1.2.2.1
  · exact selected.1.2.2.1

/-- The public prefix preserves every instance cell, irrespective of which
caller outputs it has initialized. Subsequent error mode writes are separate. -/
theorem before_frame (reason : Reason) (query : StepCases.Query) (heap : Heap) (p : Address)
    (reads : Reads reason query heap p) (selected : StepCases.Condition query reason.outcome)
    (address : Address) (inside : address.block = p.block) :
    beforeHeap reason query heap address = heap address := by
  by_cases writes : reason.writesOutputs = true
  · obtain ⟨buffers, outputs⟩ := buffers_present reason query selected writes
    simp only [beforeHeap, writes, ↓reduceIte, outputHeap_of_buffers query heap buffers outputs]
    exact (reads.outputs writes buffers outputs).instance_frame query.time address inside
  · simp only [beforeHeap, writes, Bool.false_eq_true, ↓reduceIte]

theorem before_load (reason : Reason) (query : StepCases.Query) (heap : Heap) (p : Address)
    (reads : Reads reason query heap p) (selected : StepCases.Condition query reason.outcome) (name : String) :
    load (beforeHeap reason query heap) (p.member name) = load heap (p.member name) := by
  simp only [load, before_frame reason query heap p reads selected (p.member name) rfl]

theorem suppressed_call {E : Type} (reason : Reason) (query : StepCases.Query) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (member : StepEntry.signature ∈ signatures) :
    letI : CInterface := RuntimeEnvironment.interface query.header objects literals
    ∀ (program : Events.Program E) (heap : Heap) (p message : Address) (flag : Bool)
      (range : -(2^31) ≤ query.observed ∧ query.observed < 2^31) (logger : Option Address) (logging : Bool),
      program.internal = LiteralPreparation.program model signatures →
      (reason.observesRounding = true → program.externals "fegetround" =
        some (CMathCalls.roundingExternal rfl query.observed range)) →
      (reason = .discard → StepGuards.Progress query.time (StepCases.nextTime query) →
        program.externals "floor" = some (CMathCalls.floorExternal rfl)) →
      (reason ≠ .discard → literals reason.message = some message) →
      query.handle = some p → Reads reason query heap p → StepCases.Condition query reason.outcome →
      (reason ≠ .discard → ∃ old, heap (p.member "mode") = some ⟨.int32, true, old⟩) →
      load heap (p.member "logger") = some (.pointer logger) →
      load heap (p.member "logging") = some (boolean logging) →
      (logger = none ∨ logging = false) → ∀ behavior,
      (Events.machine program).Behaves (start query heap flag) behavior ↔
      behavior = .terminates [] ⟨.integer (status reason), afterHeap reason query heap p⟩ := by
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  intro program heap p message flag range logger logging actual rounding floorBound literal
    handle reads selected writable loggerValue loggingValue suppressed behavior
  let context := ErrorContext.withRounding (ErrorContext.static objects literals) query.header
  have path := public_path reason query objects literals model signatures unique member program heap p flag range
    actual rounding floorBound handle reads selected
  have loggerAfter := (before_load reason query heap p reads selected "logger").trans loggerValue
  have loggingAfter := (before_load reason query heap p reads selected "logging").trans loggingValue
  by_cases discard : reason = .discard
  · simp only [Path, if_pos discard] at path
    obtain ⟨env, types, rest, reached, instanceValue, statusValue⟩ := path
    have result := StepDiscard.suppressed_behaviors context program env types rest
      (beforeHeap reason query heap) p logger logging instanceValue statusValue loggerAfter loggingAfter suppressed
    have call := (reached.silent_finite_behaviors (by intro history divergent; have impossible := (result (.diverges history)).mp divergent; simp at impossible) behavior).trans (result behavior)
    simpa only [status, afterHeap, discard, ↓reduceIte] using call
  · simp only [Path, if_neg discard] at path
    obtain ⟨old, mode⟩ := writable discard
    have helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      rw [actual]
      exact LiteralPreparation.helpers_bound model signatures Runtime.helpers[0] (by simp [Runtime.helpers])
    have call := StaticErrors.path_suppressed_behaviors context program (start query heap flag)
      (beforeHeap reason query heap) p message reason.message old logger logging path helper (literal discard)
      ((before_frame reason query heap p reads selected (p.member "mode") rfl).trans mode)
      loggerAfter loggingAfter suppressed behavior
    simpa only [status, afterHeap, discard, ↓reduceIte] using call

theorem logged_call {E : Type} (reason : Reason) (query : StepCases.Query) (objects : Objects)
    (literals : CLiteralAddresses) (model : Solve.FMI3Model source) (signatures : List Signature)
    (unique : ((LiteralPreparation.functions model signatures).map (fun fn => fn.signature.name)).Nodup)
    (member : StepEntry.signature ∈ signatures) :
    letI : CInterface := RuntimeEnvironment.interface query.header objects literals
    ∀ (program : Events.Program E) (heap : Heap) (p message category logger : Address) (flag : Bool)
      (range : -(2^31) ≤ query.observed ∧ query.observed < 2^31)
      (environment : Option Address) (name : String) (foreign : Events.External E),
      program.internal = LiteralPreparation.program model signatures →
      (reason.observesRounding = true → program.externals "fegetround" =
        some (CMathCalls.roundingExternal rfl query.observed range)) →
      (reason = .discard → StepGuards.Progress query.time (StepCases.nextTime query) →
        program.externals "floor" = some (CMathCalls.floorExternal rfl)) →
      literals reason.message = some message → literals "logStatus" = some category →
      program.addresses logger = some name → program.externals name = some foreign →
      foreign.signature = Logging.signature name →
      query.handle = some p → Reads reason query heap p → StepCases.Condition query reason.outcome →
      (reason ≠ .discard → ∃ old, heap (p.member "mode") = some ⟨.int32, true, old⟩) →
      load heap (p.member "logger") = some (.pointer (some logger)) →
      load heap (p.member "logging") = some (.integer 1) →
      load heap (p.member "environment") = some (.pointer environment) → ∀ behavior,
      (Events.machine program).Behaves (start query heap flag) behavior ↔
      (∃ events value after, foreign.execute (arguments reason environment category message)
        (afterHeap reason query heap p) events value after ∧
        behavior = .terminates events ⟨.integer (status reason), after⟩) ∨
      ((∀ events value after, ¬ foreign.execute (arguments reason environment category message)
        (afterHeap reason query heap p) events value after) ∧ behavior = .wrong []) := by
  letI : CInterface := RuntimeEnvironment.interface query.header objects literals
  intro program heap p message category logger flag range environment name foreign actual rounding floorBound
    literal categoryBound address external prototype handle reads selected writable loggerValue loggingValue environmentValue behavior
  let context := ErrorContext.withRounding (ErrorContext.static objects literals) query.header
  have path := public_path reason query objects literals model signatures unique member program heap p flag range
    actual rounding floorBound handle reads selected
  have loggerAfter := (before_load reason query heap p reads selected "logger").trans loggerValue
  have loggingAfter := (before_load reason query heap p reads selected "logging").trans loggingValue
  have environmentAfter := (before_load reason query heap p reads selected "environment").trans environmentValue
  by_cases discard : reason = .discard
  · simp only [Path, if_pos discard] at path
    obtain ⟨env, types, rest, reached, instanceValue, statusValue⟩ := path
    have result := StepDiscard.all_behaviors context program env types rest (beforeHeap reason query heap)
      p message category logger environment name foreign instanceValue statusValue loggerAfter loggingAfter environmentAfter
      address categoryBound (by simpa only [discard, Reason.message] using literal) external prototype
    have call := (reached.silent_finite_behaviors (by intro history divergent; have impossible := (result (.diverges history)).mp divergent; simp at impossible) behavior).trans (result behavior)
    simpa only [status, afterHeap, discard, ↓reduceIte, arguments, StepDiscard.arguments] using call
  · simp only [Path, if_neg discard] at path
    obtain ⟨old, mode⟩ := writable discard
    have helper : program.internal.definitions "fail" = some (.tree Runtime.helpers[0]) := by
      rw [actual]
      exact LiteralPreparation.helpers_bound model signatures Runtime.helpers[0] (by simp [Runtime.helpers])
    have call := StaticErrors.path_all_behaviors context program (start query heap flag)
      (beforeHeap reason query heap) p message category logger reason.message name environment old foreign
      path helper literal address external prototype categoryBound
      ((before_frame reason query heap p reads selected (p.member "mode") rfl).trans mode)
      loggerAfter loggingAfter environmentAfter behavior
    simpa only [status, afterHeap, discard, ↓reduceIte, arguments, Logging.arguments] using call

end Rumoca.FMI3.StepRejections
end
