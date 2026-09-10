import RumocaFMI3.CInterface
import ProofAudit.Audit
import RumocaFMI3.HistoryBodies

/-! Concrete execution discriminators for the generated time-history blocks
and public event/completion bodies. Universal contracts are in HistoryProofs
and HistoryBodies; these controls exercise pointer writes and mode changes. -/
namespace Rumoca.FMI3.HistoryChecks
private local instance : StaticLiterals := ⟨fun _ => none⟩
private local instance targetInterface : CInterface := cInterface
open CTree CMemory CBody HistoryProofs
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def model : Address := ⟨1, [], 0⟩
def output : Address := ⟨2, [], 0⟩
def source : AST.Model := ⟨"M", "x", "x", "M"⟩
def prepared : Solve.FMI3Model source :=
  (Solve.lower (DAE.lower (Flat.lower source ⟨rfl, rfl⟩))).prepareFMI3

def parameters : Locals := fun name =>
  if name = "instance" then some (.pointer (some model))
  else if name = "enterEventMode" || name = "terminateSimulation" then some (.pointer (some output))
  else if name = "startTime" then some (.finite Binary64.negativeZero)
  else none
def locals : Locals := CBody.bind parameters "m" (.pointer (some model))

def heap (c : Time.Clock) : Heap := fun p =>
  if p = model.member "time" then some (cell c.time)
  else if p = model.member "timeMin" then some (cell c.minimum)
  else if p = model.member "eventTime" then some (cell c.eventTime)
  else if p = model.member "lastCompleted" then some (cell c.lastCompleted)
  else if p = model.member "kind" then some ⟨.int32, true, some (.integer 0)⟩
  else if p = model.member "mode" then some ⟨.int32, true, some (.integer 3)⟩
  else if p = output then some ⟨.boolean, true, some (.integer 1)⟩
  else if p = StateProofs.stateAddress model then some (cell Binary64.negativeZero)
  else none

def fields (h : Heap) : List (Option Value) :=
  [load h (model.member "time"), load h (model.member "timeMin"),
   load h (model.member "eventTime"), load h (model.member "lastCompleted")]
def encodings (c : Time.Clock) : List (Option Value) :=
  [some (.finite c.time), some (.finite c.minimum),
   some (.finite c.eventTime), some (.finite c.lastCompleted)]

def observe (count : Nat) (code : List Stmt) (env : Locals) (c : Time.Clock) :
    Option (Value × List (Option Value) × Option Value × Option Value × Option Value) := do
  let .returned r ← run count (.running code env (heap c)) | none
  return (r.value, fields r.heap, load r.heap (model.member "mode"),
    load r.heap output, load r.heap (StateProofs.stateAddress model))

def expected (c : Time.Clock) (mode : Int := 3) (out : Int := 1) :=
  some (Value.integer 0, encodings c, some (Value.integer mode),
    some (Value.integer out), some (Value.finite Binary64.negativeZero))

def oldClock : Time.Clock :=
  ⟨Binary64.one, Binary64.threeHalves, Binary64.positiveZero, Binary64.half⟩

theorem initial_preserves_encoding_and_frame :
    observe 5 (Runtime.initialTime ++ [Runtime.ok]) locals oldClock =
      expected (Time.Clock.initial Binary64.negativeZero) := by decide +kernel

theorem completed_drops_obsolete_bound :
    observe 5 (Runtime.completedTime ++ [Runtime.ok]) locals oldClock =
      expected ⟨Binary64.one, Binary64.half, Binary64.positiveZero, Binary64.one⟩ := by decide +kernel

theorem event_retains_second_last_bound :
    observe 3 (Runtime.eventTime ++ [Runtime.ok]) locals oldClock =
      expected ⟨Binary64.one, Binary64.threeHalves, Binary64.one, Binary64.half⟩ := by decide +kernel

def earlier : Time.Clock :=
  ⟨Binary64.threeHalves, Binary64.half, Binary64.positiveZero, Binary64.one⟩

theorem event_raises_bound :
    observe 4 (Runtime.eventTime ++ [Runtime.ok]) locals earlier =
      expected ⟨Binary64.threeHalves, Binary64.threeHalves, Binary64.threeHalves, Binary64.one⟩ := by
  decide +kernel

theorem equal_zero_bound_retains_bits :
    observe 3 (Runtime.eventTime ++ [Runtime.ok]) locals (Time.Clock.initial Binary64.negativeZero) =
      expected (Time.Clock.initial Binary64.negativeZero) := by decide +kernel

def staleCompleted : List Stmt :=
  [Runtime.raiseField "timeMin" (Runtime.field "lastCompleted"),
   Runtime.put "lastCompleted" (Runtime.field "time")]

theorem running_max_mutation_detected :
    observe 3 (staleCompleted ++ [Runtime.ok]) locals oldClock ≠
      expected ⟨Binary64.one, Binary64.half, Binary64.positiveZero, Binary64.one⟩ := by decide +kernel

theorem completed_alias_outputs :
    observe 11 (Runtime.body prepared ⟨"fmi3Status", "fmi3CompletedIntegratorStep", []⟩)
      parameters oldClock =
      expected ⟨Binary64.one, Binary64.half, Binary64.positiveZero, Binary64.one⟩ 3 0 := by decide +kernel

theorem event_public_body :
    observe 8 (Runtime.body prepared ⟨"fmi3Status", "fmi3EnterEventMode", []⟩)
      parameters earlier =
      expected ⟨Binary64.threeHalves, Binary64.threeHalves, Binary64.threeHalves, Binary64.one⟩ 2 := by
  decide +kernel

theorem initial_readonly_field_stuck :
    run 2 (.running Runtime.initialTime locals
      (replace (heap oldClock) (model.member "timeMin")
        ⟨.float64, false, some (.finite Binary64.positiveZero)⟩)) = none := by decide +kernel

def two : Binary64.Value := ⟨1024 * Binary64.fractionCount, by decide +kernel⟩
def historyActions : List Time.Action :=
  [.setTime Binary64.one, .completed, .setTime two, .completed,
   .setTime Binary64.one, .completed, .setTime two, .completed]

theorem positional_cache_regression :
    (historyActions.foldl Time.Clock.apply (Time.Clock.initial Binary64.positiveZero)).minimum =
      Binary64.one := by decide +kernel

def completed : List Stmt := Runtime.body prepared ⟨"fmi3Status", "fmi3CompletedIntegratorStep", []⟩
def eventBody : List Stmt := Runtime.body prepared ⟨"fmi3Status", "fmi3EnterEventMode", []⟩

def observeHeap (fuel : Nat) (code : List Stmt) (env : Locals) (h : Heap) : Option (Value × List (Option Value)) := do
  let .returned r ← run fuel (.running code env h) | none
  return (r.value, fields r.heap)

theorem uninitialized_output_allowed :
    observeHeap 11 completed (HistoryBodies.completedParameters model output output false)
      (replace (heap oldClock) output ⟨.boolean, true, none⟩) =
      some (.integer 0, encodings ⟨Binary64.one, Binary64.half, Binary64.positiveZero, Binary64.one⟩) := by
  decide +kernel

theorem missing_output_storage_stuck :
    run 5 (.running completed (HistoryBodies.completedParameters model output output false)
      (fun p => if p = output then none else heap oldClock p)) = none := by decide +kernel

theorem readonly_output_stuck :
    run 5 (.running completed (HistoryBodies.completedParameters model output output true)
      (replace (heap oldClock) output ⟨.boolean, false, some (.integer 1)⟩)) = none := by decide +kernel

def omitMode : Stmt → List Stmt
  | .assign (.field (.id "m") "mode" true) _ => []
  | s => [s]

theorem missing_event_mode_detected :
    observe 7 (eventBody.flatMap omitMode) (HistoryBodies.parameters model) earlier =
      expected ⟨Binary64.threeHalves, Binary64.threeHalves, Binary64.threeHalves, Binary64.one⟩ 3 := by
  decide +kernel

def changeOutput : Stmt → Stmt
  | .assign (.deref (.id "enterEventMode")) _ => Runtime.out "enterEventMode" (Runtime.n 1)
  | s => s

def observeOutputs (body : List Stmt) : Option (Value × Option Value × Option Value) := do
  let h := replace (heap oldClock) (output.index 1) ⟨.boolean, true, some (.integer 1)⟩
  let .returned r ← run 11 (.running body
    (HistoryBodies.completedParameters model output (output.index 1) false) h) | none
  return (r.value, load r.heap output, load r.heap (output.index 1))

theorem distinct_outputs_correct :
    observeOutputs completed = some (.integer 0, some (boolean false), some (boolean false)) := by
  decide +kernel

theorem changed_output_detected :
    observeOutputs (completed.map changeOutput) =
      some (.integer 0, some (boolean true), some (boolean false)) := by
  decide +kernel

#audit axioms initial_preserves_encoding_and_frame
#audit axioms completed_drops_obsolete_bound
#audit axioms event_retains_second_last_bound
#audit axioms event_raises_bound
#audit axioms equal_zero_bound_retains_bits
#audit axioms running_max_mutation_detected
#audit axioms completed_alias_outputs
#audit axioms event_public_body
#audit axioms initial_readonly_field_stuck
#audit axioms positional_cache_regression
#audit axioms uninitialized_output_allowed
#audit axioms missing_output_storage_stuck
#audit axioms readonly_output_stuck
#audit axioms missing_event_mode_detected
#audit axioms distinct_outputs_correct
#audit axioms changed_output_detected
end Rumoca.FMI3.HistoryChecks
