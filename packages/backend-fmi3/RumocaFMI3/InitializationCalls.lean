import RumocaFMI3.InitializationArguments

noncomputable section
namespace Rumoca.FMI3.InitializationCalls
open Initialization
open CTree CMemory CBody

/-- Entry overwrites these fields and does not inspect their old payloads. -/
structure ClockStorage (heap : Heap) (p : Address) : Prop where
  time : ∃ old, heap (p.member "time") = some ⟨.float64, true, old⟩
  minimum : ∃ old, heap (p.member "timeMin") = some ⟨.float64, true, old⟩
  eventTime : ∃ old, heap (p.member "eventTime") = some ⟨.float64, true, old⟩
  lastCompleted : ∃ old, heap (p.member "lastCompleted") = some ⟨.float64, true, old⟩

def message : String := "Invalid initialization time interval"
def tail : List Stmt := Runtime.initialTime ++ [
  Runtime.put "stop" (Runtime.v "stopTime"), Runtime.put "stopDefined" (Runtime.v "stopTimeDefined"),
  Runtime.setMode .initialization, Runtime.ok]
def code : List Stmt := Runtime.require .enterInitialization ++ [Runtime.reject guard message] ++ tail
def function : Function := { signature := signature, body := code }

/-- This is the function actually emitted for every prepared unit model. -/
theorem function_eq (model : Solve.FMI3Model source) :
    Runtime.function model signature = function := by
  simp [Runtime.function, Runtime.body, signature, function, code, tail, guard, message,
    List.append_assoc]

theorem closed : code.all CBodyEmbedding.closedBlocks = true := by
  simp [code, tail, Runtime.require, Runtime.instancePrefix, Runtime.reject,
    Runtime.branch, Runtime.fail, Runtime.ret, Runtime.initialTime, Runtime.put,
    Runtime.setMode, Runtime.ok, CBodyEmbedding.closedBlocks, CLoops.noDeclarations]

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem guard_run (heap : Heap) (p : Address) (args : Raw) (kind : Kind)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer 0)) :
    run 4 (.running code (parameters (some p) args) heap) =
      some (.running ((if rejects args then [Runtime.fail message] else []) ++ tail) (locals p args) heap) := by
  have entered := LifecycleGuard.accept (parameters (some p) args) heap p .enterInitialization kind
    .instantiated (Runtime.reject guard message :: tail)
    (by simp [parameters, CBody.bind]) (by simp [parameters, CBody.bind]) hk hm rfl
  rw [code, List.append_assoc, List.singleton_append, show 4 = 3 + 1 from rfl, run_add, entered]
  have checked := guard_eval heap p args
  simp only [locals] at checked
  cases h : rejects args <;>
    simp [run, CBody.next, CBody.nextWith, CBody.legacyExpressions, Runtime.reject, Runtime.branch, checked, locals, h, boolean, Value.truth]

/-- All seven instance fields are written from the original heap, with no
finite/readable old-clock premise. The initial model state is not overwritten. -/
theorem tail_run (heap : Heap) (p : Address) (args : Initialization.Arguments)
    (storage : ClockStorage heap p) (stopOld flagOld : Option Value)
    (modeStored : heap (p.member "mode") = some ⟨.int32, true, some (.integer 0)⟩)
    (stopStored : heap (p.member "stop") = some ⟨.float64, true, stopOld⟩)
    (flagStored : heap (p.member "stopDefined") = some ⟨.boolean, true, flagOld⟩) :
    run 8 (.running tail (locals p (Raw.ofFinite args)) heap) =
      some (.returned ⟨.integer 0, InitializationEntry.finalHeap heap p args⟩) := by
  obtain ⟨⟨time, ht⟩, ⟨minimum, hn⟩, ⟨eventTime, he⟩, ⟨lastCompleted, hl⟩⟩ := storage
  cases flag : args.stopDefined <;>
    simp [tail, Runtime.initialTime, Runtime.put, Runtime.field, Runtime.v, Runtime.setMode,
      Runtime.mode, Runtime.n, Runtime.ok, Runtime.ret, Mode.code,
      run, CBody.next, CBody.nextWith, CBody.legacyExpressions, CBody.eval, CBody.evalWith, CBody.lvalue, CBody.lvalueWith, locals, parameters, Raw.ofFinite, CBody.bind, resolve, constants,
      Value.address, Value.finite, boolean, Value.truth, store, convert,
      InitializationEntry.finalHeap, HistoryProofs.initialHeap, HistoryProofs.write, HistoryProofs.cell,
      replace, ht, hn, he, hl, modeStored, stopStored, flagStored, flag]

theorem body_run (heap : Heap) (p : Address) (args : Initialization.Arguments) (kind : Kind)
    (admissible : Arguments.Admissible args) (storage : ClockStorage heap p) (stopOld flagOld : Option Value)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (modeStored : heap (p.member "mode") = some ⟨.int32, true, some (.integer 0)⟩)
    (stopStored : heap (p.member "stop") = some ⟨.float64, true, stopOld⟩)
    (flagStored : heap (p.member "stopDefined") = some ⟨.boolean, true, flagOld⟩) :
    run 12 (.running code (parameters (some p) (Raw.ofFinite args)) heap) =
      some (.returned ⟨.integer 0, InitializationEntry.finalHeap heap p args⟩) := by
  have modeLoaded : load heap (p.member "mode") = some (.integer 0) := by simp [load, modeStored, convert]
  have entered := guard_run heap p (Raw.ofFinite args) kind hk modeLoaded
  rw [(finite_admissible args).mpr admissible] at entered
  simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append] at entered
  rw [show 12 = 4 + 8 from rfl, run_add, entered]
  exact tail_run heap p args storage stopOld flagOld modeStored stopStored flagStored

theorem call_behaviors (program : CCalls.Events.Program E) (heap : Heap) (p : Address)
    (args : Initialization.Arguments) (kind : Kind) (admissible : Arguments.Admissible args)
    (storage : ClockStorage heap p) (stopOld flagOld : Option Value)
    (defined : program.internal.definitions signature.name = some (.tree function))
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (modeStored : heap (p.member "mode") = some ⟨.int32, true, some (.integer 0)⟩)
    (stopStored : heap (p.member "stop") = some ⟨.float64, true, stopOld⟩)
    (flagStored : heap (p.member "stopDefined") = some ⟨.boolean, true, flagOld⟩) (behavior) :
    (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (Raw.ofFinite args)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, InitializationEntry.finalHeap heap p args⟩ := by
  exact CCalls.Events.body_call_behaviors program function _ _ heap _ (.integer 0) 12
    defined (parameters_bound _ _) closed
    (body_run heap p args kind admissible storage stopOld flagOld hk modeStored stopStored flagStored) rfl behavior

end

/-- The writes establish a complete clock regardless of the previous payloads. -/
theorem stored (heap : Heap) (p : Address) (args : Initialization.Arguments) :
    HistoryProofs.Stored (InitializationEntry.finalHeap heap p args) p (Time.Clock.initial args.start) := by
  constructor <;> simp [InitializationEntry.finalHeap, HistoryProofs.initialHeap,
    HistoryProofs.write, HistoryProofs.cell, Time.Clock.initial, replace]

end Rumoca.FMI3.InitializationCalls
