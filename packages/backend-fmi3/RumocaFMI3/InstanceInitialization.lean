import RumocaFMI3.InstanceInitializationCode
import RumocaFMI3.Reset
import RumocaC.Subobjects

/-! The entire initialization block starts from arbitrary old field values,
including uninitialized payloads. It does not depend on zero-filled storage.
Static declarations, slot ownership and production-factory linkage are separate. -/
namespace Rumoca.FMI3.InstanceInitialization
open CTree CMemory CBody

structure Storage (heap : Heap) (p : Address) : Prop extends Reset.Storage heap p where
  kind : Reset.Writable heap (p.member "kind") .int32
  environment : Reset.Writable heap (p.member "environment") .pointer
  logger : Reset.Writable heap (p.member "logger") .pointer
  logging : Reset.Writable heap (p.member "logging") .boolean

def finalHeap (heap : Heap) (p : Address) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) : Heap :=
  replace (replace (replace (replace (Reset.finalHeap heap p)
    (p.member "kind") ⟨.int32, true, some (.integer kind.code)⟩)
    (p.member "environment") ⟨.pointer, true, some (.pointer environment)⟩)
    (p.member "logger") ⟨.pointer, true, some (.pointer logger)⟩)
    (p.member "logging") ⟨.boolean, true, some (boolean logging)⟩

section
variable [interface : CInterface]

theorem run_initialization (model : Solve.Model source) (kind : Kind)
    (env : Locals) (heap : Heap) (p : Address) (environment logger : Option Address)
    (logging : Bool) (rest : List Stmt) (storage : Storage heap p)
    (double : interface.types "double" = some .float64)
    (instanceBound : resolve env "m" = some (.pointer (some p)))
    (environmentBound : resolve env "instanceEnvironment" = some (.pointer environment))
    (loggerBound : resolve env "logMessage" = some (.pointer logger))
    (loggingBound : resolve env "loggingOn" = some (boolean logging)) :
    run 12 (.running (code model kind ++ rest) env heap) =
      some (.running rest env (finalHeap heap p kind environment logger logging)) := by
  rcases storage with ⟨⟨⟨oldState, hx⟩, ⟨oldTime, ht⟩, ⟨oldMinimum, hn⟩,
    ⟨oldEvent, he⟩, ⟨oldCompleted, hc⟩, ⟨oldStop, hs⟩, ⟨oldStopDefined, hd⟩, ⟨oldMode, hm⟩⟩,
    ⟨oldKind, hk⟩, ⟨oldEnvironment, hv⟩, ⟨oldLogger, hl⟩, ⟨oldLogging, hg⟩⟩
  simp only [StateProofs.stateAddress] at hx
  have distinct (name : String) : p.member name ≠ (p.member "model").member "x" :=
    Ne.symm (HistoryBodies.state_ne_field p name)
  cases kind <;> cases logging <;>
    simp [code, put, field, state, CInitialization.Emission.statement, CInitialization.value_zero,
      run, next, eval, lvalue, instanceBound, environmentBound, loggerBound, loggingBound,
      Value.address, Value.finite, CBody.cast, double, convert, boolean, Value.truth, store,
      finalHeap, Reset.finalHeap, CInitialization.written, HistoryProofs.initialHeap,
      HistoryProofs.write, HistoryProofs.cell, LifecycleBodies.writeMode, Kind.code, Mode.code,
      StateProofs.stateAddress, replace, hx, ht, hn, he, hc, hs, hd, hm, hk, hv, hl, hg, distinct]

end

theorem frame (heap : Heap) (p q : Address) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (outside : ¬ p.InRecord q) :
    finalHeap heap p kind environment logger logging q = heap q := by
  have different (name : String) : q ≠ p.member name := by
    intro same
    subst q
    exact outside (p.member_in_record name)
  have stateDifferent : q ≠ StateProofs.stateAddress p := by
    intro same
    subst q
    exact outside ((p.member_in_record "model").member "x")
  simp only [finalHeap, replace_other _ _ _ _ (different "logging"),
    replace_other _ _ _ _ (different "logger"), replace_other _ _ _ _ (different "environment"),
    replace_other _ _ _ _ (different "kind")]
  exact Reset.frame heap p q stateDifferent (different "time") (different "timeMin")
    (different "eventTime") (different "lastCompleted") (different "stop")
    (different "stopDefined") (different "mode")

/-- Preserve every nested cell of any other object in the same instance array. -/
theorem other_instance (heap : Heap) (base : Address) (i j : Nat) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) (query : Address)
    (different : i ≠ j) (inside : (base.index j).InRecord query) :
    finalHeap heap (base.index i) kind environment logger logging query = heap query := by
  apply frame
  intro own
  exact Address.records_separate base i j different own inside rfl

theorem storage_ready (heap : Heap) (p : Address) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) :
    Storage (finalHeap heap p kind environment logger logging) p := by
  have distinct (name : String) : (p.member "model").member "x" ≠ p.member name :=
    HistoryBodies.state_ne_field p name
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;>
    simp [Reset.Writable, finalHeap, Reset.finalHeap, CInitialization.written,
      HistoryProofs.initialHeap, HistoryProofs.write, HistoryProofs.cell,
      LifecycleBodies.writeMode, StateProofs.stateAddress, replace, distinct]

/-- A later initialization replaces all earlier initialization values. -/
theorem reuse (heap : Heap) (p : Address) (oldKind kind : Kind)
    (oldEnvironment oldLogger environment logger : Option Address) (oldLogging logging : Bool) :
    finalHeap (finalHeap heap p oldKind oldEnvironment oldLogger oldLogging) p kind environment logger logging =
      finalHeap heap p kind environment logger logging := by
  funext query
  have distinct (name : String) : (p.member "model").member "x" ≠ p.member name :=
    HistoryBodies.state_ne_field p name
  by_cases written : query ∈ [StateProofs.stateAddress p, p.member "time", p.member "timeMin",
      p.member "eventTime", p.member "lastCompleted", p.member "stop", p.member "stopDefined",
      p.member "mode", p.member "kind", p.member "environment", p.member "logger", p.member "logging"]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at written
    rcases written with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [finalHeap, Reset.finalHeap, CInitialization.written, HistoryProofs.initialHeap,
        HistoryProofs.write, LifecycleBodies.writeMode, StateProofs.stateAddress, replace, distinct]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at written
    rcases written with ⟨hx, ht, hn, he, hc, hs, hd, hm, hk, hv, hl, hg⟩
    simp [finalHeap, Reset.finalHeap, CInitialization.written, HistoryProofs.initialHeap,
      HistoryProofs.write, LifecycleBodies.writeMode, replace, hx, ht, hn, he, hc, hs, hd, hm, hk, hv, hl, hg]

/-- The initialized object establishes the storage and value premises used by
the public state, time, lifecycle and logging contracts. -/
structure Initialized (heap : Heap) (p : Address) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) : Prop where
  storage : Storage heap p
  model : StateProofs.Represents heap p ⟨Binary64.positiveZero⟩
  clock : HistoryProofs.Stored heap p (Time.Clock.initial Binary64.positiveZero)
  modeValue : load heap (p.member "mode") = some (.integer Mode.instantiated.code)
  kindValue : load heap (p.member "kind") = some (.integer kind.code)
  environmentValue : load heap (p.member "environment") = some (.pointer environment)
  loggerValue : load heap (p.member "logger") = some (.pointer logger)
  loggingValue : load heap (p.member "logging") = some (boolean logging)
  stopValue : load heap (p.member "stop") = some (.finite Binary64.positiveZero)
  stopDefinedValue : load heap (p.member "stopDefined") = some (boolean false)

theorem initialized (heap : Heap) (p : Address) (kind : Kind)
    (environment logger : Option Address) (logging : Bool) :
    Initialized (finalHeap heap p kind environment logger logging) p kind environment logger logging := by
  have distinct (name : String) : (p.member "model").member "x" ≠ p.member name :=
    HistoryBodies.state_ne_field p name
  refine ⟨storage_ready heap p kind environment logger logging, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [StateProofs.Represents, finalHeap, load, replace, StateProofs.stateAddress, distinct]
      using Reset.state heap p
  · obtain ⟨ht, hn, he, hc⟩ := Reset.history heap p
    constructor <;> simp_all [finalHeap, replace]
  · simpa [finalHeap, load, replace, reset_recovers] using Reset.lifecycle heap p kind .instantiated
  · cases kind <;> simp [finalHeap, load, replace, Kind.code, convert]
  · simp [finalHeap, load, replace, convert]
  · simp [finalHeap, load, replace, convert]
  · cases logging <;> simp [finalHeap, load, replace, convert, boolean, Value.truth]
  · simpa [finalHeap, load, replace] using (Reset.stop heap p).1
  · simpa [finalHeap, load, replace] using (Reset.stop heap p).2

end Rumoca.FMI3.InstanceInitialization
