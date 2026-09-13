import RumocaFMI3.MEHistory
import RumocaFMI3.InitializationComposition

noncomputable section
namespace Rumoca.FMI3.MEHistory
open CTree CMemory

/-- Both initialization writes establish the ME control invariant, including
the not-yet-completed discrete iteration. Caller buffers survive initialization. -/
theorem initialized_stored (heap : Heap) (p : Address) (args : Initialization.Arguments)
    (state : ModelExchange.State) (addresses : String → Address)
    (admissible : args.Admissible)
    (kind : load heap (p.member "kind") = some (.integer 0))
    (model : StateProofs.Represents heap p state)
    (buffers : Buffers heap addresses) (outside : Buffers.Outside p addresses) :
    Stored (InitializationCalls.exitedHeap heap p args .me) p (Time.Clock.initial args.start)
      (ReferenceState.initial args.start args.stopTime) state addresses := by
  let entered := InitializationEntry.finalHeap heap p args
  let exited := InitializationCalls.exitedHeap heap p args .me
  have preserved (query : Address) (mode : query ≠ p.member "mode") :
      exited query = entered query := InitializationBodies.exit_frame entered p query .me mode
  constructor
  · change load exited (p.member "kind") = some (.integer 0)
    simpa only [load, preserved (p.member "kind") (by simp)] using
      (InitializationCalls.entered_kind heap p args).trans kind
  · simp [ReferenceState.initial, InitializationCalls.exitedHeap,
      InitializationBodies.exitHeap, me_initialization, Mode.code]
  · exact InitializationBodies.exit_history (InitializationCalls.stored heap p args) .me
  · exact Time.initial_represents args.start args.stopTime
  · exact InitializationBodies.exit_model (InitializationEntry.model model args) .me
  · rw [show load exited (p.member "stopDefined") = load entered (p.member "stopDefined") by
      simp only [load, preserved (p.member "stopDefined") (by simp)]]
    simpa only [ReferenceState.initial, Time.History.initial, Time.Window.initial,
      Initialization.stopTime_defined args admissible] using (InitializationEntry.stop heap p args).2
  · intro bound selected
    have bits := Initialization.stopTime_bits args admissible bound selected
    rw [show load exited (p.member "stop") = load entered (p.member "stop") by
      simp only [load, preserved (p.member "stop") (by simp)]]
    simpa only [CMemory.Value.finite, bits] using (InitializationEntry.stop heap p args).1
  · apply buffers.transport
    intro layout member
    exact InitializationCalls.exited_frame heap p (addresses layout.1) args .me
      (outside.field layout member "time") (outside.field layout member "timeMin")
      (outside.field layout member "eventTime") (outside.field layout member "lastCompleted")
      (outside.field layout member "stop") (outside.field layout member "stopDefined")
      (outside.field layout member "mode")
  · exact outside

/-- Initialization and every subsequent admitted ME control call use one
program, with the first iteration obligation established by initialization.
No initialized heap or successful target execution is supplied by the caller. -/
theorem initialize_trace [interface : CInterface] (program : CCalls.Events.Program E)
    (initialization : InitializationCalls.QuietExecutionContract program) (quiet : Quiet program)
    (heap : Heap) (p : Address) (args : Initialization.Arguments)
    (state : ModelExchange.State) (addresses : String → Address)
    (admissible : args.Admissible) (storage : InitializationCalls.EntryStorage heap p)
    (kind : load heap (p.member "kind") = some (.integer 0))
    (model : StateProofs.Represents heap p state)
    (buffers : Buffers heap addresses) (outside : Buffers.Outside p addresses)
    (admitted : ReferenceTrace (ReferenceState.initial args.start args.stopTime) actions final) :
    let entered := InitializationEntry.finalHeap heap p args
    let exited := InitializationCalls.exitedHeap heap p args .me
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling InitializationCalls.signature.name
        (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, entered⟩) ∧
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) entered .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, exited⟩) ∧
    ∃ after finalClock, Calls program p addresses exited actions after ∧
      Stored after p finalClock final state addresses ∧
      (∀ query, Outside p addresses query → after query = exited query) := by
  refine ⟨initialization.enter heap p args .me admissible storage kind,
    initialization.exit (InitializationEntry.finalHeap heap p args) p .me
      ((InitializationCalls.entered_kind heap p args).trans kind)
      (InitializationCalls.entered_mode heap p args), ?_⟩
  exact trace_frame program quiet (initialized_stored heap p args state addresses admissible kind model buffers outside) admitted

end Rumoca.FMI3.MEHistory
