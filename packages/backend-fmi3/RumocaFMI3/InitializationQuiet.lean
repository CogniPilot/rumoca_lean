import RumocaFMI3.InitializationComposition
import RumocaFMI3.InitializationExit
import RumocaFMI3.InitializationFailures

noncomputable section
namespace Rumoca.FMI3.InitializationCalls
open Initialization
open CTree CMemory

/-- Storage that successful entry writes. Only the mode payload is read. -/
structure EntryStorage (heap : Heap) (p : Address) : Prop where
  clock : ClockStorage heap p
  mode : heap (p.member "mode") = some ⟨.int32, true, some (.integer 0)⟩
  stop : ∃ old, heap (p.member "stop") = some ⟨.float64, true, old⟩
  stopDefined : ∃ old, heap (p.member "stopDefined") = some ⟨.boolean, true, old⟩

/-- Successful and null calls do not inspect the literal pool. Quantifying
over heaps permits composition across earlier public calls in the same program. -/
structure QuietExecutionContract [interface : CInterface]
    (program : CCalls.Events.Program E) : Prop where
  enter : ∀ (heap : Heap) (p : Address) (args : Initialization.Arguments) (kind : Kind),
    Arguments.Admissible args → EntryStorage heap p →
    load heap (p.member "kind") = some (.integer kind.code) →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (Raw.ofFinite args)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, InitializationEntry.finalHeap heap p args⟩
  exit : ∀ (heap : Heap) (p : Address) (kind : Kind),
    load heap (p.member "kind") = some (.integer kind.code) →
    heap (p.member "mode") = some ⟨.int32, true, some (.integer 1)⟩ →
    ∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling InitializationExit.signature.name (InitializationExit.arguments (some p)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, InitializationBodies.exitHeap heap p kind⟩
  nullEnter : ∀ heap args behavior, (CCalls.Events.machine program).Behaves
    (.calling signature.name (arguments none args) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩
  nullExit : ∀ heap behavior, (CCalls.Events.machine program).Behaves
    (.calling InitializationExit.signature.name (InitializationExit.arguments none) heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 3, heap⟩

section
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses

theorem quiet_execution_correct (model : Solve.FMI3Model source) (program : CCalls.Events.Program E)
    (enterDefined : program.internal.definitions signature.name = some (.tree function))
    (exitDefined : program.internal.definitions InitializationExit.signature.name =
      some (.tree (Runtime.function model InitializationExit.signature))) : QuietExecutionContract program := by
  constructor
  · intro heap p args kind admissible storage hk behavior
    obtain ⟨clock, mode, ⟨stopOld, hs⟩, ⟨flagOld, hf⟩⟩ := storage
    exact call_behaviors program heap p args kind admissible clock stopOld flagOld enterDefined hk mode hs hf behavior
  · intro heap p kind hk hm behavior
    exact InitializationExit.call_behaviors model program heap p kind exitDefined hk hm behavior
  · intro heap args behavior
    exact null_behaviors program heap args enterDefined behavior
  · intro heap behavior
    exact InitializationExit.null_behaviors model program heap exitDefined behavior

/-- The mandatory public-call contract is sufficient to initialize either
interface. All final representations are derived from its precise heap result. -/
theorem QuietExecutionContract.initialize (contract : QuietExecutionContract program)
    (heap : Heap) (p : Address) (args : Initialization.Arguments) (kind : Kind) (state : ModelExchange.State)
    (admissible : Arguments.Admissible args) (storage : EntryStorage heap p)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (represented : StateProofs.Represents heap p state) :
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling signature.name (arguments (some p) (Raw.ofFinite args)) heap .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, InitializationEntry.finalHeap heap p args⟩) ∧
    (∀ behavior, (CCalls.Events.machine program).Behaves
      (.calling InitializationExit.signature.name (InitializationExit.arguments (some p))
        (InitializationEntry.finalHeap heap p args) .done) behavior ↔
      behavior = .terminates [] ⟨.integer 0, exitedHeap heap p args kind⟩) ∧
    StateProofs.Represents (exitedHeap heap p args kind) p state ∧
    HistoryProofs.Stored (exitedHeap heap p args kind) p (Time.Clock.initial args.start) ∧
    Time.Represents (Time.History.initial args.start args.stopTime) (Time.Clock.initial args.start) ∧
    load (exitedHeap heap p args kind) (p.member "mode") =
      some (.integer (nextMode .exitInitialization kind .initialization).code) ∧
    (∀ time, CBody.eval (TimeProofs.locals p (Binary64.toBits time).val)
      (exitedHeap heap p args kind) Runtime.invalidTime = some (CBody.boolean false) ↔
      (Time.Window.initial args.start args.stopTime).Admissible time) := by
  exact ⟨contract.enter heap p args kind admissible storage hk,
    contract.exit _ p kind ((entered_kind heap p args).trans hk) (entered_mode heap p args),
    InitializationBodies.exit_model (InitializationEntry.model represented args) kind,
    InitializationBodies.exit_history (stored heap p args) kind, Time.initial_represents _ _,
    InitializationBodies.exit_mode _ p kind, exited_time_guard heap p args kind admissible⟩

end
end Rumoca.FMI3.InitializationCalls
