import Rumoca.FMI3StaticReset
import RumocaFMI3.ResetEnvironment
import RumocaFMI3.InitializationEnvironment

noncomputable section
namespace Rumoca.FMI3
open CTree CMemory CBody StaticFactory

/-- Complete reset and initialization calls tied to the same source artifact.
The new trajectory uses the stored Solve default at the requested new start. -/
structure Restarted [CInterface] (a : Artifact input) (program : CCalls.Events.Program E)
    (heap : Heap) (p : Address) (kind : Kind) (args : Initialization.Arguments) : Prop where
  reset : ∀ behavior, (CCalls.Events.machine program).Behaves
    (.calling Reset.signature.name [.pointer (some p)] heap .done) behavior ↔
    behavior = .terminates [] ⟨.integer 0, Reset.finalHeap heap p⟩
  enter : ∀ behavior, (CCalls.Events.machine program).Behaves
    (.calling InitializationCalls.signature.name
      (InitializationCalls.arguments (some p) (InitializationCalls.Raw.ofFinite args)) (Reset.finalHeap heap p) .done) behavior ↔
    behavior = .terminates [] ⟨.integer 0, InitializationEntry.finalHeap (Reset.finalHeap heap p) p args⟩
  exit : ∀ behavior, (CCalls.Events.machine program).Behaves
    (.calling InitializationExit.signature.name (InitializationExit.arguments (some p))
      (InitializationEntry.finalHeap (Reset.finalHeap heap p) p args) .done) behavior ↔
    behavior = .terminates [] ⟨.integer 0, InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args kind⟩
  source : ResetSourceResult a p ⟨.integer 0, Reset.finalHeap heap p⟩ (Binary64.value args.start)
  initialized : InitializationCalls.SourceInitialized a.parsed.ast
    (InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args kind) p args.start
    (Initialization.trajectory (Binary64.value args.start) (Binary64.value Binary64.positiveZero))
  unique : ∀ trajectory, InitializationCalls.SourceInitialized a.parsed.ast
    (InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args kind) p args.start trajectory →
    trajectory = Initialization.trajectory (Binary64.value args.start) (Binary64.value Binary64.positiveZero)
  frame : ∀ query, ¬ p.InRecord query →
    InitializationCalls.exitedHeap (Reset.finalHeap heap p) p args kind query = heap query

theorem restart_correct (a : Artifact input) (header : CFenv.Header) (objects : Objects)
    (literals : CLiteralAddresses) :
    letI : CInterface := RuntimeEnvironment.interface header objects literals
    ∀ (program : CCalls.Events.Program E) (heap : Heap) (p : Address) (kind : Kind) (mode : Mode)
      (args : Initialization.Arguments),
    StaticReset.ExecutionContract program →
    program.internal.definitions InitializationCalls.signature.name = some (.tree InitializationCalls.function) →
    program.internal.definitions InitializationExit.signature.name =
      some (.tree (Runtime.function a.solve.prepareFMI3 InitializationExit.signature)) →
    Reset.Storage heap p → load heap (p.member "kind") = some (.integer kind.code) →
    load heap (p.member "mode") = some (.integer mode.code) → args.Admissible →
    Restarted a program heap p kind args := by
  letI : CInterface := RuntimeEnvironment.interface header objects literals
  intro program heap p kind mode args reset enterDefined exitDefined storage hk hm admissible
  obtain ⟨entered, exited⟩ := InitializationEnvironment.calls header objects literals a.solve.prepareFMI3
    program (Reset.finalHeap heap p) p args kind enterDefined exitDefined admissible
    (StaticReset.entry_storage heap p) ((StaticReset.kind_value heap p).trans hk)
  have initialized := InitializationBodies.exit_model (InitializationEntry.model (Reset.state heap p) args) kind
  exact ⟨reset.successful heap p kind mode storage hk hm, entered, exited,
    reset_result a heap p (Binary64.value args.start),
    InitializationCalls.exited_source_initialized a.solve.prepareFMI3 (Reset.finalHeap heap p) p args kind
      ⟨Binary64.positiveZero⟩ (Reset.state heap p),
    fun _ given => InitializationCalls.source_initialized_unique given initialized,
    fun query outside => StaticReset.restarted_frame heap p query args kind outside⟩


end Rumoca.FMI3
end
