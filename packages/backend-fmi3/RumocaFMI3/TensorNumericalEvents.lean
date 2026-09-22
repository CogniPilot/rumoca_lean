import RumocaC.TensorSquareCallSites
import RumocaFMI3.RuntimeEnvironment

/-! Finite numerical calls transfer to the FMI event scheduler on the same
final heap. The scheduler excludes local shadowing; actual runtime constants
exclude global shadowing. No assumption about intermediate call states is added. -/
noncomputable section
namespace Rumoca.TensorKernel
open CTree CMemory CCalls CCallSites CCallSites.LoopCalls

theorem runtime_helpers_clear (header : CFenv.Header) (objects : FMI3.StaticFactory.Objects)
    (literals : CLiteralAddresses) :
    ∀ name, name ∈ helperNames →
      (FMI3.RuntimeEnvironment.interface header objects literals).constants name = none ∧ name ≠ "isfinite" := by
  intro name member
  simp only [helperNames, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals exact ⟨rfl, by decide +kernel⟩

theorem numerical_call_events (header : CFenv.Header) (objects : FMI3.StaticFactory.Objects)
    (literals : CLiteralAddresses) :
    letI : CInterface := FMI3.RuntimeEnvironment.interface header objects literals
    ∀ (program : Events.Program E), Typed.Extends definitions program.internal →
    ∀ (name : String) (args : List Value) (heap finalHeap : Heap),
      (CLoops.Calls.machine definitions).Behaves (.calling name args heap .done) (.terminates finalHeap) →
      Transition.Reaches (fun a b => Events.internalNext program a = some b)
        (.calling name args heap .done) (.halted ⟨.void, finalHeap⟩) := by
  letI : CInterface := FMI3.RuntimeEnvironment.interface header objects literals
  intro program linked name args heap finalHeap ran
  exact call_terminates_events program linked functions_admitted
    (runtime_helpers_clear header objects literals) name args heap finalHeap ran

def RuntimeTransfer (target : CCalls.Program) : Prop :=
  ∀ (header : CFenv.Header) (objects : FMI3.StaticFactory.Objects) (literals : CLiteralAddresses),
    letI : CInterface := FMI3.RuntimeEnvironment.interface header objects literals
    ∀ (E : Type) (program : Events.Program E), program.internal = target →
    ∀ (name : String) (args : List Value) (heap finalHeap : Heap),
      (CLoops.Calls.machine definitions).Behaves (.calling name args heap .done) (.terminates finalHeap) →
      Transition.Reaches (fun a b => Events.internalNext program a = some b)
        (.calling name args heap .done) (.halted ⟨.void, finalHeap⟩)

theorem runtime_transfer (target : CCalls.Program)
    (linked : Typed.Extends definitions target) : RuntimeTransfer target := by
  intro header objects literals
  letI : CInterface := FMI3.RuntimeEnvironment.interface header objects literals
  intro E program actual name args heap finalHeap ran
  exact numerical_call_events header objects literals program (actual ▸ linked) name args heap finalHeap ran


end Rumoca.TensorKernel
