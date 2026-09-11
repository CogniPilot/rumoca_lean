import Rumoca.Initialization
import Rumoca.Compiler
import RumocaFMI3.ResetContract

/-! Source initialization recovered from the complete emitted reset call.
This is a source-to-function-tree theorem. The caller supplies the definition
binding and instance storage; full adapter text, ZIP and native ABI contracts
are still required before this can serve as a whole-FMU guarantee. -/
noncomputable section
namespace Rumoca.FMI3
variable [static : StaticLiterals]
private local instance targetInterface : CInterface := cInterface static.addresses
open CMemory

def ResetSourceResult (a : Artifact input) (p : Address) (result : CBody.Result) (t₀ : ℝ) : Prop :=
  result.value = .integer 0 ∧ ∃ initial : Binary64.Value,
    load result.heap (StateProofs.stateAddress p) = some (.finite initial) ∧
    Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
    Source.Initializes a.parsed.ast t₀ (Initialization.trajectory t₀ (Binary64.value initial)) ∧
    ∀ x, Source.Initializes a.parsed.ast t₀ x → x t₀ = Binary64.value initial →
      x = Initialization.trajectory t₀ (Binary64.value initial)

omit static in
theorem reset_result (a : Artifact input) (heap : Heap) (p : Address) (t₀ : ℝ) :
    ResetSourceResult a p ⟨.integer 0, Reset.finalHeap heap p⟩ t₀ := by
  have zero : Binary64.value Binary64.positiveZero = 0 := by
    have units : Binary64.units Binary64.positiveZero = 0 := by decide +kernel
    simp only [Binary64.value, units, Int.cast_zero, zero_div]
  have agreement : Binary64.value Binary64.positiveZero = (a.solve.initial.initial : ℝ) := by
    rw [zero, a.solve.initial_default]
    exact Nat.cast_zero.symm
  refine ⟨rfl, Binary64.positiveZero, Reset.state heap p, agreement, ?_, ?_⟩
  · rw [agreement]
    exact (a.solve.initialization_correct t₀).1
  · intro x source initial
    rw [agreement] at initial ⊢
    exact a.solve.initialized_solution_unique t₀ x source initial

/-- The finite value comes from the returned C heap, and the source theorem
refers to the same compiled artifact's stored Solve initialization plan. -/
theorem reset_source (a : Artifact input) (program : CCalls.Program)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode) (t₀ : ℝ)
    (defined : program.definitions "fmi3Reset" =
      some (.tree (Runtime.function a.solve.prepareFMI3 Reset.signature)))
    (storage : Reset.Storage heap p)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    ∃ result,
      (∀ behavior, (CCalls.Typed.machine program).Behaves
        (.calling "fmi3Reset" [.pointer (some p)] heap .done) behavior ↔
        behavior = .terminates result) ∧ ResetSourceResult a p result t₀ :=
  ⟨⟨.integer 0, Reset.finalHeap heap p⟩,
    Reset.call_behaviors a.solve.prepareFMI3 program heap p kind mode defined storage hk hm,
    reset_result a heap p t₀⟩

theorem compile_reset_verified (compiled : compile input = .ok a) (program : CCalls.Program)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode) (t₀ : ℝ)
    (defined : program.definitions "fmi3Reset" =
      some (.tree (Runtime.function a.solve.prepareFMI3 Reset.signature)))
    (storage : Reset.Storage heap p)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    compile input = .ok a ∧ ∃ result,
      (∀ behavior, (CCalls.Typed.machine program).Behaves
        (.calling "fmi3Reset" [.pointer (some p)] heap .done) behavior ↔
        behavior = .terminates result) ∧ ResetSourceResult a p result t₀ :=
  ⟨compiled, reset_source a program heap p kind mode t₀ defined storage hk hm⟩

/-- Compose the independent function syntax and source initialization with the
actual renderer's definition table. The unique emitted names and selected
signature are explicit; an arbitrary definition binding is no longer supplied.
This is still not an actual-FMU/preprocessing or allocation certificate. -/
theorem compile_rendered_reset_verified (compiled : compile input = .ok a)
    (sigs : List CTree.Signature) (member : Reset.signature ∈ sigs)
    (unique : ((LiteralPreparation.functions a.solve.prepareFMI3 sigs).map
      (fun fn => fn.signature.name)).Nodup)
    (heap : Heap) (p : Address) (kind : Kind) (mode : Mode) (t₀ : ℝ)
    (storage : Reset.Storage heap p)
    (hk : load heap (p.member "kind") = some (.integer kind.code))
    (hm : load heap (p.member "mode") = some (.integer mode.code)) :
    compile input = .ok a ∧
    Reset.FunctionContract a.solve.prepareFMI3
      (Runtime.function a.solve.prepareFMI3 Reset.signature).render ∧
    (∃ before after : String, Runtime.render a.solve.prepareFMI3 sigs =
      before ++ (Runtime.function a.solve.prepareFMI3 Reset.signature).render ++ after) ∧
    ∃ result,
      (∀ behavior, (CCalls.Typed.machine (LiteralPreparation.program a.solve.prepareFMI3 sigs)).Behaves
        (.calling "fmi3Reset" [.pointer (some p)] heap .done) behavior ↔
        behavior = .terminates result) ∧ ResetSourceResult a p result t₀ :=
  ⟨compiled, Reset.rendered_contract a.solve.prepareFMI3,
    Reset.rendered_member a.solve.prepareFMI3 sigs member,
    reset_source a (LiteralPreparation.program a.solve.prepareFMI3 sigs) heap p kind mode t₀
      (LiteralRejection.function_bound a.solve.prepareFMI3 sigs unique Reset.signature member)
      storage hk hm⟩

end Rumoca.FMI3
