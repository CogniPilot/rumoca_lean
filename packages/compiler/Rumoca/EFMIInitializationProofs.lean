import Rumoca.EFMIArchiveProofs
import Rumoca.Initialization

/-! Source initialization recovered from the actual eFMI Production Code and
archive contracts. Valid entry storage is supplied; allocation, public ABI and
later machine compilation remain outside this authored C execution theorem. -/

noncomputable section
namespace Rumoca.EFMI
private local instance targetInterface : CInterface := cInterface
open CMemory

def InitializedSourceResult (a : Artifact input) (p : Address) (result : CBody.Result)
    (t₀ : ℝ) : Prop :=
  result.value = .integer 0 ∧ ∃ initial : Binary64.Value,
    load result.heap (p.member "x") = some (.finite initial) ∧
    Binary64.value initial = (a.solve.initial.initial : ℝ) ∧
    Source.Initializes a.parsed.ast t₀ (Initialization.trajectory t₀ (Binary64.value initial)) ∧
    ∀ x, Source.Initializes a.parsed.ast t₀ x → x t₀ = Binary64.value initial →
      x = Initialization.trajectory t₀ (Binary64.value initial)

/-- Recover source initialization from the actual Production Code certificate.
The initial real value is read from the returned C heap, and agrees with the
source-bound Solve plan. Entry storage and later machine compilation remain
the same explicit boundary as in ProductionContract. -/
theorem ProductionContract.startup_source (contract : ProductionContract a algorithm c)
    (module : Production.Module) (lowered : Production.lower a.algorithmSolve = .ok module)
    (heap : Heap) (p : Address) (oldX oldPeriod : Option Value)
    (hx : heap (p.member "x") = some ⟨.float64, true, oldX⟩)
    (hp : heap (p.member "samplePeriod") = some ⟨.float64, true, oldPeriod⟩)
    (hs : Production.StatusStorage heap p) (result : CBody.Result)
    (observed : CArithmetic.machine.Behaves
      (.running module.startup.body (Production.parameters p) heap) (.terminates result))
    (t₀ : ℝ) : InitializedSourceResult a p result t₀ := by
  obtain ⟨checked, compiled, _, _, _, _, _, _, startup, _, _⟩ := contract.target
  have same : checked = module := Except.ok.inj (compiled.symm.trans lowered)
  subst checked
  have outcome := (startup heap p oldX oldPeriod hx hp hs (.terminates result)).mp observed
  have returned : result = ⟨.integer 0, Production.initialized heap p⟩ :=
    Transition.Observation.terminates.inj outcome
  subst result
  have zero : Binary64.value Binary64.positiveZero = 0 := by
    have units : Binary64.units Binary64.positiveZero = 0 := by decide +kernel
    simp only [Binary64.value, units, Int.cast_zero, zero_div]
  have agreement : Binary64.value Binary64.positiveZero = (a.solve.initial.initial : ℝ) := by
    rw [zero, a.solve.initial_default]
    exact Nat.cast_zero.symm
  refine ⟨rfl, Binary64.positiveZero, ?_, ?_, ?_, ?_⟩
  · simp [Production.initialized, Production.written,
      replace, load, convert, Value.finite]
  · exact agreement
  · rw [agreement]
    exact (a.solve.initialization_correct t₀).1
  · intro x source initial
    rw [agreement] at initial ⊢
    exact a.solve.initialized_solution_unique t₀ x source initial

/-- A complete Startup execution guarantee for the Production Code member in
these exact ZIP bytes. This also requires termination for every admitted heap. -/
def ArchiveStartupContract (a : Artifact input) (bytes : ByteArray) : Prop :=
    ∃ (code : Archive.Code) (module : Production.Module),
      Production.lower a.algorithmSolve = .ok module ∧ module.render = code.production ∧
      (∃ before after : List UInt8, bytes.data.toList = before ++
        StoredZIP.Format.localRecord ⟨Archive.Member.production.name, code.production.toUTF8⟩ ++ after) ∧
      (∃ printed, printed.tree = module ∧ CSyntax.Denotes code.production printed) ∧
      ∀ heap p oldX oldPeriod,
        heap (p.member "x") = some ⟨.float64, true, oldX⟩ →
        heap (p.member "samplePeriod") = some ⟨.float64, true, oldPeriod⟩ →
        Production.StatusStorage heap p → ∀ t₀, ∃ result,
        (∀ behavior, CArithmetic.machine.Behaves
          (.running module.startup.body (Production.parameters p) heap) behavior ↔
          behavior = .terminates result) ∧ InitializedSourceResult a p result t₀

/-- The exact Production Code member of every certified archive implements the
source initialization relation. Its emitted bytes, parsed C tree, prepared
Solve product and observed initialized heap refer to the same module. -/
theorem ArchiveContract.startup_source (contract : ArchiveContract a identity bytes) :
    ArchiveStartupContract a bytes := by
  obtain ⟨code, manifests, members⟩ := contract.code_members
  obtain ⟨module, lowered, rendered, printer, _, _, _, _, startup, _, _⟩ := manifests.code.target
  refine ⟨code, module, lowered, rendered, (members .production).2, printer, ?_⟩
  intro heap p oldX oldPeriod hx hp hs t₀
  let result : CBody.Result := ⟨.integer 0, Production.initialized heap p⟩
  have behavior := startup heap p oldX oldPeriod hx hp hs
  refine ⟨result, behavior, ?_⟩
  exact manifests.code.startup_source module lowered heap p oldX oldPeriod hx hp hs result
    ((behavior (.terminates result)).mpr rfl) t₀

end Rumoca.EFMI
