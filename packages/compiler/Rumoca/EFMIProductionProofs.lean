import RumocaEFMI.CInterface
import Rumoca.EFMIProofs
import RumocaEFMI.CSyntaxProofs
import RumocaEFMI.CProtocol
import RumocaEFMI.MetadataProofs
import RumocaEFMI.StartupMapProofs

noncomputable section
namespace Rumoca.EFMI
private local instance targetInterface : CInterface := cInterface
open CMemory

/-- Both complete code members refer to the same checked source product.
The C contract covers syntax, typed entry, finite IEEE execution and the
entire resulting heap. Archive/XML and host scheduling are separate layers. -/
structure ProductionContract (a : Artifact source) (algorithm c : String) : Prop where
  algorithm_contract : AlgorithmContract a algorithm
  algorithm_names : ∃ parsed, GALEC.Syntax.parse algorithm = .ok parsed ∧ parsed.ast = GALEC.Syntax.unit
  bytes : a.productionSource = .ok c
  header : CHeader.Contract c
  startup_map : Production.StartupMap.Contract a.algorithmSolve c
  target : ∃ module : Production.Module,
    Production.lower a.algorithmSolve = .ok module ∧ module.render = c ∧
    (∃ printed, printed.tree = module ∧ CSyntax.Denotes c printed) ∧
    (∀ method p, CCalls.parameters (module.method method).signature.parameters
      [.pointer (some p)] = some (Production.parameters p)) ∧
    (∀ method, CHeader.returnValue (module.method method).signature.result (.integer 0) =
      some (.integer 0)) ∧
    Metadata.Contract a.algorithmSolve module ∧
    (∀ method heap p (state : GALEC.UnitProfile.State Binary64.Value),
      Production.Represents heap p state →
      (∀ behavior, CArithmetic.machine.Behaves
        (.running (module.method method).body (Production.parameters p) heap) behavior ↔
        behavior = .terminates ⟨.integer 0, Production.resultHeap heap p state method⟩) ∧
      Production.Represents (Production.resultHeap heap p state method) p
        (GALEC.UnitProfile.solveExecute a.algorithmSolve.block Binary64.positiveZero
          Binary64.one GALEC.roundedAdd method state) ∧
      (∀ q, q ≠ p.member "x" → q ≠ p.member "samplePeriod" →
        q ≠ p.member CHeader.statusName →
        Production.resultHeap heap p state method q = heap q)) ∧
    (∀ heap p oldX oldPeriod,
      heap (p.member "x") = some ⟨.float64, true, oldX⟩ →
      heap (p.member "samplePeriod") = some ⟨.float64, true, oldPeriod⟩ →
      Production.StatusStorage heap p →
      ∀ behavior, CArithmetic.machine.Behaves
        (.running module.startup.body (Production.parameters p) heap) behavior ↔
        behavior = .terminates ⟨.integer 0, Production.initialized heap p⟩) ∧
    (∀ p c s events c', CProtocol.Related p c s → CProtocol.Trace module p c events c' →
      ∃ s', GALEC.Protocol.Trace (CProtocol.execute a.algorithmSolve) s events s' ∧
        CProtocol.Related p c' s') ∧
    (∀ p c s events s', CProtocol.Related p c s →
      GALEC.Protocol.Trace (CProtocol.execute a.algorithmSolve) s events s' →
      ∃ c', CProtocol.Trace module p c events c' ∧ CProtocol.Related p c' s')

theorem production_source_is_unit (a : Artifact source) :
    a.productionSource = .ok Production.unitModule.render := by
  simp only [Artifact.productionSource, Production.StartupMap.render_unchanged, Production.lower_is_unit]
  rfl

theorem production_correct (a : Artifact source) (alg : AlgorithmContract a algorithm)
    (hc : a.productionSource = .ok c) : ProductionContract a algorithm c := by
  have he := (production_source_is_unit a).symm.trans hc
  cases Except.ok.inj he
  have named : ∃ parsed, GALEC.Syntax.parse algorithm = .ok parsed ∧ parsed.ast = GALEC.Syntax.unit := by
    rw [← alg.bytes]
    exact render_parses a.algorithmCode
  refine ⟨alg, named, hc, CHeader.render_contract _, Production.StartupMap.correct _ hc,
    Production.unitModule, Production.lower_is_unit _, rfl,
    CSyntax.print_denotes a.algorithmSolve _ (Production.lower_is_unit a.algorithmSolve),
    Production.parameters_checked,
    Production.return_checked,
    Metadata.correct a.algorithmSolve _ (Production.lower_is_unit _),
    ?_, ?_, ?_, ?_⟩
  · exact fun method heap p state h =>
      Production.method_correct _ _ (Production.lower_is_unit _) method heap p state h
  · exact fun heap p oldX oldPeriod hx hp hs =>
      CArithmetic.behaviors_of_run (Production.startup_run heap p oldX oldPeriod hx hp hs)
  · exact fun p c s events c' h t =>
      CProtocol.trace_sound a.algorithmSolve _ (Production.lower_is_unit _) p s h t
  · exact fun p c s events s' h t =>
      CProtocol.trace_complete a.algorithmSolve _ (Production.lower_is_unit _) p c h t

/-- Successful compilation and actual-byte binding license both code products;
no separate source or Solve instance can supply the C member's semantics. -/
theorem compile_production_verified (h : compile source = .ok a)
    (ha : a.algorithmSource = algorithm) (hc : a.productionSource = .ok c) :
    compile source = .ok a ∧ ProductionContract a algorithm c :=
  ⟨h, production_correct a (algorithm_correct a ha) hc⟩

end Rumoca.EFMI
