import RumocaEFMI.StartupMap
import RumocaEFMI.StartupOriginProofs
import RumocaEFMI.ProductionProofs

namespace Rumoca.EFMI.Production.StartupMap
open Rumoca.CTree Printed
private local instance targetInterface : CInterface := cInterface

theorem Emission.startup_correct (emission : Emission model) :
    (StartupOrigins.inputs model).TraceCorrect (emission.module_eq ▸ emission.startup) := by
  rcases emission with ⟨module, lowered⟩
  have same := Except.ok.inj ((lower_is_unit model).symm.trans lowered)
  cases same
  exact (StartupOrigins.inputs model).trace_correct

theorem Emission.startup_every (emission : Emission model) :
    emission.startup.Every (StartupOrigins.inputs model).Allowed := by
  rcases emission with ⟨module, lowered⟩
  have same := Except.ok.inj ((lower_is_unit model).symm.trans lowered)
  cases same
  exact (StartupOrigins.inputs model).trace_every

theorem Emission.document_every (emission : Emission model) :
    emission.document.body.EveryOrigin (StartupOrigins.inputs model).Allowed := by
  simpa only [document, Document.append, Document.text, Doc.EveryOrigin,
    true_and, and_true, Function.Origins.document_every] using emission.startup_every

/-- Ranges are relative to the complete Production C file, including the
actual preceding header bytes. Their origins are limited to Startup. -/
theorem Emission.map_exact (emission : Emission model)
    (entry : Entry (Origin (StartupOrigins.inputs model).outputTable)) :
    entry ∈ emission.document.entries ↔
    ∃ beforeText segment suffix,
      Region emission.document.body entry.origin beforeText segment suffix ∧
      emission.module.render = beforeText ++ segment ++ suffix ∧
      entry.start = beforeText.utf8ByteSize ∧
      entry.stop = entry.start + segment.utf8ByteSize ∧
      emission.module.render.toByteArray.extract entry.start entry.stop = segment.toByteArray := by
  constructor
  · intro member
    obtain ⟨beforeText, segment, suffix, region, first, last⟩ :=
      (emission.document.body.map_iff entry).mp member
    refine ⟨beforeText, segment, suffix, region,
      emission.document_render.symm.trans region.render_eq, first, last, ?_⟩
    rw [← emission.document_render, last, first]
    exact region.bytes
  · rintro ⟨beforeText, segment, suffix, region, _, first, last, _⟩
    exact (emission.document.body.map_iff entry).mpr ⟨beforeText, segment, suffix, region, first, last⟩

theorem Emission.map_allowed (emission : Emission model)
    (entry : Entry (Origin (StartupOrigins.inputs model).outputTable))
    (member : entry ∈ emission.document.entries) : (StartupOrigins.inputs model).Allowed entry.origin :=
  emission.document.body.map_every _ emission.document_every entry member

/-- The mapped actual Startup has the previously proved complete behavior
contract, including initially uninitialized state/period/status storage. -/
theorem Emission.startup_behaviors (emission : Emission model)
    (heap : CMemory.Heap) (p : CMemory.Address) (oldX oldPeriod : Option CMemory.Value)
    (hx : heap (p.member "x") = some ⟨.float64, true, oldX⟩)
    (hp : heap (p.member "samplePeriod") = some ⟨.float64, true, oldPeriod⟩)
    (hs : StatusStorage heap p) :
    ∀ behavior, CArithmetic.machine.Behaves
      (.running emission.module.startup.body (parameters p) heap) behavior ↔
      behavior = .terminates ⟨.integer 0, initialized heap p⟩ := by
  rw [emission.module_eq]
  exact CArithmetic.behaviors_of_run (startup_run heap p oldX oldPeriod hx hp hs)

/-- One witness binds the actual complete file to Startup's independently
checked annotation roles, every map range and all Startup execution behaviors.
The remaining methods and native compilation are outside this map increment. -/
def Contract (model : Solve.Algorithm.Model source) (c : String) : Prop :=
  ∃ emission : Emission model,
    emit model = .ok emission ∧ emission.document.render = c ∧
    (StartupOrigins.inputs model).TraceCorrect (emission.module_eq ▸ emission.startup) ∧
    (_root_.Parser.Provenance.TracesTo (StartupOrigins.inputs model).outputTable
      ((StartupOrigins.inputs model).original (StartupOrigins.inputs model).stateLiteral)
      (model.origin.dae.flat.context.site .declaration)) ∧
    (_root_.Parser.Provenance.TracesTo (StartupOrigins.inputs model).outputTable
      ((StartupOrigins.inputs model).original (StartupOrigins.inputs model).periodLiteral)
      (model.origin.dae.flat.context.site .model)) ∧
    (∀ entry, entry ∈ emission.document.entries ↔
      ∃ beforeText segment suffix,
        Region emission.document.body entry.origin beforeText segment suffix ∧
        c = beforeText ++ segment ++ suffix ∧
        entry.start = beforeText.utf8ByteSize ∧
        entry.stop = entry.start + segment.utf8ByteSize ∧
        c.toByteArray.extract entry.start entry.stop = segment.toByteArray) ∧
    (∀ entry, entry ∈ emission.document.entries → (StartupOrigins.inputs model).Allowed entry.origin) ∧
    (∀ heap p oldX oldPeriod,
      heap (p.member "x") = some ⟨.float64, true, oldX⟩ →
      heap (p.member "samplePeriod") = some ⟨.float64, true, oldPeriod⟩ →
      StatusStorage heap p →
      ∀ behavior, CArithmetic.machine.Behaves
        (.running emission.module.startup.body (parameters p) heap) behavior ↔
        behavior = .terminates ⟨.integer 0, initialized heap p⟩)

theorem correct (model : Solve.Algorithm.Model source)
    (emitted : (fun emission => emission.document.render) <$> emit model = .ok c) : Contract model c := by
  obtain ⟨emission, success⟩ := emit_success model
  rw [success] at emitted
  have bytes : emission.document.render = c := Except.ok.inj emitted
  refine ⟨emission, success, bytes, emission.startup_correct,
    StartupOrigins.state_literal_source model, StartupOrigins.period_literal_source model,
    ?_, emission.map_allowed,
    emission.startup_behaviors⟩
  intro entry
  rw [← bytes, emission.document_render]
  exact emission.map_exact entry

end Rumoca.EFMI.Production.StartupMap
