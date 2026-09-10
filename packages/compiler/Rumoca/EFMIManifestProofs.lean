import RumocaEFMI.CInterface
import Rumoca.EFMIProductionProofs
import RumocaEFMI.ManifestProofs

noncomputable section
namespace Rumoca.EFMI
private local instance targetInterface : CInterface := cInterface
open XML CMemory

/-- Actual Algorithm/Production/root XML strings describe the same checked
code pair. This binds XML syntax, decoded mappings and the raw-byte checksum
construction, but does not yet certify XSD membership or an archive. -/
structure ManifestContract (a : Artifact source) (identity : Manifest.Identity)
    (algorithm c algorithmXML productionXML contentXML : String) : Prop where
  identity_valid : identity.Valid
  code : ProductionContract a algorithm c
  target : ∃ module : Production.Module,
    Production.lower a.algorithmSolve = .ok module ∧ module.render = c ∧
    let documents := Manifest.prepare a.parsed.ast.name identity algorithm module
    documents.valid = true ∧
    documents.Identified identity ∧
    documents.Named a.parsed.ast.name ∧
    document documents.algorithm = algorithmXML ∧
    document documents.production = productionXML ∧
    document documents.content = contentXML ∧
    Document documents.algorithm algorithmXML ∧
    Document documents.production productionXML ∧
    Document documents.content contentXML ∧
    (∀ var : Metadata.Variable,
      Manifest.algorithmVariable var ∈ Manifest.select documents.algorithm ["Variables", "RealVariable"] ∧
      (Manifest.algorithmVariable var).attributes.lookup "id" = some var.id ∧
      (Manifest.algorithmVariable var).attributes.lookup "name" = some var.name ∧
      var.shape = Tensor.scalar) ∧
    (∀ method var heap p (state : GALEC.UnitProfile.State Binary64.Value),
      Production.Represents heap p state → ∀ result : CBody.Result,
      CArithmetic.machine.Behaves
        (.running (module.method method).body (Production.parameters p) heap) (.terminates result) →
      Manifest.MappedResult a.algorithmSolve module documents.production method var p state result)

theorem manifests_correct (a : Artifact source) (identity : Manifest.Identity)
    (identityValid : identity.Valid)
    (code : ProductionContract a algorithm c)
    (valid : (Manifest.prepare a.parsed.ast.name identity algorithm Production.unitModule).valid = true)
    (algorithmBytes : document (Manifest.prepare a.parsed.ast.name identity algorithm Production.unitModule).algorithm = algorithmXML)
    (productionBytes : document (Manifest.prepare a.parsed.ast.name identity algorithm Production.unitModule).production = productionXML)
    (contentBytes : document (Manifest.prepare a.parsed.ast.name identity algorithm Production.unitModule).content = contentXML) :
    ManifestContract a identity algorithm c algorithmXML productionXML contentXML := by
  have targetBytes := Except.ok.inj ((production_source_is_unit a).symm.trans code.bytes)
  have parsedXML := Manifest.documents_valid _ valid
  refine ⟨identityValid, code, Production.unitModule, Production.lower_is_unit _, targetBytes,
    valid, Manifest.prepare_identified _ _ _ _ identityValid, Manifest.prepare_named _ _ _ _,
    algorithmBytes, productionBytes, contentBytes,
    algorithmBytes ▸ parsedXML.1, productionBytes ▸ parsedXML.2.1, contentBytes ▸ parsedXML.2.2,
    Manifest.variable_declared a.parsed.ast.name identity algorithm, ?_⟩
  exact fun method var heap p state h result executed =>
    Manifest.mapped_execution a.algorithmSolve _ (Production.lower_is_unit _) a.parsed.ast.name identity _
      method var heap p state h result executed

/-- Compose independently checked document facts without normalizing their
checksum dependency graph again at each concrete theorem application. -/
theorem manifests_correct_of_documents (a : Artifact source) (identity : Manifest.Identity)
    (identityValid : identity.Valid)
    (code : ProductionContract a algorithm c) (algorithmTree productionTree contentTree : Element)
    (graph : Manifest.prepare a.parsed.ast.name identity algorithm Production.unitModule =
      Manifest.Documents.mk algorithmTree productionTree contentTree)
    (valid : (Manifest.Documents.mk algorithmTree productionTree contentTree).valid = true)
    (algorithmBytes : document algorithmTree = algorithmXML)
    (productionBytes : document productionTree = productionXML)
    (contentBytes : document contentTree = contentXML) :
    ManifestContract a identity algorithm c algorithmXML productionXML contentXML := by
  apply manifests_correct a identity identityValid code
  · rw [graph]; exact valid
  · rw [graph]; exact algorithmBytes
  · rw [graph]; exact productionBytes
  · rw [graph]; exact contentBytes

/-- Read the source model name from every actual XML member's tree. This
observation follows from the full code/manifest contract, including the
independent XML syntax relation, rather than just a renderer equality. -/
theorem ManifestContract.source_name
    (contract : ManifestContract a identity algorithm c algorithmXML productionXML contentXML) :
    ∃ documents : Manifest.Documents,
      Document documents.algorithm algorithmXML ∧
      Document documents.production productionXML ∧
      Document documents.content contentXML ∧ documents.Named a.parsed.ast.name := by
  obtain ⟨module, _, _, _, _, named, _, _, _, ha, hp, hc, _, _⟩ := contract.target
  exact ⟨Manifest.prepare a.parsed.ast.name identity algorithm module, ha, hp, hc, named⟩

end Rumoca.EFMI
