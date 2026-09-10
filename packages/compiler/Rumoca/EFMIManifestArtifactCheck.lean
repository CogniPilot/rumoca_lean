import Rumoca.EFMIProductionArtifactCheck
import Rumoca.EFMIManifestProofs
import SHA1.CertificateCheck
import XML.CertificateCheck

/-! Fixed file adapter for the three eFMU manifests. Candidate identity fields
and XML trees are quoted data, never proof authority. Shared checksum and
serialization facts avoid recomputing the dependency graph in every field.
The kernel checks all actual code and XML strings together, including the
identity profile. General XSD conformance and archive binding remain separate
obligations. -/
namespace Rumoca.EFMIManifestArtifactCheck
open Lean Elab Command

def check (input : EFMICheckOptions.Code) (files : EFMI.Directory.Snapshot) : CommandElabM Unit := do
  let ⟨algorithm, c, algorithmXML, productionXML, contentXML, identity⟩ := files
  let ⟨containerId, algorithmId, productionId, generated⟩ := identity
  let ⟨source, _, grammar, algGrammar⟩ := input
  let .ok candidate := compile source | throwError "source compilation failed"
  let .ok module := EFMI.Production.lower candidate.algorithmSolve | throwError "Production C lowering failed"
  let documents ← match EFMI.Manifest.checked candidate.parsed.ast.name identity algorithm module with
    | .ok documents => pure documents
    | .error error => throwError "{error}"
  if XML.document documents.val.algorithm != algorithmXML ||
      XML.document documents.val.production != productionXML ||
      XML.document documents.val.content != contentXML then
    throwError "actual manifest differs from the correlated code products"
  let src := Syntax.mkStrLit source
  let modelName := Syntax.mkStrLit candidate.parsed.ast.name
  let alg := Syntax.mkStrLit algorithm
  let out := Syntax.mkStrLit c
  let ax := Syntax.mkStrLit algorithmXML
  let px := Syntax.mkStrLit productionXML
  let cx := Syntax.mkStrLit contentXML
  let cid := Syntax.mkStrLit containerId
  let aid := Syntax.mkStrLit algorithmId
  let pid := Syntax.mkStrLit productionId
  let date := Syntax.mkStrLit generated
  let ebnf := Syntax.mkStrLit grammar
  let algEbnf := Syntax.mkStrLit algGrammar
  let codeRoot := mkIdent `Rumoca.CheckedEFMIFiles.source_to_production
  let modelNameRoot := mkIdent `Rumoca.CheckedEFMIFiles.source_model_name
  let identityName := mkIdent `Rumoca.CheckedEFMIFiles.manifest_identity
  let identityValid := mkIdent `Rumoca.CheckedEFMIFiles.manifest_identity_valid
  let aTree := mkIdent `Rumoca.CheckedEFMIFiles.algorithm_xml_tree
  let pTree := mkIdent `Rumoca.CheckedEFMIFiles.production_xml_tree
  let cTree := mkIdent `Rumoca.CheckedEFMIFiles.content_xml_tree
  let aText := mkIdent `Rumoca.CheckedEFMIFiles.algorithm_xml_bytes
  let pText := mkIdent `Rumoca.CheckedEFMIFiles.production_xml_bytes
  let cText := mkIdent `Rumoca.CheckedEFMIFiles.content_xml_bytes
  elabCommand (← `(command| def $identityName:ident : EFMI.Manifest.Identity := ⟨$cid, $aid, $pid, $date⟩))
  elabCommand (← `(command|
    theorem $identityValid:ident : EFMI.Manifest.Identity.Valid $identityName := by decide +kernel))
  XML.CertificateCheck.certify aTree.getId aText.getId documents.val.algorithm algorithmXML
  XML.CertificateCheck.certify pTree.getId pText.getId documents.val.production productionXML
  XML.CertificateCheck.certify cTree.getId cText.getId documents.val.content contentXML
  XML.CertificateCheck.certifyValidity aTree.getId documents.val.algorithm
  XML.CertificateCheck.certifyValidity pTree.getId documents.val.production
  XML.CertificateCheck.certifyValidity cTree.getId documents.val.content
  EFMIProductionArtifactCheck.check input c
  let aHash := mkIdent `Rumoca.CheckedEFMIFiles.algorithm_checksum
  let cHash := mkIdent `Rumoca.CheckedEFMIFiles.production_checksum
  let axHash := mkIdent `Rumoca.CheckedEFMIFiles.algorithm_xml_checksum
  let pxHash := mkIdent `Rumoca.CheckedEFMIFiles.production_xml_checksum
  for (name, input) in [(aHash, algorithm), (cHash, c), (axHash, algorithmXML), (pxHash, productionXML)] do
    SHA1.CertificateCheck.certify name.getId input
  let aEq := mkIdent `Rumoca.CheckedEFMIFiles.algorithm_tree_eq
  let pEq := mkIdent `Rumoca.CheckedEFMIFiles.production_tree_eq
  let cEq := mkIdent `Rumoca.CheckedEFMIFiles.content_tree_eq
  elabCommand (← `(command|
    theorem $aEq:ident : EFMI.Manifest.algorithm $modelName $identityName $alg = $aTree := by
      simp only [EFMI.Manifest.algorithm, EFMI.Manifest.files, EFMI.Manifest.file, $aHash:ident]
      rfl))
  elabCommand (← `(command|
    theorem $pEq:ident : EFMI.Manifest.production $modelName $identityName $ax EFMI.Production.unitModule = $pTree := by
      have codeBytes : EFMI.Production.unitModule.render = $out := by rw [EFMI.CSyntax.render_unit]; rfl
      simp only [EFMI.Manifest.production, EFMI.Manifest.files, EFMI.Manifest.file,
        codeBytes, $cHash:ident, $axHash:ident]
      rfl))
  elabCommand (← `(command|
    theorem $cEq:ident : EFMI.Manifest.content $modelName $identityName $ax $px = $cTree := by
      simp only [EFMI.Manifest.content, EFMI.Manifest.representation, $axHash:ident, $pxHash:ident]
      rfl))
  let graph := mkIdent `Rumoca.CheckedEFMIFiles.manifest_graph
  elabCommand (← `(command|
    theorem $graph:ident : EFMI.Manifest.prepare $modelName $identityName $alg EFMI.Production.unitModule =
        EFMI.Manifest.Documents.mk $aTree $pTree $cTree := by
      simp only [EFMI.Manifest.prepare, $aEq:ident, $aText:ident, $pEq:ident, $pText:ident, $cEq:ident]))
  let valid := mkIdent `Rumoca.CheckedEFMIFiles.manifest_xml_valid
  let aValid := mkIdent (aTree.getId.str "valid_eq")
  let pValid := mkIdent (pTree.getId.str "valid_eq")
  let cValid := mkIdent (cTree.getId.str "valid_eq")
  elabCommand (← `(command|
    theorem $valid:ident : (EFMI.Manifest.Documents.mk $aTree $pTree $cTree).valid = true := by
      simp only [EFMI.Manifest.Documents.valid, $aValid:ident, $pValid:ident, $cValid:ident, Bool.and_self]))
  let theoremName := `Rumoca.CheckedEFMIFiles.source_to_manifests
  let theoremId := mkIdent theoremName
  elabCommand (← `(command| attribute [local irreducible] EFMI.Manifest.prepare XML.document))
  elabCommand (← `(command|
    theorem $theoremId:ident :
        Generated.source = $ebnf ∧ GALEC.Generated.source = $algEbnf ∧
        ∃ a : Artifact $src, compile $src = .ok a ∧
          EFMI.ManifestContract a ⟨$cid, $aid, $pid, $date⟩ $alg $out $ax $px $cx := by
      obtain ⟨g₁, g₂, a, compiled, code⟩ := $codeRoot:ident
      exact ⟨g₁, g₂, a, compiled,
        EFMI.manifests_correct_of_documents (algorithm := $alg) (c := $out)
          (algorithmXML := $ax) (productionXML := $px) (contentXML := $cx)
          a $identityName $identityValid:ident code $aTree $pTree $cTree
          (by rw [$modelNameRoot:ident a.parsed]; exact $graph:ident)
          $valid:ident $aText:ident $pText:ident $cText:ident⟩))
  let axioms ← collectAxioms theoremName
  for dependency in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in manifest contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {axioms.toList}"

elab "verify_efmi_manifest_files" : command => do
  let root := ← EFMICheckOptions.required rumoca.efmi.root
  let files ← EFMI.Directory.read root
  check (← EFMICheckOptions.readCode files.algorithm) files

end Rumoca.EFMIManifestArtifactCheck
