import Rumoca.EFMITensorProductionArtifactCheck
import Rumoca.EFMITensorArchiveProofs
import RumocaEFMI.TensorManifestProofs
import SHA1.CertificateCheck
import XML.CertificateCheck

/-! Fixed actual-file adapter for the three tensor eFMU manifests. Candidate
identity fields and XML trees are quoted data, never proof authority. The
Algorithm/Production/container XML and their SHA-1 checksums are certified
against the actual bytes, then composed into the frozen tensor manifest
contract. General XSD conformance and the archive binding are separate layers.
The checksum certificates reduce SHA-1 through the structural message schedule,
so the 7.4 KB Production Code manifest certifies within the gate's budget. -/
namespace Rumoca.EFMITensorManifestArtifactCheck
open Lean Elab Command
open Rumoca Rumoca.EFMI

def check (input : EFMICheckOptions.Code) (files : EFMI.Directory.Snapshot) : CommandElabM Unit := do
  let ⟨algorithm, c, algorithmXML, productionXML, contentXML, identity⟩ := files
  let ⟨containerId, algorithmId, productionId, generated⟩ := identity
  let ⟨_, _, _, grammar, algGrammar⟩ := input
  -- Preliminary rejections against the pinned tensor products and the read XML.
  let .ok candidate := compileTensor input.input | throwError "tensor source compilation failed"
  if c != EFMI.TensorProduction.render then
    throwError "actual tensor Production C differs from the certified translation unit"
  if algorithm != EFMI.tensorUnitSource then
    throwError "actual tensor Algorithm Code differs from the pinned tensor square profile"
  let modelName := candidate.name
  let docs := EFMI.TensorManifest.prepare modelName identity EFMI.tensorUnitSource
  if XML.document docs.algorithm != algorithmXML ||
      XML.document docs.production != productionXML ||
      XML.document docs.content != contentXML then
    throwError "actual tensor manifest differs from the correlated code products"
  -- The production contract exposes `production_render_eq` and `production_chars`.
  EFMITensorProductionArtifactCheck.check input c
  let inputTerm ← input.inputTerm
  let nameLit := Syntax.mkStrLit modelName
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
  let srcLit := Syntax.mkStrLit input.source
  let productionRoot := mkIdent `Rumoca.CheckedTensorEFMIFiles.source_to_production
  let renderEq := mkIdent `Rumoca.CheckedTensorEFMIFiles.production_render_eq
  let modelChars := mkIdent `Rumoca.CheckedTensorEFMIFiles.production_chars.part_0
  let identityName := mkIdent `Rumoca.CheckedTensorEFMIFiles.manifest_identity
  let identityValid := mkIdent `Rumoca.CheckedTensorEFMIFiles.manifest_identity_valid
  let aTree := mkIdent `Rumoca.CheckedTensorEFMIFiles.algorithm_xml_tree
  let pTree := mkIdent `Rumoca.CheckedTensorEFMIFiles.production_xml_tree
  let cTree := mkIdent `Rumoca.CheckedTensorEFMIFiles.content_xml_tree
  let aText := mkIdent `Rumoca.CheckedTensorEFMIFiles.algorithm_xml_bytes
  let pText := mkIdent `Rumoca.CheckedTensorEFMIFiles.production_xml_bytes
  let cText := mkIdent `Rumoca.CheckedTensorEFMIFiles.content_xml_bytes
  elabCommand (← `(command| def $identityName:ident : EFMI.Manifest.Identity := ⟨$cid, $aid, $pid, $date⟩))
  elabCommand (← `(command|
    theorem $identityValid:ident : EFMI.Manifest.Identity.Valid $identityName := by decide +kernel))
  -- XML serialization and validity certificates for the three read documents.
  XML.CertificateCheck.certify aTree.getId aText.getId docs.algorithm algorithmXML
  XML.CertificateCheck.certify pTree.getId pText.getId docs.production productionXML
  XML.CertificateCheck.certify cTree.getId cText.getId docs.content contentXML
  XML.CertificateCheck.certifyValidity aTree.getId docs.algorithm
  XML.CertificateCheck.certifyValidity pTree.getId docs.production
  XML.CertificateCheck.certifyValidity cTree.getId docs.content
  -- SHA-1 checksum certificates for the code files and the hashed manifests.
  let aHash := mkIdent `Rumoca.CheckedTensorEFMIFiles.algorithm_checksum
  let cHash := mkIdent `Rumoca.CheckedTensorEFMIFiles.production_checksum
  let axHash := mkIdent `Rumoca.CheckedTensorEFMIFiles.algorithm_xml_checksum
  let pxHash := mkIdent `Rumoca.CheckedTensorEFMIFiles.production_xml_checksum
  for (name, s) in [(aHash, algorithm), (cHash, c), (axHash, algorithmXML), (pxHash, productionXML)] do
    SHA1.CertificateCheck.certify name.getId s
  -- The read algorithm bytes are the pinned Lean source; the read production
  -- bytes are the certified render form. These bridge the tree's Lean constants
  -- to the certified checksums without re-reducing the renderer.
  let algBridge := mkIdent `Rumoca.CheckedTensorEFMIFiles.algorithm_source_eq
  let renderBridge := mkIdent `Rumoca.CheckedTensorEFMIFiles.render_source_eq
  elabCommand (← `(command| theorem $algBridge:ident : EFMI.tensorUnitSource = $alg := by decide +kernel))
  elabCommand (← `(command| theorem $renderBridge:ident : EFMI.TensorProduction.render = $out :=
    ($renderEq:ident).trans (by rfl)))
  -- Rebuild each manifest tree from the certified checksums.
  let aEq := mkIdent `Rumoca.CheckedTensorEFMIFiles.algorithm_tree_eq
  let pEq := mkIdent `Rumoca.CheckedTensorEFMIFiles.production_tree_eq
  let cEq := mkIdent `Rumoca.CheckedTensorEFMIFiles.content_tree_eq
  elabCommand (← `(command|
    theorem $aEq:ident : EFMI.TensorManifest.algorithm $nameLit $identityName EFMI.tensorUnitSource = $aTree := by
      simp only [EFMI.TensorManifest.algorithm, EFMI.Manifest.files, EFMI.Manifest.file,
        $algBridge:ident, $aHash:ident]
      rfl))
  elabCommand (← `(command|
    theorem $pEq:ident : EFMI.TensorManifest.production $nameLit $identityName $ax = $pTree := by
      simp only [EFMI.TensorManifest.production, EFMI.Manifest.files, EFMI.Manifest.file,
        $renderBridge:ident, $cHash:ident, $axHash:ident]
      rfl))
  elabCommand (← `(command|
    theorem $cEq:ident : EFMI.TensorManifest.content $nameLit $identityName $ax $px = $cTree := by
      simp only [EFMI.TensorManifest.content, EFMI.TensorManifest.representation, $axHash:ident, $pxHash:ident]
      rfl))
  let graph := mkIdent `Rumoca.CheckedTensorEFMIFiles.manifest_graph
  elabCommand (← `(command|
    theorem $graph:ident : EFMI.TensorManifest.prepare $nameLit $identityName EFMI.tensorUnitSource =
        EFMI.TensorManifest.Documents.mk $aTree $pTree $cTree := by
      simp only [EFMI.TensorManifest.prepare, $aEq:ident, $aText:ident, $pEq:ident, $pText:ident, $cEq:ident]))
  let valid := mkIdent `Rumoca.CheckedTensorEFMIFiles.manifest_xml_valid
  let aValid := mkIdent (aTree.getId.str "valid_eq")
  let pValid := mkIdent (pTree.getId.str "valid_eq")
  let cValid := mkIdent (cTree.getId.str "valid_eq")
  elabCommand (← `(command|
    theorem $valid:ident : (EFMI.TensorManifest.Documents.mk $aTree $pTree $cTree).valid = true := by
      simp only [EFMI.TensorManifest.Documents.valid, $aValid:ident, $pValid:ident, $cValid:ident, Bool.and_self]))
  let theoremName := `Rumoca.CheckedTensorEFMIFiles.source_to_manifests
  let theoremId := mkIdent theoremName
  elabCommand (← `(command| attribute [local irreducible] EFMI.TensorManifest.prepare XML.document))
  elabCommand (← `(command|
    theorem $theoremId:ident :
        Generated.source = $ebnf ∧ GALEC.Generated.source = $algEbnf ∧
        ∃ a : TensorArtifact $inputTerm, compileTensor $inputTerm = .ok a ∧
          TensorExecutedManifestContract a ⟨$cid, $aid, $pid, $date⟩ $alg $out $ax $px $cx := by
      obtain ⟨g₁, g₂, a, compiled, code⟩ := $productionRoot:ident
      refine ⟨g₁, g₂, a, compiled, ?_⟩
      let parsed : ArrayProfile.Parsed $srcLit :=
        ⟨squareAst.tokens, squareAst, by rfl,
          ParserActions.parseTokens_complete ArrayProfile.actions squareAst⟩
      have hsame : a = TensorArtifact.ofParsed $inputTerm parsed squareAst_resolved :=
        Except.ok.inj (compiled.symm.trans
          (compileTensor_eq_parsed $inputTerm parsed squareAst_resolved))
      have hname : a.name = $nameLit := by
        rw [hsame]; exact TensorArtifact.name_square _ rfl
      have code' : TensorExecutedProductionContract a $alg $out := by
        have hc : (String.ofList $modelChars) = $out := by rfl
        exact hc ▸ code
      exact {
        toTensorManifestContract :=
          tensor_manifests_correct_of_documents a $identityName $identityValid:ident
            code'.toTensorProductionContract $aTree $pTree $cTree
            (by rw [hname]; exact $graph:ident) $valid:ident $aText:ident $pText:ident $cText:ident
        execution := code' }))
  let axioms ← collectAxioms theoremName
  for dependency in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in tensor manifest contract: {dependency}"
  logInfo m!"{theoremName} depends on axioms: {axioms.toList}"

elab "verify_tensor_efmi_manifest_files" : command => do
  let root := ← EFMICheckOptions.required rumoca.efmi.root
  let files ← EFMI.Directory.read root
  check (← EFMICheckOptions.readCode files.algorithm) files

end Rumoca.EFMITensorManifestArtifactCheck
