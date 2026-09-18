import Rumoca.EFMITensorManifestArtifactCheck
import RumocaEFMI.ZIPArchiveCertificateCheck
import RumocaEFMISchemaCertificates

/-! Fixed actual-eFMU adapter for the frozen tensor two-representation profile.
The candidate reader and early comparisons can reject input but cannot certify
it. Complete ZIP bytes and the tensor source/code/manifest chain are checked
together by the kernel, mirroring the scalar `EFMIArchiveArtifactCheck` over the
tensor manifest contract. This does not certify the external C compiler or full
XSD/prose semantics, and it does not publish an archive.

The tensor manifest certificate (`EFMITensorManifestArtifactCheck`) fits the
shared gate's memory budget, but composing it with the additional stored-ZIP
transport certificate over all fifty archive members here still peaks above the
8 GiB gate budget (dominated by the per-element XML serialization certificate).
This adapter is therefore not yet wired into the gate or CLI admission; its
`tensor-efmi-archive` kind exists so the composition can be completed once that
cost is reduced. See dev/standards-review.md and dev/verification-performance.md. -/
namespace Rumoca.EFMITensorArchiveArtifactCheck
open Lean Elab Command EFMI

elab "verify_tensor_efmi_archive" : command => do
  let path ← EFMICheckOptions.required rumoca.efmi.root
  let bytes ← IO.FS.readBinFile path
  let items ← match StoredZIP.decodeCandidate bytes with
    | .ok entries => pure entries
    | .error error => throwError "{error}"
  unless items.map (·.name) == Archive.paths do
    throwError "tensor eFMU member roster differs from the certified profile"
  for resource in Resources.schemas do
    unless Archive.lookup items resource.name == some resource.text.toUTF8 do
      throwError "archive schema resource differs from the pinned release: {resource.name}"
  let readMember (member : Archive.Member) : CommandElabM String := do
    let some raw := Archive.lookup items member.name | throwError "missing {member.name}"
    let some text := String.fromUTF8? raw | throwError "invalid UTF-8 in {member.name}"
    return text
  let code : Archive.Code := ⟨← readMember .algorithm, ← readMember .production,
    ← readMember .algorithmManifest, ← readMember .productionManifest, ← readMember .content⟩
  let files ← match Directory.snapshot code.algorithm code.production code.algorithmXML
      code.productionXML code.contentXML with
    | .ok files => pure files
    | .error error => throwError "{error}"
  let input ← EFMICheckOptions.readCode code.algorithm
  EFMITensorManifestArtifactCheck.check input files
  let mut candidates : Array StoredZIP.ArchiveCertificateCheck.Candidate := #[]
  for (member, i) in Archive.members.zipIdx do
    let name := `Rumoca.CheckedTensorEFMIArchive |>.str s!"code_{i}"
    StoredZIP.CertificateCheck.certifyCRC name (code.text member)
    candidates := candidates.push ⟨member.name, code.text member, name⟩
  for (resource, i) in Resources.schemas.zipIdx do
    candidates := candidates.push ⟨resource.name, resource.text,
      `Rumoca.EFMI.SchemaCertificates |>.str s!"resource_{i}"⟩
  let archiveName := `Rumoca.CheckedTensorEFMIArchive
  StoredZIP.ArchiveCertificateCheck.certify archiveName bytes candidates
  let algorithm := Syntax.mkStrLit code.algorithm
  let production := Syntax.mkStrLit code.production
  let algorithmXML := Syntax.mkStrLit code.algorithmXML
  let productionXML := Syntax.mkStrLit code.productionXML
  let contentXML := Syntax.mkStrLit code.contentXML
  let codeName := mkIdent (archiveName.str "code")
  let entries := mkIdent (archiveName.str "entries_0")
  let archiveBytes := mkIdent (archiveName.str "bytes")
  let transport := mkIdent (archiveName.str "conforms")
  let entriesEq := mkIdent (archiveName.str "entries_eq")
  elabCommand (← `(command| def $codeName:ident : Archive.Code :=
    ⟨$algorithm, $production, $algorithmXML, $productionXML, $contentXML⟩))
  elabCommand (← `(command| theorem $entriesEq:ident : $entries = Archive.entries $codeName := rfl))
  let inputTerm ← input.inputTerm
  let grammar := Syntax.mkStrLit input.grammar
  let galecGrammar := Syntax.mkStrLit input.galecGrammar
  let identity := mkIdent `Rumoca.CheckedTensorEFMIFiles.manifest_identity
  let manifests := mkIdent `Rumoca.CheckedTensorEFMIFiles.source_to_manifests
  let rootName := `Rumoca.CheckedTensorEFMIFiles.source_to_archive
  let root := mkIdent rootName
  elabCommand (← `(command| theorem $root:ident :
      Generated.source = $grammar ∧ GALEC.Generated.source = $galecGrammar ∧
      ∃ a : TensorArtifact $inputTerm, compileTensor $inputTerm = .ok a ∧
        TensorArchiveContract a $identity $archiveBytes := by
    obtain ⟨g₁, g₂, a, compiled, manifests⟩ := $manifests:ident
    have archive := tensor_archive_correct a $identity $codeName manifests
      ($entriesEq:ident ▸ $transport:ident)
    exact ⟨g₁, g₂, a, compiled, archive⟩))
  if (← get).messages.hasErrors then throwError "tensor source-to-archive certificate failed"
  let dependencies ← collectAxioms rootName
  for dependency in dependencies do
    unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
      throwError "unapproved axiom in tensor archive contract: {dependency}"
  logInfo m!"{rootName} depends on axioms: {dependencies.toList}"

end Rumoca.EFMITensorArchiveArtifactCheck
