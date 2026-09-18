import Rumoca.EFMITensorArchive
import RumocaEFMI.ArchiveProofs
import RumocaEFMI.TensorManifestProofs
import RumocaEFMI.TensorProductionProofs

/-! Composed contracts and archive theorem for the frozen tensor eFMU. The
tensor square Algorithm Code, the certified-kernel Production Code and the three
manifests are the same code/XML strings covered by the tensor source/kernel and
manifest contracts, packed by the shared stored-ZIP generator with the exact
pinned schema resources. The archive theorem (member roster, checksums,
container-manifest correlation and stored-ZIP bytes) is universal in the
packaging identity and the model name. General XSD semantics, physical C
compilation and full prose-standard conformance remain separate layers. -/
namespace Rumoca
open EFMI

/-- The tensor Algorithm Code member contract: the emitted bytes are the pinned
tensor square Algorithm Code, and that text parses to the resolved tensor block
denoting the artifact's prepared kernel. -/
structure TensorAlgorithmContract (a : TensorArtifact input) (emitted : String) : Prop where
  bytes : EFMI.tensorUnitSource = emitted
  parsed : ∃ p, GALEC.Syntax.parseTensor emitted = .ok p ∧
    EFMI.TensorDenotes p.ast a.prepared.kernel

/-- The tensor Production Code member contract: the emitted translation unit is
the certified-kernel tensor Production Code, so the derivative method computes the
prepared derivative, the Jacobian output computes the doubled input, and the
certified tensor C artifact contract holds, universal in the state shape. -/
structure TensorProductionContract (a : TensorArtifact input) (algorithm c : String) : Prop where
  algorithm_contract : TensorAlgorithmContract a algorithm
  bytes : EFMI.TensorProduction.render = c
  code : EFMI.TensorProduction.Contract c

/-- The tensor manifest member contract: the actual Algorithm/Production/container
XML strings are the serialized tensor manifests of the artifact's model name and
the packaging identity, they lie in the checked XML output grammar, and the origin
reference hashes the serialized Algorithm Code manifest. -/
structure TensorManifestContract (a : TensorArtifact input) (identity : Manifest.Identity)
    (algorithm c algorithmXML productionXML contentXML : String) : Prop where
  identity_valid : identity.Valid
  code : TensorProductionContract a algorithm c
  algorithmXMLBytes :
    XML.document (TensorManifest.prepare a.name identity EFMI.tensorUnitSource).algorithm = algorithmXML
  productionXMLBytes :
    XML.document (TensorManifest.prepare a.name identity EFMI.tensorUnitSource).production = productionXML
  contentXMLBytes :
    XML.document (TensorManifest.prepare a.name identity EFMI.tensorUnitSource).content = contentXML
  valid : (TensorManifest.prepare a.name identity EFMI.tensorUnitSource).valid = true
  wellformed_algorithm :
    XML.Document (TensorManifest.prepare a.name identity EFMI.tensorUnitSource).algorithm algorithmXML
  wellformed_production :
    XML.Document (TensorManifest.prepare a.name identity EFMI.tensorUnitSource).production productionXML
  wellformed_content :
    XML.Document (TensorManifest.prepare a.name identity EFMI.tensorUnitSource).content contentXML
  origin_checksum : ∃ origin,
    Manifest.select (TensorManifest.prepare a.name identity EFMI.tensorUnitSource).production
      ["ManifestReferences", "ManifestReference"] = [origin] ∧
    origin.attributes.lookup "checksum" =
      some (SHA1.hash (XML.document
        (TensorManifest.prepare a.name identity EFMI.tensorUnitSource).algorithm).toUTF8)

/-- The pinned tensor Algorithm Code of a square artifact parses to the resolved
tensor block denoting its prepared kernel. -/
theorem tensor_algorithm_correct (a : TensorArtifact input)
    (hast : a.prepared.parsed.parsed.ast = squareAst) (he : EFMI.tensorUnitSource = emitted) :
    TensorAlgorithmContract a emitted := by
  subst he
  refine ⟨rfl, ?_⟩
  obtain ⟨p, hp, hd⟩ := (squareAlgorithmArtifact a hast).algorithm_correct
  exact ⟨p, hp, hd⟩

/-- The certified-kernel tensor Production Code satisfies its contract. -/
theorem tensor_production_correct (a : TensorArtifact input)
    (alg : TensorAlgorithmContract a algorithm) (hc : EFMI.TensorProduction.render = c) :
    TensorProductionContract a algorithm c :=
  ⟨alg, hc, EFMI.TensorProduction.production_correct c hc.symm⟩

/-- Compose independently checked document facts (well-formedness, validity and
the checksum graph) into the manifest contract without renormalizing the checksum
dependency graph at each field. -/
theorem tensor_manifests_correct_of_documents (a : TensorArtifact input)
    (identity : Manifest.Identity) (identityValid : identity.Valid)
    (code : TensorProductionContract a algorithm c)
    (algorithmTree productionTree contentTree : XML.Element)
    (graph : TensorManifest.prepare a.name identity EFMI.tensorUnitSource =
      TensorManifest.Documents.mk algorithmTree productionTree contentTree)
    (valid : (TensorManifest.Documents.mk algorithmTree productionTree contentTree).valid = true)
    (algorithmBytes : XML.document algorithmTree = algorithmXML)
    (productionBytes : XML.document productionTree = productionXML)
    (contentBytes : XML.document contentTree = contentXML) :
    TensorManifestContract a identity algorithm c algorithmXML productionXML contentXML := by
  have wf := TensorManifest.documents_valid _ valid
  have checks := (TensorManifest.prepare_checksums a.name identity EFMI.tensorUnitSource).1
  exact {
    identity_valid := identityValid
    code := code
    algorithmXMLBytes := by rw [graph]; exact algorithmBytes
    productionXMLBytes := by rw [graph]; exact productionBytes
    contentXMLBytes := by rw [graph]; exact contentBytes
    valid := by rw [graph]; exact valid
    wellformed_algorithm := by rw [graph]; exact algorithmBytes ▸ wf.1
    wellformed_production := by rw [graph]; exact productionBytes ▸ wf.2.1
    wellformed_content := by rw [graph]; exact contentBytes ▸ wf.2.2
    origin_checksum := checks }

/-- One complete tensor archive contains the same code/XML strings covered by the
tensor source/kernel and manifest contracts, plus the exact pinned schema
resources, packed by the shared stored-ZIP generator. -/
def TensorArchiveContract (a : TensorArtifact input) (identity : Manifest.Identity)
    (bytes : ByteArray) : Prop :=
  ∃ code : Archive.Code,
    TensorManifestContract a identity code.algorithm code.production
      code.algorithmXML code.productionXML code.contentXML ∧
    StoredZIP.Format.Conforms (Archive.entries code) bytes

theorem tensor_archive_correct (a : TensorArtifact input) (identity : Manifest.Identity)
    (code : Archive.Code)
    (manifests : TensorManifestContract a identity code.algorithm code.production
      code.algorithmXML code.productionXML code.contentXML)
    (transport : StoredZIP.Format.Conforms (Archive.entries code) bytes) :
    TensorArchiveContract a identity bytes := ⟨code, manifests, transport⟩

/-- Every code/XML member's exact bytes occur in the actual tensor archive, with
the manifest contract providing its source and kernel interpretation. -/
theorem TensorArchiveContract.code_members (h : TensorArchiveContract a identity bytes) :
    ∃ code : Archive.Code,
      TensorManifestContract a identity code.algorithm code.production
        code.algorithmXML code.productionXML code.contentXML ∧
      ∀ member : Archive.Member,
        Archive.lookup (Archive.entries code) member.name = some (code.text member).toUTF8 ∧
        ∃ before after : List UInt8, bytes.data.toList = before ++
          StoredZIP.Format.localRecord ⟨member.name, (code.text member).toUTF8⟩ ++ after := by
  obtain ⟨code, manifests, transport⟩ := h
  exact ⟨code, manifests, fun member => ⟨Archive.code_lookup code member,
    StoredZIP.Format.conforms_member transport (Archive.code_mem code member)⟩⟩

theorem TensorArchiveContract.schema_members (h : TensorArchiveContract a identity bytes)
    (resource : Resources.Resource) (mem : resource ∈ Resources.schemas) :
    ∃ before after : List UInt8, bytes.data.toList = before ++
      StoredZIP.Format.localRecord ⟨resource.name, resource.text.toUTF8⟩ ++ after := by
  obtain ⟨code, _, transport⟩ := h
  exact StoredZIP.Format.conforms_member transport (Archive.schema_mem code resource mem)

/-- The conformance relation licenses exactly the fixed roster, with unique
paths; extra files cannot be appended to a certified member sequence. -/
theorem TensorArchiveContract.roster (h : TensorArchiveContract a identity bytes) :
    ∃ items : List StoredZIP.Entry,
      StoredZIP.Format.Conforms items bytes ∧ items.map StoredZIP.Entry.name = Archive.paths ∧
      (items.map StoredZIP.Entry.name).Nodup ∧ items.length = 50 := by
  obtain ⟨code, _, transport⟩ := h
  exact ⟨Archive.entries code, transport, Archive.entry_names code,
    StoredZIP.Format.conforms_names_unique transport, Archive.member_count code⟩

end Rumoca
