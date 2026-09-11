import Rumoca.EFMIManifestProofs
import RumocaEFMI.ArchiveProofs
import Rumoca.EFMIArchive

namespace Rumoca.EFMI

/-- One complete archive contains the same code/XML strings covered by the
source/DAE/GALEC/Solve/C contract, plus the exact pinned schema resources.
This is the authored stored-ZIP and manifest profile. General XSD semantics,
physical C compilation and full prose-standard conformance remain separate. -/
def ArchiveContract (a : Artifact source) (identity : Manifest.Identity) (bytes : ByteArray) : Prop :=
  ∃ code : Archive.Code,
    ManifestContract a identity code.algorithm code.production
      code.algorithmXML code.productionXML code.contentXML ∧
    StoredZIP.Format.Conforms (Archive.entries code) bytes

theorem archive_correct (a : Artifact source) (identity : Manifest.Identity) (code : Archive.Code)
    (manifests : ManifestContract a identity code.algorithm code.production
      code.algorithmXML code.productionXML code.contentXML)
    (transport : StoredZIP.Format.Conforms (Archive.entries code) bytes) :
    ArchiveContract a identity bytes := ⟨code, manifests, transport⟩

/-- The executable preparation function retains the source, execution and
manifest contracts for every successful result, including checked identities. -/
theorem archive_code_correct (a : Artifact source) (identity : Manifest.Identity)
    (h : a.archiveCode identity = .ok code) :
    ManifestContract a identity code.algorithm code.production
      code.algorithmXML code.productionXML code.contentXML := by
  simp only [Artifact.archiveCode, Production.StartupMap.emit_is_unit,
    Production.StartupMap.Emission.document_render, bind, Except.bind] at h
  cases checked : Manifest.checked a.parsed.ast.name identity a.algorithmSource Production.unitModule with
  | error error => simp [checked] at h
  | ok documents =>
    simp only [checked, pure, Except.pure] at h
    cases Except.ok.inj h
    have facts := Manifest.checked_correct _ _ _ _ documents checked
    apply manifests_correct a identity facts.1
      (production_correct a (algorithm_correct a rfl) (production_source_is_unit a))
    · rw [← facts.2.1]; exact documents.property
    · rw [← facts.2.1]
    · rw [← facts.2.1]
    · rw [← facts.2.1]

/-- The pure archive generator preserves the complete authored contract.
The later file adapter must still bind a physical archive to this endpoint. -/
theorem efmu_archive_correct (a : Artifact source) (identity : Manifest.Identity)
    (h : a.efmuArchive identity = .ok bytes) : ArchiveContract a identity bytes := by
  cases prepared : a.archiveCode identity with
  | error error => simp [Artifact.efmuArchive, prepared, bind, Except.bind] at h
  | ok code =>
    apply archive_correct a identity code (archive_code_correct a identity prepared)
    apply Archive.encode_correct code
    simpa only [Artifact.efmuArchive, prepared, bind, Except.bind] using h

theorem compile_archive_verified (compiled : compile source = .ok a)
    (emitted : a.efmuArchive identity = .ok bytes) :
    compile source = .ok a ∧ ArchiveContract a identity bytes :=
  ⟨compiled, efmu_archive_correct a identity emitted⟩

/-- Every code/XML member's exact bytes occur in the actual archive, with the
same manifest contract providing its source and execution interpretation. -/
theorem ArchiveContract.code_members (h : ArchiveContract a identity bytes) :
    ∃ code : Archive.Code,
      ManifestContract a identity code.algorithm code.production
        code.algorithmXML code.productionXML code.contentXML ∧
      ∀ member : Archive.Member,
        Archive.lookup (Archive.entries code) member.name = some (code.text member).toUTF8 ∧
        ∃ before after : List UInt8, bytes.data.toList = before ++
          StoredZIP.Format.localRecord ⟨member.name, (code.text member).toUTF8⟩ ++ after := by
  obtain ⟨code, manifests, transport⟩ := h
  exact ⟨code, manifests, fun member => ⟨Archive.code_lookup code member,
    StoredZIP.Format.conforms_member transport (Archive.code_mem code member)⟩⟩

theorem ArchiveContract.schema_members (h : ArchiveContract a identity bytes)
    (resource : Resources.Resource) (mem : resource ∈ Resources.schemas) :
    ∃ before after : List UInt8, bytes.data.toList = before ++
      StoredZIP.Format.localRecord ⟨resource.name, resource.text.toUTF8⟩ ++ after := by
  obtain ⟨code, _, transport⟩ := h
  exact StoredZIP.Format.conforms_member transport (Archive.schema_mem code resource mem)

/-- The conformance relation licenses exactly the fixed roster, with unique
paths; extra files cannot be appended to a certified member sequence. -/
theorem ArchiveContract.roster (h : ArchiveContract a identity bytes) :
    ∃ items : List StoredZIP.Entry,
      StoredZIP.Format.Conforms items bytes ∧ items.map StoredZIP.Entry.name = Archive.paths ∧
      (items.map StoredZIP.Entry.name).Nodup ∧ items.length = 50 := by
  obtain ⟨code, _, transport⟩ := h
  exact ⟨Archive.entries code, transport, Archive.entry_names code,
    StoredZIP.Format.conforms_names_unique transport, Archive.member_count code⟩

end Rumoca.EFMI
