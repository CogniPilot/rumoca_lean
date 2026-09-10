import RumocaEFMI.CInterface
import RumocaEFMI.AlgorithmProofs
import ProofAudit.Audit
import RumocaEFMI.CSyntaxProofs
import RumocaEFMI.CProtocol
import RumocaEFMI.ZIPProofs
import RumocaEFMI.MetadataProofs
import RumocaEFMI.ManifestProofs
import RumocaEFMI.ArchiveProofs
import RumocaEFMI.ZIPCertificate
import RumocaEFMI.ZIPArchiveCertificate
import RumocaEFMISchemaCertificates

namespace Rumoca.EFMI.ProductionChecks
private local instance targetInterface : CInterface := cInterface

theorem reserved_identifier_rejected : CSyntax.identifier "while" = false := by decide +kernel

theorem literal_assignment_rejected :
    (CSyntax.Statement.assign .zero (.atom .one)).valid = false := rfl

theorem tensor_fill_not_scalarized :
    CAlgorithm.emitProgram
      (Solve.Algorithm.Program.fill (shape := ⟨[2, 3]⟩) .one
        (.ret (.there .here)) : Solve.Algorithm.Program [Tensor.scalar] Tensor.scalar)
      (Production.initialName "x") (Production.stateField "x") 0 =
        .error "Production C storage currently requires rank-zero tensors" := by rfl

#audit axioms Solve.Algorithm.Model.block_is_unit
#audit axioms Production.lower_is_unit
#audit axioms Production.parameters_checked
#audit axioms Production.return_checked
#audit axioms CHeader.interface_alias
#audit axioms CHeader.interface_return
#audit axioms CHeader.header_declares
#audit axioms CHeader.render_contract
#audit axioms CHeader.real_alias
#audit axioms CHeader.status_alias
#audit axioms CHeader.model_fields
#audit axioms CHeader.success_return
#audit axioms CArithmetic.floatAdd_finite
#audit axioms CArithmetic.floatAdd_one
#audit axioms CArithmetic.behaviors_of_run
#audit axioms Production.startup_run
#audit axioms Production.recalibrate_run
#audit axioms Production.doStep_run
#audit axioms Production.method_correct
#audit axioms Production.result_represents
#audit axioms Production.result_frame
#audit axioms Production.result_other_instance
#audit axioms Production.read_output
#audit axioms CSyntax.render_unit
#audit axioms CSyntax.atom_render
#audit axioms CSyntax.term_render
#audit axioms CSyntax.statement_render
#audit axioms CSyntax.statements_render
#audit axioms CSyntax.function_render
#audit axioms CSyntax.program_render
#audit axioms CSyntax.print_denotes
#audit axioms CProtocol.step_sound
#audit axioms CProtocol.step_complete
#audit axioms CProtocol.trace_sound
#audit axioms CProtocol.trace_complete
#audit axioms Metadata.algorithm_variables
#audit axioms Metadata.references_unique
#audit axioms Metadata.functions_correct
#audit axioms Metadata.read_correct
#audit axioms Metadata.execution_preserves
#audit axioms Metadata.correct
#audit axioms Manifest.decode_dataMapping
#audit axioms Manifest.decode_function
#audit axioms Manifest.data_nodes
#audit axioms Manifest.function_nodes
#audit axioms Manifest.variable_declared
#audit axioms Manifest.mapped_execution
#audit axioms Manifest.file_checksum
#audit axioms Manifest.origin_reference
#audit axioms Manifest.representation_reference
#audit axioms Manifest.prepare_graph
#audit axioms Manifest.prepare_named
#audit axioms Manifest.Identity.matches_length
#audit axioms Manifest.Identity.uuid_length
#audit axioms Manifest.Identity.calendar_date
#audit axioms Manifest.Identity.utc_fields
#audit axioms Manifest.Identity.valid_iff
#audit axioms Manifest.Identity.valid_distinct
#audit axioms Manifest.prepare_identified
#audit axioms Manifest.documents_valid
#audit axioms Manifest.checked_correct
#audit axioms Archive.entry_names
#audit axioms Archive.paths_unique
#audit axioms Archive.member_count
#audit axioms Archive.lookup_of_mem
#audit axioms Archive.code_lookup
#audit axioms Archive.schema_lookup
#audit axioms Archive.encode_correct
#audit axioms StoredZIP.encode_sound
#audit axioms StoredZIP.encode_complete
#audit axioms StoredZIP.decode_sound
#audit axioms StoredZIP.check_accepts_iff
#audit axioms StoredZIP.Format.number_value
#audit axioms StoredZIP.Format.conforms_names_unique
#audit axioms StoredZIP.Format.conforms_entries_fit
#audit axioms StoredZIP.Format.conforms_member
#audit axioms StoredZIP.Format.conforms_bytes_unique
#audit axioms StoredZIP.Certificate.utf8_of_chars
#audit axioms StoredZIP.Certificate.encode_cons
#audit axioms StoredZIP.Certificate.crc_cons
#audit axioms StoredZIP.Certificate.crc_of_bytes
#audit axioms StoredZIP.Certificate.localRecord_parts
#audit axioms StoredZIP.Certificate.centralRecord_parts
#audit axioms StoredZIP.Certificate.local_cons
#audit axioms StoredZIP.Certificate.directory_cons
#audit axioms StoredZIP.Certificate.archive
#audit axioms StoredZIP.Certificate.Text.byteSize
#audit axioms StoredZIP.Certificate.Text.entryFits
#audit axioms StoredZIP.Certificate.append_length
#audit axioms StoredZIP.Certificate.append_equal
#audit axioms StoredZIP.Certificate.entry_fits_cons
#audit axioms reserved_identifier_rejected
#audit axioms literal_assignment_rejected
#audit axioms tensor_fill_not_scalarized

end Rumoca.EFMI.ProductionChecks

#audit axioms Rumoca.EFMI.grammar_processed

#audit axioms Rumoca.EFMI.render_denotes
