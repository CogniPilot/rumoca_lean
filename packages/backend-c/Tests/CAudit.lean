import ProofAudit.Audit
import RumocaC.TreePreprocessing
import RumocaC.Initialization
import RumocaC.InitializationOriginProofs
import RumocaC.InitializationMap
import RumocaC.MappedFunction
import RumocaC.Lowering
import RumocaC.Statements
import RumocaC.Calls
import RumocaC.Arithmetic
import RumocaC.BooleanProofs
import RumocaC.BodyEmbedding
import RumocaC.StringLiteral
import RumocaC.LiteralStorage
import RumocaC.LiteralPointers
import RumocaC.LiteralLowering
import RumocaC.LiteralCallLowering
import RumocaC.LiteralPoolLowering
import RumocaC.TreeLexical
import RumocaC.Decimal
import RumocaC.LiteralDeclarationBlock
import RumocaC.LiteralCollection
import RumocaC.LiteralNames

#audit axioms Rumoca.CTree.Preprocessing.unspliced_append
#audit axioms Rumoca.CTree.Preprocessing.Stable.append
#audit axioms Rumoca.CTree.Preprocessing.plain_stable
#audit axioms Rumoca.CTree.Preprocessing.ascii_unspliced
#audit axioms Rumoca.CTree.Preprocessing.quote_stable
#audit axioms Rumoca.CTree.Preprocessing.Stable.no_rewrite
#audit axioms Rumoca.CTree.Preprocessing.Stable.preprocessed
#audit axioms Rumoca.CTree.Preprocessing.Stable.join
#audit axioms Rumoca.CTree.Preprocessing.Stable.intercalate
#audit axioms Rumoca.CTree.Preprocessing.natural_stable
#audit axioms Rumoca.CTree.Preprocessing.binOp_stable
#audit axioms Rumoca.CTree.Preprocessing.expression_stable
#audit axioms Rumoca.CTree.Preprocessing.expression_preprocessed
#audit axioms Rumoca.CTree.Preprocessing.indent_stable
#audit axioms Rumoca.CTree.Preprocessing.statement_stable
#audit axioms Rumoca.CTree.Preprocessing.parameter_stable
#audit axioms Rumoca.CTree.Preprocessing.signature_stable
#audit axioms Rumoca.CTree.Preprocessing.function_stable
#audit axioms Rumoca.CTree.Preprocessing.function_preprocessed

#audit axioms Rumoca.CLiteral.Declaration.denotes_unique
#audit axioms Rumoca.CTree.Stmt.Origins.every_root
#audit axioms Rumoca.Printed.Document.render_join
#audit axioms Rumoca.Printed.Document.join_every
#audit axioms Rumoca.Printed.Document.every_if
#audit axioms Rumoca.CTree.Stmt.Origins.document_render
#audit axioms Rumoca.CTree.Stmt.Origins.documents_render
#audit axioms Rumoca.CTree.Stmt.Origins.root_region
#audit axioms Rumoca.CTree.Stmt.Origins.document_every
#audit axioms Rumoca.CTree.Stmt.Origins.documents_every
#audit axioms Rumoca.CTree.Stmt.Origins.map_exact
#audit axioms Rumoca.CTree.Stmt.Origins.map_every
#audit axioms Rumoca.CTree.Parameter.Origins.document_render
#audit axioms Rumoca.CTree.Parameter.Origins.document_every
#audit axioms Rumoca.CTree.Parameter.Origins.documentsTail_render
#audit axioms Rumoca.CTree.Parameter.Origins.documents_render
#audit axioms Rumoca.CTree.Parameter.Origins.documentsTail_every
#audit axioms Rumoca.CTree.Parameter.Origins.documents_every
#audit axioms Rumoca.CTree.Signature.Origins.document_render
#audit axioms Rumoca.CTree.Signature.Origins.document_every
#audit axioms Rumoca.CTree.Function.Origins.document_render
#audit axioms Rumoca.CTree.Function.Origins.document_every
#audit axioms Rumoca.CTree.Function.Origins.root_region
#audit axioms Rumoca.CTree.Function.Origins.map_exact
#audit axioms Rumoca.CTree.Function.Origins.map_every
#audit axioms Rumoca.Printed.Doc.render_size
#audit axioms Rumoca.Printed.Doc.entriesInto_eq
#audit axioms Rumoca.Printed.Region.render_eq
#audit axioms Rumoca.Printed.Region.bytes
#audit axioms Rumoca.Printed.Region.mem_entries
#audit axioms Rumoca.Printed.Doc.entries_region
#audit axioms Rumoca.Printed.Doc.map_iff
#audit axioms Rumoca.Printed.Doc.map_bounds
#audit axioms Rumoca.Printed.Region.origin_checked
#audit axioms Rumoca.Printed.Doc.map_every
#audit axioms Rumoca.CTree.Expr.Origins.document_render
#audit axioms Rumoca.CTree.Expr.Origins.root_region
#audit axioms Rumoca.CTree.Expr.Origins.map_exact
#audit axioms Rumoca.CTree.Expr.Origins.document_every
#audit axioms Rumoca.CInitialization.Emission.document_render
#audit axioms Rumoca.CInitialization.Emission.write_region
#audit axioms Rumoca.CInitialization.Emission.target_region
#audit axioms Rumoca.CInitialization.Emission.value_region
#audit axioms Rumoca.CInitialization.Emission.value_literal_region
#audit axioms Rumoca.CInitialization.Emission.literal_region
#audit axioms Rumoca.CInitialization.Emission.document_every
#audit axioms Rumoca.CInitialization.Emission.map_origins
#audit axioms Rumoca.CInitialization.Emission.map_ancestry
#audit axioms Rumoca.CInitialization.Emission.map_exact
#audit axioms Rumoca.CInitialization.Emission.printed_preserves
#audit axioms Rumoca.CInitialization.value_zero
#audit axioms Rumoca.CInitialization.value_printed
#audit axioms Rumoca.CInitialization.value_evaluated
#audit axioms Rumoca.CInitialization.write_step
#audit axioms Rumoca.CInitialization.written_frame
#audit axioms Rumoca.CInitialization.write_behaviors
#audit axioms Rumoca.CTree.Expr.Origins.uniform_root
#audit axioms Rumoca.CTree.Expr.Origins.uniform_every
#audit axioms Rumoca.CTree.Expr.Origins.uniformList_every
#audit axioms Rumoca.CTree.Expr.Origins.every_root
#audit axioms Rumoca.CTree.Expr.Origins.every_mono
#audit axioms Rumoca.CTree.Expr.Origins.everyList_mono
#audit axioms Rumoca.CProvenance.fromCore_traces_iff
#audit axioms Rumoca.CInitialization.Emission.trace_correct
#audit axioms Rumoca.CInitialization.emit_trace_correct
#audit axioms Rumoca.CInitialization.Origins.initial_ancestry
#audit axioms Rumoca.CInitialization.Origins.conversion_ancestry
#audit axioms Rumoca.CInitialization.Origins.target_ancestry
#audit axioms Rumoca.CInitialization.Origins.write_ancestry
#audit axioms Rumoca.CInitialization.Emission.preserves
#audit axioms Rumoca.CLiteral.Declaration.render_ascii
#audit axioms Rumoca.CLiteral.Declaration.render_safe
#audit axioms Rumoca.CLiteral.Declaration.render_preprocessed
#audit axioms Rumoca.CLiteral.Declaration.render_denotes
#audit axioms Rumoca.CLiteral.Declaration.render_correct
#audit axioms Rumoca.CLiteral.Declaration.render_storage
#audit axioms Rumoca.CLiteral.Declaration.block_unique
#audit axioms Rumoca.CLiteral.Declaration.renderBlock_chars
#audit axioms Rumoca.CLiteral.Declaration.renderBlock_denotes
#audit axioms Rumoca.CLiteral.Declaration.splice_append
#audit axioms Rumoca.CLiteral.Declaration.renderBlock_safe
#audit axioms Rumoca.CLiteral.Declaration.renderBlock_preprocessed
#audit axioms Rumoca.CLiteral.Declaration.renderBlock_correct
#audit axioms Rumoca.CLiteral.Declaration.renderBlock_storage
#audit axioms Rumoca.CLiteral.expressionTexts_lowered
#audit axioms Rumoca.CLiteral.statementTexts_lowered
#audit axioms Rumoca.CLiteral.functionTexts_lowered
#audit axioms Rumoca.CLiteral.Pool.forFunctions_coverage
#audit axioms Rumoca.CLiteral.Pool.forFunctions_complete
#audit axioms Rumoca.CLiteral.Pool.forFunctions_behaviors
#audit axioms Rumoca.CLiteral.Pool.make_spelling
#audit axioms Rumoca.CLiteral.Pool.make_name_conditions
#audit axioms Rumoca.CLiteral.Pool.headerFresh_of_reserved

#audit axioms Rumoca.CString.denotes_unique
#audit axioms Rumoca.CTree.Syntax.lex_identifier
#audit axioms Rumoca.CTree.Syntax.lex_natural
#audit axioms Rumoca.CDecimal.digits_value
#audit axioms Rumoca.CDecimal.render_denotes
#audit axioms Rumoca.CDecimal.denotes_unique
#audit axioms Rumoca.CString.quote_iff
#audit axioms Rumoca.CString.quote_preprocessed
#audit axioms Rumoca.CString.render_correct
#audit axioms Rumoca.CCharacter.value_byteOf
#audit axioms Rumoca.CReadOnly.body_reaches
#audit axioms Rumoca.CReadOnly.loop_reaches
#audit axioms Rumoca.CReadOnly.typed_reaches
#audit axioms Rumoca.CReadOnly.typed_load
#audit axioms Rumoca.CLiteral.installed
#audit axioms Rumoca.CLiteral.install_preserves
#audit axioms Rumoca.CLiteral.rendered_memory
#audit axioms Rumoca.CLiteral.Stored.after_steps
#audit axioms Rumoca.CLiteral.eval_string
#audit axioms Rumoca.CLiteral.eval_string_missing
#audit axioms Rumoca.CLiteral.pointer_argument
#audit axioms Rumoca.CLiteral.eval_index
#audit axioms Rumoca.CLiteral.rendered_pointer
#audit axioms Rumoca.CLiteral.Valid.after_steps
#audit axioms Rumoca.CLiteral.Lowering.expression_correct
#audit axioms Rumoca.CLiteral.Lowering.arguments_correct
#audit axioms Rumoca.CLiteral.Lowering.body_next
#audit axioms Rumoca.CLiteral.Lowering.body_run
#audit axioms Rumoca.CLiteral.Lowering.body_terminates
#audit axioms Rumoca.CLiteral.Lowering.body_behaviors
#audit axioms Rumoca.CLiteral.Lowering.loop_expression_correct
#audit axioms Rumoca.CLiteral.Lowering.noDeclarations_lowered
#audit axioms Rumoca.CLiteral.Lowering.loop_safe_next
#audit axioms Rumoca.CLiteral.Lowering.loop_next
#audit axioms Rumoca.CLiteral.Lowering.loop_behaviors
#audit axioms Rumoca.CLiteral.Lowering.callOperand_lowered
#audit axioms Rumoca.CLiteral.Lowering.parameter_bindings
#audit axioms Rumoca.CLiteral.Lowering.enterCall_lowered
#audit axioms Rumoca.CLiteral.Lowering.resume_lowered
#audit axioms Rumoca.CLiteral.Lowering.next_lowered
#audit axioms Rumoca.CLiteral.Lowering.next_safe
#audit axioms Rumoca.CLiteral.Lowering.call_behaviors
#audit axioms Rumoca.CLiteral.Lowering.invocation_behaviors
#audit axioms Rumoca.CLiteral.Interface.expression_agreement
#audit axioms Rumoca.CLiteral.Interface.loop_expression_agreement
#audit axioms Rumoca.CLiteral.Interface.extend_existing
#audit axioms Rumoca.CLiteral.Interface.expression_extended
#audit axioms Rumoca.CLiteral.Interface.next_agreement
#audit axioms Rumoca.CLiteral.Interface.next_agrees
#audit axioms Rumoca.CLiteral.Interface.call_behaviors
#audit axioms Rumoca.CLiteral.Interface.invocation_behaviors
#audit axioms Rumoca.CLiteral.Pool.entry_valid
#audit axioms Rumoca.CLiteral.Pool.entry_fresh
#audit axioms Rumoca.CLiteral.Pool.noIntrinsic
#audit axioms Rumoca.CLiteral.Pool.global_binding
#audit axioms Rumoca.CLiteral.Pool.globals_fresh
#audit axioms Rumoca.CLiteral.Pool.make_coverage
#audit axioms Rumoca.CLiteral.Pool.blocks_unique
#audit axioms Rumoca.CLiteral.Pool.installed
#audit axioms Rumoca.CLiteral.Pool.storage_valid
#audit axioms Rumoca.CLiteral.Pool.install_existing
#audit axioms Rumoca.CLiteral.Pool.install_preserves
#audit axioms Rumoca.CLiteral.Pool.globalBindings
#audit axioms Rumoca.CLiteral.Pool.reserved_agreement
#audit axioms Rumoca.CLiteral.Pool.storage_after_steps
#audit axioms Rumoca.CLiteral.Pool.statement_safe
#audit axioms Rumoca.CLiteral.collected_names_cover
#audit axioms Rumoca.CLiteral.Pool.program_agrees
#audit axioms Rumoca.CLiteral.Pool.program_safe
#audit axioms Rumoca.CLiteral.Pool.invocation_behaviors

#audit axioms Rumoca.C.compileProgram_correct
#audit axioms Rumoca.C.ideal_run_correct
#audit axioms Rumoca.C.sample_correct
#audit axioms Rumoca.C.sample_deterministic
#audit axioms Rumoca.C.emission_is_unit
#audit axioms Rumoca.CSyntax.expression_render
#audit axioms Rumoca.CSyntax.module_render
#audit axioms Rumoca.CSyntax.lexes_unique
#audit axioms Rumoca.CSyntax.expression_tokens_unique
#audit axioms Rumoca.CSyntax.program_tokens_unique
#audit axioms Rumoca.CSyntax.denotes_unique
#audit axioms Rumoca.CExecution.rhs_eval
#audit axioms Rumoca.CExecution.step_eval
#audit axioms Rumoca.CExecution.step_deterministic
#audit axioms Rumoca.CExecution.sample_reaches
#audit axioms Rumoca.CExecution.sample_accessible
#audit axioms Rumoca.CExecution.sample_all_executions
#audit axioms Rumoca.CExecution.sample_result_unique
#audit axioms Rumoca.CExecution.counter_in_range
#audit axioms Rumoca.C.lower_correct
#audit axioms Rumoca.C.lower_binary64_correct
#audit axioms Rumoca.CSyntax.lower_correct
#audit axioms Rumoca.CStatements.decrement_positive
#audit axioms Rumoca.CStatements.lower_scoped
#audit axioms Rumoca.CStatements.denotes_statements
#audit axioms Rumoca.CStatements.lower_correct
#audit axioms Rumoca.CStatements.behaviors_correct
#audit axioms Rumoca.CStatements.all_terminate
#audit axioms Rumoca.CStatements.all_complete
#audit axioms Rumoca.CStatements.unbound_rhs_stuck
#audit axioms Rumoca.CMemory.Value.isFinite_finite
#audit axioms Rumoca.CMemory.store_float64
#audit axioms Rumoca.CMemory.store_frame
#audit axioms Rumoca.CMemory.store_other_block
#audit axioms Rumoca.CMemory.store_unallocated
#audit axioms Rumoca.CMemory.store_readonly
#audit axioms Rumoca.CBody.run_reaches
#audit axioms Rumoca.CBody.run_add
#audit axioms Rumoca.CBody.behaviors_of_run
#audit axioms Rumoca.CBody.BoolProofs.eval_and
#audit axioms Rumoca.CBody.BoolProofs.eval_or
#audit axioms Rumoca.CBody.BoolProofs.eval_not
#audit axioms Rumoca.CCalls.finiteValue_finite
#audit axioms Rumoca.CCalls.counterValue_counter
#audit axioms Rumoca.CCalls.cast_counter
#audit axioms Rumoca.CCalls.tree_entry
#audit axioms Rumoca.CCalls.run_reaches
#audit axioms Rumoca.CCalls.behaviors_of_run
#audit axioms Rumoca.CCalls.body_step
#audit axioms Rumoca.CCalls.body_reaches
#audit axioms Rumoca.CCalls.body_behaviors
#audit axioms Rumoca.CCalls.kernel_step
#audit axioms Rumoca.CCalls.kernel_reaches
#audit axioms Rumoca.CCalls.kernel_correct
#audit axioms Rumoca.CBody.truth_boolean
#audit axioms Rumoca.CMemory.Address.member_inj
#audit axioms Rumoca.CCalls.body_behaviors_of_reaches
#audit axioms Rumoca.CArithmetic.floatAdd_finite
#audit axioms Rumoca.CArithmetic.floatAdd_one
#audit axioms Rumoca.CArithmetic.run_reaches
#audit axioms Rumoca.CArithmetic.behaviors_of_run

#audit axioms Rumoca.CBodyEmbedding.eval_refines
#audit axioms Rumoca.CBodyEmbedding.next_refines
#audit axioms Rumoca.CBodyEmbedding.run_refines
#audit axioms Rumoca.CBodyEmbedding.typed_return_reaches
#audit axioms Rumoca.CBodyEmbedding.typed_body_behaviors
#audit axioms Rumoca.CCalls.Parameters.convert_stable
#audit axioms Rumoca.CCalls.Parameters.parameters_typed
#audit axioms Rumoca.CCalls.Parameters.parameters_length
#audit axioms Rumoca.CCalls.Parameters.parameters_unknown
#audit axioms Rumoca.CBodyEmbedding.typed_call_reaches
#audit axioms Rumoca.CBodyEmbedding.typed_call_behaviors
