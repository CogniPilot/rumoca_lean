import RumocaC.MathCalls
import RumocaC.IntegerConversions
import RumocaC.OutputAtomicFrame
import RumocaC.BodyReachability
import RumocaC.OutputAssignments
import RumocaC.PointerConditions
import RumocaC.Storage
import RumocaC.LiteralInterfaceBody
import RumocaC.ObjectDeclaration
import RumocaC.ObjectDeclarationSemantics
import RumocaC.TypedMemory
import RumocaC.CallEventPrefix
import RumocaC.StorageTransfer
import RumocaC.AtomicFrame
import RumocaC.ConcurrentCalls
import RumocaC.StringCallProofs
import RumocaC.StringBindings
import RumocaC.SilentCallChoices
import RumocaC.NamedCallSites
import RumocaC.NamedDeclarations
import RumocaC.StringASCII
import RumocaC.AtomicScanCalls
import RumocaC.AtomicScanPrinter
import RumocaC.Subobjects
import RumocaC.NullPointerPrinter
import RumocaC.MemoryUpdates
import RumocaC.LoopEvents
import RumocaC.KernelEvents
import RumocaC.FiniteValue
import RumocaC.CallEventChoices
import RumocaC.BodyEvents
import RumocaC.LiteralEventPool
import RumocaC.ObservedCalls
import ProofAudit.Audit
import RumocaC.TreePreprocessing
import RumocaC.Punctuator
import RumocaC.StringBoundary
import RumocaC.TreeBoundary
import RumocaC.PreprocessingNumber
import RumocaC.IdentifierToken
import RumocaC.ExpressionSyntax
import RumocaC.ExpressionPrinter
import RumocaC.FunctionPrinter
import RumocaC.TreeConcatenation
import RumocaC.TreeTokenization
import RumocaC.FunctionSequence
import RumocaC.TokenStarts
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
import RumocaC.UnsignedMemory
import RumocaC.CallSignature

#audit axioms Rumoca.CUnsigned.modulus_pos
#audit axioms Rumoca.CUnsigned.value_correct
#audit axioms Rumoca.CUnsigned.value_unique
#audit axioms Rumoca.CUnsigned.value_in_range
#audit axioms Rumoca.CUnsigned.value_idempotent
#audit axioms Rumoca.CUnsigned.value_bits
#audit axioms Rumoca.CMemory.convert_unsigned_iff
#audit axioms Rumoca.CMemory.convert_unsigned_bits
#audit axioms Rumoca.CMemory.convert_unsigned_in_range
#audit axioms Rumoca.CMemory.store_unsigned
#audit axioms Rumoca.CMemory.load_unsigned_written
#audit axioms Rumoca.CCalls.Signature.Arguments.length
#audit axioms Rumoca.CCalls.Signature.locals_cons
#audit axioms Rumoca.CCalls.Signature.locals_missing
#audit axioms Rumoca.CCalls.Signature.parameters_bound
#audit axioms Rumoca.CCalls.Signature.call_entry
#audit axioms Rumoca.CCalls.Signature.witness_valid
#audit axioms Rumoca.CCalls.Signature.arguments_exist

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
#audit axioms Rumoca.CLiteral.Pool.install_load
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

#audit axioms Rumoca.CPunctuator.consumes_unique
#audit axioms Rumoca.CPunctuator.consumes_space
#audit axioms Rumoca.CPunctuator.consumes_boundary
#audit axioms Rumoca.CPunctuator.consumes_before_word
#audit axioms Rumoca.CPunctuator.consumes_before_operand
#audit axioms Rumoca.CPunctuator.consumes_unextendable
#audit axioms Rumoca.CPunctuator.consumes_separator
#audit axioms Rumoca.CPunctuator.binop_consumes
#audit axioms Rumoca.CString.Fragments.boundary_unique
#audit axioms Rumoca.CString.literal_boundary_unique
#audit axioms Rumoca.CString.literal_prefix_free
#audit axioms Rumoca.CString.quote_boundary
#audit axioms Rumoca.CTree.Syntax.OperandStart.append
#audit axioms Rumoca.CTree.Syntax.expression_start
#audit axioms Rumoca.CTree.Syntax.punctuator_before_expression
#audit axioms Rumoca.CLexical.Nondigit.characters
#audit axioms Rumoca.CPPNumber.Spells.characters
#audit axioms Rumoca.CPPNumber.Spells.append_digits
#audit axioms Rumoca.CPPNumber.natural_spells
#audit axioms Rumoca.CPPNumber.natural_consumes
#audit axioms Rumoca.CPPNumber.consumes_unique
#audit axioms Rumoca.CIdentifierToken.Spells.characters
#audit axioms Rumoca.CIdentifierToken.Spells.append_ascii
#audit axioms Rumoca.CIdentifierToken.word_spells
#audit axioms Rumoca.CIdentifierToken.word_consumes
#audit axioms Rumoca.CIdentifierToken.identifier_consumes
#audit axioms Rumoca.CIdentifierToken.consumes_unique
#audit axioms Rumoca.CString.QuoteBody.append
#audit axioms Rumoca.CString.QuoteBody.boundary_unique
#audit axioms Rumoca.CString.Fragments.envelope
#audit axioms Rumoca.CString.denotes_quoted
#audit axioms Rumoca.CString.Quoted.boundary_unique
#audit axioms Rumoca.CString.quote_maximal
#audit axioms Rumoca.CTokens.Prefix.append
#audit axioms Rumoca.CTokens.Prefix.finish
#audit axioms Rumoca.CTokens.word_prefix
#audit axioms Rumoca.CTokens.natural_prefix
#audit axioms Rumoca.CTokens.string_prefix
#audit axioms Rumoca.CTokens.punctuator_prefix
#audit axioms Rumoca.CTree.Syntax.TypeSpecifier.word_parts
#audit axioms Rumoca.CTree.Syntax.TypeSpelling.named
#audit axioms Rumoca.CTree.Syntax.TypeSpelling.const
#audit axioms Rumoca.CTree.Syntax.TypeSpelling.pointer
#audit axioms Rumoca.CTree.Syntax.binary_render_syntax
#audit axioms Rumoca.CTree.Syntax.Expression.binary_grouped
#audit axioms Rumoca.CLexical.identStart_not_digit
#audit axioms Rumoca.CTree.Syntax.Expression.identifier_inputs
#audit axioms Rumoca.CText.intercalate_one
#audit axioms Rumoca.CText.intercalate_cons
#audit axioms Rumoca.CTree.Printer.tail_safe_separator
#audit axioms Rumoca.CTree.Printer.identifier_renders
#audit axioms Rumoca.CTree.Printer.natural_renders
#audit axioms Rumoca.CTree.Printer.string_renders
#audit axioms Rumoca.CTree.Printer.binary_renders
#audit axioms Rumoca.CTree.Printer.unary_renders
#audit axioms Rumoca.CTree.Printer.cast_renders
#audit axioms Rumoca.CTree.Printer.sizeof_renders
#audit axioms Rumoca.CTree.Printer.index_renders
#audit axioms Rumoca.CTree.Printer.field_renders
#audit axioms Rumoca.CTree.Printer.arguments_render
#audit axioms Rumoca.CTree.Printer.call_renders
#audit axioms Rumoca.CTree.Printer.expression_renders
#audit axioms Rumoca.CTokens.separator_prefix
#audit axioms Rumoca.CTokens.Prefix.whitespaces
#audit axioms Rumoca.CTokens.Prefix.indent
#audit axioms Rumoca.CTree.Printer.declare_renders
#audit axioms Rumoca.CTree.Printer.assign_renders
#audit axioms Rumoca.CTree.Printer.eval_renders
#audit axioms Rumoca.CTree.Printer.return_void_renders
#audit axioms Rumoca.CTree.Printer.return_value_renders
#audit axioms Rumoca.CTree.Printer.items_render
#audit axioms Rumoca.CTree.Printer.while_renders
#audit axioms Rumoca.CTree.Printer.if_then_renders
#audit axioms Rumoca.CTree.Printer.if_else_renders
#audit axioms Rumoca.CTree.Printer.statement_renders
#audit axioms Rumoca.CTree.Printer.parameter_renders
#audit axioms Rumoca.CTree.Printer.parameters_render
#audit axioms Rumoca.CTree.Printer.signature_renders
#audit axioms Rumoca.CTree.Printer.function_renders
#audit axioms Rumoca.CTree.Printer.function_denotes

#audit axioms Rumoca.CTokens.PhaseSix.Separated.no_rewrite
#audit axioms Rumoca.CTokens.PhaseSix.Separated.unchanged
#audit axioms Rumoca.CTokens.PhaseSix.Separated.empty
#audit axioms Rumoca.CTokens.PhaseSix.Separated.single
#audit axioms Rumoca.CTokens.PhaseSix.Separated.prepend
#audit axioms Rumoca.CTokens.PhaseSix.Separated.append_separator
#audit axioms Rumoca.CTokens.PhaseSix.Separated.all_nonstring
#audit axioms Rumoca.CTokens.PhaseSix.Closed.separated
#audit axioms Rumoca.CTokens.PhaseSix.Closed.empty
#audit axioms Rumoca.CTokens.PhaseSix.Closed.append
#audit axioms Rumoca.CTokens.PhaseSix.Closed.prepend
#audit axioms Rumoca.CTokens.PhaseSix.Closed.seal
#audit axioms Rumoca.CTokens.PhaseSix.Closed.between
#audit axioms Rumoca.CTokens.PhaseSix.Closed.all_nonstring
#audit axioms Rumoca.CTree.Syntax.TypeTokens.nonstring
#audit axioms Rumoca.CTree.Syntax.Expression.separated
#audit axioms Rumoca.CTree.Syntax.BlockItem.closed
#audit axioms Rumoca.CTree.Syntax.BlockItems.closed
#audit axioms Rumoca.CTree.Syntax.ParameterPhrase.nonstring
#audit axioms Rumoca.CTree.Syntax.ParametersPhrase.nonstring
#audit axioms Rumoca.CTree.Syntax.SignaturePhrase.nonstring
#audit axioms Rumoca.CTree.Syntax.FunctionPhrase.closed
#audit axioms Rumoca.CTree.Syntax.FunctionPhrase.concatenation_unchanged
#audit axioms Rumoca.CTree.Printer.FunctionDenotes.phase_six

#audit axioms Rumoca.CTokens.Competition.Starts.append
#audit axioms Rumoca.CTokens.Competition.Starts.prefix
#audit axioms Rumoca.CTokens.Competition.Starts.head
#audit axioms Rumoca.CTokens.Competition.nondigit_starts
#audit axioms Rumoca.CTokens.Competition.identifier_starts
#audit axioms Rumoca.CTokens.Competition.IdentifierStart.not_digit
#audit axioms Rumoca.CTokens.Competition.NumberStart.append
#audit axioms Rumoca.CTokens.Competition.NumberStart.prefix
#audit axioms Rumoca.CTokens.Competition.number_starts
#audit axioms Rumoca.CTokens.Competition.identifier_no_quote
#audit axioms Rumoca.CTokens.Competition.word_not_encoded
#audit axioms Rumoca.CTokens.Competition.NumberStart.not_identifier
#audit axioms Rumoca.CTokens.Competition.word_not_number

#audit axioms Rumoca.CTokens.Competition.Starts.disjoint
#audit axioms Rumoca.CTokens.Competition.Starts.positive
#audit axioms Rumoca.CTokens.Competition.IdentifierStart.character
#audit axioms Rumoca.CTokens.Competition.NumberStart.first
#audit axioms Rumoca.CTokens.Competition.encoded_starts
#audit axioms Rumoca.CTokens.Competition.word_starts
#audit axioms Rumoca.CTokens.Competition.number_start_not_identifier
#audit axioms Rumoca.CTokens.Competition.number_input_starts
#audit axioms Rumoca.CTokens.Competition.quoted_starts
#audit axioms Rumoca.CTokens.Competition.string_input_starts
#audit axioms Rumoca.CTokens.Competition.punctuator_starts
#audit axioms Rumoca.CTokens.Competition.punctuator_input_starts
#audit axioms Rumoca.CTokens.Competition.punctuator_before_number
#audit axioms Rumoca.CTokens.Competition.punctuator_not_number
#audit axioms Rumoca.CTokens.Normal.Spelling.candidate
#audit axioms Rumoca.CTokens.Normal.Spelling.positive
#audit axioms Rumoca.CTokens.Competition.word_longest
#audit axioms Rumoca.CTokens.Competition.number_longest
#audit axioms Rumoca.CTokens.Competition.string_longest
#audit axioms Rumoca.CTokens.Competition.punctuator_longest
#audit axioms Rumoca.CTokens.Normal.CommentStart.head
#audit axioms Rumoca.CTokens.word_no_comment
#audit axioms Rumoca.CTokens.number_no_comment
#audit axioms Rumoca.CTokens.string_no_comment
#audit axioms Rumoca.CTokens.punctuator_no_comment
#audit axioms Rumoca.CTokens.Consumes.normal
#audit axioms Rumoca.CTokens.Prefix.normal
#audit axioms Rumoca.CTokens.Lexes.normal
#audit axioms Rumoca.CTree.Printer.FunctionDenotes.tokenization
#audit axioms Rumoca.CTree.Printer.function_sequence_renders
#audit axioms Rumoca.CTree.Printer.function_sequence_tokenization

#audit axioms Rumoca.CReadOnly.typed_nextWith
#audit axioms Rumoca.CCalls.Indirect.value_pointer_iff
#audit axioms Rumoca.CCalls.Indirect.local_pointer
#audit axioms Rumoca.CCalls.Indirect.local_null
#audit axioms Rumoca.CCalls.Indirect.named_iff
#audit axioms Rumoca.CCalls.Indirect.field_pointer
#audit axioms Rumoca.CCalls.Events.enter_preserves
#audit axioms Rumoca.CCalls.Events.internal_preserves
#audit axioms Rumoca.CCalls.Events.step_preserves
#audit axioms Rumoca.CCalls.Events.reaches_preserves
#audit axioms Rumoca.CCalls.Events.termination_preserves
#audit axioms Rumoca.CCalls.Events.external_entry_exclusive
#audit axioms Rumoca.CCalls.Events.external_reaches
#audit axioms Rumoca.CCalls.Events.internal_unique
#audit axioms Rumoca.CCalls.Events.body_step
#audit axioms Rumoca.CCalls.Events.body_reaches
#audit axioms Rumoca.CCalls.Events.internal_prefix
#audit axioms Rumoca.CCalls.Events.tree_entry
#audit axioms Rumoca.CCalls.Events.external_prefix
#audit axioms Rumoca.CCalls.Events.return_forced
#audit axioms Rumoca.CCalls.Events.external_behaviors
#audit axioms Rumoca.CCalls.Events.observed_outcome
#audit axioms Rumoca.CCalls.Events.observed_unique
#audit axioms Rumoca.CCalls.Indirect.resolved_supported

#audit axioms Rumoca.CLiteral.Lowering.Events.target_lowered
#audit axioms Rumoca.CLiteral.Lowering.Events.resolve_lowered
#audit axioms Rumoca.CLiteral.Lowering.Events.operand_lowered
#audit axioms Rumoca.CLiteral.Lowering.Events.operand_head_safe
#audit axioms Rumoca.CLiteral.Lowering.Events.enter_lowered
#audit axioms Rumoca.CLiteral.Lowering.nextWith_lowered
#audit axioms Rumoca.CLiteral.Lowering.nextWith_safe
#audit axioms Rumoca.CLiteral.Lowering.Events.operand_fresh
#audit axioms Rumoca.CLiteral.Lowering.Events.enter_safe
#audit axioms Rumoca.CLiteral.Lowering.Events.internal_lowered
#audit axioms Rumoca.CLiteral.Lowering.Events.internal_safe
#audit axioms Rumoca.CLiteral.Lowering.Events.step_safe
#audit axioms Rumoca.CLiteral.Lowering.Events.step_lowered
#audit axioms Rumoca.CLiteral.Lowering.Events.internal_reflected
#audit axioms Rumoca.CLiteral.Lowering.Events.step_reflected
#audit axioms Rumoca.CLiteral.Lowering.Events.behaviors
#audit axioms Rumoca.CLiteral.Lowering.Events.invocation_behaviors
#audit axioms Rumoca.CLiteral.Interface.nextWith_agreement
#audit axioms Rumoca.CLiteral.Interface.nextWith_agrees
#audit axioms Rumoca.CLiteral.Interface.Events.target_agreement
#audit axioms Rumoca.CLiteral.Interface.Events.resolve_agreement
#audit axioms Rumoca.CLiteral.Interface.Events.callee_agreement
#audit axioms Rumoca.CLiteral.Interface.Events.operand_agreement
#audit axioms Rumoca.CLiteral.Interface.Events.enter_agreement
#audit axioms Rumoca.CLiteral.Interface.Events.enter_agrees_next
#audit axioms Rumoca.CLiteral.Interface.Events.internal_agreement
#audit axioms Rumoca.CLiteral.Interface.Events.internal_agrees
#audit axioms Rumoca.CLiteral.Interface.Events.converted_agreement
#audit axioms Rumoca.CLiteral.Interface.Events.step_agrees
#audit axioms Rumoca.CLiteral.Interface.Events.step_forward
#audit axioms Rumoca.CLiteral.Interface.Events.step_backward
#audit axioms Rumoca.CLiteral.Interface.Events.behaviors
#audit axioms Rumoca.CLiteral.Interface.Events.invocation_behaviors
#audit axioms Rumoca.CLiteral.Pool.event_invocation_behaviors

#audit axioms Rumoca.CCalls.Events.internal_prefix_behaviors
#audit axioms Rumoca.CCalls.Events.external_step_iff
#audit axioms Rumoca.CCalls.Events.external_choices_behaviors
#audit axioms Rumoca.CCalls.Events.observed_choices
#audit axioms Rumoca.CCalls.Events.body_call_reaches
#audit axioms Rumoca.CCalls.Events.body_call_prefix
#audit axioms Rumoca.CCalls.Events.body_call_behaviors

#audit axioms Rumoca.CCalls.Events.body_prefix_reaches

#audit axioms Rumoca.CMemory.Value.isFinite_true_iff
#audit axioms Rumoca.CMemory.Value.float64_cases

#audit axioms Rumoca.CCalls.Events.kernel_step
#audit axioms Rumoca.CCalls.Events.kernel_reaches
#audit axioms Rumoca.CCalls.Events.kernel_correct
#audit axioms Rumoca.CCalls.Events.kernel_behaviors

#audit axioms Rumoca.CCalls.Events.loop_prefix
#audit axioms Rumoca.CCalls.Events.loop_reaches
#audit axioms Rumoca.CLoops.counter_reset

#audit axioms Rumoca.CMemory.replace_overwrite

#audit axioms Rumoca.CStorage.store_preserves
#audit axioms Rumoca.CStorage.Preserves.absent
#audit axioms Rumoca.CStorage.Preserves.cell
#audit axioms Rumoca.CStorage.body_next
#audit axioms Rumoca.CStorage.loop_next
#audit axioms Rumoca.CStorage.resume_preserves
#audit axioms Rumoca.CStorage.typed_nextWith
#audit axioms Rumoca.CStorage.event_enter_preserves
#audit axioms Rumoca.CStorage.internal_next
#audit axioms Rumoca.CStorage.internal_reaches
#audit axioms Rumoca.CStorage.internal_no_new_cells
#audit axioms Rumoca.CNull.Compared.iff
#audit axioms Rumoca.CNull.comparison_iff
#audit axioms Rumoca.CNull.equal_right
#audit axioms Rumoca.CNull.unequal_right
#audit axioms Rumoca.CNull.equal_left
#audit axioms Rumoca.CNull.unequal_left
#audit axioms Rumoca.CNull.nonnull_unsupported
#audit axioms Rumoca.CNull.literal_eval
#audit axioms Rumoca.CNull.zero_variable_not_constant
#audit axioms Rumoca.CNull.equal_eval
#audit axioms Rumoca.CNull.unequal_truth
#audit axioms Rumoca.CNull.branch_preserved
#audit axioms Rumoca.CNull.literal_printable
#audit axioms Rumoca.CNull.literal_renders
#audit axioms Rumoca.CNull.literal_contract
#audit axioms Rumoca.CBody.zeroLiteral_true
#audit axioms Rumoca.CBody.zeroLiteral_false
#audit axioms Rumoca.CLiteral.Lowering.expression_zeroLiteral

#audit axioms Rumoca.CMemory.Address.member_index_eq_iff
#audit axioms Rumoca.CMemory.Address.instances_separate
#audit axioms Rumoca.CMemory.Address.fields_separate
#audit axioms Rumoca.CMemory.Address.member_in_record
#audit axioms Rumoca.CMemory.Address.InRecord.member
#audit axioms Rumoca.CMemory.Address.InRecord.index
#audit axioms Rumoca.CMemory.Address.records_separate
#audit axioms Rumoca.CMemory.store_other_record

#audit axioms Rumoca.CAtomicBoolean.read_iff
#audit axioms Rumoca.CAtomicBoolean.exchange_iff
#audit axioms Rumoca.CAtomicBoolean.write_iff
#audit axioms Rumoca.CAtomicBoolean.exchange_same
#audit axioms Rumoca.CAtomicBoolean.ordinary_load_unsupported
#audit axioms Rumoca.CAtomicBoolean.ordinary_store_unsupported
#audit axioms Rumoca.CAtomicBoolean.exchange_storage
#audit axioms Rumoca.CAtomicBoolean.exchange_readonly
#audit axioms Rumoca.CAtomicBoolean.write_storage
#audit axioms Rumoca.CAtomicBoolean.write_readonly
#audit axioms Rumoca.CAtomicBoolean.initial_read
#audit axioms Rumoca.CAtomicBoolean.initial_frame
#audit axioms Rumoca.CAtomicBoolean.initial_readonly
#audit axioms Rumoca.CAtomicBoolean.Calls.exchange_behaviors
#audit axioms Rumoca.CAtomicBoolean.Calls.write_behaviors
#audit axioms Rumoca.CAtomicScan.outcome_exists
#audit axioms Rumoca.CAtomicScan.outcome_bounds
#audit axioms Rumoca.CAtomicScan.outcome_reserved
#audit axioms Rumoca.CAtomicScan.outcome_exhausted
#audit axioms Rumoca.CAtomicScan.outcome_frame
#audit axioms Rumoca.CAtomicScan.outcome_storage
#audit axioms Rumoca.CAtomicScan.scan_prefix
#audit axioms Rumoca.CAtomicScan.parameters_bound
#audit axioms Rumoca.CAtomicScan.parameter_types
#audit axioms Rumoca.CAtomicScan.initialization
#audit axioms Rumoca.CAtomicScan.call_prefix
#audit axioms Rumoca.CAtomicScan.call_correct
#audit axioms Rumoca.CAtomicScan.Printer.function_printable
#audit axioms Rumoca.CAtomicScan.Printer.function_printable_in
#audit axioms Rumoca.CAtomicScan.Printer.function_denotes
#audit axioms Rumoca.CAtomicScan.Printer.function_tokenization

#audit axioms Rumoca.CStoreInvariant.internal_next
#audit axioms Rumoca.CAtomicBoolean.ordinary_store_preserves
#audit axioms Rumoca.CAtomicBoolean.internal_preserves
#audit axioms Rumoca.CCalls.Concurrent.resumes_result
#audit axioms Rumoca.CCalls.Concurrent.other_thread
#audit axioms Rumoca.CCalls.Concurrent.reaches_readonly

#audit axioms Rumoca.CCalls.Casts.sizeReturn
#audit axioms Rumoca.CCalls.Casts.intReturn
#audit axioms Rumoca.CStringMemory.Contents.unique
#audit axioms Rumoca.CStringMemory.Contents.nonzero
#audit axioms Rumoca.CStringMemory.of_indexed
#audit axioms Rumoca.CStringMemory.of_literal
#audit axioms Rumoca.CStringOperations.span_le_length
#audit axioms Rumoca.CStringOperations.span_eq_length
#audit axioms Rumoca.CStringOperations.comparison_zero
#audit axioms Rumoca.CStringOperations.comparison_exists
#audit axioms Rumoca.CStringCalls.length_behaviors
#audit axioms Rumoca.CStringCalls.span_behaviors
#audit axioms Rumoca.CStringCalls.compare_behaviors
#audit axioms Rumoca.CStringCalls.compare_zero
#audit axioms Rumoca.CTree.Syntax.TypeSpelling.volatile
#audit axioms Rumoca.CStringCalls.library_name
#audit axioms Rumoca.CCalls.Events.external_silent_equivalence
#audit axioms Rumoca.CCalls.Events.named_assign_entry
#audit axioms Rumoca.CCalls.Events.assign_result
#audit axioms Rumoca.CCalls.Events.expression_return
#audit axioms Rumoca.CStringMemory.literal_contents
#audit axioms Rumoca.CStringMemory.content_eq
#audit axioms Rumoca.CStringMemory.NonzeroASCII.bytes
#audit axioms Rumoca.CStringMemory.NonzeroASCII.content
#audit axioms Rumoca.CCalls.Events.named_declare_entry
#audit axioms Rumoca.CCalls.Events.declare_result
#audit axioms Rumoca.CCalls.Events.internal_path
#audit axioms Rumoca.CCalls.Events.external_path
#audit axioms Rumoca.CAtomicScan.attempt_path
#audit axioms Rumoca.CAtomicScan.return_path
#audit axioms Rumoca.CAtomicScan.scan_path
#audit axioms Rumoca.CAtomicScan.call_path
#audit axioms Rumoca.CMemory.store_converted
#audit axioms Rumoca.CMemory.load_converted

#audit axioms Rumoca.CObject.field_renders
#audit axioms Rumoca.CObject.fields_render
#audit axioms Rumoca.CObject.record_renders
#audit axioms Rumoca.CObject.array_renders
#audit axioms Rumoca.CObject.constant_renders
#audit axioms Rumoca.CObject.Shape.leaf_scalar
#audit axioms Rumoca.CObject.Shape.leaf_member
#audit axioms Rumoca.CObject.zero_converts
#audit axioms Rumoca.CObject.zero_load
#audit axioms Rumoca.CObject.zero_atomic
#audit axioms Rumoca.CObject.cellType_block
#audit axioms Rumoca.CObject.initial_at
#audit axioms Rumoca.CObject.initial_frame
#audit axioms Rumoca.CObject.initial_other_block
#audit axioms Rumoca.CObject.initial_scalar
#audit axioms Rumoca.CObject.initial_member
#audit axioms Rumoca.CObject.initial_readonly
#audit axioms Rumoca.CObject.initial_atomic
#audit axioms Rumoca.CObject.resolveFields_iff
#audit axioms Rumoca.CObject.record_resolves
#audit axioms Rumoca.CObject.FieldsMean.names
#audit axioms Rumoca.CObject.array_initializes
#audit axioms Rumoca.CObject.array_printed_initializes
#audit axioms Rumoca.CLiteral.Interface.body_next_agrees
#audit axioms Rumoca.CLiteral.Interface.body_next_agreement
#audit axioms Rumoca.CLiteral.Interface.body_run_agreement
#audit axioms Rumoca.CLiteral.Interface.body_bisimulation
#audit axioms Rumoca.CLiteral.Interface.body_behaviors

#audit axioms Rumoca.CBody.run_of_reaches
#audit axioms Rumoca.COutputAssignments.after_preserves_stored
#audit axioms Rumoca.COutputAssignments.frame
#audit axioms Rumoca.COutputAssignments.outputs_stored
#audit axioms Rumoca.COutputAssignments.ready_preserved
#audit axioms Rumoca.COutputAssignments.run_all
#audit axioms Rumoca.COutputAssignments.run_one
#audit axioms Rumoca.COutputAssignments.writable_preserved
#audit axioms Rumoca.COutputAssignments.write_frame
#audit axioms Rumoca.COutputAssignments.write_preserves_stored
#audit axioms Rumoca.CPointerConditions.missing_eval
#audit axioms Rumoca.CPointerConditions.missing_iff

#audit axioms Rumoca.CAtomicBoolean.replace_nonatomic
#audit axioms Rumoca.COutputAssignments.write_atomic
#audit axioms Rumoca.COutputAssignments.after_atomic

#audit axioms Rumoca.CIntegerConversions.integer_float64
#audit axioms Rumoca.CIntegerConversions.integer_float64_value
#audit axioms Rumoca.CIntegerConversions.finite_size
#audit axioms Rumoca.CIntegerConversions.finite_size_iff
#audit axioms Rumoca.CIntegerConversions.nonfinite_size
#audit axioms Rumoca.CIntegerConversions.finite_size_correct
#audit axioms Rumoca.CIntegerConversions.cast_integer
#audit axioms Rumoca.CIntegerConversions.cast_size
#audit axioms Rumoca.CIntegerConversions.eval_integer_cast
#audit axioms Rumoca.CIntegerConversions.eval_size_cast

#audit axioms Rumoca.CMathCalls.finite_injective
#audit axioms Rumoca.CMathCalls.floor_arguments
#audit axioms Rumoca.CMathCalls.rounding_arguments
#audit axioms Rumoca.CMathCalls.floor_effect
#audit axioms Rumoca.CMathCalls.floor_mathematical
#audit axioms Rumoca.CMathCalls.floor_behaviors
#audit axioms Rumoca.CMathCalls.rounding_effect
#audit axioms Rumoca.CMathCalls.rounding_behaviors
