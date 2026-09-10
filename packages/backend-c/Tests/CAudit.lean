import ProofAudit.Audit
import RumocaC.Lowering
import RumocaC.Statements
import RumocaC.Calls
import RumocaC.Arithmetic
import RumocaC.BooleanProofs

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
