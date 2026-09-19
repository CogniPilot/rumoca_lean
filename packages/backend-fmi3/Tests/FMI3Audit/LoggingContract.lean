import RumocaFMI3.LoggingContract
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.LoggingContract.

#audit axioms Rumoca.FMI3.Logging.execution_correct
#audit axioms Rumoca.FMI3.Logging.category_collected
#audit axioms Rumoca.FMI3.Logging.prepared_correct
#audit axioms Rumoca.FMI3.Logging.rendered_contract
#audit axioms Rumoca.FMI3.Logging.metadata_correct
#audit axioms Rumoca.FMI3.Logging.all_execution_correct
#audit axioms Rumoca.FMI3.Logging.all_prepared_correct
#audit axioms Rumoca.FMI3.Logging.AllExecutionContract.determined
#audit axioms Rumoca.FMI3.Logging.AllPreparedContract.determined
#audit axioms Rumoca.FMI3.Logging.silent_prepared_correct
