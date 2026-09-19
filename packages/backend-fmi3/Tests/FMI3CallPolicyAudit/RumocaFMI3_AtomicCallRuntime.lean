import RumocaFMI3.AtomicCallRuntime
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaFMI3.AtomicCallRuntime.

#audit axioms Rumoca.FMI3.AtomicCallPolicy.entry_valid
#audit axioms Rumoca.FMI3.AtomicCallPolicy.exchange_value
#audit axioms Rumoca.FMI3.AtomicCallPolicy.logged_concurrent_reaches
#audit axioms Rumoca.FMI3.AtomicCallPolicy.logged_named_only
#audit axioms Rumoca.FMI3.AtomicCallPolicy.logged_reaches
#audit axioms Rumoca.FMI3.AtomicCallPolicy.ranked_entry
#audit axioms Rumoca.FMI3.AtomicCallPolicy.release_value
