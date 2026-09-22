import RumocaC.ReadOnly
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.ReadOnly.

#audit axioms Rumoca.CReadOnly.body_reaches
#audit axioms Rumoca.CReadOnly.loop_reaches
#audit axioms Rumoca.CReadOnly.typed_reaches
#audit axioms Rumoca.CReadOnly.typed_load
#audit axioms Rumoca.CReadOnly.typed_nextWith

#audit axioms Rumoca.CReadOnly.body_next
#audit axioms Rumoca.CReadOnly.body_nextWith
#audit axioms Rumoca.CReadOnly.enter_preservesWith
#audit axioms Rumoca.CReadOnly.loop_next
#audit axioms Rumoca.CReadOnly.loop_nextWith
#audit axioms Rumoca.CReadOnly.resume_preservesWith
#audit axioms Rumoca.CReadOnly.typed_nextIn
#audit axioms Rumoca.CReadOnly.typed_nextWithExpressions
#audit axioms Rumoca.CReadOnly.typed_reachesWith
