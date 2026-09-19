import RumocaC.Storage
import ProofAudit.Audit

-- Axiom audit for the roots defined in RumocaC.Storage.

#audit axioms Rumoca.CStorage.store_preserves
#audit axioms Rumoca.CStorage.Preserves.absent
#audit axioms Rumoca.CStorage.body_next
#audit axioms Rumoca.CStorage.loop_next
#audit axioms Rumoca.CStorage.resume_preserves
#audit axioms Rumoca.CStorage.typed_nextWith
#audit axioms Rumoca.CStorage.event_enter_preserves
#audit axioms Rumoca.CStorage.internal_next
#audit axioms Rumoca.CStorage.internal_reaches
#audit axioms Rumoca.CStorage.internal_no_new_cells
