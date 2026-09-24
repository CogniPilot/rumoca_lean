import RumocaFMI3.Runtime
import ProofAudit.Audit

#audit axioms Rumoca.FMI3.Runtime.eval_region
#audit axioms Rumoca.FMI3.Runtime.arrayAccessGuardWith
#audit axioms Rumoca.FMI3.Runtime.pointerCheckWith
#audit axioms Rumoca.FMI3.Runtime.logicalPointerCheck
#audit axioms Rumoca.FMI3.Runtime.pointerCheck

#audit axioms Rumoca.FMI3.Runtime.arrayAccessGuardWithConditions
#audit axioms Rumoca.FMI3.Runtime.getFloat64
#audit axioms Rumoca.FMI3.Runtime.setFloat64Values

-- Factory pointer migration: retained generic domains and actual typed routes.
#audit axioms Rumoca.FMI3.Runtime.body
