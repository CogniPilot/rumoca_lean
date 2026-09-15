import Rumoca.FMI3RuntimeStorage
import Rumoca.FMI3StateSetterPolicy
import Rumoca.FMI3RuntimeLinkage
import Rumoca.FMI3CallPolicy
import ProofAudit.Audit

/-! Independently cached formal audits for the call policy; no example-based tests. -/

#audit axioms Rumoca.FMI3.CallPolicy.actual_adapter_policy
#audit axioms Rumoca.FMI3.CallPolicy.source_program_policy

#audit axioms Rumoca.FMI3.RuntimeLinkage.source_logged_environment

#audit axioms Rumoca.FMI3.RuntimeStorage.source_resource_environment
#audit axioms Rumoca.FMI3.StateSetterPolicy.source_permission
