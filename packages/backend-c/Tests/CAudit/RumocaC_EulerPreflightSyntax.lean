import RumocaC.EulerPreflightSyntax
import ProofAudit.Audit

-- Audit the complete dependency closure of the module's exported roots.

#audit axioms Rumoca.CEulerPreflight.Syntax.render_denotes
#audit axioms Rumoca.CEulerPreflight.Syntax.Denotes
#audit axioms Rumoca.CEulerPreflight.Syntax.config
#audit axioms Rumoca.CEulerPreflight.Syntax.tokens
