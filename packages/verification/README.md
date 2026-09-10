# ProofAudit

This independent package depends only on Lean. `ProofAudit.Audit`
provides `#audit axioms theoremName`: Lean collects the declaration's complete
kernel-checked axiom dependencies and rejects anything outside `propext`,
`Classical.choice` and `Quot.sound`.

Its Lake package name is `proof_audit`; its public namespace is `ProofAudit`.
It has no Rumoca dependency.

Package check libraries use this command instead of relying on a separate
interpretation of printed audit logs. Failure prevents Lake from accepting the
build. Successful checks are cached with their source and transitive imports,
like other Lean modules. Runtime compiler libraries do not import this package.
Actual-file checking entry points still read and certify their current inputs.

From the repository root: `lake build proof_audit/ProofAudit`.
