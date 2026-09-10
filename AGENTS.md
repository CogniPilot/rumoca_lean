# Verification-first development

Grow the small compiler core one formally checked slice at a time.

- The user has authorized the minimal input/state initialization profile for
  FMI 3 alongside the unit-derivative regression profile, and now requests
  arrays, the `jacobian` built-in, tensor-native operators, and proved
  forward/reverse automatic differentiation as the next slice. Develop it with
  mathematical derivative/adjoint proofs; production acceptance of each new
  source case still requires its complete lowering and actual-artifact contract.
  Keep tensor rank, extents and operations in every indexed IR; do not
  enumerate tensor elements during compiler lowering.
  Do not add FMI/eFMI packaging, target plugins,
  optimizations, or machine backends as a substitute for core verification.
- Solve IR owns the executable IVP. Solver policy and FMI lifecycle wrap it.
  `packages/backend-c` owns shared C emission and target semantics; the FMI
  backends own their interfaces and artifacts. C consumes prepared Solve IR:
  DAE → GALEC → Solve for eFMI, and DAE → Solve for FMI 3. Backends must not
  resolve source names, infer shapes, select solvers or redo DAE lowering.
- Read docs/verification.md before changing semantics or claims.
- Every new case needs its source semantics, lowering theorem, target execution
  theorem, and actual-artifact certificate in the same change.
- Before every spiral-stage grammar expansion, review the entire admitted
  subset against the pinned Modelica Language Specification (MLS), FMI 3 ME/CS,
  and eFMI Algorithm/Production Code standards. Record applicable clauses,
  formal coverage, artifact evidence and open findings using the recurring
  stage checklist in dev/standards-review.md.
  Unresolved compliance findings for that subset block expansion. A schema
  check, importer run or green CI alone does not establish conformance.
- The required gate is `nix develop .#verification --command lake test`.
  `lake build audit` alone does not establish the C contract.
- Never introduce `sorry`, `admit`, new axioms, or native-reduction proof axioms.
  Never weaken the contract or axiom audit to make a check pass.
- Prefer formal proofs over unit tests. Prove compiler properties universally
  in Lean; do not replace them with example-based checks. Tests are a last
  resort for boundaries outside the proof model, such as native execution,
  file I/O and protocol transport. Extend existing boundary checks when needed
  rather than creating new test suites. Retain the required artifact gate.
- Distinguish the authored C subset and IEEE semantics in Lean from later
  machine compilation and tested host behavior. Keep the trusted boundary explicit.
- The compiler, EBNF tooling, semantics, and every proof must be in Lean.
  Do not introduce Rocq/Coq adapters or cross-prover assumptions. CompCert
  and Flocq are design references, not required proof tools.
- Follow docs/layout.md for repository ownership. Keep implementation and Lean
  checks in their packages, language EBNFs in their frontend packages' grammar/ directories, and
  cross-package integration scripts in tests/. The root Lake file only
  coordinates package builds and cross-package integration commands.
