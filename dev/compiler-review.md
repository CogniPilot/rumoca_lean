# Compiler semantic-preservation review

Review date: 2026-09-08. Scope: the local Lean working tree, including parser,
all four IRs, C rendering/parsing and execution, arithmetic, driver capstones,
actual-file checking and required tests. This is a first-party engineering
review, not an independent certification. Follow-up work is tracked in
the closure checklist.

The later [certified-printer checkpoint](efmi.md#certified-printers-and-shared-c-ownership)
replaces this review's C-reader round-trip path with structural printing and
grammar-denotation proofs. The current theorem statements are in
[the verification contract](../docs/verification.md); historical API names below
refer to the reviewed tree.

## Assessment

**The frozen compiler has genuine, kernel-checked semantic preservation, but
CompCert-level assurance is not established.** The distinction is between the
validity of the proved implication and the adequacy of its specifications,
composition interfaces and delivered artifact boundary. No contradiction in
the current tiny-core theorem was found during this review. That is not a
proof that its authored semantics perfectly describes Modelica, ISO C or IEEE.

CompCert's `transf_c_program_correct` connects successful compilation of a
CompCert C AST to backward simulation by the resulting assembly AST. Its
driver composes per-pass relations and simulations. Its behavior corollary
allows a target behavior to improve source undefined behavior; for safe source
programs, target behavior must be a permitted source behavior.
Sources: [Compiler](https://compcert.org/doc/html/compcert.driver.Compiler.html),
[Behaviors](https://compcert.org/doc/html/compcert.common.Behaviors.html).

Our `compiler_semantic_preservation` instead relates successful compilation
and actual C text to **equivalence of all function-call behaviors** in an
authored, finite C profile. For this deterministic, terminating language,
equivalence is appropriate. Its stronger-looking `↔` does not imply greater
assurance: the language and observations are much smaller. CompCert's boundary
also has exclusions, including preprocessing and external assembly/linking;
it should not be described as proving arbitrary source files all the way to
physical hardware. [CompCert scope](https://compcert.org/man/manual001.html)

Stopping this project at C is reasonable. Assembly generation is not needed
to establish a good theorem for that boundary. A later machine-code claim
would require a proved semantic bridge to a downstream compiler, not merely
invoking CompCert on this output.

## What the checked theorem actually covers

| Boundary | Evidence | Limitation |
| --- | --- | --- |
| Actual Modelica text → AST | `lex_correct`, `parseTokens_iff`, `parse_complete`, `parsed_lexes` | Authored ASCII lexical slice and fixed AST action; not all MLS grammar |
| Actual EBNF → recognized tokens | Generated source/table certificates, alphabet reflection, `parsed_in_ebnf` | EBNF reader itself defines its dialect |
| AST → Flat | `flatten_correct`, `Flat.lower_correct` | One named derivative, one state; name resolution is required |
| Flat → DAE | `dae_correct`, `DAE.lower_correct` | Equality becomes the residual `dx - 1 = 0` |
| DAE → Solve | `solve_correct`, `Solve.lower_correct` | Only the unit derivative program is constructible |
| Solve → C | `C.compileProgram_correct`, `C.lower_binary64_correct`, `CStatements.behaviors_correct` | Register elimination has a generic expression proof; whole target proof remains specific to this profile |
| C AST → emitted text → parsed C | `CSyntax.print_parses`, `parse_sound`, `parse_statements` | Fixed declarations/header and authored statement subset |
| All executions | `Transition.Machine.behavior_iff`, all-call accessibility/completion | Return encoding, divergence and stuckness; no external events or memory observations |
| Real solution | `Source.solution_unique`, `CStatements.real_refinement` | Host-supplied finite initial value and integer sample times |
| Actual artifact | `ArtifactCheck`, `compile_verified` | Trusted file-to-proposition adapter and stable filesystem/build environment |

All admitted source models differ only in names/whitespace. Their one
semantic equation is the same. Consequently equality to `unitDerivative` or
`unitModule` is a legitimate proof technique here. It is **not evidence** that
future expressions, different equations or optimization passes are covered.
The successful-compilation premise is not a vacuous escape hatch:
`compile_complete` covers all resolved sources admitted by the lexical/AST
specification, and positive artifact controls exercise it.

`x` is a mathematical real in the source ODE. The target stores a finite
binary64 encoding. Exact preservation concerns the declared nearest-even
numerical policy; the error bound against any real initial-value solution is
separate. The conservative bound `|error| ≤ n` alone would admit a frozen
sampler, but the complete behavioral contract rejects that implementation.

## Findings, ordered by assurance impact

### RV01 — Source and target specification correspondence remains open (high)

The guarantees are relative to authored definitions in
[Source](../packages/compiler/Rumoca/Source.lean),
[Syntax](../packages/backend-fmi3/RumocaC/Syntax.lean),
[Statements](../packages/backend-fmi3/RumocaC/Statements.lean) and
[Binary64](../packages/core/RumocaCore/Real/Binary64.lean).
Existing design notes map MLS clauses, but there is no completed, independently
reviewed clause/assumption ledger for the entire supported source/C/IEEE profile.
Kernel checking cannot establish correspondence to prose by itself.

The MLS review also requires a precise distinction around `Real`:
[MLS 3.7 §4.9.1](https://specification.modelica.org/maint/3.7/class-predefined-types-and-declarations.html#real-type)
requires finite stored Real values. `Source.Solves` here is an ideal continuous
ODE over mathematical reals on all real times; it does not impose stored-value
bounds or model the full predefined Real class. The finite execution policy
has a separate representation/rounding contract. Do not describe the ideal
trajectory theorem alone as complete operational MLS Real preservation.

In particular, the model observes returned bits and termination, not floating
exception flags, traps, allocation, callbacks or an arbitrary surrounding C
program. The header's format checks do not establish nearest rounding, gradual
underflow or ABI correctness. This is a restricted callable numerical library
contract, not a proof of arbitrary C contextual equivalence.

Action: S01–S03, N01 and C01. Do not demand a formal proof of prose; require a
precise reviewed mapping and mathematical correspondence lemmas where possible.

### RV02 — Behavioral composition bypassed the real pass contracts (high; fixed for this profile)

Before this change, `CStatements.lower_behavior_correct` rewrote target and
source behaviors to a fixed `profileResult`. The public real-equation chain
was separately proved and included in `ArtifactContract`, but was not used
to transport the behavioral relation through the intervening IRs. This was
valid for the singleton semantic language, but a weak architecture for growth.

Implemented in [Profile](../packages/core/RumocaCore/Profile.lean) and
[Behavioral](../packages/compiler/Rumoca/Behavioral.lean):

* `Profile.AdmitsUnit` requires the **complete** derivative solution set to be
  `{1}` before the fixed numerical method is applicable.
* `Profile.behavior_congr` transports that condition and relational rounding
  behavior across an equation-equivalence theorem.
* `Flat.behavior_correct`, `DAE.behavior_correct` and `Solve.behavior_correct`
  lift the corresponding real pass contracts.
* `CStatements.solve_behavior_correct` supplies the operational target edge;
  `lower_behavior_correct` composes all four edges. The existing artifact and
  driver capstones now use that composition.

This is intentionally a **unit-derivative policy**, not a purported general
ODE solver. General partial-pass interfaces, error relations, state mappings
and a reusable driver framework remain P01 work. Both an incorrect derivative
equation and an underdetermined equation now have explicit rejection proofs.

### RV03 — Source semantics depended on a C function enumeration (medium; fixed)

`Source.SampledBehavior` previously accepted `CStatements.Function`. That
made the supposedly source-level interface depend on the selected backend.
The call vocabulary and numerical policy now live in shared core `Profile`;
the C backend aliases the shared vocabulary. `Rumoca.Source` has no transitive
backend or driver import. Source name resolution remains an explicit condition,
because constant derivative assignments alone cannot check names.

### RV04 — No convenient source-property transfer theorem (medium; fixed)

The all-behavior theorem implied property transfer but exposed only the
equivalence statement. [Verified](../packages/compiler/Rumoca/Verified.lean)
now includes `compiler_preserves_property`: any predicate proved for all
source-profile observations holds for every behavior of the actual parsed
output. It is derived from the existing capstone, without an added assumption
about target execution. This supports safety/result properties directly.

### RV05 — EBNF correctness stops at an executable dialect definition (medium)

[EBNF](../packages/parser/Parser/EBNF.lean) is total and its result is
kernel checked when certifying generated tables. The recognizer certificates
are substantive. However, there is no independent declarative metalanguage
relation with reader soundness/completeness. AST construction is a separate
fixed 16-token decoder; accepting a new EBNF does not automatically prove new
semantic actions. Action: P02–P03. Recursive grammar support is not required
to fix this for the current acyclic dialect.

### RV06 — C semantics and printing are specific to fixed function shapes (medium)

The statement interpreter separately executes assignment, decrement, guards
and return. It really proves termination and absence of stuck execution for
all valid inputs; it is not merely a comparison with a reference CSV trace.
However, `print_parses`, scoping and several arithmetic proofs use
`lower_is_unit`. There is no general typed C memory semantics, reusable
declaration printer proof, or independently reusable backend contract.

`CExecution` and `CStatements` also remain two execution models. Both have
results about the generated code, but there is no explicit simulation between
them. Describing the former as a proved abstraction of the latter overstates
what is proved. The documentation now calls it an earlier model with separate
proofs. Action: C02; retire it or prove the abstraction relation.

### RV07 — Binary64 model needs independent validation (high)

The finite-bit bijection, signed zeros, nearest/even specification, overflow
precondition for `x+1`, exactness conditions and real-error bounds are proved.
`roundWitness` is opaque but has a checked value/proof, not an extra axiom.
It is never executed by the compiler. Those are sound design choices.

What remains is an independent review/correspondence argument for IEEE field
decoding, spacing, ties and overflow. The generic finite minimum saturates to
a finite value outside the admitted domain; C expression evaluation excludes
overflow and the emitted operation proves the exclusion cannot be reached.
This must remain explicit when arithmetic is extended. Action: N01–N02.

### RV08 — Artifact evidence is not yet a reproducible release record (medium)

The fixed checker reads actual source/C/EBNF strings and constructs its own
proposition. A producer's `True` proof or a genuine proof about different
bytes does not authorize output. Existing adversarial tests cover both cases.

The shell manifest records selected artifacts and metadata, not the complete
local proof-source/build closure, all options or the identity of every loaded
compiled Lean module. The workflow also assumes files/build inputs stay stable
while checking and hashing; it is not a hostile-filesystem protocol. These
are provenance/trust boundaries, not demonstrated false Lean theorems.
Action: A01, including fresh-checkout reproduction and failure cleanup.

### RV09 — Performance assurance is not measured (medium)

The runtime imports stay small; mathematical finite minimization is excluded
from execution. Nonetheless, no versioned workloads or regression budgets
measure compilation, proof checking, memory or C performance separately.
Kernel checking of generated certificates already dominates the small example.
Action: E01. A mathematical termination proof does not bound embedded latency.

### RV10 — The product is not an FMI FMU (high for the requested product)

Current C output exposes `rumoca_rhs`, `rumoca_step` and `rumoca_sample`.
There is no FMI ABI, instance lifecycle, `modelDescription.xml`, source build
description or `.fmu` archive. These functions must not be presented as FMI
Model Exchange or Co-Simulation.

The existing Rumoca reference was inspected at
`crates/rumoca-phase-codegen/src/templates/fmi3/`: its target emits both ME and
CS around shared component state, with internal derivative evaluation and an
RK4 routine used by CS. Its README labels its standards/importer evidence
separately from formal proof. No Rust/Jinja implementation is copied into this
Lean compiler.
Reference checkout: branch `msl-trace-parity-50`, commit
`a1daf47556c1a6ffd7f4b203235ff09711089a85` (read only).

The requested direction is **a shared ME model kernel, used by both an ME ABI
and a CS lifecycle with an embedded solver**. FMI's two interfaces remain
distinct; internal reuse does not permit ME-only ABI calls on a CS instance.
FMI defines the interfaces, not the numerical solver algorithm.
[FMI 3.0.2, Model Exchange and Co-Simulation](https://fmi-standard.org/docs/3.0.2/)

Action: the new F01–F04 sequence in the roadmap. It must cover lifecycle/time,
error atomicity, state access, solver arithmetic, ABI and package consistency.
Neither adding FMI-named C functions nor validating XML extends the current
compiler theorem automatically.

Initial implementation: [Solve.ModelExchange](../packages/core/RumocaCore/Solve/ModelExchange.lean)
now separates ME state/derivative evaluation, a unit-step solver and CS state
containing the ME state. State access, derivative preservation, no overflow,
repeated-step result and exact step-count progress have Lean theorems.
`CStatements.model_exchange_correct` and `co_simulation_correct` connect the
existing scalar exports to these internal semantics, and both are included
in `ArtifactContract`. This starts F01; it does not close Float64 time, lifecycle,
C instance-memory, ABI or packaging obligations. No `.fmu` is generated yet.

## Validation and residual claim

The mandatory reproduction command is:

```sh
nix develop .#verification --command lake test
```

This review adds sixteen audited theorem roots and three semantic regression
roots. Final gate results are recorded in the roadmap. Broad assurance items
stay open until their own exit criteria are met. The current defensible claim
is a verified frozen compiler **relative to the documented source, numerical
and C specifications**, with explicit work remaining before CompCert-level
assurance or a verified FMI product can be claimed.
