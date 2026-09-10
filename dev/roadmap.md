# Roadmap to a verified Modelica compiler core

The current full gate is `nix develop .#verification --command lake test`.
Make commands in dated checkpoints below record historical runs before the
Lake migration; see the [current commands](../docs/development.md).

Status reviewed: **2026-09-10**. This file is the local, authoritative task
tracker. [verification.md](../docs/verification.md) records what is proved today;
this roadmap records the work and evidence required for stronger claims.
An open item is not a current guarantee. The active first-party review and
initial fixes are owned by Codex; independent review owners are unassigned.
See [the detailed compiler review](compiler-review.md) for findings RV01–RV10.
The [MLS/FMI/eFMI standards review](standards-review.md) records SR01–SR08 from
the unit implementation and artifacts. Its repair order takes priority over the next
tensor/FMI implementation increment; full standards compliance is not claimed.

**Hard stage-completion gate, reaffirmed by the user:** before adding any more
scope, the entire admitted subset must justify calling the resulting compiler
formally verified. A proved operator, lowering, numerical core, or successful
body is progress inside an unfinished stage. It does not complete that stage.
The present unit-only FMI/eFMI stage is unfinished. In particular, a green
`lake test` run does not close obligations outside its checked propositions.

Completion requires preservation theorems for every lowering, composed into
the actual compiler's end-to-end contract for **all admitted sources**, with
the emitted production C and both target artifacts bound to those semantics.
The contract must account for every supported public operation and reachable
behavior, including initialization, errors, memory effects, lifecycle and
solver/numerical conditions. Unsupported features must remain rejected or
follow their specified interface behavior. Parser and printer soundness,
artifact binding, FMI/eFMI conformance obligations and the stated trusted
boundary must all be reviewed at the scope of the whole claim. No new axioms,
weaker contracts, hidden successful-execution premises or narrower tests may
substitute for missing coverage. The proof target remains the authored C
semantics; subsequent native compilation is an explicit external boundary,
not a reason to add a machine backend now.

**Recurring standards gate:** before each spiral-stage grammar expansion,
review the complete admitted subset against **MLS 3.7, FMI 3 ME/CS and eFMI
Algorithm/Production Code**, using the pinned normative versions. Record the
source revision and artifacts reviewed, applicable clauses, source/IR/target
theorems, external assumptions and unresolved findings. Carry forward earlier
findings and recheck affected interactions, including initialization, numeric
representation, lifecycle, errors and correlated metadata. Any open compliance
finding for that subset blocks expansion; the full compiler/artifact proof
gate remains required as well. Tests remain a last resort for external
boundaries, and no schema/importer pass substitutes for normative alignment.
The standard-language portion and the deliberate `jacobian` extension must be
identified separately. MLS means the Modelica Language Specification here;
support for the Modelica Standard Library is a different coverage question.
Use the [recurring stage checklist and current clause map](standards-review.md#required-review-at-every-spiral-stage)
for the review record. It currently leaves the unit stage open.

The tiny [eFMI Algorithm Code checkpoint](efmi.md#algorithm-code-checkpoint-evidence)
passes the full gate: E01–E03 cover the checked DAE product, tensor Solve
refinement and actual `.alg` file. E04 now also checks the complete Production
C member, memory effects and serial traces. The correlated eFMU now has an
actual source-to-archive contract and a passing publication gate; E05–E06
remain open for the documented standards/checker discrepancy, cross-standard
initialization correspondence and release review. The status-mapping correction
is checked below. This checkpoint does not close whole-FMU or generic parser
completeness obligations in this roadmap.

The destination is a maintainable Lean compiler whose supported Modelica
language has compositional correctness guarantees through
**Modelica → Flat → DAE → Solve → production C inside an FMI 3 FMU**.
The user has selected a tiny input/state profile and now requests a minimal
array/operator slice with the `jacobian` built-in and proved forward/reverse AD;
see [the tensor AD plan](tensor-ad.md). The unit-derivative compiler remains
the verified regression floor. Each newly admitted production case still
requires the complete lowering and actual-artifact contract.
The development array parser now covers the two-wide driven and square/Jacobian
profiles. Its EBNF tables, decoder contracts, lexical extension and exact call
spans pass the package audit; native checks preserve ordinary call names and
confirm that production still rejects both new profiles. The array AST → Flat
→ DAE → executable Solve chain now preserves the complete equations, fixed
initialization and dense Jacobian observation. The compiler's development
preparation API binds its stored kernel to the located source parse and EBNF
membership. See the checked roots in [tensor-ad.md](tensor-ad.md).
Whole-program forward AD now
emits ordinary typed Solve instructions with primal preservation, a constant
instruction expansion bound and a mathlib derivative theorem. Saved-primal
reverse execution has the corresponding adjoint theorem, including shared
register accumulation. Static reverse lowering and finite target/artifact
contracts remain open. The complete local and hosted gates passed for both
the AD checkpoint and the array source-to-Solve chain. Exact product rounding,
signed underflow, ordered finite tensor execution and the array RHS/Jacobian
coefficient error bounds passed both their package audits and hosted CI.
The counted C add/multiply helper bodies now have all-behavior finite Solve
and memory-frame theorems, plus an independent token/printing contract and a
fixed actual-file checker. The eleven new roots pass `build/c-tensor-audit.log`.
Whole-program storage/call composition, prepared metadata, overflow/FMI policy
and actual tensor FMU/eFMU artifacts remain the next obligations. The helper
contract does not admit the array models into production compilation.
The next increment now also checks ordinary helper calls, parameter conversion,
caller restoration and runtime fills for the existing initialization/AD seeds.
It strengthens the actual-file contract and shares one counted-write proof
across all three helpers. Its package and artifact gates pass in
`build/c-tensor-call-fill-audit.log` and `build/c-tensor-call-fill-gate.log`.
The call/fill checkpoint passed the full local gate and
[CI for e89e4f4](https://github.com/CogniPilot/rumoca_lean/actions/runs/34471779750).
The complete prepared-program execution proof now composes disjoint
intermediate buffers and the exact result reference. Its structural C printer,
22 new audit roots and the actual-file/native gate pass in
`build/c-tensor-program-gate.log`; the full repository gate passed in
`build/c-tensor-program-full-gate.log` and in
[CI for 08b8a7d](https://github.com/CogniPilot/rumoca_lean/actions/runs/34476481293).
The subsequent outer-call theorem proves parameter binding, complete execution
and return. The fixed file contract now also derives scratch/input invariants
from concrete symbolic initial storage for the square coefficient program.
Allocation, native object layout and ABI remain outside these proofs.
All 34 added roots and the stronger actual-file/native gate pass in
`build/c-tensor-entry-gate.log`; the required full gate passed in
`build/c-tensor-entry-full-gate.log` and in
[CI for 6d4ec7c](https://github.com/CogniPilot/rumoca_lean/actions/runs/34479402664).
The diagonal output helper now has a complete call, matrix-value and memory-frame
theorem, tied to the prepared Solve diagonal and its actual printed file.
Its 35 new roots and the actual-file/native check pass in
`build/c-diagonal-gate.log`; the full gate passed in `build/c-diagonal-full-gate.log`
and in [CI for 8a3b902](https://github.com/CogniPilot/rumoca_lean/actions/runs/34483284726).
The complete Jacobian function now composes coefficient production and diagonal
output, with call-entry/return, concrete symbolic storage and full memory-frame
proofs. Its 23 added roots and the actual-file/native gate pass in
`build/c-diagonal-model-gate.log`; the full gate passed in
`build/c-diagonal-model-full-gate.log` and in
[CI for f63d69a](https://github.com/CogniPilot/rumoca_lean/actions/runs/34487668082).
The reusable named function builder now constructs initial, RHS and optional
Jacobian entries from one prepared IVP, with a per-member complete-call/printer
contract. The same square model's three actual C files also require the concrete
initializer/RHS and existing Jacobian storage proofs. Its 22 added roots and
the actual-file/native gate pass in `build/c-ivp-gate.log`; the required full
gate is tracked in `build/c-ivp-full-gate.log`.
Typed tensor calls now compose with value-returning caller contexts, and the
prepared IVP's actual-file contracts include that stronger result. Actual FMI
wrapper execution is still open. After the standards corrections below,
compose those public wrappers, bind instance storage/metadata, and establish the finite overflow/error,
lifecycle/time and source-to-archive contracts for FMI and eFMI.
Preserve the existing diagonal representation;
general sparsity analysis, compressed storage and coloring follow this FMU
round, with structural-zero and execution-preservation proofs. No new grammar
case is needed for the current work.
The roadmap does not declare the broader core finished because the unit
integrator has a theorem. It also does not equate a supported core with all
of Modelica 3.7.

## Standards corrections before the next backend increment

- [x] **SR01/F03/F04:** declare the source-FMU math dependency and numerical
  compilation profile; have the existing source rebuild consume that metadata.
  **Implemented:** shared Linux/GCC recipes drive XML and the native invocation;
  independently decoded requirements and actual XML bytes strengthen the
  numerical file contract. Six new audit roots pass `build/fmi-build-package.log`.
  The existing rebuild reads the XML and uses a separate symbol-resolution
  process; the actual-file, schema, native and mutation gate passes in
  `build/fmi-build-artifact-gate.log`. The required full gate passed in
  `build/fmi-build-full-gate.log`. This closes the source-build metadata correction.
  [CI for f1ce838](https://github.com/CogniPilot/rumoca_lean/actions/runs/34502115582)
  also passed.
  The complete FMI adapter/model-description/archive capstone remains open.
- [x] **SR02/F03/F04:** give numerical symbols private or consistently namespaced
  linkage, certify the declaration change, and check two source FMUs link together.
  **Implemented, full local gate passed:** generalized C/whole-compiler contracts
  retain all prior obligations for internal linkage; FMI compiles one adapter
  source including its private kernel. Parsed names determine valid, distinct
  identifiers for distinct source names. The actual-file contract includes the
  source prefix and ME/CS XML identities; the remaining adapter/CPP/linker/ZIP
  capstone stays open. Thirteen new roots pass `build/fmi-linkage-package.log`.
  The actual-file, importer, source-link, mutation and failure-preservation gate
  passes in `build/fmi-linkage-artifact-gate.log`.
  The required full local gate passed in `build/fmi-linkage-full-gate.log` at
  `efb5c80`; [its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34509004071)
  also passed. This closes the source-linkage correction only.
- [x] **SR03/E05:** map each C status result to the Algorithm Code error anchor,
  prove that decoded mapping observes execution, and strengthen the actual
  manifest/archive contract. Schema validation alone previously missed this.
  **Implemented:** per-instance status storage/return, unique decoded mappings,
  complete method/printer proofs and both initialized/uninitialized status
  observations in the archive contract. Nine new roots pass the package audit
  in `build/efmi-status-package.log`; the complete artifact gate passed in
  `build/efmi-status-full-gate.log`, including redirected-status rejection.
  [CI for feb57a9](https://github.com/CogniPilot/rumoca_lean/actions/runs/34499145712)
  also passed.
  This closes the unit status-mapping correction; E05's broader obligations remain.
- [ ] **SR04–SR05/F02:** correct premature nominal-state access and resolve the
  strict initialization policy from normative clauses; include rejected behavior.
  **SR04 guard corrected:** the independent predicate and generated guard now
  reject Instantiated. The rejection-prefix theorem preserves caller storage
  and embeds in the typed tensor-call model. Complete disabled-logging error
  body behavior and both logging dispatch branches are proved; public argument
  binding, enabled callback execution and actual adapter-byte binding remain
  open. Sixteen new roots pass `build/fmi-error-embedding-audit.log`.
  The bridge exposed an existing nested declaration in SetFloat64. The existing lifecycle
  check rejects the old artifact; all thirteen groups and the actual-file gate
  pass for the correction in `build/fmi-nominals-artifact-gate.log`.
  The required full gate passed in `build/fmi-nominals-full-gate.log` at
  `904e9bd`, and [its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34512618273)
  also passed. This closes that correction's validation, not the full failed-call proof.
  **Scope correction:** the setter now binds its instance before the empty-call
  branch and shares its mode guard. An all-behavior hoisting law retains the
  original empty/nonempty/null outcomes in the authored C model; typed proofs
  cover the emitted empty/null bodies and nonempty lifecycle prefix. Every
  generated FMI body now satisfies the unchanged scope predicate, with no
  SetFloat64 exclusion. Nine new roots pass `build/fmi-setter-scope-audit.log`.
  All thirteen existing artifact/importer groups and the source-link/mutation
  gate pass in `build/fmi-setter-scope-artifact-gate.log`, including null setters
  and empty-call state preservation. The required full gate passed in
  `build/fmi-setter-scope-full-gate.log` at `1a53884`; [its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34516914151)
  passed as well. **Public entry:** unsized-array parameters now adjust to
  explicitly resolved pointer types. Shared binding proofs derive matching
  value/type environments and exact arity. Complete ME get/set continuous-state
  calls connect to the existing Solve observations and updates, including exact
  bit patterns and memory frames. Twelve new roots and the full package audit
  pass in `build/fmi-array-call-audit.log`. The FMI artifact/mutation gate and
  all thirteen native groups pass in `build/fmi-array-call-full-gate.log`.
  That required full local run also passed the complete GALEC/eFMU archive,
  extracted-manifest and mutation checks at `30ef448`;
  [its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34521375057)
  also passed.
  Other public signatures, rejected calls, strings/callbacks, nonempty setter
  loops and the actual adapter contract remain open.
- [ ] **C01/F03, string-printer and storage prerequisite:** `CTree.quote` previously left
  question marks unescaped. A C11 translation of its output for `??/n` changed
  the bytes through trigraph replacement (strict GCC also rejects it under
  `-Werror=trigraphs`). Reproduced at `30ef448` in
  `build/c-string-trigraph-before.log`. Existing unit-runtime literal inputs
  do not contain this sequence; this is a generic printer defect, not an
  observed failure of the current FMU. **Printer correction implemented:**
  `CTree.quoteByte` now escapes question marks. `CString.render_correct`
  universally binds the actual expression printer to independent, unique
  UTF-8-plus-zero byte denotation after trigraph/line-splice rewrites, under
  the eight-bit ASCII C profile. All four added roots and the package audit
  pass in `build/c-string-printer-audit.log`. The original failing example,
  emitted through the actual Lean printer, passes strict native C11 in
  `build/c-string-trigraph-after.log`; no new permanent test suite was added.
  The required full gate is tracked in `build/c-string-printer-full-gate.log`.
  Immutable literal storage, pointer decay, ordinary string-parameter binding
  and complete error-call/actual-adapter composition remain open.
- [ ] **SR06–SR07/E06/F04:** resolve the official checker's standalone-layout
  mismatch and complete independent semantic/coding-guideline release review.
  A diagnostic wrapped copy passes deeper checker checks; the actual standalone
  archive has no official-checker pass. Remaining FMI capstone proofs stay open.

The [review](standards-review.md) gives reproduction evidence and closure
conditions. These corrections add no grammar cases. Each interface increment
must connect a cited requirement, independent predicate, execution theorem and
actual-artifact observation so specification errors are found before expansion.

## Frontend infrastructure before further grammar growth

The user has prioritized automatic source spans, a small Lean LSP and parallel
multi-file parsing. Their checked foundation, exact limits and remaining
IR/printer provenance obligations are tracked in [provenance.md](provenance.md).
`Parallel.map_eq` proves deterministic equivalence to sequential work for any
pure analysis function. The native CLI exposes `rumoca parse --jobs N FILES...`.
The LSP consumes structured source diagnostics; the CLI renders source context
from the same range data. None of these additions admits a new grammar case.

Name-resolution diagnostics now include a related declaration range. The
kernel-checked `LocatedParsed.resolve_error_locations` theorem identifies the
actual erroneous AST occurrence and the corresponding declaration, including
their exact source text; `resolve_complete` preserves successful resolution.
CLI JSON retains both byte ranges, terminal output renders both contexts, and
the LSP publishes the related location when the client advertises support.
The package audits and existing frontend integration checks pass in
`build/diagnostic-locations-audit.log` and
`build/diagnostic-locations-frontend.log`. The full local gate also passed at
`df382d0` in `build/diagnostic-locations-full-gate.log`, including both target
artifact gates. Migration of the compiler entry point
away from failure-only reparsing, wrapper completeness, and IR/output origin
preservation remain open in PV05–PV09. This is a diagnostic improvement, not
closure of the compiler or artifact proof gate.

The user's airborne software assurance target is tracked in
[airborne-assurance.md](airborne-assurance.md). It requires requirements and
verification traceability in addition to source ranges; no DO-178C compliance
or tool qualification claim is made.

## What “comparable to CompCert” means here

CompCert's whole-compiler result uses backward simulation; its behavior
results relate every target behavior to source behavior, with a qualification
for source undefined behavior. The relevant standard is universal semantic
preservation, composable passes, explicit side conditions and an audited
trusted boundary. See its [compiler theorem](https://compcert.org/doc/html/compcert.driver.Compiler.html)
and [behavior definitions](https://compcert.org/doc/html/compcert.common.Behaviors.html).

Our target is C, whereas CompCert targets an assembly representation.
Comparison concerns the assurance of the chosen boundary, not equal language
coverage or a machine-code theorem. CompCert also documents external steps
outside its formal result in its [scope description](https://compcert.org/man/manual001.html).

A release of this core must establish all of the following:

1. Successful compilation of every admitted source produces a well-formed C
   program whose **every observable behavior** is allowed by the source's
   declared numerical profile. Termination, divergence, errors and observable
   traces must be covered whenever the supported language can express them.
2. Each lowering has its own semantic contract and proof, and the driver
   theorem composes those contracts. Declarative equation equivalence is the
   right relation before execution is chosen; operational simulation/refinement
   is the right relation after Solve. Do not force continuous DAEs into an
   inappropriate discrete small-step model just to copy CompCert's architecture.
3. Mathematical Modelica Real semantics, numerical-method approximation and
   exact finite-arithmetic compilation are separate. No exact-real equality
   is claimed for rounded execution. Solvability, regularity and numerical
   assumptions must be explicit and justified for each supported case.
4. The semantics are independently specified and reviewed against MLS 3.7,
   the selected C profile and IEEE754. Proving a compiler correct against a
   convenient model alone does not establish that model's fidelity.
5. The actual grammar/source/output artifacts, toolchain, compiler options,
   proof dependencies and mandatory checks are bound to the release evidence.
   An untrusted candidate generator cannot choose the proposition to verify.
6. Lean remains the implementation and proof language. No placeholders,
   added axioms or native-reduction axioms; only the documented standard
   foundations. C compilation, linking and hardware stay named external
   assumptions until a separate backend-composition project proves more.

## Tracking rules

Use the task IDs below in changes and review reports. Check a box only when
its complete exit criterion is met. Attach theorem/module references,
reproducible commands, the reviewed revision (or explicitly identified working
snapshot), gate results and the review disposition. A green test or a matching
hash alone cannot close a semantic item. Reopen an item when a change invalidates
its evidence; update the language/profile matrix at the same time.

For an active item, record an owner, the concrete next action and any blocker
here. A blocker needs a missing dependency or decision, not just a difficult
proof. Splitting an item preserves all of its original exit criteria. Do not
count checked boxes as a percentage of semantic coverage.

| Release gate | Dependencies | Current state | Required decision |
| --- | --- | --- | --- |
| R0: preserved test-compiler baseline | B01–B05 | Passed 2026-09-09 including FMU integration; revalidate after changes | Required regression floor, not a parity claim |
| R1: assurance closure for frozen grammar | S01–S03, P01–P04, N01–N02, C01–C02, A01–A02 | Open | Review accepts the supported-profile claim and remaining trust boundary |
| F: tiny FMI 3 ME+CS slice | R1 assurance obligations plus F01–F04 for the selected input/state profile | Active, incomplete | Actual FMU and production-C/FMI proofs, not just an internal kernel |
| R2: reusable verified core | R1, G01–G05, E01–E02, Q01 | Open | Every supported feature is covered by the composed theorem and evidence matrix |
| R3: external products/backends | R2 plus each product's own contracts | Deferred | Separate scope; does not delay honest completion of R2 |

**Active work:** RV02–RV04 have implementation fixes: target-independent source
semantics, behavioral composition of each IR pass, and source-property transfer.
The full gate passed; evidence is in `build/compiler-review-gate.log`.
S01/P01 are partly implemented, not closed. Subsequent user instructions
prioritize FMI 3 ME-within-CS architecture (F01–F04), tensor structure in every
indexed IR, a thin `backend-fmi3`, and the minimal driven profile below.
FMI wrapper proofs are additional obligations; an FMU claim must not be inferred
from the scalar C theorem. G01–G05 remain future work and must not expand this
slice before its proof chain and conformance contracts are complete.

**Latest parser priority:** the user requested an in-tree LALR(1) implementation
and a proof-carrying grammar-to-parser boundary. P04 and LR01–LR07 in
[the parser plan](lalr-parser.md) now take priority before grammar expansion.
This infrastructure work does not close or replace the FMI obligations below.
Keep the parser reusable across grammar files and language-specific actions;
The user has since authorized the tiny GALEC/eFMI path as the second EBNF reuse
case. See [the eFMI review and gates](efmi.md). This adds no Modelica equations
and does not replace generic parser completeness or the FMI core obligations.
The parser design must also support competitive parol/ANTLR throughput across
thousands of files: immutable shared tables, pure per-file actions and bounded
parallel workers with deterministic result association. See the
[performance and batch contract](lalr-parser.md#performance-and-parallel-batch-design).
Performance parity and the concurrent adapter are not yet established.
Modelica and GALEC are the design workloads: share the verified LR engine,
but keep distinct lexical contracts and typed AST actions. Preserve standard
grammar meaning when resolving future conflicts, and account for GALEC's nested
comments and different name/number forms before reusing a lexer. See the
[language-specific design priorities](lalr-parser.md#modelica-and-galec-design-priorities).
The newly authorized GALEC profile is deliberately restricted to the existing
unit model. Full lexical features and broader language support remain deferred.

```modelica
model DrivenIntegrator
  input Real u;
  output Real x(start=0, fixed=true);
equation
  der(x) = u;
end DrivenIntegrator;
```

The production CLI still rejects this profile. Its parser/action contract and
the new tensor Flat/DAE/Solve path are development work awaiting their target
and actual-artifact contracts. See [the IR review](ir-review.md) for the concrete
comparison to `~/git/rumoca`, and [the FMI contracts](fmi3/contracts.md) for the
required ME/CS conformance theorems. Rendering uses ordinary Lean typed builders
and printers; no general template engine or additional backend is in scope.

Next: finish the tensor IVP's correlated metadata and finite input/step policy,
then prove its target/runtime edge and FMI state-machine refinement. Carry the
supported-profile/trust matrix (S01/S03), arithmetic/C correspondence (N01/C01)
and generic pass composition (P01) through that same slice.

**Unit FMU implementation (2026-09-09):** the existing production unit profile
now has a Lean ME+CS archive producer and a separate `fmu-runner` package around
FMPy. No new grammar case is admitted. The driver checks the actual staged
numerical C kernel before native compilation, validates the ZIP/XML, and
publishes only after success. New proofs cover prepared-Solve projections,
the authored lifecycle table and the generated integer/Boolean guard AST.
The complete emitted ABI adapter, Float64 communication time, instance memory,
callbacks, XML correlation and whole-FMU artifact proposition remain open.
This implementation must not be counted as closure of F01–F04 or R1.

**Validation:** `nix develop .#verification --command make test` passed on
2026-09-09 for this working tree; log: `build/fmu-gate.log`. The gate checked
142 main proof roots plus 8 scalar and 4 tensor regression roots (154 total),
with only the documented standard axioms. All ten FMI integration test groups
passed, along with CLI failure propagation and preservation of a prior FMU
when native compilation fails. `build/Integrator.fmu` contains both interfaces
and an x86_64 Linux binary; `build/Integrator-me.csv` and `Integrator-cs.csv`
both record the expected four samples. The working source inventory is
recorded in `build/fmu-snapshot.sha256`; these hashes are provenance, not proofs.

Current organization: [parser](../packages/parser/README.md),
[shared core IR](../packages/core/README.md),
[FMI 3 backend](../packages/backend-fmi3/README.md) and
[compiler](../packages/compiler/README.md) are separate Lake packages.
The independent [FMU runner](../packages/fmu-runner/README.md) is a fifth package.
The backend consumes Solve IR and owns C syntax, rendering and target proofs;
the compiler composes them with source semantics and artifact checking. The
parser owns the EBNF file and generated tables. The repository root owns only
workspace tooling and shared integration assets. This
separation supports future producers without closing the open generic-contract
or specification-review items below.

## Baseline already implemented

These items have concrete proof roots, rather than only implementation tests.
The full gate is `nix develop .#verification --command lake test`; local results
are recorded in `build/compiler-review-gate.log`. The source files below are the
lasting evidence and the command is how to reproduce it.

Earlier baseline validation: **2026-09-08**, the reviewed working snapshot with composed
behavior contracts, source/backend separation and internal ME/CS model proofs.
The complete gate passed: root build, all four package libraries, grammar
freshness, 103 main and eight regression theorem-root audits, native C tests,
actual-file verification and all forged-artifact/parser mutation controls.
See `build/compiler-review-gate.log`, `build/proof-audit.txt` and
`build/semantic-regressions.txt`. The implementation snapshot is listed in
`build/compiler-review-snapshot.sha256`; that manifest's SHA-256 is
`8f77c396dc94ba666eaa9dd73a3760655adc56f93e04c26a81c7996b402f9107`.
It records local implementation, proof and tooling files, not an independent
release attestation. The artifact manifest and source snapshot checks also
passed. R1, R2 and F01–F04 retain their open criteria.

Latest regression validation: **2026-09-08**, after the `backend-fmi3` rename,
selected reference EBNF productions, generic parser actions, tensor IVP and
mathlib storage bridge. `nix develop .#verification --command make test`
passed: all four package libraries, grammar freshness, 130 main theorem-root
audits, eight scalar and four tensor regression-root audits, native execution,
actual-file certificates and every forged-producer/mutation control. The
generated grammar now shares checked source/lexing/parsing/expansion facts;
the actual grammar equality remains in the fixed artifact proposition.
See `build/tensor-ir-gate.log`, `build/proof-audit.txt`,
`build/semantic-regressions.txt` and `build/tensor-regressions.txt`.
The implementation/proof/tooling snapshot is `build/tensor-ir-snapshot.sha256`,
whose SHA-256 is
`33725fc7961b48f3eb11977a34233dd3e6a39fe0ba7cf1284a34d585b3e758a0`.
This revalidates the unit-profile production boundary and the separate tensor
development proofs. It does not admit the driven profile to production or
close the FMI milestone. `nix develop .#verification --command lake run demo`
also passed, producing samples `0.5, 1.5, 2.5, 3.5`; see
`build/tensor-ir-demo.log`.

- [x] **B01 — Source parsing and EBNF certification.** Lexer/parser soundness and
  completeness, generated DFA certificates and original-symbol reflection.
  Evidence: [parser package](../packages/parser/README.md),
  [ParserProofs](../packages/modelica-parser/ModelicaParser/ParserProofs.lean),
  [Alphabet](../packages/parser/Parser/Alphabet.lean).
- [x] **B02 — Named per-pass contracts.** AST/Flat equation equivalence,
  residual formation, solving the sole derivative and C lowering.
  Evidence: [Lowering](../packages/compiler/Rumoca/Lowering.lean),
  [C lowering](../packages/backend-c/RumocaC/Lowering.lean),
  [Semantics](../packages/compiler/Rumoca/Semantics.lean), [IR](../packages/core/RumocaCore/IR.lean).
- [x] **B03 — Finite representation and numerical reference.** Finite-bit
  bijection, signed zeros, nearest-even specification, no overflow for x+1,
  exactness conditions, error bounds and real-solution uniqueness.
  Evidence: [Binary64](../packages/core/RumocaCore/Real/Binary64.lean),
  [Encoding](../packages/core/RumocaCore/Real/Encoding.lean), [Behavioral](../packages/compiler/Rumoca/Behavioral.lean).
- [x] **B04 — All-behavior result for the frozen profile.** Scoped C statement
  execution, all-call termination/completion and behavior equivalence with
  relational rounded sampling. Evidence: [CStatements](../packages/backend-c/RumocaC/Statements.lean),
  [Transition](../packages/core/RumocaCore/Transition.lean),
  `compiler_semantic_preservation` in [Verified](../packages/compiler/Rumoca/Verified.lean).
- [x] **B05 — Actual-file and counterexample checks.** Fixed proposition built
  from actual EBNF/source/C files; forged and mismatched candidate rejection;
  axiom audit and native examples. Evidence: [ArtifactCheck](../packages/compiler/Rumoca/ArtifactCheck.lean),
  [negative controls](../tests/verification-negative.sh),
  [semantic regressions](../packages/compiler/Tests/SemanticChecks.lean), [Audit](../packages/compiler/Tests/Audit.lean).

Current limitations motivating R1: the AST and IR invariants admit just one
semantic equation; several proofs reduce to `lower_is_unit`; the C grammar
has three fixed function shapes; the EBNF reader itself defines its dialect;
finite arithmetic is an authored specification; and the behavior framework
is specialized to deterministic calls without external events. These are
scope limitations, not counterexamples to the checked tiny-core theorems.

## R1 — Close assurance gaps before growing the grammar

### Work completed from the 2026-09-08 review

- [x] **P01a / RV02 — Compose frozen-profile behaviors through every IR.**
  `Profile.behavior_congr` lifts complete derivative solution-set equivalence.
  `Flat.behavior_correct`, `DAE.behavior_correct`, `Solve.behavior_correct` and
  `CStatements.solve_behavior_correct` compose in the actual artifact capstone.
  `lowering_chain_behavior_correct` instantiates all driver lowering functions.
  Wrong and underdetermined equation policies have rejection proofs. This
  closes the frozen composition defect, not all of P01's future-facing criteria.
- [x] **S01a / RV03 — Remove the source/backend dependency.**
  `Rumoca.Source` imports no C module; shared `RumocaCore.Profile` owns the call
  vocabulary and fixed numerical policy. Name resolution remains explicit.
- [x] **P01b / RV04 — Transfer source properties to output behaviors.**
  `compiler_preserves_property` follows from `compiler_semantic_preservation`
  for actual emitted and independently parsed C. New theorem roots are audited.
- [x] **C02a / RV06 — Correct the duplicate-machine claim.**
  Documentation now distinguishes two independently proved execution models
  from a proved simulation between them. That simulation is still open.

- [ ] **S01 — Fix the supported-language and observation contract.** Depends
  on B01–B04. Create a clause-by-clause matrix for the admitted MLS 3.7 syntax,
  name resolution, Real equation, externally supplied initialization, time
  grid and callable interface. Specify admissible inputs, failure behavior,
  observations and rejected features. **Close with:** an independent
  specification document plus reviewed correspondence to source definitions;
  every precondition is classified as checked, proved or an external contract.
  Source semantics must not depend on a target-specific function enumeration.
  **Review note:** distinguish the ideal unbounded `Source.Solves` trajectory
  from MLS §4.9.1's finite stored Real values. The numerical profile supplies
  the finite representation contract; the ideal ODE theorem alone does not.
  The [current unit clause map](standards-review.md#current-unit-stage-follow-up)
  now records this correspondence. **SR08 remains open:** reconcile source
  initial-value choices, FMI initialization metadata and GALEC Startup under
  MLS initialization/fallback rules, including required declaration diagnostics.
- [ ] **S02 — Independently review the proof statements.** Depends on S01.
  Review model fidelity, quantifiers, non-vacuity, side conditions, source
  safety and the meaning of both directions of each pass relation. Include
  counterexamples to overly weak contracts. **Close with:** a review report
  naming exact definitions/theorems, resolved findings and retained assumptions.
  The existing kernel check does not substitute for this review.
- [ ] **S03 — Maintain a trust and coverage ledger.** Depends on S01. Enumerate
  kernel/imported libraries, source/target specifications, floating operations,
  checker elaboration, file encoding/I/O, preprocessor/header meanings, ABI,
  native compiler, host and hardware. **Close with:** a coverage map from each
  top-level guarantee to proof roots or a named external assumption, including
  a policy for invalidating evidence when dependencies or compiler flags change.

### Pass structure and source front end

- [ ] **P01 — Introduce composable pass contracts.** Depends on S01. Define
  explicit pass input/output relations and a reusable driver composition
  theorem, including partial-pass errors and well-formedness preservation.
  Keep source-bound/proof-carrying IRs where useful, but distinguish structural
  invariants from semantic preservation. **Close with:** the current compiler
  instantiates the framework and the capstone uses the per-pass contracts;
  replacing a pass with an identity or incorrect transformation fails its
  contract where appropriate. No grammar expansion is needed for this refactor.
  **Progress:** `RumocaCore.Pass` now supplies generic successful-pass behavior
  composition and property transfer. The driven equation and initialization
  chains compose each actual lowering. The production driver still needs to
  instantiate the generic operational contract at the complete new boundary.
- [ ] **P02 — Specify the EBNF metalanguage independently.** Depends on S01.
  State the supported dialect as a declarative relation, including
  grouping, alternatives, optional/repeated forms, empty terminals, comments
  and error/resource cases. **Close with:** EBNF-reader soundness and the
  promised completeness theorem against that relation, connected to existing
  DFA/original-alphabet proofs and AST actions. The user now requests an in-tree
  LALR(1) parser before grammar growth. The recursive EBNF-to-CFG edge must also
  preserve this relation; see [the LALR plan](lalr-parser.md), LR01–LR07.
- [ ] **P03 — Make parser/AST actions an extensible contract.** Depends on
  P01/P02. Keep the parser package independent of compiler IRs. Specify the
  AST-action relation separately from the generated recognizer, with token
  locations/diagnostics and resource limits explicitly outside or inside the
  promised completeness domain. **Close with:** current parser instantiation
  proves the contract; package-only builds and compiler builds both pass;
  generated-file freshness and actual-grammar binding remain mandatory.
  **Progress:** `ModelicaParser.Actions`/`ActionsProofs` provide reusable action
  soundness/completeness, source binding and original-symbol EBNF membership;
  `Driven` instantiates them. The legacy parser has not yet been consolidated
  onto this interface. EBNF notation now follows the selected reference grammar;
  the independent metalanguage specification remains P02.
- [ ] **P04 — Certify the in-tree LALR(1) replacement.** Active, owned by Codex.
  Depends on P02/P03. Candidate construction and a generic checked-tree
  soundness theorem now exist in Lean, using mathlib CFG semantics. A finite
  structural validator now implies freedom from internal table/tree errors for
  every input and fuel, with kernel certificates for the actual emitted tables.
  The production parser remains the existing DFA/action implementation.
  Nullable/FIRST coverage is now proved against every CFG derivation and
  instantiated for actual emitted fact arrays. **Next:** LR-item validation
  with universal completeness, termination/resource
  certificates, verified EBNF desugaring and typed AST actions. **Close with:**
  the actual grammar-to-parser product carries the full contract; both current
  profiles instantiate it; the production source/IR/artifact chain and complete
  gate pass. A few accepted trees or native recursion tests cannot close P04.
  **Evidence (2026-09-09):** `build/lalr-safety-gate.log` records the complete
  passing gate with 328 audited roots, including fifteen additional generic
  structural safety/execution lemmas and twelve validator regression roots.
  Actual emitted Modelica/recursive table certificates were kernel checked and
  axiom audited; corrupted shifts/edge annotations failed. Recursive parsing
  through depth 500, all existing artifact controls and thirteen native FMI
  groups passed. Working inventory: `build/lalr-safety-snapshot.sha256`.
  P04 remains open for the contracts listed above. The earlier LR foundation
  evidence remains in `build/lalr-gate.log` and `build/lalr-snapshot.sha256`.
  **FIRST coverage evidence (2026-09-09):** `build/lalr-first-gate.log` records
  the complete passing gate with 352 audited roots: fourteen new generic
  prediction/derivation lemmas and ten FIRST regression roots supplement the
  preceding safety increment. Emitted fact-array certificates and coverage
  corollaries were kernel checked and audited; a missing emitted array failed
  certification. All existing artifact controls and thirteen native FMI groups
  passed, and ME/CS traces agree. Inventory: `build/lalr-first-snapshot.sha256`.
  This proves coverage, not exact FIRST sets or LR-item/table completeness.

### Arithmetic and the target boundary

- [ ] **N01 — Review the finite IEEE model against an independent specification.**
  Depends on S01/S03. Check decoding, normal/subnormal spacing, both zeros,
  nearest/even ties, binade boundaries and overflow thresholds for the admitted
  operation. **Close with:** an IEEE field/arithmetic correspondence argument
  supported by Lean lemmas wherever it is mathematical, a reviewed standard
  mapping, and adversarial bit-pattern regressions. A finite minimum satisfying
  its own definition is not alone independent IEEE conformance evidence.
- [ ] **N02 — Separate numerical policy from compiler preservation.** Depends
  on P01/N01. Give source/Flat/DAE real semantics, the chosen Solve numerical
  policy and finite Solve execution distinct interfaces. **Close with:** a
  diagram of proved relations instantiated for the current ODE; exact finite
  behavior preservation, real-solution assumptions, representable exactness
  and numerical error are separate theorem conclusions. An opaque mathematical
  rounding witness may remain; an executable rounding algorithm is required
  only if the compiler starts computing with it (for example, constant folding).
- [ ] **C01 — Independently validate the C profile and calling contract.**
  Depends on S01/S03/N01. Review fixed header handling, C double evaluation,
  lexical parsing, scopes, sequencing, assignments, loop control, unsigned
  subtraction and return/entry behavior. **Close with:** a reviewed mapping
  to the selected C standard/profile, proof of required typing/progress and
  arithmetic conditions for all reachable compiled states, and explicit
  treatment of any defined C behavior excluded by the finite profile.
  CompCert/Clight can be a reference; all project proofs remain in Lean.
- [ ] **C02 — Isolate a reusable target semantics and backend interface.**
  Depends on P01/C01/N02. Separate generic typed target syntax/semantics from
  the three emitted function templates. Retire duplicate execution models or
  give each retained abstraction an explicit simulation theorem. **Close with:**
  scoped target generation, rendering/parsing and behavior preservation compose
  without treating equality to one emitted program as the general backend
  contract. The existing frozen-profile theorem remains a corollary.

### Artifact and release evidence

- [ ] **A01 — Reproducible proof-carrying artifact workflow.** Depends on
  S03/P01/C02. Preserve the independent file-to-proposition check. Specify a
  release evidence record covering source/grammar/output, transitive dependency
  pins, options, proof roots and checker identity. **Close with:** a fresh
  workspace reproduces the record and full gate; mutations of each bound input
  or claimed proposition are rejected; a checker/generator crash produces no
  successful artifact. Hashes are provenance, never semantic proof.
- [ ] **A02 — Review and release R1.** Depends on all other R1 items. **Close
  with:** the coverage matrix has no unexplained hole for the frozen grammar,
  independent review findings are resolved, the full gate passes at the reviewed
  revision, and the published claim states its C/IEEE/host boundary exactly.
  This authorizes the next verified feature wave; it does not claim full MLS
  coverage or native-code verification.

## R2 — Grow the verified core in complete slices

For every item below, ship source syntax/semantics, each affected lowering,
finite execution, numerical conditions, actual-artifact checks and rejection
controls together. Each new operation must have justified floating semantics.
Do not smuggle a solver assumption into an unconstrained compiler hypothesis.

- [ ] **G01 — Constant derivatives and multiple states.** Depends on R1.
  Admit a documented class of Real constants and finite collections of
  independent states. Define literal-to-real and literal-to-binary64 conversion,
  name/index mapping, initialization interface and state layout. **Close with:**
  proofs for arbitrary admitted constants/state counts, state-permutation and
  duplicate/unbound-name cases, exact rounded results and numerical refinement;
  multiple semantically different source programs appear in the evidence corpus.
- [ ] **G02 — Expressions and acyclic algebraic equations.** Depends on G01.
  Add a deliberately specified arithmetic vocabulary, parameters and acyclic
  algebraic dependencies. **Close with:** evaluation/order/rounding contracts,
  substitution/alias and scheduling preservation, a verified cycle check or
  certificate checker, and rejection of unsupported or unsafe cases. Floating
  reassociation is not justified by real-ring identities.
- [ ] **G03 — Coupled explicit ODEs.** Depends on G02. Begin with affine systems
  and then the supported expression class. **Close with:** Flat/DAE/Solve
  contracts over vectors, initial-value/regularity conditions, a named numerical
  method and proved local/global error on its stated domain. Exact preservation
  of finite solver instructions is still distinct from ODE accuracy. Benchmarks
  include different equation orders and coupling, not copies of the unit model.
- [ ] **G04 — Nontrivial DAE → Solve transformations.** Depends on G02/G03.
  Start with a precisely delimited solvable affine algebraic class. Use checked
  elimination/matching certificates if that keeps complex search untrusted.
  **Close with:** solution-set preservation with explicit variable projection,
  proved or checked invertibility/solvability conditions, and singular,
  inconsistent and underdetermined rejection cases. General implicit/high-index
  DAEs require a later contract; equation balancing alone is insufficient.
- [ ] **G05 — Source composition within the selected core.** Depends on G01–G04.
  Select and specify the smallest useful class/component/parameter composition
  needed by the core users. **Close with:** elaboration/flattening preserves
  equations under renaming and instantiation, defined parameter scope and
  modification rules, and model-composition examples. Inheritance, connectors,
  arrays and events enter the catalog only with their own semantics and proof
  slices; absence from the catalog is explicit, not silently approximated.

### Maintainability and efficiency

- [ ] **E01 — Measure and enforce implementation budgets.** Depends on P03/C02;
  establish a baseline before G01 and extend it with each G item. Measure native
  parsing/compilation, memory, certificate checking and generated C execution
  separately on versioned workloads. Agree regression limits after measurement.
  **Close with:** reproducible reports and CI checks; the runtime dependency
  graph stays small and does not execute mathematical enumeration. Performance
  results are not semantic proof or embedded worst-case timing guarantees.
- [ ] **E02 — Verify any enabled optimization.** Depends on the relevant G
  slice and E01. Introduce optimizations only for measured needs: representation
  changes, scheduling, dead code or constant folding each need their own pass
  theorem and side conditions. **Close with:** the composed theorem covers all
  enabled options and adversarial signed-zero/rounding cases. No optimization
  is required merely to resemble CompCert; an empty optimization set must be
  recorded explicitly if none is needed.
- [ ] **Q01 — Release the reusable core.** Depends on G01–G05/E01/E02. **Close
  with:** a supported-feature matrix maps every grammar and IR constructor to
  source semantics, lowering contracts, target execution and numerical/artifact
  evidence; independent review and a fresh full gate pass; known exclusions
  and trust assumptions accompany the release. Tests alone cannot certify a
  feature, and proving only the unit-integrator corollary cannot close R2.

## Per-stage obligations for every extension

| Edge | Semantic relation | Required evidence beyond type correctness |
| --- | --- | --- |
| Text → AST | Character/token/grammar and action relation | Soundness, promised completeness, resolution, actual EBNF binding |
| AST → Flat | Equality of source and flattened solution sets under name/state mapping | Scope, instantiation, parameter evaluation and preserved equations |
| Flat → DAE | Residual-system equivalence with explicit coordinates | Derivative/state mapping, equation ordering, initial constraints |
| DAE → Solve | Solving/refinement under explicit domain conditions | Matching/elimination correctness, solvability, projection of auxiliary variables |
| Solve real → numerical → finite | Method refinement followed by rounding semantics | Existence/regularity, discretization and rounding bounds, exceptional cases |
| Finite Solve → C | Operational/behavior preservation | Types, scopes, arithmetic, layout/calls, all reachable states and observations |
| C AST → bytes | Parsing/rendering relation plus actual-file binding | Names/literals/declarations, exact emitted artifact, checked options/ABI assumptions |

## Deferred product work

After R2, track each of these as a separate product with its own proof boundary:
Lean/WebAssembly deployment, typed Solve backend plugins, FMI 2 packaging,
eFMI AlgorithmCode/ProductionCode and `target.toml` products, events/hybrid
semantics, and broader MSL coverage. Templates may package proven products;
a template's flexibility is not a proof of a new language backend.

Keep **Modelica → C** and **C → assembly** as separate projects for now. An
optional later native-code claim needs a proved bridge to the chosen downstream
compiler semantics and a precise ABI/linking contract. Merely running generated
C through CompCert or GCC does not compose the proofs. ARM emission, the host
CSV driver and FMU wrappers are not shortcuts for completing the core roadmap.

## FMI 3 architecture requested during this review

The user has promoted FMI 3 from deferred product work. The design reference
is Rumoca's `templates/fmi3` target: ME and CS share the component model, with
the numerical solver inside CS. An ME instance exposes model evaluation and
state access; a CS instance invokes the shared model through an internal solver.
This does not mean issuing ME-only FMI ABI calls on a CS instance. Consult
[FMI 3.0.2](https://fmi-standard.org/docs/3.0.2/).

The implementation remains Lean. Reuse official FMI headers and schemas when
adding the ABI/package; do not retype the standard or port Rust/Jinja code.
Use the unit step as the initial numerical profile. For `der(x)=u`, its finite
addition and overflow/error policy still need proof; the old `der(x)=1` theorem
does not prove this extension. Variable communication steps require additional
finite arithmetic/time and numerical-refinement proofs. They cannot be obtained
by relabeling `rumoca_sample`.

- [ ] **F01 — Shared ME model and internal CS solver contract (in progress).** Depends on
  S01/P01/N02. Own instance state and derivative evaluation in an ME model
  layer consuming Solve; keep numerical advancement in a separate solver
  consumed by CS. **Close with:** state get/set and derivative preservation,
  solver-to-model composition, time/step admissibility and finite iteration
  theorems. The current C helper interface remains identified as such until
  the FMI ABI and packaging exist.
  **Implemented:** `RumocaCore.Solve.ModelExchange` separates model state and
  derivative evaluation, the unit solver, and a CS state containing the model.
  It proves state access, derivative preservation, no overflow, repeated-step
  results and step-count progress. The current `ArtifactContract` binds scalar
  exports to this internal model/solver contract. **Remaining:** FMI Float64
  time/admissibility and composition with F02/F03; these are not implied by an
  exact natural step counter.
  Require a time-progress check or proved horizon: finite `time + 1` can round
  back to `time` at large magnitudes. Include `2^53` as a rejection/progress
  discriminator; the existing state-update no-overflow proof does not solve it.
  **Tensor foundation:** shared nominal shapes and array-backed values,
  mathlib Matrix equivalence, compact programs with a proved evaluator,
  explicit Flat/DAE initialization residuals and adjacent real-equation/
  initialization proofs now exist. `Solved.Model.exportData` binds the IVP and
  declaration names to one source chain. These do not close F01 or extend the
  production source-to-C theorem. See `build/tensor-ir-gate.log` for the full
  regression run on this working snapshot.
- [ ] **F02 — FMI 3 lifecycle and error semantics.** Depends on F01/C01.
  Specify instantiation, initialization, event/continuous/step modes,
  termination/reset, permitted gets/sets and `doStep`. **Close with:** valid
  call traces, invalid-call rejection, finite input checks, error atomicity,
  time consistency and repeated-step preservation. Every unsupported
  capability is absent from metadata and rejected according to its ABI contract.
  Add named ME and CS conformance theorems against independently specified
  reference transitions, including error recovery, lifetime and instance
  isolation. Composing the Solve-to-C theorem alone cannot discharge this row.
  **Implemented for the unit profile:** finite-mode reference predicates and
  checked guard generation (`FMI3.allowed_correct`, `guard_reference`); generated
  allocation/free/reset, state access, ME/CS dispatch, logging, numerical
  argument validation, error recovery and rejected-step rollback. Raw ABI tests
  exercise these operations. **Next:** authored memory/call semantics and a
  function-body refinement, including Float64 times and output pointers.
  **State-access proof increment:** `RumocaFMI3.Memory` checks typed cell access
  and permissions at symbolic subobject addresses. `Execution` supplies
  independent small-step rules over the emitted tree constructors and reuses
  the all-behavior transition framework. `StateProofs.get_behaviors` covers
  successful ME reads in initialization/event/continuous modes; `set_behaviors`
  covers successful continuous-state writes, preserving the full Float64 bits
  and relating the final heap to the shared ME model. Frame theorems preserve
  other addresses/instance blocks under explicit ownership hypotheses.
  The common null-instance prefix also has a no-write/Error body theorem.
  **Next:** helper call/return and logging traces, the remaining error paths,
  allocation/free and Float64 time/CS bodies, then target-text and ABI/layout
  correspondence. Unsupported interpreter operations are stuck; these partial
  body contracts must not be presented as whole-FMU verification.
  **Evidence (2026-09-09):** the complete `make test` gate passed in
  `build/fmi-memory-gate.log`: 156 main roots, 8 scalar, 4 tensor and 6 memory
  regression roots (174 total), with the existing axiom policy unchanged.
  All artifact mutation controls and ten native FMI test groups passed.
  The working source inventory is `build/fmi-memory-snapshot.sha256`.
  **Call/return proof increment:** `CCalls` gives ordinary calls fresh scopes,
  checked arguments and return conversions, explicit continuations and an
  execution bridge to the existing numerical statement machine. Successful
  memory executions lift without changing their transitions. The actual model
  RHS helper and state-advance helper now have compositional body contracts;
  the latter agrees with the shared CS model for all finite states and uint64
  counts. `DerivativeProofs.get_behaviors` executes the public ME derivative
  body through both helper calls and the caller-buffer write in every permitted
  ME mode. Mutation checks distinguish changed helpers and numerical bodies.
  **Still open:** public CS Float64 time/admissibility, logging and error paths,
  allocation/free, full lifecycle traces, actual adapter bytes and native layout.
  An internal advancement proof alone does not close F02 or prove `fmi3DoStep`.
  **Evidence (2026-09-09):** the complete gate passed in
  `build/fmi-calls-gate.log`: 173 main, 8 scalar, 4 tensor, 6 memory and 9 call
  regression roots (200 total), with the axiom policy unchanged. Artifact
  mutation/forged-producer controls and all ten native FMI test groups passed.
  The gate recreated `build/Integrator.fmu` and both runner CSVs. The working
  source inventory is `build/fmi-calls-snapshot.sha256`.
  **ME time proof increment:** binary64 comparison results now refine real
  order for every finite encoding; infinity/NaN classification and unordered
  comparisons are explicit. `Time.Window` independently records the normative
  ME history bounds. `TimeProofs.guard_reference` proves exact acceptance for
  their represented window, including backward trial times and optional stop;
  `set_behaviors` proves the generated successful time update and full-heap
  frame. Nonfinite inputs reject before loading bounds. **Remaining:** prove
  history maintenance through initialization/completion/event bodies, complete
  rejected-call logging/status/lifecycle behavior, public CS Float64 arithmetic,
  lifetime and actual adapter/ABI binding. Comparison results alone do not
  model floating exception flags or signaling traps.
  **Evidence (2026-09-09):** the time increment passed the complete gate with
  191 main, 8 scalar, 4 tensor, 6 memory, 9 call and 14 time regression roots
  (232 total), with the axiom policy unchanged. All actual-file mutation and
  forged-producer controls and eleven native FMI groups passed. Historical
  evidence paths were `build/fmi-time-gate.log` and
  `build/fmi-time-snapshot.sha256`; generated build output can be cleared.
  **History maintenance increment:** the native adapter reproduced an
  over-restrictive bound after completion timestamps `1, 2, 1, 2`, all
  interleaved with time queries admitted by the reference interval. The
  running maximum retained `2`, rejecting a subsequent query at `1.5`.
  The implementation now stores the event/start floor separately and sets
  `timeMin := max(eventTime, lastCompleted)` before replacing `lastCompleted`.
  This follows the positional bounds in FMI 3.0.2 §3.2.1 without adding an
  unexplained monotonic-completion premise. `Time.trace_represents` proves
  the cache invariant over admitted reference histories. The actual generated
  initialization, event and completion history blocks have universal execution,
  representation and frame contracts, composed with the existing time guard.
  **Still required:** enclosing public initialization validation/stop writes,
  completion output writes, event mode writes and full lifecycle composition.
  Concrete kernel/native public-body regressions are not substitutes for those
  universal proofs. Error/logging, CS arithmetic and actual-FMU binding remain
  open; F02 is not complete.
  **Evidence (2026-09-09):** `build/fmi-history-gate.log` records the complete
  passing gate with 208 main, 8 scalar, 4 tensor, 6 memory, 9 call, 14 time and
  10 history regression roots (259 total). The audit still permits only
  `propext`, `Classical.choice` and `Quot.sound`. Actual-file mutation and
  forged-producer controls, all twelve native FMI groups and publication
  failure controls passed. The combined FMU and both runner CSVs were rebuilt;
  ME and CS both produce `0.5, 1.5, 2.5, 3.5` at times `0, 1, 2, 3`.
  Source inventory: `build/fmi-history-snapshot.sha256`.
  **Public event/completion body increment:** `HistoryBodies.event_correct`
  and `completed_correct` execute the complete successful public C-tree bodies
  and compose with the independent history, lifecycle mode and shared model.
  Instance/lifecycle and output guards, Boolean output writes, history updates,
  the event-mode write and status return all participate in execution. Their
  all-behavior contracts exclude divergence and stuck runs under explicit
  entry bindings and typed-storage premises. Completion buffers may be
  uninitialized and may alias one another; they must be outside the instance's
  storage block. Full-heap frames and model-state corollaries are checked.
  **Next:** complete public initialization validation/stop writes and
  cross-call lifecycle composition, then rejected calls/logging and lifetime.
  CS arithmetic and actual adapter/ABI/package binding still remain; the new
  successful-call proofs do not close F02 or justify production grammar growth.
  **Evidence (2026-09-09):** `build/fmi-history-bodies-gate.log` records the
  complete passing gate with 226 main, 8 scalar, 4 tensor, 6 memory, 9 call,
  14 time and 16 history roots (283 total), the unchanged axiom audit, all
  actual-file adversarial controls and thirteen native FMI groups. The combined
  FMU and both ME/CS runner traces were rebuilt successfully.
  **Initialization-exit increment:** `InitializationBodies.exit_correct`
  covers every behavior of the complete successful public body for both ME
  and CS. It returns OK, reaches the reference lifecycle mode, and preserves
  the shared model state and clock history; a frame theorem preserves every
  other cell. Supplied entry bindings and typed writable initialization-mode
  storage are explicit premises. The seven new roots passed the package check
  in `build/fmi-initialization-exit-package.log` with the unchanged axiom policy.
  The aggregate `lake build audit` also passed in
  `build/fmi-initialization-exit-audit.log`. These proof checks supplement the
  publication gate already running when this proof-only increment was added;
  they do not replace its actual-artifact checks.
  No runtime or grammar case changed, and no example-test matrix was added.
  **Next:** initialization-entry validation and stop storage, then cross-call
  lifecycle/error/lifetime composition. This body theorem does not close F02
  or bind the public ABI and actual adapter bytes.
  **Initialization-entry increment:** the core now owns an independent finite
  initialization admission profile. `InitializationEntry.guard_reference`
  relates the actual argument guard to mathematical real order and finite
  encodings, including arbitrary unused tolerance/stop bits. `correct` executes
  the complete successful ME/CS body, preserves model state, initializes the
  reference history and establishes the existing `SetTime` window/stop
  representation. Stop and Boolean cells may be uninitialized before the call;
  typed writable clock/mode storage and supplied arguments remain explicit
  premises. The package check passed in
  `build/fmi-initialization-entry-package.log` with the same axiom whitelist.
  No runtime, grammar or numerical policy changed; no example tests were added.
  `then_exit` composes both successful calls through the same intermediate
  heap. It preserves initialized history/model state and reaches the reference
  final mode. The aggregate audit passed in
  `build/fmi-initialization-entry-audit.log`, including this composition.
  **Still open:** standards review of the existing strict tolerance/stop policy,
  nonfinite-start and other rejected initialization paths, general lifecycle
  composition, logging, lifetime, CS time arithmetic and actual adapter/ABI
  binding. This successful-body proof does not close F02.
  **General lifecycle-prefix increment (2026-09-10):**
  `LifecycleGuard.reference` connects the actual guard to the independent
  lifecycle predicate in the shared C memory/execution model. `require_run`
  covers every existing command, kind and represented mode, preserves the
  whole heap, and reaches either the continuation or the emitted failure call.
  The event/completed-step prefix and initialization entry/exit now use this
  theorem; `CBody.run_add` composes blocks through the exact intermediate state.
  Existing body theorem statements and all prior audit roots are retained.
  `lake build check-c check-fmi3` passed in
  `build/fmi-lifecycle-guard-package.log`. No runtime, grammar or example-test
  case changed. The required actual-artifact gate remains separate.
  **Alignment review:** the current Rust `rumoca-ir-solve/src/fmi.rs` keeps
  FMI metadata correlated with one owned Solve kernel; its typed program keeps
  tensor types, storage and source provenance together. This increment adds
  only adapter execution proofs. It leaves Solve ownership intact and adds no
  scalarization, alternate solver representation or backend lowering. The
  provenance and actual-metadata obligations already tracked here remain open.
  **Standards finding (2026-09-10):** the private error mode blocks final-value
  reads, contrary to FMI 3's error-to-Terminated transition. ME getter guards
  also excluded Terminated. The reference, guards and error helper now agree
  on Terminated; general getter proofs cover it. `LifecycleBodies` proves
  mode-write frames and all behaviors of successful termination. Core/C/FMI
  audits passed in `build/fmi-termination-package.log`; the corrected combined
  FMU passed the existing thirteen ABI/importer test groups in
  `build/fmi-termination-artifact.log`. The complete cross-package gate remains
  required. See [the correction](fmi3/contracts.md#error-state-correction).
  **Next:** complete failed-call/helper execution and lifecycle composition,
  then bind the remaining adapter and metadata proofs to actual artifact bytes.
- [ ] **F03 — Generated ME+CS C and actual package binding.** Depends on
  F01/F02/C02/A01. Emit both FMI interfaces over the shared model, official C
  types/signatures, model/build XML and a flat `.fmu` archive. Extend the C
  semantics to required instance memory and calls before claiming wrapper
  verification. **Close with:** the artifact proposition binds every semantic
  product, capability declaration and source member to the same Solve model.
  Checking the old scalar `Model.c` separately is not a wrapper proof.
  **Implemented:** typed C syntax construction, official pinned FMI signatures,
  model/build XML, source and native Linux binary members, actual-kernel checking
  and atomic `.fmu` publication. `RumocaC` remains the verified numerical target;
  `RumocaFMI3.CTree` is construction syntax with a limited guard semantics.
  **Next:** extend independent target parsing/execution and the fixed artifact
  proposition to the actual adapter and correlated metadata. The included
  checking log cannot authenticate arbitrary archive members.
- [ ] **F04 — Independent FMI validation and release.** Depends on F03.
  Validate official schemas, an independent importer, direct ABI lifecycle
  tests and ME/CS trace parity. **Close with:** source and binary package
  consistency, malformed metadata/call/step negative controls, the complete
  Lean gate, and a precise claim separating interface conformance, proved
  semantics, native toolchain and importer evidence. No full-FMI capability
  claim for the restricted continuous one-state profile.
  **Implementation checks:** `tests/fmi3.sh` drives the Lean producer and runner;
  `tests/fmi3.py` checks ZIP restrictions, official schemas via FMPy, all required
  ABI symbols, ME/CS traces, instance isolation, initialization/event access,
  time backtracking/stop bounds, bad inputs, reset, rollback, binary64 boundary
  values and an independent C rebuild. These checks are part of `lake test`.
  **Remaining:** all dependent proof obligations, independent reference-FMU
  runner coverage, review and the release conformance statement.

Design inputs: [Rumoca specification mapping](../docs/design.md),
[MLS 3.7](https://specification.modelica.org/maint/3.7/MLS.html), and the current
[exact verification contract](../docs/verification.md). This file proposes future
scope; updating it does not itself expand the implemented grammar.
