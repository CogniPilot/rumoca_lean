# IR alignment review

## Mandatory provenance direction, 2026-09-11

The local Rust reference is now on `multibody-library-coverage`, HEAD
`bc71577f85df24957e5c9ab30fdaf4ed48da4311`, with unrelated local changes including
initialization and `rumoca-core/src/ir_primitives.rs`. It was read without
modification. Its source identity/range types and separate Solve shape-span
metadata remain useful design references. The current
`rumoca-ir-solve/src/layout.rs::validate_shape_span_metadata` permits an empty
span map, and `shape_span` then returns `None`. The local core draft also has a
`ProvenanceSpan` constructor that rejects the dummy sentinel, consistent with
the required-origin direction. The permissive empty-map path still does not
meet the user's invariant for this Lean core; a checked field must carry the
actual origin, not merely make validation available to callers.

The Lean compiler now requires a checked located parse in every artifact.
Its independent lexical specification proves total span attachment, and its
compiler completeness theorem retains the same source assumptions. This is
the prerequisite for required IR origins, not proof of their propagation.
IR occurrences will use compact references into a shared immutable origin
table; derived entries retain their parents and generating rule. The table
must preserve input identity outside source contents, including equal-content
files. Source ranges must not be replaced by dummy values or a whole-file span
when an exact declaration origin is required.

The source provenance meaning of an origin must remain distinct from tensor
slice coordinates: the `origin` arrays in Rust typed slice instructions are
index coordinates, not source spans. Adding provenance must preserve one
operation per tensor operation and must not materialize per-element source
graphs. Existing predecessor IR retention remains the separate memory issue
listed below; duplicating those structures is not the provenance design.

The frontend/driver checkpoint passes its package audit in
`build/located-provenance/package-gate.log` and its required full artifact gate
in `build/located-provenance/full-gate.log`. Per-IR
origin-preservation theorems and actual emitted-byte maps remain open in
[provenance.md](provenance.md). No grammar or numerical lowering changed.

## Tensor AD direction, 2026-09-10

The next user-authorized slice is static arrays and the `jacobian` built-in,
with forward/reverse rules formally checked before production admission.
Reviewed Rust `rumoca-ir-solve/src/fmi.rs`, the typed tensor program and
SPEC_0051_JACOBIAN_SYNTHESIS. Solve still owns one executable tensor kernel;
the backend consumes its prepared operations and correlated metadata.

The new pointwise primitives retain shape-indexed dense storage and use an
explicit scalar arithmetic interface. Their mathlib proofs cover every shape,
and the square pullback sums both uses of its input. The typed Solve program
now includes these operators, with a forward transformation and saved-primal
reverse evaluator proved against the whole-program mathlib derivative.
These are not array-FMU theorems. The first intended grammar slice
is recorded in [tensor-ad.md](tensor-ad.md). The intrinsic will remain a
parsed built-in call; typed lowering will synthesize tensor programs rather
than adopting Rust's generated-Modelica/unrolled-seed implementation.

Rechecked Rust `typed_program/program.rs` during this increment: its binary
operations consume typed register IDs and retain tensor shape. The Lean
program similarly emits one operator per tensor operation. Lean's dependent
references make ill-typed use impossible, but the current function-backed
environment is a reference evaluator; a proved packed-register implementation
is still needed for comparable lookup/update costs. Source provenance through
these programs remains an open obligation in [provenance.md](provenance.md).

The FMI correction in this round changes only adapter lifecycle semantics:
errors enter Terminated and final ME queries remain available. It preserves
Solve ownership, tensor shapes and the solver policy. Core/C/FMI audits and
the actual combined FMU checks passed; callback and full artifact-capstone
obligations remain open.

The current full gate is `nix develop .#verification --command lake test`.
Make commands in dated checkpoints below record historical runs before the
Lake migration; see the [current commands](../docs/development.md).

Reviewed 2026-09-08 against the local `~/git/rumoca` checkout, branch
`msl-trace-parity-50`, commit `a1daf47556c1a6ffd7f4b203235ff09711089a85`.
The reference checkout has unrelated local verification work; it was read
without modification. This review compares implementation definitions as well
as specifications. It does not promote draft Rust contracts to proved facts.

The four stages are appropriate. The original Lean unit-integrator IR is a
regression model of those stages, not yet a reusable implementation of their
full responsibilities. The tensor/initialization work below corrects that
direction without adding arrays, PDEs, neural ODEs or optimizations to the
admitted source language.

## What the stages mean

| Stage | Meaning in Rumoca | Small Lean contract |
| --- | --- | --- |
| AST | Source syntax, operators, names and provenance; parsing does not solve the model | Preserve the selected model's declaration, reference and attribute spelling. Resolve names separately. The minimal AST currently omits per-node spans. |
| Flat | Instantiated, resolved, typed equation system. Modifications have been applied; `der` is still a Modelica operation. Arrays remain aggregate. | Rank-zero Real declarations, resolved input/state identities, a `der` equation and an explicit fixed-start equation. No integration method. |
| DAE | Canonical semantic system using derivative/state/input coordinates. Continuous and initialization residuals have distinct owners. | `dx - u = 0` and `x - 0 = 0`, expressed as tensor residuals. DAE must completely specify this tiny system before Solve. |
| Solve | Typed executable programs, logical storage/layout and initialization. Numerical structure is prepared for consumers. | A checked explicit IVP with tensor initialization, derivative and output programs. An external solver supplies time stepping. |
| FMI view | Checked deployment projection of one Solve model and its sealed variable catalog | Derive metadata, value references and kernel bindings from one correlated export root. It is not another Modelica lowering stage. |
| C inside FMI | Executable rendering of the prepared model plus the shared FMI runtime/solver | Prove the final target edge against Solve/runtime semantics, then compose with earlier theorems. C does not infer shapes or solve equations. |

The distinction between Flat and DAE is **not** merely equality versus
subtraction. Rust Flat already stores many equations as residual expressions.
The important change is eliminating Modelica-specific operators and obtaining
the canonical semantic coordinates and systems. Our Flat `der` and DAE
`derivative` constructors make that boundary visible in the tiny profile.

Solve is also not synonymous with an explicit RHS. Rust `SolveProblem` retains
continuous, initialization, discrete, event and clock systems; its continuous
system can include implicit residuals and algebraic projections. Our `IVP`
is deliberately the explicit, event-free slice. Do not present it as sufficient
for arbitrary Modelica DAEs or use the narrow type to discard unsupported
constraints when the language eventually grows.

## Findings and changes

1. **The unit-only register IR is too narrow to become the tensor core.**
   `RumocaCore.IR` keeps the existing checked unit path for regression. New
   shared `Tensor.Shape`/`Value` types retain rank and extents, and
   `Solve.Tensor.Program` keeps fills and references as tensor operations.
   `driven_compact` proves the program-node count is independent of extent.
   No scalar instruction list is materialized during this lowering.

2. **Initialization was missing from the draft driven DAE.** Fixed-start
   initialization now has explicit Flat expressions and a separate DAE
   residual. `Flat.lower_initial`, `DAE.lower_initial`,
   `Solved.lower_initial` and `initialization_chain_correct` prove the complete
   initial solution set. This prevents a correct differential equation from
   hiding an invented or discarded initial condition.

3. **Tensor shape belongs to all indexed stages.** Shared shape/storage types
   live in `RumocaCore.Tensor`; Flat does not obtain its shape definition from
   Solve. A nominal `Value` wrapper prevents exchanging a 2×3 matrix and a
   length-six vector just because they have equal volume. Storage uses Lean's
   existing array-backed `Vector`, and the semantic rank-two view is equivalent
   to mathlib `Matrix`, using mathlib's `finProdFinEquiv` index mapping.
   Matrix operations and algebra should reuse mathlib through that view.
   Real-algebra theorems do not authorize reassociating floating-point
   reductions; each admitted finite operation will need its specified order
   and rounding contract separately.

4. **A raw IVP is not sufficient authority for FMI metadata.**
   `Solve.ModelData` pairs the executable problem with its two declarations;
   `Solved.Model.exportData` derives it from the same checked lowering chain.
   Names are presentation data, with typed declaration identities and a
   distinctness proof. Shapes are projected from the retained problem. This
   is the first small step toward Rust's sealed catalog, not an implemented
   FMI inventory: evaluated attributes, FMI references, capabilities and XML
   correlation still need their own contracts before F03 closes.

5. **Keep solver and FMI policy out of canonical equations/programs.**
   Neither tensor programs nor IVP contain an FMI mode, step size, C type,
   allocation policy or native toolchain. The old internal ME/CS unit model
   remains useful proof evidence, but its natural step count is not an FMI
   Float64-time or lifecycle proof. A runtime/compiler-to-runtime proof is
   required around the new tensor IVP.

6. **Retaining every predecessor is proof convenience, not a final memory
   strategy.** Existing source-indexed records retain earlier IR data, while
   only their `Prop` fields erase. The backend receives a projected executable
   root. Before larger models, measure retained data and separate runtime
   products from optional source/proof inspection artifacts; do not duplicate
   per-element graphs or metadata to simplify a backend.

7. **Grammar provenance should be explicit.** The reference grammar is now
   `crates/rumoca-phase-parse/src/modelica.par`, not `crates/parser`. The selected
   EBNF follows its production names and notation; used keyword productions
   are verbatim. [The grammar note](../packages/modelica-parser/grammar/README.md)
   documents narrowed alternatives and omitted parol action directives.
   Supporting those EBNF notations does not imply support for the full parol
   language, arbitrary Modelica expressions or recursive grammar references.

## Evidence and limits of the reference

Read these concrete definitions:

- [AST ClassTree](../../rumoca/crates/rumoca-ir-ast/src/lib.rs) and
  [Expression](../../rumoca/crates/rumoca-ir-ast/src/nodes.rs): the actual
  ClassTree co-retains type/scope tables populated by later semantic analysis.
  The pipeline spec's clean parse-stage description is a stage contract,
  not a claim that this Rust aggregate contains syntax alone at all times.
- [Flat Model, Variable and StructuredEquationFamily](../../rumoca/crates/rumoca-ir-flat/src/lib.rs):
  resolved attributes, source occurrence/span, dimensions and structured
  families. Some paths retain scalar views alongside the structured owner.
  We should preserve the compact owner directly rather than copy that legacy
  transition machinery into the new Lean core.
- [DAE root and storage](../../rumoca/crates/rumoca-ir-dae/src/model.rs): separate
  continuous/initialization systems and a canonical variable catalog.
- [SolveProblem](../../rumoca/crates/rumoca-ir-solve/src/lib.rs),
  [SolveModel](../../rumoca/crates/rumoca-ir-solve/src/model.rs),
  [variable catalog](../../rumoca/crates/rumoca-ir-solve/src/variable_catalog.rs),
  [ComputeNode/ComputeBlock](../../rumoca/crates/rumoca-ir-solve/src/tensor.rs), and
  [FmiComponent](../../rumoca/crates/rumoca-ir-solve/src/fmi.rs): compact
  MatMul/Map/AffineStencil nodes, prepared numerical systems, and one checked
  model behind deployment metadata. MLIR's execution adapter consumes the
  same SolveModel. Some constructors still perform root validation; draft
  valid-by-construction aspirations are not all implementation facts.

Normative design anchors are SPEC_0007 and SPEC_0040; SPEC_0031 explains the
DAE/Solve/FMI/solver boundary. SPEC_0036 is marked DRAFT. Reusing these ideas
does not import Rust verification claims into Lean.

## Proof and release boundary

The new tensor evaluator, mathlib storage bridge, source/Flat/DAE/Solve equation
and initialization edges are checked in Lean and included in the axiom audit.
They do not yet extend `compiler_semantic_preservation` or the actual-C
certificate to the driven model. The production CLI still rejects that model.
Admitting it requires the remaining Solve-to-target, FMI runtime and
actual-archive work in F01–F04. The package rename to `backend-fmi3` does not
itself produce an FMU.

The required regression command remains
`nix develop .#verification --command make test`; it passed on 2026-09-08,
including 130 main, eight scalar and four tensor theorem-root audits and all
actual-file/forged-producer controls. The run is recorded in
`build/tensor-ir-gate.log`, with the working code snapshot in
`build/tensor-ir-snapshot.sha256`. The grammar certificate now composes shared
checked character, lexing, parsing, length and expansion facts, avoiding
repeated UTF-8 normalization while retaining its exact source contract.
Do not treat this review or a passing unit
artifact check as a completed FMI conformance result.

## State-access proof spiral, 2026-09-09

Rechecked the moving Rust reference at commit
`b5303b2e0bd41085d0c92b9aa93d618210270a22` on `msl-trace-parity-50`.
`typed_program/program.rs` retains typed slots, storage classes and read/write
permissions; `program/tensor.rs` retains aggregate operations and dimensions.
`fmi.rs` now emphasizes one private Solve owner, one value-reference inventory
and a narrowed `FmiEventFreeCodegenView`. Those boundaries remain the direction
for Lean: memory permissions in a target semantics must not move storage or
shape inference into the emitter, and XML/C identities need one correlated
prepared owner before further source growth.

This round adds no Modelica grammar case. The prior round produced a working
unit ME/CS FMU, but its adapter had only guard proofs. The new target-side
memory/statement semantics now support generated ME state get/set body proofs,
including exact binary64 payloads, full final heaps, explicit valid-storage
preconditions, and preservation of other addresses/instance blocks. This closes
part of the missing runtime edge without changing tensor IVPs, canonical DAE
equations or the admitted compiler language.

The design deviation is deliberate: the proof memory uses symbolic C
subobjects, while Rust's storage/layout machinery is executable infrastructure.
Lean still needs a byte-layout/ABI bridge, complete correlated metadata,
helper calls, CS/time/lifetime semantics and actual adapter-text binding.
The existing runtime C is unchanged by this proof increment. Do not grow the
production grammar until this remaining edge and the already selected driven
profile have their complete contracts.

The required full gate passed for this increment on 2026-09-09, with 174
audited roots and all actual-artifact/native-FMU checks. See
`build/fmi-memory-gate.log` and `build/fmi-memory-snapshot.sha256` for this
working snapshot. F01–F04 remain open at their full stated scope.

## Helper-call proof spiral, 2026-09-09

Rechecked the Rust reference at the same
`b5303b2e0bd41085d0c92b9aa93d618210270a22` revision, including
`typed_program/call.rs`. Its typed pure-call interfaces retain explicit input
and output contracts. The Lean target now carries explicit call arguments,
fresh parameter scopes, return conversions and continuations. These are target
execution rules; they add no equation solving, tensor decomposition or solver
selection to the backend. Solve remains the owner of numerical execution.

The new call machine formally lifts successful memory transitions and executes
the existing numerical C statement machine. The model RHS and model-advance
helpers now compose with Solve/ME/CS semantics, and the actual ME derivative
getter has an all-behavior body theorem through nested calls and its output
write. Negative controls change a helper return and a numerical function body
to check that symbol names do not substitute for executing definitions.

This round admits no new source syntax. The public CS time/error/lifetime
contract, C rendering/parsing and whole-FMU binding still precede production
grammar growth. Memory addresses remain symbolic subobjects rather than a
native ABI layout. The call semantics support pure arguments and the emitted
whole-operand call forms; callbacks and general effectful expressions are
explicitly unsupported. These limits keep the increment reviewable without
silently expanding the claimed C semantics.

The full gate passed with 200 audited roots, actual-artifact mutation controls
and all ten native FMI test groups. It recreated the combined ME/CS
`build/Integrator.fmu` and checked both runner CSVs. Evidence is recorded in
`build/fmi-calls-gate.log` and `build/fmi-calls-snapshot.sha256`. This completes
the helper-call increment; the full F01–F04 contracts remain open.

## ME time proof spiral, 2026-09-09

The Rust reference remains at `b5303b2e0bd41085d0c92b9aa93d618210270a22`.
Revisited `rumoca-ir-solve/src/fmi.rs` and SPEC_0031: the correlated component
owns one Solve model and inventory, while time stepping remains a runtime
policy. The Lean change follows that boundary. Binary64 comparison and an
independent FMI time window live in shared core; C-tree interpretation and
generated-body proofs live in the backend. There is no new grammar production,
shape inference, tensor scalarization or solver selection in the emitter.

Reviewed the time-window reference against
[FMI 3.0.2 §3.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3SetTime). It records
start time, the second-last completed step and last event-mode entry, allowing
bounded backtracking rather than assuming trial times always increase.
The existing emitted condition was factored into `Runtime.invalidTime` for
direct proof reuse; the constructed condition and C behavior are unchanged.
The generated ME time guard and successful setter now have proofs, including
exact input encodings and preservation of the shared model state. Checked
controls distinguish bit equality from numerical equality, reject NaN/Inf,
exercise interval edges and detect an altered time assignment.

The reference-history-to-`timeMin` invariant remains a premise until the
initialization, event and completed-step bodies are proved. Rejected-call
logging, CS arithmetic and full actual-FMU binding remain open. The comparison
model describes results, with floating flags/traps outside its observations;
the distinction is explicit in [C11 draft N1570 §§7.12.14/F.9.3](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
These are required next edges, not permission to grow production syntax yet.

The full gate passed for this increment with 232 audited roots, all artifact
mutation controls and eleven native FMI test groups, including ME time bit
patterns and interval boundaries. The combined FMU and both runner CSVs were
rebuilt. See `build/fmi-time-gate.log` and `build/fmi-time-snapshot.sha256`.
The history proof must also review the current running-maximum update against
the reference's particular prior calls; the roadmap records a concrete
backtracking/completion sequence to analyze before closing that invariant.

## ME history maintenance spiral, 2026-09-09

Re-read the Rust FMI component at
`c4834ae4e17e157f566e0903bf03a639325692a9`, especially
`crates/rumoca-ir-solve/src/fmi.rs` and SPEC_0031. The component still owns one
correlated Solve root and inventory; execution policy belongs to runtime.
This increment changes only FMI history storage, its shared reference model
and proofs. It adds no source syntax, tensor element enumeration, backend
name/shape inference or solver selection.

The native backtracking probe reproduced an obsolete completed-step bound.
The new compact clock retains the event/start floor separately and recomputes
the completion floor from the particular prior call required by
[FMI 3.0.2 §3.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3SetTime).
The reference trace invariant and the generated history blocks now have Lean
proofs over all finite clock values satisfying that invariant, with explicit
typed storage and frame conditions. The comparison/store branches execute in
the existing independent C-tree semantics. The guards and complete public
lifecycle bodies still need to be composed; the metadata/native ABI and whole
FMU artifact theorem remain open. Production syntax therefore remains the
unit-derivative model.

The complete gate passed in `build/fmi-history-gate.log`: 259 audited roots,
the unchanged axiom policy, all actual-file mutation controls, twelve native
FMI test groups and runner/publication failure checks. It rebuilt the combined
FMU and checked identical unit-step ME/CS CSV traces. The working source
inventory is `build/fmi-history-snapshot.sha256`. The next proof increment is
the complete public initialization/completion/event bodies, including their
non-history writes and lifecycle composition; the block invariants alone do
not close those contracts.

## Public ME history body spiral, 2026-09-09

Revisited the Rust component and SPEC_0031 from the checkout whose HEAD was
`c185df807fe9695027a7d6ac4e9d345c01bdc24e` at the start of this round.
The component remains correlated with one Solve root; runtime stepping and
FMI host interactions remain outside compiler lowering. This round adds
proofs of two existing public runtime bodies without changing source grammar,
the Solve program, tensor shape ownership or generated behavior.

`HistoryBodies` composes the previous clock-block proofs through the actual
instance/lifecycle guards, caller output writes, mode update and return.
Its successful-body theorems connect the full final heap to the independent
reference history and mode, and preserve the shared ME model state. Output
buffers have explicit type, writability and ownership requirements; Boolean
outputs may alias each other. This closes the successful public event-entry
and completed-step portion of the prior history obligation, while initialization,
cross-call lifecycle traces, rejected-call behavior and actual-FMU binding remain
open. Reviewed the selected event-free behavior against
[FMI 3.0.2 §3.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3CompletedIntegratorStep).

The full gate passed in `build/fmi-history-bodies-gate.log`, with 283 audited
roots and thirteen native FMI groups, including the new public output/history
test. Artifact, importer, runner and publication failure controls passed.

## In-tree LALR foundation spiral, 2026-09-09

The user's latest priority is our own verified LALR(1) parser before further
grammar growth. Re-read SPEC_0007 and the parser build/grammar in the Rust
checkout at `6ea5ea44d9c4ad70dca67f957e5721d1bb31fa90`. Its parser now lives in
`crates/rumoca-phase-parse`; the AST remains source syntax, and name resolution,
instantiation and equation lowering belong to subsequent stages. The new
`Parser.LALR` modules depend on grammar semantics, not compiler IRs or the
FMI backend. The existing source grammar, AST actions, Flat/DAE/Solve chain and
production runtime are unchanged. Parser-only recursive fixtures do not admit
new Modelica features.

The Lean implementation builds canonical LR(1) items and merges LR(0) kernels,
reports conflicts, and executes a stack-based parser with separate syntax,
resource and internal-table errors. Its generic checked-tree theorem reaches
mathlib's independent CFG derivation semantics. Full table safety/completeness,
termination bounds, EBNF desugaring and typed AST actions remain required before
production replacement. See [LR01–LR07](lalr-parser.md); this is an incremental
foundation, not closure of the requested verified parser or FMI compiler.

The complete gate passed in `build/lalr-gate.log` with 301 audited roots,
the unchanged axiom policy, recursive/candidate-emitter checks, all existing
actual-file controls and thirteen native FMI groups. Both current EBNF syntax
profiles parse using 76 LALR states (81 canonical states); native recursive
fixtures pass through depth 500. The combined FMU and both runner traces were
rebuilt. Working source inventory: `build/lalr-snapshot.sha256`.

## LALR structural safety spiral, 2026-09-09

Rechecked the Rust reference at the same
`6ea5ea44d9c4ad70dca67f957e5721d1bb31fa90` commit, including SPEC_0007,
`rumoca-phase-parse/build.rs`, the grammar and generated parser. The reference
uses parol's LL(k) runtime with maximum lookahead three. Our requested LALR(1)
replacement is a separate parser design; both still belong entirely before
AST-to-Flat lowering. No source language, indexed IR, solver or backend case was
added in this round.

The new independent finite validator checks action/goto dimensions and complete
edge annotations. Backwards state summaries prove reductions are safe for every
concrete stack represented by those edges, including arbitrary recursive depth.
`Safety.validated_parse_safe` rules out internal table and tree errors for any
input and fuel. The final tree check cannot fail because `RuntimeProofs` proves
tree validity and exact input preservation through actual raw execution.
The emitter now includes kernel certificates about its actual table/edge
constants. Mutation controls corrupt those constants and require rejection.

This is progress on LR04, not its completion. A proved reject-all counterexample
demonstrates why safety is insufficient: LR-item/FIRST validation, completeness,
parsing bounds, the EBNF frontend and typed AST actions remain open. Those proofs
must precede production replacement and subsequent grammar growth. Generator
scaling and parol feature differences are recorded in the
[parser plan](lalr-parser.md#algorithm-and-cost-boundary).

The complete gate passed in `build/lalr-safety-gate.log` with 328 audited roots,
kernel checking/auditing of the emitted structural certificates, deliberate
table/annotation corruptions, all existing artifact controls and thirteen
native FMI groups. The combined FMU and ME/CS traces were rebuilt. Working
inventory: `build/lalr-safety-snapshot.sha256`. Review disposition: progress on
generic parser assurance with unchanged production semantics; keep LR04–LR07
and the FMI compiler obligations open.

## LALR nullable/FIRST coverage spiral, 2026-09-09

The reference checkout was reviewed at
`0cfc506d9fd8ad8cc7433b173ec20b51ef603a57`. The parser and SPEC_0007 files are
unchanged from the preceding review; that commit develops prepared Solve
projection behavior. Our work remains before AST lowering and does not add an
IR, solver or source-language case.

`LALR.First` now owns the shared nullable/FIRST summaries and lookahead
calculation. The candidate generator uses the same computation as before, now
factored out of its search module. An independent finite validator checks
closure under the grammar equations. `FirstProofs.derives_below` proves that
every CFG rewriting step, and consequently every derivation, is covered by
the checked summaries. The public empty-word, first-token and inherited
lookahead theorems quantify over mathlib's grammar semantics.

The emitter includes actual fact arrays, their kernel certificates and coverage
corollaries. Positive and corrupted actual-output checks accompany symbolic
controls for nullable chains, transitive predictions, dimensions and EOF. An
overapproximation regression prevents advertising coverage as exactness. This
is a prerequisite for LR-item/table completeness, not the completeness theorem
itself. The production parser and complete FMI compiler boundaries are unchanged.

The complete gate passed in `build/lalr-first-gate.log` with 352 audited roots,
actual generated safety/FIRST certificates and corruption controls, all existing
source/C artifact checks and thirteen native FMI groups. The combined FMU and
both matching runner traces were rebuilt. Working inventory:
`build/lalr-first-snapshot.sha256`. Review disposition: progress on the next
LR04 prerequisite; keep the remaining completeness/frontend/action and FMI
obligations open. User-directed Modelica/GALEC and parallel performance choices
are recorded in the parser plan; no new language or concurrency implementation
is admitted by this round.
