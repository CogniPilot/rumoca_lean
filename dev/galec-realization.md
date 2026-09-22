# Bounded tensor realization prerequisites — 2026-09-22

## Recursive source execution and declaration-derived storage — owner passed

Seven reviewed modules now live under `Elaboration.Bodies` (Lowering, Source,
Correctness) and `Elaboration.Layout` (Base, Shapes, NoAlias, Execution). These
are namespace/import migrations of the checked scratch, not a production
grammar or actual-artifact cutover. The owner passed 2,377 jobs, 869 complete
whitelisted reports and all 62 new roots; 15 source/audit hashes are recorded
under `build/galec-layout-adoption/`. The required full gate remains pending.

The mutually recursive lowerer consumes actual AST statements and body lists,
retaining the exact binder/count and outer scope across siblings. Its independent
typing iff covers the authored positive explicit unit-range profile. Source
execution recursively uses source assignments and mathematical Integer iteration,
with an exact one-based Fin witness rather than saturation or default indices.
The universal conditional execution iff preserves all intermediate stores and
partial/nondeterministic arithmetic through sequence and loop composition.
This is not complete semantics for arbitrary Integer locals, strides, shadowing
or omitted steps, nor an error-state/rollback theorem.

Logical storage construction partitions whole-shaped fields by explicitly
supplied roles, preserving order and full descriptor metadata. Each field
receives a distinct existing typed reference; rank/extents remain in its type,
and lowering never enumerates tensor cells. Shift inverses prove slot separation
even for duplicate names/shapes, without permitting duplicate source declarations
or asserting native memory separation. All-key shape lookup agrees with the
same ordered declarations. The closed-body compiler and execution theorem use
that table for both source reads/writes and static size queries; source shape
meaning remains the independent declaration judgment.

Scratch layout final-v1/session19234 passed five modules and 38 complete roots;
all four implementation logs are empty. Nested-body final-v2/session12520 passed
four modules and 24 roots. Main read the NoAlias proof and independent reviews,
and checked exact migration equality for all seven modules. The layout review
is `build/galec-layout-draft/layout-review.md`; nested reviews are under
`build/galec-nested-body-draft/`. Independent adoption review confirmed exact
identity and all 62 roots, with no finding (`build/galec-layout-adoption/review.md`).
The full declaration-profile gate below does
not cover these subsequent modules.

Remaining: validate method roles and complete initial scope, establish scanner
and environment provenance, compose actual parsed/rendered bodies with prepared
SquareBodies/Solve and actual C/archive contracts, prove target counter behavior,
and repair startup/broadcast and GJ01/GJ03/N01 findings. No method-specific
permission follows from the role tags alone. No new source admission or broad
standards/MISRA/native conformance follows from this prerequisite adoption.

## Source declarations, headers and assignment bodies — full gate passed

Fifteen checked scratch modules are adopted under core ownership. The
mathematical Integer range relation is `GALEC.IntegerIteration`; declaration
checking and source-derived shape lookup are under `Elaboration.Declarations`;
explicit positive unit ranges and fresh headers under `Elaboration.Loops`.
`Elaboration` also owns Reads, Expressions, Locations, Targets, Assignments
and StatementLists. Changes are mechanical namespace/import migrations; no
scratch imports or semantic rewrites remain. The generic NamedLists import
was preserved to avoid an unrelated dependency refactor during adoption.

Declaration checks preserve order and visibility/direction/variability,
reject duplicate names, and retain positive individually bounded dimensions.
Their shape-provider contract is stated independently over actual source
declarations. Header semantics evaluates all three explicit range expressions
through bounded static semantics, checks semantic start/step values of one and
a positive stop, and preserves old iterator references under fresh extension.
Freshness includes noniterator barriers, not merely failed iterator lookup.
Neither preserved direction metadata nor writable execution-context membership
is asserted to establish full eFMI method permissions.

Reads and locations have exact shaped-reference/coordinate semantics independent
of store values. Assignment source semantics evaluates the RHS in the before
store, writes one addressed tensor cell and preserves the whole-store frame.
Its correctness and sequential composition permit arbitrary partial or
nondeterministic arithmetic. The sole new non-migration lemma,
`Iteration.executes_congr`, transports pointwise body iff through all prefixes,
preserving actual intermediate states; it does not assume a total evaluator.

Core owner12392 passed 2,363 jobs and 807 complete whitelisted reports, all
135 new roots (74 declarations/ranges,60 reads/assignments,1 congruence), and
33 owner/audit input hashes. Main read all migrated sources or independently
verified their exact transformations; independent Astra review found no
substantive issue and confirmed all retained roots. Evidence is under
`build/galec-body-adoption/`, including owner/post-owner logs/exits, new-roots,
source hashes and both review documents. Implementation `f1fa7b9` passed the
required full gate V1/session32753 and post-audit V1/session73458, both terminal0.
All 2,593 frozen tracked inputs matched; all 8,421 complete axiom reports passed
the unchanged whitelist, all 275 selected roots were present and four actual
retained FMU roots passed a separate audit. The three FMI matrices covered
75 functions each and 526/650/526 cells, with zero recorded-finding discrepancies
or unexpected results. Scalar/tensor Algorithm Code and Production C members
are byte-identical to the preceding completed gate. Evidence:
`build/galec-body-elaboration-full-gate-v1.*`, `-post-audit-v1.*`,
`-required-roots-v1.txt`, `-fmu-retained-v1.axioms`, `-before-members-v1.sha256`,
`-after-members-v1.sha256`, `-archives-v1.sha256`.
No grammar, emitter or artifact predicate is changed. Subsequent scratch
recursive-body and storage-layout work is outside this gate's coverage.

Actual mutually recursive AST/body lowering and its execution proof remain
separate work. Initial scope/declaration→execution capability validation,
target counter arithmetic, source/renderer/Solve composition and actual bytes
must still be proved. The explicit range/freshness restrictions are authored
repair profiles, not full normative GALEC loop/shadowing completeness. No new
Modelica admission or standards/native/MISRA finding closes.

## Static and indexed source elaboration — combined full gate passed

`RumocaCore.GALEC.Elaboration` now contains the reviewed generic prerequisite
chain, with the scratch implementations moved by import/namespace changes only:

- `IteratorNames`, `IteratorIndices`, `Subscripts`: lexical first-match lookup
  precedes exact extent checking. Non-iterator barriers stop lookup without
  adding an intrinsic iterator slot. Independent source Integer evaluation is
  exactly the one-based intrinsic coordinate; ordered bounds and actual checked
  decoding preserve every axis. Rank traversal does not enumerate tensor cells.
- `Bindings`, `Path`: immutable original Solve references retain shape and
  method capabilities. Qualified keys remain component lists. State paths
  preserve final indices and reject indexed intermediate components. Lookup
  never falls through to a duplicate binding after a shape/capability failure.
- `Static.Dimensions`, `Static.Naturals`, `Static.Bounded`: metadata-only shape
  queries, unsigned decimal literal Tokens and parentheses. Independent
  relational semantics gives executable soundness/completeness. The explicit
  Integer ceiling is checked for every nested axis and selected result.
- `Parser.DecimalNat`: reusable ASCII decimal semantics, exact parsing and
  canonical rendering for every Nat. Leading zeros denote decimal, not octal.
  The parser package owns this helper; it imports neither frontend nor backend.

The core owner check passed 2,333 jobs and 672 complete whitelisted reports,
including all 88 new public declarations registered in existing per-module
audits. The parser owner passed 954 jobs and 322 complete whitelisted reports,
including all seven decimal roots; its source matches the reviewed scratch
helper byte-for-byte (`build/decimal-adoption/`). Scratch static final-v1 passed
five modules/26 selected roots after
repairing only `fit_iff` equality substitution with omega. Earlier failed logs
remain distinct. Evidence: `build/galec-static-elaboration-owner-v1.*`,
`-post-owner-v1.*`, `-required-roots.txt`, and `build/galec-static-draft/`.
Independent Astra adoption review confirmed mechanical identity of all eight
core modules and complete public-root registration, with no substantive finding:
`build/galec-index-elaboration-adoption-review.md` (main read in full).
Implementation `ba65b18` passed full gate V1/session74650 and post-audit
V1/session8668, both terminal0. All2,563 frozen inputs matched, all8,286 complete
reports passed the unchanged whitelist, all140selected roots and four retained
FMU roots were present. FMI matrices covered75functions each and526/650/526cells
with no recorded-finding discrepancies/unexpected results. Actual scalar/tensor
AlgorithmCode and ProductionC members were byte-identical to baseline. Evidence:
`build/galec-static-elaboration-full-gate-v1.*`, `-post-audit-v1.*`,
`-required-roots-v1.txt`, `-fmu-retained-v1.axioms`, `-before-members-v1.sha256`,
`-after-members-v1.sha256`, `-archives-v1.sha256`. Subsequent source declaration
and range scratch work is not part of this gate or production admission.

No production grammar, accepted source, emitter or actual-artifact predicate
changes. This does not validate arbitrary declaration tables, source shadowing,
direction rules, target widths or counter increments. Zero-sized mathematical
shapes/iterator contexts do not establish source admission. General signed
Integer expressions, indexed intermediate record paths, loop AST lowering and
its complete actual-artifact correspondence remain open. The eFMI loop syntax
in the pinned text is TODO-labelled; this change does not assume a normative
omitted-step default. Retain GJ01/GJ03/N01 and all standards/native/MISRA findings.

## Typed loop bodies and prepared square composition — full gate passed

The concrete typed pointwise, nested rectangular-clear, diagonal-scatter and
whole square/Jacobian bodies now instantiate the reusable statement semantics.
They are parameterized by extents, typed input/output references, iterator
contexts and arbitrary initial stores. Loop bodies are constructed once, not
per tensor element. The pointwise/coefficient templates are explicitly rank
one; clearing is rectangular rank two. No all-rank renderer is claimed.

`StoreIteration` lifts arbitrary partial/nondeterministic tensor executions to
the existing typed environment, with a sufficient and necessary whole-store
frame. `CoefficientTerms` reifies the certified immutable expression into
ordinary reads/operators without AD or arithmetic rewrites. `MatrixClear`
proves exact row/nested prefixes and all-cell clearing; `MatrixBodies` connects
the literal-only nested body to it without assuming scalar arithmetic total.
`VectorBodies` proves exact finite execution of pointwise and scatter bodies;
`VectorDiagonal` composes clearing/scattering, retaining every expression domain.

`SquareBodies.body_executes` is an iff between the actual typed body execution
and the original prepared square RHS finite execution plus the exact final
two-update store. Existing `square_from_finite_rhs` supplies coefficient domains:
the primal multiplication is not dropped merely because doubling is finite.
`jacobian_value_prepared` relates each matrix coordinate to the actual
AD-generated `DiagonalProgram.eval`, with a proved vector-coordinate bridge.
`body_outputs` retains the finite RHS, prepared matrix and every unrelated
binding. Vector and matrix destinations are distinct by rank, even at equal
volume. Output equality is exact Binary64.Value equality, including signed zero;
off-diagonal clearing uses positive zero. Evaluator equality alone is explicitly
not a successful-execution or signal-handling claim.

The old public `scatter_prefix` statement is unchanged: its induction proof is
factored into the more general `scatterWith_prefix`, and the old theorem is a
wrapper. Existing `scatter` execution remains definitionally the same. One
dependent proof needs explicit beta reduction; no theorem or contract is weakened.
Generic bound reindexing changes only a proved-equal Fin bound, not tensor shape.

Owner V1 passed `lake build check-core` (2,312 jobs): 584 complete whitelisted
reports, all 62 new roots plus all 44 preceding typed-statement roots, no
new-module warnings. Independent Astra review found no semantic/adoption issue
and reconciled the 62 new roots. The matrix-clear sidecar's 15 roots were checked
and reviewed before adoption; main added independent loop-relation consequences.
Evidence: `build/galec-typed-bodies-owner-v1.*`,
`build/galec-typed-bodies-{new,required}-roots.txt`, and
`build/galec-matrix-clear-draft/`. Earlier failed elaboration logs remain separate.

Implementation `a7b854a`, including the `c9843b1` statement addition, passed
the required full gate V1/session92788 and post-audit V1/session52530, both
terminal exit 0. All 2,545 frozen inputs are unchanged; 8,184 complete reports
pass the unchanged whitelist; all 106 required roots and four retained FMU
roots are present. Three FMI matrices cover 75 functions each and 526/650/526
behavior cells, with no discrepancies/unexpected results. Existing actual-file,
native and mutation boundaries pass. Actual scalar/tensor Algorithm Code and
Production C members are byte-identical to baseline. Evidence:
`build/galec-typed-bodies-full-gate-v1.*`, `-post-audit-v1.*`,
`build/galec-typed-bodies-{before,after}-members.sha256`,
`build/galec-typed-bodies-fmu-retained-v1.axioms` and `-archives-v1.sha256`.
No grammar, emitter, production source
case or actual-artifact contract has changed. Parsed/elaborated GALEC linkage,
surface/target Integer bounds, signal/failure-state behavior, native aliasing
and repaired artifact evidence remain open. Adopt the prepared recurring review
before grammar edits, then connect these typed bodies through LALR actions,
elaboration, rendering, target refinement and actual-file/archive contracts.
GJ01/GJ03/N01 and all retained standards/MISRA findings remain open.

## Typed statement integration — owner passed; full repair gate pending

The next core prerequisite adds four modules, without grammar, source
admission, emitter or artifact-contract changes:

- `Tensor.Coordinates`: arbitrary-rank coordinates, a row-major dense-index
  equivalence, exact agreement with the existing vector/matrix layouts,
  one-based bounds and an exact checked one-based decoder round trip.
- `Solve.Tensor.Environment`: updates of the existing typed `Env`, with exact
  addressed reads and an independent frame iff for every other reference,
  including different nominal shapes. There is no new untyped register map
  or Solve-to-GALEC dependency.
- `GALEC.IndexSyntax`: intrinsically bounded iterator references and per-axis
  subscripts, with weakening/capture-preservation proofs even when nested
  binders have equal extents. Names are absent from this resolved core syntax.
- `GALEC.Statements`: typed scalar reads, output-only indexed writes,
  sequencing and bounded nested loops. Independent scalar/write/frame/loop
  relations compose to `Statement.execute_correct`, universal in syntax,
  contexts, arithmetic, iterator environments and initial/final states.

The evaluator theorem explicitly assumes total deterministic scalar arithmetic.
The independent execution relation permits partial/nondeterministic arithmetic;
it is not a proof that finite IEEE execution always succeeds. Future finite
execution with mutable output reads needs intermediate-state domain reasoning.
Inputs and iterators are separate immutable semantic environments; native
aliasing and parsed-source mutability still need their translation proofs.
Prepared Nat bounds do not prove target Integer representability or surface
range semantics. Zero-volume mathematics does not admit zero-sized GALEC arrays.
No callback or enumerated scalar instruction list is stored in the statement IR.

Scratch checks passed before adoption, including 44 complete whitelisted roots.
Integrated owner V1 passed `lake build check-core` (2,298 jobs): 522 complete
whitelisted reports, all 44 new roots, no new-module warnings. Independent
Astra semantic and adoption reviews found no issue after correcting ownership:
Environment imports Solve directly, while Statements imports TensorWrites.
All four audit modules are wired into the existing CoreAudit aggregator.
Evidence: `build/galec-statements-owner-v1.*`,
`build/galec-statements-required-roots.txt`, and scratch `build/galec-index-draft/`.

The full gate recorded below covers `8f9034b`, NOT these newer modules.
Next instantiate the pointwise and nested matrix-clear/diagonal-scatter bodies
in this typed syntax and connect their execution to the previously proved
realizations. Then complete the parser/elaboration/render/actual-artifact chain
under the reviewed repair scope. The prospective whole-subset checklist in
`build/galec-loop-stage-review-draft.md` was read by main, but still needs
adoption into the recurring ledger before any grammar edit. GJ01/GJ03/N01 and
all retained conformance/native/MISRA findings remain open.

## Gated bounded-execution and coefficient baseline

This is core semantic preparation for GJ01/GJ03, not a grammar cutover or a
new admitted source case. The production parser, emitted GALEC/C and artifact
contracts are unchanged. GJ01/GJ03/N01 and the other standards findings remain
open. In particular, existing artifacts still contain the unresolved GALEC
`jacobian` call and pointwise `.*` spelling.

## Reusable mechanisms

`RumocaCore.GALEC.BoundedIteration` defines structurally bounded ascending
execution and a separate inductive execution relation. Universal prefix/full
correspondence covers total deterministic bodies; guarded correspondence also
retains every index-dependent partial-arithmetic condition. Prefix invariants,
observation frames and one-based mathematical bounds are proved. No evaluator
fuel, opaque-callback IR or compiled list of scalar instructions is introduced.
The body argument is a semantic interpretation, to be supplied by a future
typed statement interpreter. State-dependent guards, errors and early exits
are not silently included in the guarded theorem.

`TensorWrites` proves independent indexed-assignment correspondence, prefix
and untouched-cell properties, complete pointwise overwrites, and matrix
zero-fill followed by diagonal scatter. Results are independent of arbitrary
old destination contents. `diagonal_prepared` relates the result to the
existing `Solve.Tensor.DiagonalProgram` for all shapes, arithmetic and typed
environments. It materializes prepared coefficients; it does not synthesize AD.

`CoefficientRealization` separates exact evaluator equality from successful
ordered finite execution. Its scalar expressions refer to an immutable input;
the pointwise interpretation retains the full nominal tensor shape. Independent
rounding relations supply expression execution, then indexed writes. Generic
pointwise and two-phase diagonal execution theorems connect these relations to
the tensor results. A `FiniteRealization` explicitly retains conditions from
ordered source instructions omitted by a compact expression. Its final
`materializes_iff` preserves both the original program domain and exact result.

`SquareRealization` reuses the existing source-owned square/AD proofs. It
instantiates pointwise scalar multiplication for the prepared RHS, and scalar
`u + u` for prepared Jacobian coefficients. It does not recompute AD or assume
an algebraic identity for arbitrary arithmetic. The finite bridge preserves
exact encodings, including negative zero, and retains primal-square finiteness
as well as finite coefficient additions. Execution of the original square RHS
supplies these conditions; they are not extra caller assumptions. The matrix
clear uses positive zero, independently of the coefficient's sign.

## Boundaries

All shapes, including zero volume and rank-zero volume one, are covered by
the semantic statements. That does not license GALEC zero-sized declarations,
an unchecked `1:0` range, or a flattened higher-rank surface index. Every value
and result retains rank and extents. Iterating cells is semantic runtime
execution, not compiler-lowering enumeration.

These modules do not establish mutable input/output nonaliasing, machine
Integer representability, surface one-based index conversion, GALEC loop-nest
syntax, parser/action completeness, signal/overflow policy, native floating
environment correspondence, or actual-file certificates for repaired output.
The recursive semantic evaluator is not a host stack/resource guarantee.
Finite arithmetic is a partial specification, not a claim that ordinary
GALEC arithmetic automatically signals or aborts on overflow.

Next: introduce reusable typed loop/index syntax with its elaboration and
execution proofs; connect it to these realizations, the existing prepared
Solve/C refinement and the actual-artifact chain. Review the entire admitted
subset before any repair grammar change. No backend name/shape inference or
AD, hardcoded parser path, contract weakening or new admission is authorized
by this prerequisite checkpoint.

## Evidence status

Core owner V5 passed (`lake build check-core`, 2,290 jobs): 478 complete axiom
reports passed the unchanged whitelist, with all 66 new declaration roots
present and no new-module warnings. All authored declarations have per-module
audit roots wired into `Tests.CoreAudit`; no old roots are removed. V1/V2/V4
retain elaboration failures; V3 passed the initial diagonal bridge before the
pointwise addition. The final owner log is `build/galec-realization-owner-v5.log`.

Independent Astra review found no issue in the iteration/write mechanisms or
the final finite/pointwise/diagonal composition. It explicitly retained the
limits above, including no failure-state/trace equivalence or executed
preflight guarantee. The reviewer did not duplicate the main owner's builds.
The required full artifact gate subsequently passed for implementation
`8f9034b`: `nix develop .#verification --command lake test`, V1 exit0. The
post-audit also passed: 2,523 frozen inputs unchanged, 8,078 complete reports
under the unchanged whitelist, all 66 new roots present, four retained FMU
roots separately audited. The three FMI matrices exercised 75 functions each
and 526/650/526 cells, with no recorded-finding discrepancies or unexpected
results. Existing parser/LSP/source/C/helper/FMI/eFMI artifact, mutation and
native boundaries passed. Actual scalar/tensor Algorithm Code and Production
C members are byte-identical to the baseline; this gate does not repair their
still-open GJ01/GJ03 output findings.

Evidence: `build/galec-realization-full-gate-v1.*`,
`build/galec-realization-post-audit-v1.*`,
`build/galec-realization-{before,after}-members.sha256`,
`build/galec-realization-fmu-retained-v1.axioms` and
`build/galec-realization-archives-v1.sha256`. Gate21657 and post98157 are
terminal exit0. No future typed-statement or renderer change is covered by
this frozen implementation's gate.
