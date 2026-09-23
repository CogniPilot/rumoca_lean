# Exact verification contract

**Shaped initialization and source lowering (full artifact gate passed):**
Core `GALEC.VectorClear` realizes literal-zero rank-one clearing with existing
bounded/assignment statements. `InitializationBodies` composes vector clear,
rectangular matrix clear and scalar literal-one assignment. Independent
`Initializes` specifies exact shaped values and the complete other-reference
frame; execution is iff that predicate and iff the exact ordered environment
update. Rank 1/2/0 forces distinct typed references even at equal volumes.
The core proofs quantify over independent natural extents (including zero),
arbitrary scalar values and partial/nondeterministic arithmetic, without reading
old destinations or inputs and without enumerating elements during lowering.

`Elaboration.Initialization.{VectorClear,Body}` proves actual generic recursive
AST lowering, retaining all trailing skips, and independent source execution
iff the same core result. These source bodies require positive bounded extents;
the composed source currently uses a square matrix matching the vector extent.
Writable bindings and the all-key shape-lookup/meaning correspondence remain
explicit premises, not an inferred Startup permission policy or declaration
validator. No parser/grammar, production source admission or artifact changes.

Four owner implementations are namespace/import/reference migrations of checked
scratch. Main checked exact migrations and read the independent source review.
Independent adoption review also confirmed exact migrations and registration of
all 29 roots, with no substantive finding; main read it completely.
Owner V1/session9879 passed 2,406 jobs; post-owner V1/session74549 passed 985
complete unchanged-whitelist reports, all 29 new roots and nine recorded owner
hashes. Evidence: `build/startup-core-owner-v1.*`,
`build/galec-startup-adoption/`, `build/galec-startup-core-draft/` and
`build/galec-startup-source-draft/`. Implementation `7cef7b0` subsequently passed
the required full gate V1/session22907 and post-audit V1/session46912, both
terminal0. All 2,638 frozen tracked hashes matched; 8,615 complete reports passed
the unchanged whitelist, all 469 selected roots were present and four retained
actual FMU roots passed separate audit. Three FMI matrices covered 75 functions
each and 526/650/526 behavior cells, with zero recorded-finding discrepancies or
unexpected results. Scalar/tensor Algorithm Code and Production C members
remained byte-identical. Evidence prefix: `build/startup-initialization-`
(full-gate/post-audit V1 logs, frozen inputs, required roots, retained FMU audits,
before/after-member and archive hashes). Later policy/named-preparation/parser
repair drafts are outside this gate; no compliance finding closes.

Separate checked C scratch composes the actual numerical initializer for both
`x` and `J`, then status/period/return, under allocated-only storage with exact
positive-zero reads and a full heap frame. Conditional source/core-to-C scratch
connects the same values to that candidate body without assuming old finite
heap values. It does not enter the unchanged public Startup function or bind an
actual emitted file. These candidate proofs are outside the owner adoption;
Startup input policy, public-entry/artifact cutover and standards/MISRA findings
remain open. Evidence: `build/galec-startup-{c,link}-draft/`.

**Method selection and DoStep capabilities (full artifact gate passed):**
The generic parser utility `UniqueSelection` selects one key occurrence, rejecting
duplicates even when their values are identical. Core `Elaboration.Methods`
retains original token categories and whole methods, then checks public visibility
and the matching end-name. Invalid matching headers cannot be filtered away
before duplicate detection. These are independent selection/header judgments,
not a body recognizer or complete block validation.

Core `Elaboration.Capabilities.DoStep` derives writable roles from variable
variability and non-input direction. It traces actual typed target paths and
full shapes back to declaration metadata, and universally proves an independent
recursive write-side condition for the original nested AST. Source declaration
validity/uniqueness, method identity and complete permissions remain separate;
the policy does not apply to Startup, absent parameter kinds or range handling.
No source admission, production grammar/emitter or artifact predicate changes.

Five implementations are exact namespace/import/reference migrations from
reviewed scratch. The combined parser/core owner V1/session67533 passed 2,423
jobs; post-owner V1/session82937 passed 1,294 complete unchanged-whitelist
reports, all 44 new roots and 11 input hashes. Main checked exact migration;
independent Astra adoption review found no substantive issue and confirmed all
audit registrations. Evidence: `build/method-capability-adoption/`.
Implementation `07e1060` subsequently passed the required full gate
V1/session15943 and post-audit V1/session82397, both terminal exit 0. All 2,630
frozen tracked input hashes matched; 8,586 complete reports passed the unchanged
whitelist, all 440 selected roots were present and four retained actual FMU
roots passed separate audit. Three FMI matrices covered 75 functions each and
526/650/526 behavior cells, with zero recorded-finding discrepancies or
unexpected results. Scalar/tensor Algorithm Code and Production C members
remained byte-identical. Evidence: `build/method-capability-full-gate-v1.*`,
`-post-audit-v1.*`, `-required-roots-v1.txt`, `-fmu-retained-v1.axioms`,
`-before-members-v1.sha256`, `-after-members-v1.sha256`, `-archives-v1.sha256`.
Prospective named-source/C, whole-interface-header and Startup repair
certificates remain scratch, outside this gate. Existing compliance findings
remain open; no production source admission or behavior changed.

**Generic exact-tree and typed-action certificates (combined full gate passed):**
The parser package now owns `LALR.ExactTree` and `LALR.ActionCertificate`.
The two exact-tree theorems specialize existing universal completeness and
resource proofs to an independently checked candidate with the exact full input
yield. They establish the actual bounded parser result without assumed tree
uniqueness or replaying LR tables by conversion. Original token payloads,
scanner provenance and typed AST correspondence remain separate obligations.

The action certificate builder constructs proofs of the existing independent
`StructuralActions.Denotes` using its constructors and reflexivity. It synthesizes
map results before checking the requested result; normal kernel checking and the
unchanged axiom audit remain authoritative. It is not a replacement interpreter,
and no completeness/performance guarantee is claimed for bounded metaprogram
search. The existing arbitrary-depth action fixture now uses it in the base case
for arbitrary identifier spellings; the theorem statement and inductive step are
unchanged. No grammar, source admission, production emitter or artifact predicate
changes, and no lifecycle/native/MISRA finding closes.

Both implementations match reviewed scratch by namespace migration only. Main
checked exact diffs; independent Astra adoption review found no substantive
issue and confirmed all three audit roots. `lake build check-parser` passed
956 jobs and 325 complete unchanged-whitelist reports; four source/audit hashes
matched in post-audit. Evidence: `build/parser-certificate-adoption/`.
Implementation `e5b8a39` subsequently passed the required full gate V1/session68139
and post-audit V1/session55080, both terminal exit 0. All 2,621 tracked input
hashes matched; 8,542 complete reports passed the unchanged whitelist, all 396
selected roots were present and four actual retained FMU roots passed separate
audit. Three FMI matrices covered 75 functions each and 526/650/526 behavior
cells, with zero recorded-finding discrepancies or unexpected results. Actual
scalar/tensor Algorithm Code and Production C members remained byte-identical.
Evidence: `build/parser-certificate-full-gate-v1.*`, `-post-audit-v1.*`,
`-required-roots-v1.txt`, `-fmu-retained-v1.axioms`, `-before-members-v1.sha256`,
`-after-members-v1.sha256`, `-archives-v1.sha256`. Later scratch method selection,
capabilities, named preparation and interface-header work are outside this gate.
No open compliance finding closes.

**Surface square/AD composition (combined full gate passed):**
Reusable `StatementRelations` proves skip, sequencing and bounded-loop
congruence for partial/nondeterministic execution. Generic surface witnesses
live in `Elaboration.Surface`; the existing rank-one square repair instances
live in `Elaboration.Square`. The actual square/clear/scatter AST lowers through
generic `Bodies` to the exact statement tree, including every trailing skip.
Only relational congruence connects that result to prepared `SquareBodies`;
no source-body recognizer, arithmetic rewrite or compiler optimization is added.

The four source declarations produce the same logical table used by reads,
writes and dimension queries. The source execution iff retains the original
finite square RHS domain and exact final store, with observations equal to the
prepared AD-generated matrix in Binary64 encodings. Both matrix axes and
distinct equal-extent iterator slots remain explicit; no cells are enumerated
during lowering. Supplied method roles remain separate from normative permission
validation. Actual scanner/rendered-text identity, complete method/lifecycle
legality, target counters, initialization and actual artifact composition remain
required. No production grammar, source admission or target bytes change.

The six owner modules and six audit leaves passed 2,389 core jobs, 925 complete
unchanged-whitelist reports and all 56 new roots; 13 adopted source/audit hashes
were recorded. Scratch combined final-v1/session30892 passed seven modules and
56 roots, with all six implementation logs empty. Main read the generic
relation proof and all three independent semantic reviews; no substantive
finding. Independent adoption review confirmed exact namespace/import/open
migration and complete registration of all 56 roots, with no finding
(`build/galec-square-adoption/review.md`). Evidence: `build/galec-square-adoption/`,
`build/galec-composition-draft/*-final-v1.*` and its three review documents.
The preceding full gate below does not cover this subsequent adoption.

Implementation `ba6c98f` subsequently passed the required
`nix develop .#verification --command lake test` (V1/session11824) and
post-audit (V1/session5263), both terminal exit 0. All 2,619 tracked input
hashes remained unchanged; 8,539 complete axiom reports passed the unchanged
whitelist, all 393 selected roots were present and four retained actual FMU
roots passed separate audit. The three FMI matrices covered 75 functions each
and 526/650/526 behavior cells, with zero recorded-finding discrepancies or
unexpected results. Scalar/tensor Algorithm Code and Production C members
remained byte-identical to the preceding gate. Evidence:
`build/galec-square-full-gate-v1.*`, `-post-audit-v1.*`,
`-required-roots-v1.txt`, `-fmu-retained-v1.axioms`,
`-before-members-v1.sha256`, `-after-members-v1.sha256`, `-archives-v1.sha256`.
This covers the adopted surface prerequisites, not subsequent scratch
source-preparation, source-to-C composition or exact-tree certificate work.
No production admission or open compliance finding changes.

**Recursive source bodies and logical storage (combined full gate passed):**
Core `Elaboration.Bodies` now structurally lowers the actual nested AST and
proves exact typing and conditional execution correspondence with independent
source semantics. Mathematical Integer iteration preserves actual nested bodies,
iterator environments and intermediate stores. Arithmetic may remain partial
or nondeterministic; no total evaluator or replacement canonical body defines
source meaning. Compiler recursion visits syntax, not iterations or tensor cells.

`Elaboration.Layout` constructs existing shaped input/output references in
declaration order from full Real descriptors and separately supplied roles.
All allocated role-tagged typed slots are distinct, including repeated shapes;
this is not a native-address nonaliasing claim. Its shape lookup agrees for all
keys with the same validated source declarations. The closed-body execution
composition therefore discharges the previously assumed shape-provider premise
using the exact table employed for expression and assignment resolution.
Roles are not inferred from direction/variability, and their method legality is
not proved here. Complete initial scope, scanner provenance, environment
initialization, target counters and actual rendered-body/Solve/artifact linkage
remain obligations. No grammar, accepted source, emitter or artifact predicate
changes, and no standards/native/MISRA finding closes.

The seven modules and their audit leaves passed `lake build check-core`:
2,377 jobs, 869 complete unchanged-whitelist reports and all 62 new roots.
Fifteen adopted source/audit hashes were recorded. Main checked the exact
namespace/import migration from reviewed scratch; independent Astra review
confirmed all seven modules and exact 62-root registration, with no finding
(`build/galec-layout-adoption/review.md`). The layout scratch check
passed five modules and 38 roots, with its four implementation logs empty;
the prior nested-body check passed four modules and 24 roots. Evidence:
`build/galec-layout-adoption/`, `build/galec-layout-draft/*-final-v1.*`,
`build/galec-layout-draft/layout-review.md`, and
`build/galec-nested-body-draft/*-final-v2.*` plus its semantic reviews.
These owner checks are not the required combined C/actual-artifact gate.

Implementation `b1b1335` subsequently passed the required full gate and
post-audit V1, both terminal exit 0. All 2,607 tracked input hashes remained
unchanged; 8,483 complete axiom reports passed the unchanged whitelist, all
337 selected roots were present and four actual retained FMU roots passed a
separate audit. The three FMI matrices covered 75 functions each and
526/650/526 behavior cells, with zero recorded-finding discrepancies or
unexpected results. Actual scalar/tensor Algorithm Code and Production C
members remained byte-identical to the preceding gate. Evidence:
`build/galec-layout-full-gate-v1.*`, `-post-audit-v1.*`,
`-required-roots-v1.txt`, `-fmu-retained-v1.axioms`,
`-before-members-v1.sha256`, `-after-members-v1.sha256`, `-archives-v1.sha256`.
The gate does not cover subsequent scratch surface-square composition or
source-preparation proofs and does not close the open compliance findings.

**Declaration/range and assignment elaboration (combined full gate passed):**
Fifteen reviewed modules now live in core: source declaration/shape-provider
validation, mathematical Integer iteration and explicit fresh unit-loop
headers, shaped reads/locations, Real expressions, writable assignments and
ordered statement-list composition. Independent source judgments retain
partial/nondeterministic arithmetic, exact addresses, per-axis dimensions and
whole-store frames. `Iteration.executes_congr` universally lifts pointwise
body-relation equivalence through every bounded prefix. No tensor cells are
enumerated and no callbacks are stored in resolved IR.

The combined core owner passed 2,363 jobs, 807 complete unchanged-whitelist
reports and all 135 new roots; 33 owner/audit input hashes were recorded.
Main and independent Astra reviews confirmed mechanical identity to checked
scratch, preserved root coverage and the new relational congruence lemma.
Evidence: `build/galec-body-adoption/{owner-v1.*,post-owner-v1.*,new-roots.txt,
declarations-range-review.md,read-assignment-review.md}`. Actual recursive loop
AST lowering remains separate scratch; this adoption does not admit source
cases, change the production parser/emitter or prove complete loop artifacts.
Method capability and scope policy, target counters, normative range-policy
coverage and GJ01/GJ03/N01 remain open. See [details](../dev/galec-realization.md).

Implementation `f1fa7b9` passed the required full gate and post-audit V1,
both terminal exit 0. All 2,593 tracked input hashes remained unchanged;
8,421 complete axiom reports passed the unchanged whitelist, all 275 selected
roots were present, and four actual retained FMU roots passed a separate audit.
The three FMI matrices covered 75 functions each and 526/650/526 behavior cells,
with zero recorded-finding discrepancies or unexpected results. Actual scalar
and tensor Algorithm Code and Production C members remained byte-identical to
the preceding gate. Evidence: `build/galec-body-elaboration-full-gate-v1.*`,
`-post-audit-v1.*`, `-required-roots-v1.txt`, `-fmu-retained-v1.axioms`,
`-before-members-v1.sha256`, `-after-members-v1.sha256`, `-archives-v1.sha256`.
This covers the adopted prerequisites, not subsequent scratch recursive-body
or storage-layout proofs, and does not close the open compliance findings.

**Static/indexed GALEC elaboration prerequisites (combined full gate passed):**
The core now owns immutable shaped read/write binding metadata, retained AST
state paths, lexical iterator resolution with non-iterator barriers, exact
per-axis subscript elaboration and static decimal/dimension-query evaluation.
Every executable classifier is related to an independent source judgment;
iterator values correspond exactly to one-based coordinates with per-axis
Integer bounds. Shape queries use declared metadata, not runtime tensor values.
The bounded static evaluator checks every nested query axis and result against
an explicit caller-supplied ceiling, not only the final value. Decimal spelling
and universal rendering proofs live in the generic parser package, without a
backend dependency. No tensor elements are enumerated during elaboration.

`lake build check-core` passed 2,333 jobs; all 672 complete axiom reports pass
the unchanged whitelist, including all 88 new public core roots. The parser
owner passed 954 jobs and 322 complete whitelisted reports, including all seven
decimal roots; its adopted source is byte-identical to the reviewed scratch
helper (`build/decimal-adoption/`). The preceding
scratch static chain passed five module checks and 26 selected roots. Evidence:
`build/galec-static-elaboration-owner-v1.*`, `-post-owner-v1.*`,
`-required-roots.txt`, and `build/galec-static-draft/*-final-v1.*`.
Independent Astra adoption review found no substantive issue and confirmed
the eight core modules differ from checked scratch only in namespaces/imports
(`build/galec-index-elaboration-adoption-review.md`).
These are prerequisites, not a production syntax/admission cutover. Validated
declaration/table construction, lexical scope projection, zero-size policy,
target Integer/counter execution, actual parsed body execution and artifact
linkage remain required. Method capabilities are not blanket eFMI direction
rules. General Integer expressions and arbitrary indexed intermediate record
components are not admitted. See [scope](../dev/galec-realization.md).

Implementation `ba65b18` passed the required full gate and post-audit V1,
both terminal exit 0. All 2,563 tracked input hashes remained unchanged;
8,286 complete axiom reports passed the unchanged whitelist, all 140 selected
roots were present, and four actual retained FMU roots passed a separate audit.
The three FMI matrices covered 75 functions each and 526/650/526 behavior cells,
with zero recorded-finding discrepancies or unexpected results. Actual scalar
and tensor Algorithm Code and Production C members remained byte-identical to
the preceding gate. Evidence: `build/galec-static-elaboration-full-gate-v1.*`,
`-post-audit-v1.*`, `-required-roots-v1.txt`, `-fmu-retained-v1.axioms`,
`-before-members-v1.sha256`, `-after-members-v1.sha256`, `-archives-v1.sha256`.
This gate does not cover the subsequent scratch declaration/range checks and
does not close GJ01/GJ03/N01 or other standards/native/MISRA findings.

**Combined parser/indexed-AST gate (passed, frozen `e08ddef`):**
The required `nix develop .#verification --command lake test` and its V2
post-audit both terminated with exit 0. All 2,546 tracked input hashes stayed
unchanged. The unchanged whitelist accepted 8,191 complete axiom reports,
all 45 selected parser/AST/retained execution roots were present, and four
actual retained FMU roots passed a separate audit. The three FMI matrices
covered 75 functions each and 526/650/526 behavior cells, with zero recorded-
finding discrepancies or unexpected results. Actual scalar/tensor Algorithm
Code and Production C members are byte-identical to the preceding gated
baseline. The named-repeat and signed-credit mutation boundary passed as part
of this gate. Evidence: `build/galec-signed-budget-full-gate-v2.*`,
`-post-audit-v2.*`, `-required-roots-v2.txt`, `-fmu-retained-v2.axioms`,
`-before-members-v2.sha256`, `-after-members-v2.sha256`, `-archives-v2.sha256`.
This covers the signed resource, closure-decision and AST prerequisites below,
not the subsequent scratch loop elaborator. No new source admission or emitted
algorithm follows; GJ01/GJ03/N01 and the other standards/MISRA/native findings
remain open. Historical V1 was stopped with exit 143, not passed.

**Indexed GALEC AST prerequisite (owner and combined full gate passed):**
Mutual expressions/references/components retain computed indices at every path
component, ordinary call Tokens, dimension queries and nested loop bodies with
explicitly omitted or supplied steps. This is unresolved syntax, not a claim
of static bounds, valid Integer indices, shape/mutability checking or execution.
The production grammar is unchanged and its actions construct unindexed paths.
Old scalar/tensor projections require empty base/field indices and reject loops;
all existing arbitrary-AST exact-image/retraction and word/yield/coverage/source
compatibility contracts retain their quantifiers. The factored noinline runtime
checks remain; no token reconstruction or profile-only loop semantics is added.

Owner `lake build check-galec-parser` passed814jobs/162completewhitelistedreports,
including the new `Reference.unindexed` root and retained parser/projection roots.
Main reviewed the worker's AST/projection migration; dependent action and word
proofs rechecked. Host parser `ProfileProjection.c` is144550bytes, separate from
authored Production C. Evidence: `build/galec-surface-ast-owner-v1.*` and
`build/galec-surface-ast-adoption/focused-v2.*`. No grammar, source admission,
emitter or artifact contract changes; the combined V2 gate above covers this
representation and the two generic parser repairs below.

**Kernel-reducible lookahead closure (owner and named certificate passed):**
The original generated `decide +kernel` certificate could not normalize
sorted nullable lookaheads. This reproduces even on the exact named-repetition
fixture required by `tests/lalr.sh`. Full gate5075 for `f33a1eb` was therefore
stopped deliberately (terminal143), not passed or timed out. Its V1 logs remain;
no post-audit or artifact evidence is inferred from that incomplete run.

`LookaheadCandidates` now provides structurally recursive predictions and three
universal exact-membership/specification/bounded-forall equivalences, including
arbitrary missing, repeated or unsorted FIRST facts. Only `ItemCheck.Closed`'s
Decidable implementation changes. `Closed`, `Conditions`, `validate`, sorted
metadata and parser execution contracts retain their definitions/obligations.
The adapter uses `decidable_of_iff`, not an unchecked Bool or native proof axiom.
Owner1555jobs/315completewhitelistedreports/all3newroots passed; independent
review found no weakening. The unchanged named-repetition certificate now
passes. Both production grammar directories and the fixture regenerate
byte-identically. All nine split certificate modules for the prospective
183-state loop grammar now pass, including source, items, three reduction
groups, safety, resources and umbrella; all24selected roots pass the whitelist.
This is a grammar-level certificate, not typed actions/elaboration or artifact
semantics for the new syntax.
Evidence: `build/lalr-lookahead-owner-v1.*`,
`build/lalr-items-draft/named-repeat-v{1,2}.{log,exit}`, `split-*-v1.*` and
`build/lalr-items-draft/audit-v1.{log,axioms}`.
No grammar/admission/emitter/artifact-contract expansion follows. The combined
required V2 full gate above covers this repair and the AST integration.

**Signed LALR resource credits (owner and combined full gate passed):**
The reusable parser can now carry positive symbol weights through named
token-consuming rules. Three universal lemmas characterize repetition and
the old nonnegative-credit obstruction. The existing valid-tree bound,
all-input termination, safety and membership equivalence retain their premises
and guarantees; no validator or axiom policy is weakened. Runtime fuel still
uses only token allowance and state-credit ceiling. The old resource search
is tried first; bounded signed fallback recomputes grammar and state credits
on every attempt, without claiming search completeness.

Owner `lake build check-parser parser/lalrgen` passed 1,553 jobs and 312
complete whitelisted reports, including all three new roots. Actual generation
and full directory comparisons preserve both production grammars' generated
bytes. Independent review found one mutation-selector bug, corrected before
the required full gate; no semantic weakening was found. Existing recursive
native/mutation checks now use a named repeated body and nonvacuously corrupt
its negative credits. Their gate remains pending. Evidence:
`build/galec-signed-budget-owner-v1.*` and production regeneration under
`build/galec-signed-budget-draft/{modelica,galec}/`.
No production grammar, accepted source, emitted algorithm/C or artifact
contract changes. The larger prospective loop grammar's initial item-closure
normalization failure was repaired by the structural closure decision above;
its checked scratch certificates do not constitute a production cutover.
The combined V2 gate certifies `e08ddef`; the older full gate below certifies
the preceding `a7b854a`.

**Typed square/Jacobian loop bodies (combined full gate passed):**
Concrete pointwise and clear-then-scatter bodies now execute through the typed
statement semantics. The complete square body has exact partial finite
execution correspondence to the original prepared square RHS and a final store
whose Jacobian cells equal the existing AD-generated prepared matrix. The
original primal domain, signed zeros and unrelated binding frames are retained.
No new arithmetic-totality premise is imposed. Owner V1 passed 2,312jobs and
584 complete whitelisted reports, including 62 new and the prior 44 roots;
independent semantic/adoption review found no issue. Implementation `a7b854a`,
including `c9843b1`, passed the required full gate and post-audit (both exit 0):
2,545 unchanged tracked inputs, 8,184 complete whitelisted reports, all 106
required roots and four retained FMU roots. All three FMI matrices passed
75 functions and 526/650/526 behavior cells with no discrepancies or unexpected
results. Existing artifact/native/mutation boundaries passed; actual scalar
and tensor Algorithm Code and Production C members are unchanged. Evidence:
`build/galec-typed-bodies-full-gate-v1.*`, `-post-audit-v1.*`,
`build/galec-typed-bodies-{before,after}-members.sha256`,
`build/galec-typed-bodies-fmu-retained-v1.axioms` and `-archives-v1.sha256`.
No grammar, admission, emission or
artifact contract changes; GJ01/GJ03/N01 remain open. See
[the precise scope and evidence](../dev/galec-realization.md).

**Typed GALEC statement prerequisite (owner passed; full repair gate pending):**
Rank-preserving coordinate/one-based conversion, typed Solve environment
updates, scoped per-axis indices and generic assignment/sequence/bounded-loop
semantics are now integrated. Universal execution correspondence uses
independent scalar/write/frame/iteration relations and explicitly requires
total deterministic arithmetic for the executable evaluator theorem; the
relation itself may use partial arithmetic. Owner V1 passed 2,298jobs and
522 complete whitelisted reports, including all 44 new declaration roots.
Independent semantic/adoption review found no issue. No parser, admission,
emission or artifact contract changes; no repair/conformance finding closes.
The full gate below is for the earlier `8f9034b` baseline, not this addition.
See [exact scope, evidence and next obligations](../dev/galec-realization.md).

**GALEC bounded tensor realization (semantic prerequisites; full gate passed):**
Four new core modules supply universal bounded-loop/write correspondence,
shape-preserving pointwise and diagonal execution, and proof-bearing prepared
coefficient realization. The finite square instance reuses existing AD proofs,
preserves exact encodings and retains the original primal-square domain.
Independent scalar rounding and write relations compose to the prepared
result. See [the scope and evidence record](../dev/galec-realization.md).
No production grammar, accepted source case, emitter or artifact contract
changes. GJ01/GJ03/N01 and other standards/native/MISRA findings remain open;
the unchanged emitted GALEC still has its recorded output findings.

Implementation `8f9034b` passed the required
`nix develop .#verification --command lake test` (V1, exit0), followed by a
successful post-audit. All 2,523 frozen inputs were unchanged; all 8,078
complete reports passed the unchanged whitelist. All 66 new declaration
roots were present and four retained FMU roots were separately audited.
All three FMI matrices passed 75 functions and 526/650/526 cells with no
recorded-finding discrepancies or unexpected results. Existing parser/LSP,
source/C/helper, FMI/eFMI artifact/native/mutation boundaries passed. Actual
scalar/tensor Algorithm Code and Production C members match the baseline
byte-for-byte. Independent Astra review found no issue within the stated
semantic scope. Gate21657 and post98157 are terminal exit0.
Evidence: `build/galec-realization-full-gate-v1.*`,
`build/galec-realization-post-audit-v1.*`,
`build/galec-realization-{before,after}-members.sha256`,
`build/galec-realization-fmu-retained-v1.axioms` and
`build/galec-realization-archives-v1.sha256`.

**GJ02 declaration placement repair (full gate passed; positional finding closed):**

Implementation `4371eb3` passed the required
`nix develop .#verification --command lake test` (V1, exit0). All 2,514 frozen
tracked inputs were unchanged. All 8,012 complete printed axiom reports passed
the unchanged whitelist; all 18 selected roots, including the five new
rejection roots, were present. Four roots retained in the three FMUs were
separately audited. FMI matrices passed 75functions each and 526/650/526cells,
with zero recorded-finding discrepancies or unexpected results. Existing
parser/LSP, source/C/helper and scalar/tensor FMI/eFMI artifact, native and
mutation boundaries passed, including all three new old-order mutations.

Main inspected `AlgorithmCode/model.alg` in the actual `build/TensorSquare.efmu`:
all three declarations place dimensions after names. Its SHA-256 is
`69c3fc4e3dd6800a558404f7a5d8d369c2d26d610eec9f7b76d12be47b127b36`;
the archive SHA-256 is
`f359de826bf6fa468194db794e1d5e6e7490f4bd4554fe48cb69406b85140f5c`.
Scalar Algorithm Code and both scalar/tensor Production C members are
byte-for-byte unchanged against the pre-repair archive hashes.
Evidence: `build/gj02-full-gate-v1.*`, `build/gj02-fmu-retained-v1.*`,
`build/gj02-{before,after}-{algorithm,production-c}.sha256` and
`build/gj02-efmu-v1.sha256`. Gate3446 and post-audit69453 are terminal exit0.

This closes only GJ02's dimensional-position mismatch, not whole GALEC
declaration conformance. The separate block-direction ambiguity remains. Main
also confirmed GJ03: the current `.*` spelling is absent from the pinned G-3
arithmetic-operator production. GJ01/GJ03/N01 and other standards/native/MISRA
findings remain open; no new Modelica case is admitted.

The tensor GALEC grammar, generated Lean LALR tables, typed action slots,
`TensorBlock.tokens` specification and emitted Algorithm Code now put constant
dimensions after declaration names: `Real u[2]`, `Real x[2]`, `Real J[2, 2]`.
The AST, indexed shapes, derivative/adjoint mathematics, prepared Solve and
numerical C implementation are unchanged. Ordinary identifier call handling
remains intact; GJ01's missing normative `jacobian` definition is not repaired.

Universal corrected-profile acceptance, arbitrary-tree yield/build equivalence,
actual emitted-text lexing/parsing and kernel refinement re-elaborated. New
`DeclarationOrder.source_rejected_at_position` proves actual parser rejection
for arbitrary source/token tails with a dimension bracket in any declaration-
name slot, including combinations and the old all-three-misplaced form. Five
new theorems have audit roots; the existing renderer-completeness theorem now
also has an explicit audit entry. Current specification/reference equality is
not described as historical language equality across the intentional repair.

Owner V3 passed 2,314 jobs / 456 complete audited reports, all 18 selected roots
present (five new), unchanged whitelist and no new-module warnings. V1 failed
only on two new proof-script rewrites; V2 passed proofs but lacked the explicit
renderer audit entry. Evidence: `build/gj02-owner-v3.log`, `.exit`, `.axioms`,
`build/gj02-required-roots.txt`. Bounded independent Astra review found no
positional, proof-scope or mutation issue; it did not run builds. The existing
tensor actual-file boundary now includes three independent nonvacuous old-order
mutations; both script syntax and full-gate execution passed.

The nine-row whole-subset review is recorded in `dev/standards-review.md`.
The repair's own corrected artifacts and required gate establish the bounded
GJ02 closure recorded above; the previous baseline gate was not substituted
for repair evidence. Block-direction ambiguity and the other findings remain.

**GALEC structural cutover and PA11 repair (full gate passed):**

Implementation `acf3046` passed the required
`nix develop .#verification --command lake test` (V2, exit 0). All 2,513 frozen
tracked inputs were unchanged. All 8,006 complete printed axiom reports passed
the unchanged whitelist, including all 62 cutover and 64 projection-repair roots.
The four certificates retained inside the three actual FMUs were independently
audited. FMI matrices passed 75 functions each and 526/650/526 behavior cells
for Integrator/TensorSquare/ConstantRates, with zero recorded-finding
discrepancies or unexpected results. Parser/LSP, actual source/C, tensor/helper,
scalar/tensor FMI/eFMI, native-boundary and mutation checks passed.

Evidence: `build/galec-cutover-full-gate-v2.log`, `.exit`, `.axioms`,
`-inputs.sha256`, `-post-audit.log`/`.exit`, and
`build/galec-cutover-fmu-retained-v2.axioms`/`.sha256`.
Session84939 and post-audit session18202 are terminal exit0. V1 below remains a
deliberately stopped failed run; it is not relabeled as pass evidence.
This closes the cutover's missing artifact gate and PA11's observed host-build
failure. It does not close GJ01/GJ02/N01, native correspondence, the other
standards findings or MISRA compliance. No grammar/source admission changed.

**PA11 projection repair (owner/native evidence preceding full gate):**

The GALEC structural cutover now uses compositional `@[noinline]` AST checks,
with unchanged embeddings and six public projection/retraction theorem
statements. Independent helper and exact-image proofs cover all ASTs, including
malformed rejection. The previous giant matcher is removed entirely; there is
no token reconstruction, decoder fallback, second parse or valid-AST premise.
Scratch migration proofs establish equality to the previous projectors using
their exact-image contracts; those old matchers are not imported into production.
Bounded independent Astra review found no issue in the draft or integration.

Owner checks passed 829 jobs and 465 complete audited reports, including all
64 added roots, with the unchanged whitelist and no new-module warnings.
Evidence: `build/galec-projection-factor-owner-v1.log`, `.exit`, `.axioms`,
and `build/galec-projection-factor-new-roots.txt`.
The integrated host C is 5,159 lines / 142,920 bytes; its native object built
successfully in 2.2 seconds (`build/galec-projection-factor-native-v1.log`,
`.exit`). These measurements repair the observed PA11 build-cost problem,
not the model-C trusted boundary or standards findings. The required full
artifact gate subsequently passed as recorded above; stopped cutover V1 below
remains failed evidence.
No grammar, admission, lowering, emitted model C or contract weakening occurred.

**GALEC structural action cutover (owner checks passed; full gate pending):**

The source entrypoints now pass the actual accepted LALR CST to structural
conversion, the reusable typed rule-table engine and direct AST profile
projections. They parse once and retain the original token categories, names,
ordinary call identifiers and explicit extents. The old token decoders are
noncomputable proof-only compatibility specifications, not a runtime fallback.
All nine current rules have exhaustive coverage/licensing certificates.

Generic independent token-yield semantics plus direct frontend profile proofs
establish exact token/AST correspondence for arbitrary valid start-rule trees,
without the earlier finite-action engine, reconstructed canonical trees or CST
uniqueness. Exact unconditional `Except` equalities preserve both successful
source results and diagnostic text/precedence against proof-only pre-cutover
references. Existing source completeness and lexical/grammar/resolution fields
are retained. Bounded Astra review found no code-contract issue; it did not
establish elaboration of the then-live final equality proof or the artifact gate.
The equality proofs subsequently passed. Final owner checks passed 829 jobs
and 401 complete printed axiom reports, including all 62 new roots, under the
unchanged whitelist, with no new-module warnings. Evidence:
`build/galec-cutover-owner-v2.log` and `.axioms`. V1 failed on a duplicated
documentation comment, fixed before V2; earlier source-proof iterations were
not pass evidence. The first required full gate was deliberately stopped during
native compilation: the nested AST projection generated 54,459,127 bytes of
host C, and GCC reached 529 seconds / 12,206,916 KiB observed RSS. This was
host compiler code, not emitted model C. Gate V1 exited 1 after that targeted
termination; all 2,513 frozen inputs were unchanged. It is not pass evidence.
PA11 in `dev/performance-audit.md` records the required proof-preserving
projection refactor. The actual-artifact gate remains incomplete.

No grammar, source-admission, lowering, emitted-C or artifact-contract change.
This is an architectural prerequisite for authorized repairs, not closure of
GJ01/GJ02/N01, the other standards findings, native correspondence or MISRA.
Earlier full-gate records below do not certify this working-tree cutover.

**Recursive structural actions (full gate passed):**

`Parser.LALR.EBNFActions` adds reusable typed rule-table delegation over the
actual structural tree, including empty, optional and repeated expressions.
Lexicographic structural termination permits recursive source rules and nullable
repetitions without another fuel parameter. Independent denotation, exhaustive
source-rule coverage and rule licensing prove soundness, totality, unique
results and exact valid-tree domains. The executable composition with the
existing structural bridge preserves the actual LALR parser's complete language.
One body per rule name is required; alternatives reside inside that body.
Runtime inputs contain no proof-only lowering witness. The classifier boundary
remains `decode ∘ encode`; meaningful frontend AST semantics remain obligations.

Universal heterogeneous-rule recursion and nullable-repetition instantiations
are package-owned proofs, not bounded acceptance examples. Standalone checks
passed 18 roots. Owner checks passed 798 jobs and 297 complete axiom reports,
including all 18 new roots, under the unchanged whitelist; no new-module
warnings. Evidence: `build/recursive-actions-owner-v2.log` and `.axioms`.
The earlier V1 package run failed on missing proof-module registration and is
not pass evidence. Independent Astra review found no bounded engine,
parser-composition or recursive-fixture issue. The required full gate for
implementation `e9a8bdd` passed (exit 0): all 2,500 frozen tracked inputs were
unchanged; all 7,880 complete printed axiom reports, including all 18 new roots,
passed the unchanged whitelist. Four roots retained in the actual FMUs were
separately audited. All three FMI matrices passed 75 functions each and
526/650/526 behavior cells with zero discrepancies. Existing parser, source/C,
helper, FMI and scalar/tensor eFMI actual-artifact, native-boundary and mutation
checks passed. Evidence: `build/recursive-actions-full-gate-v1.log`, `.exit`,
`.axioms`, `-inputs.sha256`, and `build/recursive-actions-fmu-retained-v1.axioms`.
Only three evidence documents changed after the frozen gate.

Frontend cutover, grammar/source admission and emitted C are unchanged. The
later scratch GALEC table/profile compatibility and already-accepted-CST build
API are not integrated or covered by this gate. Existing standards and
numerical findings, native correspondence and MISRA closure remain open.

**Fixed-rate Euler interval preflight (full gate passed):**

Solve now specifies independent scalar and shape-indexed tensor finite prefixes
for a supplied finite increment and bounded Nat step count. Universal proofs
characterize success, absorbing rejection, exact real overflow thresholds and a
globally reachable tensor failure boundary. Tensor rank/extents remain indexed;
these proofs introduce no element enumeration in compiler lowering.

The shared C helper checks each scalar candidate immediately, copies it only
when finite and preserves the entire heap. Parameter/header conversions and
return to arbitrary saved callers are proved for finite operands and count
below 2^64. Unique terminal behavior is stated for the empty continuation,
not for later caller execution. Executable C construction is separated from
proof-only arithmetic witnesses. The fixed actual-file contract requires exact
bytes, independent token syntax, contextual execution and independent finite-
prefix/real-overflow characterizations together, using the unchanged whitelist.

Standalone staging checks passed all seven modules and 40 audit roots. Bounded
independent Astra review found no issue. The staged file adapter passed;
arithmetic/reset/guard mutants were rejected, and the existing strict native
boundary plus 15 Euler cases passed. Package integration wires the six audit
snippets, fixed checker, existing emitter and existing boundary script. Focused
owner checks passed 2,900 jobs; all 2,051 complete printed reports, including
the 40 new roots, passed the unchanged whitelist. There were no warnings in
the new modules. Evidence: `build/euler-preflight-owner-v1.log`. The required
full gate for this integrated increment passed (exit 0), with all 2,498 frozen
input hashes unchanged. All 7,862 complete printed axiom reports, all 40 new
roots, the actual-helper contract and four retained FMU roots passed the
unchanged whitelist. The integrated arithmetic/reset/guard mutations were
nonvacuous and rejected; the existing native boundary and its 15 Euler cases
passed. FMI matrices passed 75 functions each and 526/650/526 cells with zero
discrepancies; existing parser and scalar/tensor FMI/eFMI artifact, native and
mutation gates passed. Evidence: `build/euler-preflight-full-gate-v1.log`.
Only three evidence documents changed after the frozen gate.

This is a prerequisite for whole-call CS numerical Discard, not its production
invocation. The increment is not yet linked to prepared RHS or a public step
size; public clocks, tensor C composition, FMI callback behavior and GALEC
repairs remain open. The scanner certifies this fixed token profile, not all C.
Native floating-environment/compiler correspondence and MISRA conformance are
not established by these proofs or tests. No grammar or source admission changes.

**Structural EBNF bridge (full gate passed):**

Checkpoint `3f413a7` adds `Parser.LALR.EBNFStructure`: conversion of the actual
payload CST through the existing annotated lowering witness, preserving named
rules, branches, nullable repetitions and exact payloads. Universal soundness
and totality use independent EBNF derivations and preserve the actual token
parser's complete language. Both generated frontends now expose computable
runtime annotations certified equal to their proof-only witnesses. Production
frontend actions, grammars, admission and emitted C remain unchanged.

The source-symbol contract is `decode ∘ encode`; compatibility with each
frontend's independent classifier and structural AST construction remain open.
Focused owner/parser/frontend/native checks passed, with 19 new generic and
four frontend roots within the unchanged axiom whitelist. Bounded independent
Astra review found no remaining issue. The required
`nix develop .#verification --command lake test` passed (exit 0), with all
2,485 frozen input hashes unchanged. All 7,809 printed axiom reports (wrapped
lists included), all 23 new roots, the recursive fixture's two runtime-annotation
roots and four retained FMU roots passed the unchanged whitelist. The three FMI
matrices passed 75 functions each and 526/650/526 cells with zero discrepancies.
Existing parser, source/C, tensor-helper and scalar/tensor FMI/eFMI actual-artifact,
native and mutation checks passed. Evidence:
`build/ebnf-structure-full-gate-v2.log`. Existing warnings remain; no new bridge
warnings were reported. The original V1 run had no terminal success evidence
and is not counted as a pass. Only four evidence documents changed after V2's
frozen gate.

GJ01 in `dev/standards-review.md` additionally records an undeclared `jacobian`
call in emitted tensor GALEC. Internal derivative and artifact proofs do not
establish normative function lookup. Existing standards, native correspondence
and MISRA findings remain open. The user authorized repair-only GALEC grammar
changes for the existing findings, without new Modelica admission. GJ02 also
records incorrect array-dimension placement in emitted GALEC. Neither repair
nor a safety-critical claim follows from this bridge alone.

**Generic CST payload attachment (full gate passed):**

`Parser.LALR.Payloads` attaches original payloads to an existing concrete parse
tree without changing terminal order, production indices or nonterminal
identities. Universal Lean proofs establish exact erasure and payload recovery,
prefix/suffix consumption, success exactly when the encoded word agrees, and
total attachment after the actual `TokenParser.run` succeeds. Encoders need not
be injective. Grammar validity comes from the existing checked parser, not
attachment alone. The worker consumes leaves once; no machine stack or formal
complexity bound is claimed.

Focused builds passed 735 owner jobs and 795 parser-check jobs; all 260 printed
audit reports, including eight new roots, passed the unchanged whitelist.
Independent Astra review found no issue in the bounded structural contract.
The required `nix develop .#verification --command lake test` passed (exit 0,
observed 2026-09-22 at 13:22 UTC), with all 2,483 frozen input hashes unchanged.
All 7,758 printed axiom reports (wrapped lists included), all eight new roots
and four retained FMU roots passed the unchanged whitelist. The three FMI
matrices passed 75 functions each and 526/650/526 cells for Integrator,
TensorSquare and ConstantRates, with zero discrepancies. Existing LALR,
source/C, tensor-helper and scalar/tensor FMI/eFMI artifact, native and mutation
checks passed. Evidence: `build/cst-payload-full-gate-v1.log`. No new-module
warnings; existing warnings remain. Only three evidence documents changed
after the frozen gate.

Only the parser audit imports the new module. Current frontend execution,
grammars, admission, lowering and emission are unchanged. This is a prerequisite
for structural actions, not their production cutover or completed MLS/FMI/eFMI
conformance. N01, K02–K05, histories, native correspondence and MISRA closure
remain open and continue to block grammar expansion.

**Tensor FMI derivative numerical Discard (full gate passed):**

The production tensor derivative getter now runs the shared read-only product
preflight before RHS, Jacobian or caller-output writes. For finite encoded
inputs, a universal dichotomy supplies either the existing finite execution
and finite Jacobian additions, or an independent real square-overflow witness.
The latter reaches numerical `fmi3Discard` with the original heap. Disabled or
absent logging preserves that heap through return; enabled callback execution
retains every modeled foreign outcome and its explicit post-callback heap.
No callback frame or native floating-environment correspondence is assumed.
The old success theorem statements and caller-buffer aliasing premises remain.

The shared segment uses scalar locals, not tensor scratch storage. Mandatory
adapter contracts connect failure execution, prepared message storage, function
lookup and rendered code to the actual source-build checker. The existing native
matrix checks overflow, untouched state/output, logging configurations and finite
recovery; both reset and preflight mutations are rejected by that checker.
Focused owner checks passed 2,563 jobs. The required
`nix develop .#verification --command lake test` passed (exit 0), with all 2,482
frozen input hashes unchanged. All 7,750 printed axiom reports (wrapped lists
included), all 34 new roots and four retained FMU roots passed the unchanged
whitelist. All three FMI matrices passed 75 functions: TensorSquare exercised
650 cells, Integrator and ConstantRates 526 each, with zero discrepancies.
Shared-helper and scalar/tensor eFMI artifact/native/mutation checks passed.
Evidence: `build/fmi-preflight-full-gate-v2.log`. Existing warnings remain;
none occurred in the new modules. Only three evidence documents changed after
the frozen gate.

Bounded independent proof/linkage review found no issue, but did not establish
MISRA compliance. Subsequent focused Rule 10.1 review replaced integer `!valid`
with `valid == 0`; the earlier V1 gate was deliberately stopped, not passed.
Grammar and source admission are unchanged. This closes the modeled finite-input
ME getter failure path, not eFMI N01, CS Euler overflow, complete histories,
K02–K05, native correspondence or MISRA closure. Those findings still block
grammar expansion. Earlier checkpoint statements below describe their own
revisions, not the current production invocation status.

**Read-only tensor product preflight (full gate passed):**

The shared C backend now has a reusable counted-expression finiteness proof
and a multiplication preflight. Each iteration computes into one scalar local
and immediately classifies it; no tensor scratch buffer or element enumeration
is introduced. On finite input encodings, the canonical contextual C call
returns exactly Solve's encoded product classifier and preserves the entire
heap, without writable-storage or input-separation assumptions. Empty inputs
may be null. The independent finite-product domain and square specialization
give the old finite Solve execution boundary and a real overflow witness.

The fixed actual-file checker requires emitted bytes, independent token syntax,
call execution, unique behavior and those numerical characterizations together.
The existing helper integration script now checks the new file, rejects a
changed arithmetic operator and exercises native overflow/underflow, aliasing,
empty-input and byte-preservation boundaries. Owner checks passed 2,155 jobs;
all 29 printed axiom reports, including 14 new roots and the existing scanner
roots, passed the unchanged whitelist. Evidence:
`build/tensor-preflight-owner-v7.log`. The old scanner's bytes and theorem
statements are retained. Bounded independent review found no issues. The required
`nix develop .#verification --command lake test` passed (exit 0, observed
2026-09-22 at 11:09 UTC), with all 2,464 frozen input hashes unchanged. All
7,711 printed axiom reports (wrapped lists included), all 14 new roots and four
retained FMU roots passed the unchanged whitelist. All three FMI matrices passed
75 functions and 526 cells each with zero discrepancies; actual-helper mutation
rejection/native checks and scalar/tensor eFMI artifact checks passed. Evidence:
`build/tensor-preflight-full-gate-v1.log`. Only three evidence documents changed
after the frozen gate. Existing warnings remain; none occurred in the new
modules in the final owner build.

This prepares the state-preserving FMI numerical-failure path; production
methods do not yet invoke it. Source admission, grammar and public failure
policy are unchanged. Floating exception flags/traps, native correspondence,
public status/logging composition, CS Euler overflow, N01, K02–K05 and MISRA
closure remain open. No grammar expansion is authorized by this helper result.

**Total prepared tensor RHS outcomes (full gate passed):**

The prepared square RHS wrapper now has a total finite-input execution proof,
including overflowing square results. A reusable theorem handles any valid
single-product indexed Solve entry with its ordinary lowering match, parameter
bindings and nested helper call. The square specialization preserves the exact
encoded result heap, output writability and outside frame; finite execution
recovers exactly the previous finite heap, and rejection has an independent real
overflow-threshold witness. Shared storage setup is reused by both proofs.

Actual FMI source-build and eFMI Production/manifest/archive contracts now
mandate these RHS outcomes alongside every existing field. The concrete tables
discharge helper/entry lookup and field-free obligations. Canonical C calls
retain arbitrary declared objects and saved callers; the eFMI instantiation also
discharges header/runtime-table linkage. Owner/audit builds and the extended
existing native driver passed, including actual RHS overflow, aliasing of the
two input pointers, underflow, signed zero and guarded output storage.
The final owner/audit build passed 2,643 jobs; all 59 printed axiom reports,
including wrapped lists and all 24 new roots, passed the unchanged whitelist.
Bounded independent review identified a fragment-versus-file linkage clarity
issue; both outcome products now explicitly bind the complete surrounding bytes
to the same rendered function table used by the execution contract. The reviewer
confirmed resolution with no remaining findings. Owner evidence:
`build/tensor-rhs-outcomes-final-owner-v3.log`. The required
`nix develop .#verification --command lake test` passed (exit 0, observed
2026-09-22 at 10:32 UTC), with all 2,456 frozen input hashes unchanged. All
7,683 printed axiom reports (wrapped lists included), all 24 new roots and four
retained FMU roots passed the unchanged whitelist. All three FMI matrices passed
75 functions and 526 cells each with zero discrepancies; scalar/tensor eFMI
actual-byte, publication/reuse/mutation and native checks passed. Only three
evidence documents were updated after the frozen gate. Existing warnings remain;
none occurred in the new proof modules. Full evidence:
`build/tensor-rhs-outcomes-full-gate-v1.log`.

Emitted C, source admission, grammar and public failure policy are unchanged.
This proves the RHS computation needed before detection, not execution of the
scanner by FMI/eFMI methods. Nonfinite operands, CS Euler-overflow handling,
complete histories, native correspondence, N01, K02–K05 and MISRA closure remain
open. Evidence: `build/tensor-rhs-outcomes-checkpoint.md`.

**Runtime tensor finiteness scanner (full gate passed):**

The shared C backend now emits a reusable, read-only counted scanner and proves
that its returned `int32_t` flag is exactly Solve's whole-tensor encoded
finiteness classifier. The universal result includes every binary64 pattern,
all coordinates and zero-volume shapes (including a null input for an empty
tensor). Readable input storage, the 64-bit count bound, explicit header types
and the actual function definition remain premises. The canonical contextual C
machine executes the body and return conversion under arbitrary caller stacks
and declared-object contexts, preserving the entire heap. A reusable field-free
body transport theorem supports nonvoid results without a second scheduler.

The fixed actual-file checker requires exact emitted bytes, independent token
syntax, typed call execution, unique behavior and the finite-bit characterization
together. Owning-module builds, bounded independent proof review, actual-file
certification, deliberate detector mutation rejection and the extended existing
native tensor driver passed. The native checks cover signed zeros, subnormals,
finite extrema, both infinities, signed quiet-NaN payloads, failure positions,
empty/null input and unchanged guarded storage; these are host-boundary checks,
not universal native correspondence. The required
`nix develop .#verification --command lake test` passed (exit 0, observed
2026-09-22 at 09:28 UTC), with all 2,450 frozen input hashes unchanged. All
7,640 printed axiom reports (wrapped lists included), all 16 new roots and
four retained FMU roots passed the unchanged whitelist. Each FMI matrix passed
75 functions and 526 cells with zero discrepancies; scalar/tensor eFMI
actual-byte, publication/reuse/mutation and native checks passed. Evidence:
`build/tensor-finite-scan-full-gate-v1.log`. Only the three evidence documents
were updated after the frozen gate. Existing warnings remain; none occurred
in the new scanner modules.

This helper is not yet invoked by production FMI/eFMI methods. Source admission,
grammar and public failure policy are unchanged. Native `isfinite`, headers,
signaling-NaN/trap/exception behavior, all-path detection/consumer composition,
N01, K02–K05 and MISRA compliance remain open. Evidence is tracked in
`build/tensor-finite-scan-checkpoint.md`; grammar expansion remains blocked.

**Numerical classification foundation (full gate passed):**

Solve now owns rank-preserving numerical multiplication outcomes and a total
encoded finiteness detector. Its universal proofs cover every binary64 pattern,
all tensor coordinates and zero-volume shapes. For the square program, acceptance
is equivalent to existence of the old finite execution; rejection has an exact
real overflow-threshold witness. Signed zero and subnormals remain finite.
The shared C value classifier agrees with the core bit test. The mandatory
actual multiplication-helper contract now also classifies its exact final heap,
without removing any previous execution, storage, frame or source fields.

The emitted C and public status policy are unchanged: a proved classification
of stored outputs is **not an executed C detector**. N01, MISRA, public numerical
failure protocols, source histories and native correspondence remain open.
No grammar/admission expansion. Owning-module checks and bounded independent
review passed. The affected-package rebuild passed 4,289 jobs; all 5,402 printed
axiom reports (including wrapped lists) passed the unchanged whitelist and
contained all 20 new roots. Evidence: `build/numerical-detection-package-v1.log`.
The required `nix develop .#verification --command lake test` passed (exit 0,
observed 2026-09-22 at 08:39 UTC), with all 2,444 input hashes unchanged. All
7,608 printed axiom reports, including wrapped lists and all 20 new roots,
and four retained FMU roots passed the unchanged whitelist. All three FMI
matrices passed 75 functions and 526 cells each with zero discrepancies;
scalar/tensor eFMI actual-byte, reuse/mutation and native checks passed.
Evidence: `build/numerical-detection-full-gate-v1.log` and
`build/numerical-detection-checkpoint.md`. Only the three evidence documents
were updated after the frozen gate; existing warnings remain. See
`dev/numerical-outcomes-review.md` for the detection closure requirements.

**Finite-input multiplication outcomes (full gate passed):**

`Binary64.MultipliesResult` independently specifies finite or signed-infinite
nearest/even products. Its unique implementation `mulResult` is exactly
equivalent to the previous guarded multiplication on every finite result,
including signed zero and gradual underflow. The shared C `floatMul` now uses
this result instead of getting stuck on finite-input overflow; all existing
finite theorem statements remain. Nonfinite operands are still unsupported.

The tensor multiplication proof uses the existing typed `ArrayStore` through
a rank-preserving encoded view and counted writer. The old finite tensor and
diagonal heaps are exact specializations. Total helper execution, output reads,
independent numerical results and outside frame share one heap, with the same
storage, separation, size and header/function premises. FMI source-build and
eFMI production/manifest/archive contracts now require these outcomes and the
same actual numerical text. No emitted C, source grammar or admission changes.

Core/helper compilation, focused independent review and native helper rehearsals
passed. The complete affected package rebuild then passed all 4,286 jobs, with
all 32 new roots and all 5,382 printed axiom reports (wrapped lists included)
passing the unchanged whitelist. No warnings occurred in the new proof modules;
existing warnings remain. Evidence: `build/multiplication-outcomes-package-v1.log`
and `build/multiplication-outcomes-checkpoint.md`. The required
`nix develop .#verification --command lake test` then passed (exit 0, observed
2026-09-22 at 07:09 UTC), with all 2,440 input fingerprints unchanged. All 32
new roots, all 7,583 printed axiom reports and four retained FMU roots passed
the unchanged whitelist, with wrapped reports included. Each FMI matrix passed
75 functions and 526 cells with zero discrepancies; scalar/tensor eFMI actual-byte,
reuse/mutation and native checks passed, including signed multiplication overflow,
underflow, subnormals and zero signs. The final log is
`build/multiplication-outcomes-full-gate-v1.log`. Only the three evidence documents
were updated after this frozen gate.
This does not establish complete source RHS/public DoStep overflow,
source trajectories, nonfinite-input arithmetic, exception flags/traps, native
correspondence or MISRA compliance. K02–K05 and grammar-expansion gates remain.

**Encoded Jacobian overflow outcomes (full gate passed):**

The unchanged scratch-free square-Jacobian helper now has a total encoded-result
proof for arbitrary finite inputs, including positive/negative infinity when
doubling overflows. Its generic bit-preserving diagonal storage view specializes
exactly to the old finite heap. Execution, matrix reads and the outside frame
share one final heap; shape bounds, disjoint input/output storage and explicit
header/function bindings remain. The independent `Binary64.Adds` relation fixes
rounding, signed zero and both overflow signs. No NaN result arises from finite
inputs. The FMI source-build and eFMI production/manifest/archive products now
mandate these helper outcomes and the same actual numerical C text; all old
fields and finite source/public-method theorems remain unchanged.

Owning-package checks passed in `build/jacobian-overflow-package-v1.log` (3,675
jobs), with 24 new audited roots. The extended existing native boundary driver
passed on a fresh extraction of the retained production archive, including both
overflow signs and adjacent finite/overflow inputs. Focused independent review
found no issues. The required `nix develop .#verification --command lake test`
then passed (exit 0, observed 2026-09-22 at 05:41 UTC), with all 2,429 input
fingerprints unchanged. All 24 new roots, all 7,530 printed axiom reports
(including wrapped lists) and four retained FMU roots passed the unchanged
whitelist. Each FMI matrix passed 75 functions and 526 cells with zero
discrepancies; eFMI actual-byte/reuse/mutation checks and the extended native
overflow boundary passed. Evidence: `build/jacobian-overflow-full-gate-v1.log`
and `build/jacobian-overflow-checkpoint.md`. Only the three evidence documents
were updated after the gate; existing warnings remain. This does not prove
overflowing source RHS or public DoStep behavior, nonfinite-input
arithmetic, exception flags/traps, native correspondence or MISRA compliance.
No grammar, admission, emitter or solver changes; expansion stays frozen.

**Finite-square Jacobian domain (full gate passed):**

The universal binary64 proof `ADExact.finite_square_doubling` establishes that
a finite square implies finite doubling. The ordered square forward-AD program
therefore needs no additional addition-domain assumption. Its canonical result
preserves exact encodings, including signed zero; the unused primal square is
still checked. `TensorExecutedProductionContract.finiteSourceDoStep` now requires
source-bound public DoStep execution from finite RHS execution alone, retaining
source/Jacobian observations, actual C bytes and one common final heap. All old
contract fields remain. The fixed production/manifest/archive checkers require
the strengthened product, not a separate optional certificate.

Owning-package checks passed in `build/finite-square-package-v1.log`, and a
focused independent review found no issues. The required
`nix develop .#verification --command lake test` passed (exit 0, observed
2026-09-22 at 04:49 UTC), with all 2,423 input fingerprints unchanged. All seven
new roots were present; all 7,378 printed axiom reports and four retained FMU
roots passed the unchanged whitelist. The three FMI matrices each passed all
75 functions and 526 cells with zero discrepancies; eFMI actual-byte, reuse,
mutation and native finite/signed-zero checks passed. Existing warnings remain.
Evidence: `build/finite-square-full-gate-v1.log` and
`build/finite-square-checkpoint.md`. Only these evidence documents were updated
after the gate. No source case, grammar, emission, solver or boundary suite
changes. Square overflow, complete histories, native correspondence, MISRA and
K02–K05 remain open; grammar stays frozen.

**Canonical tensor execution (full artifact gate passed):**

Shared C now has one context-parameterized expression evaluator and scheduler
path; legacy APIs instantiate its empty-context wrapper. Declared record/array
metadata supplies the public tensor method context. The tensor eFMI contracts
compose Startup, Recalibrate and DoStep with prepared Solve execution and exact
forward-AD/Jacobian observations on the same final heap and actual byte witness.
Existing contracts, allocated storage, finite RHS/addition and external-call
premises remain explicit. This is not arbitrary numerical-outcome coverage,
complete source histories, a native compiler proof, or MISRA conformance.

The complete affected consumer closure passed in the isolated candidate, including
all 267 final FMI/compiler owners and their 896 original audit roots. Package-local
checks now retain the new roots, quotation diagnostics and two universal
counterexamples distinguishing ledger alignment from freshness and equality guards
from range checks. Five introductory comments were corrected without changing
contracts. The existing eFMI integration suite now also executes the public tensor
methods from the actual extracted C archive member; this tests host behavior only.

The reviewed source candidate and prior actual tensor archive certificate are
recorded in /tmp/rumoca-canonical-executed.i68EWO/CONSUMER-CLOSURE.md and EXECUTED.md.
The required `nix develop .#verification --command lake test` passed (exit 0,
observed 2026-09-22 at 04:13:55 UTC), with all 331 gate-input fingerprints unchanged.
All 462 new package roots were present; all 7,477 printed axiom reports and the
four retained FMU source/C/build roots passed the unchanged whitelist. All three
FMI matrices passed 75/75 functions and 526 cells, with zero recorded-finding
discrepancies or unexpected results. Scalar/tensor eFMI publication, actual-file,
reuse and mutation checks passed, including native tensor Startup/Recalibrate/
DoStep finite and signed-zero checks. Existing warnings remain. Evidence is in
build/canonical-context-full-gate-v1.log and build/canonical-context-integration.md.
Only documentation status updates followed the gate; implementation inputs remain
identical. This validates the increment, not full standards conformance.
No new source case, grammar, emitted C or solver policy is added. K02–K05,
full numerical/source-history obligations, native correspondence and MISRA remain
open; grammar expansion stays blocked.

**Numerical tree linkage and concrete accepted execution (full gate passed):**

The 79-file numerical-linkage increment is promoted. Core owns the prepared
square IVP; shared C owns its indexed plans and exact ordered function table,
with test modules reduced to consumers. Canonical numerical proofs require only
operations present in the indexed programs. Legacy theorem statements and all
earlier contract fields remain.

The mandatory tensor source-build product now identifies the compiled Solve IVP
and independently read numerical bytes with that table. One adapter signature
witness per static-literal environment owns the rendered adapter, prepared
rejections, numerical extension and accepted execution. Accepted calls discharge
internal lookup/library and reachable helper-resolution premises, retaining the
previous storage, alias, lifecycle, external-math and finite-arithmetic inputs
and all observations on the same final heap.

The FMI dictionary now includes the emitted double-pointer spellings. Actual
runtime header facts and their source-product instantiation passed the coherent
package rebuild: all 4,163 jobs, all 150 new audit roots, and 4,857 printed axiom
lists using only permitted axioms. The first build failed at an implicit event
type in the runtime wrapper; explicitly introducing that universally quantified
type repaired the proof without changing its statement. Logs are
build/numerical-linkage-package.log and build/numerical-linkage-package-repair.log.
The required full artifact gate passed (exit 0, observed 2026-09-21 at 22:12 UTC)
in build/numerical-linkage-full-gate.log with unchanged implementation inputs.
All 150 new roots were present; all 6,753 printed axiom lists and four retained
FMU source/C/build audit roots use only permitted axioms. All three FMI matrices
passed 75/75 functions and 526 cells with zero discrepancies. Scalar/tensor eFMI
publication, actual-artifact, reuse and mutation checks passed. Scalar eFMI
includes native driver execution; the tensor eFMI native boundary here is C
compilation, not execution of its complete public methods. Existing warnings remain.
Evidence is in build/numerical-linkage-checkpoint.md; provenance is recorded in
/tmp/rumoca-numerical-promotion.KRyn7b/README.md. No grammar, emitted C, solver
policy or boundary suite changed. Full numerical outcomes, source histories,
native correspondence, MISRA and K02–K05 remain open.

**Prepared step composition and accepted observations (full gate passed):**

Both tensor and constant adapter contracts now require successful literal-pool
preparation and six prepared logged rejection paths. The actual-byte certifiers
derive pool readiness from the same kernel-checked function trees used for the
rendered adapter. The call proofs derive diagnostic/category addresses and exact
stored C-string contents at callback entry, retaining arbitrary represented
callback effects and the no-outcome case. Installation freshness, the initial
read-only frame and runtime linkage remain explicit; no native or post-callback
storage guarantee follows from pool construction alone.

The existing accepted execution products additionally require
`StepEntry.SuccessState` on the same final-heap witness: the three output flags
are false and the selected instance's mode cell is unchanged. The canonical
loop/solve/call proofs retain their residual frames to derive these observations.
All earlier premises and state/time/last-time/other-instance/execution conclusions
remain, including Boolean-buffer aliasing and conditional finite arithmetic.
The lifecycle-history consumer retains its previous statement.

Independent review and isolated owner compilation passed; 58 selected roots
(39 new, with strengthened and retained roots) use only permitted axioms.
Prepared-adapter byte-certifier rehearsals passed before the accepted-observation
addition. Those rehearsals do not certify the integrated source build. Owning
package checks passed all 4,055 jobs (exit 0) in
`build/step-composition-package-v3.log`; all 39 new roots were present and all
4,215 printed axiom lists used only permitted axioms. Existing profile warnings
remain. The required full gate passed (exit 0, observed 2026-09-21 at 20:47:09 UTC)
in `build/step-composition-full-gate-v3.log`, with unchanged implementation inputs.
All three FMI matrices passed 75/75 functions and 526 cells with zero discrepancies;
scalar/tensor eFMI artifact and mutation checks passed. All 6,525 printed axiom
lists and four retained FMU audit roots use only permitted axioms. Evidence is in
`build/step-composition-checkpoint-v3.md`.
The numerical checkpoint below predates this increment. No grammar, emitted C,
solver policy or boundary suite changed.
Actual numerical-kernel/program linkage, finite-arithmetic outcomes, complete
source histories, native correspondence, MISRA and K02–K05 remain open.

At that checkpoint, the linkage review found a concrete premise gap: `FMI3.cTypes`
did not bind the emitted helper spellings `double *` and `const double *`.
Lean diagnostics prove that `CTensor.HeaderTypes`, and hence the full numerical
`Library` premise, could not be instantiated in that standard tensor fenv
interface. This limits applicability of its conditional accepted-execution
products; it is not a native-execution failure or a defect in the implication
proofs. Repairing those bindings, restricting binary-helper requirements to
actual instructions, and requiring the actual tree-backed table/source-IVP
linkage are one pending increment. Diagnostic evidence is in
`build/kernel-header-gap-diagnostic.log`; no repair or full-gate validation of
the promoted next increment is claimed by this historical checkpoint.

**Step numerical rejection (full gate passed):**

Both tensor and constant step contracts now additionally require
`roundingRejected`, `stopRejected` and `discardRejected`. Shared actual-function
prefix theorems derive the guard paths from syntax, without a solver-execution
premise. Each contract covers suppressed, enabled and missing-callback logging
under arbitrary checked error contexts. Rounding and stop errors initialize the
outputs and then terminate the instance before invoking the callback. Discard
covers both a nonprogressing/nonfinite next clock and an off-grid/over-bound
duration after the earlier stop guard is admitted; it does not write the mode.
Floor bindings are required only on the progressing-clock branch. Logged cases
retain arbitrary represented callback events/heaps and the no-outcome case.

All earlier contract fields and audit roots remain. The 22 new roots passed
scratch owner/profile rehearsals and the integrated owning-package check passed
all 3,795 jobs (exit 0) in `build/step-numeric-contract-package.log`. The new
shared proof modules produced no warnings; existing profile warnings remain.
Independent review confirmed mandatory propagation through both adapter and
fixed actual-source-build contracts. The required full gate passed on
2026-09-21 (exit 0, observed 19:22:37 UTC) in
`build/step-numeric-contract-full-gate.log`, with unchanged implementation
fingerprints. All three production FMI matrices passed 75/75 functions and 526
cells with zero discrepancies; scalar/tensor eFMI actual-artifact and mutation
checks passed. The four retained FMU source/C/build audit records and all 6,485
printed axiom lists use only the permitted axioms. Evidence and artifact hashes
are in `build/step-numeric-contract-checkpoint.md`. The argument-rejection
checkpoint below predates these fields.
No grammar, emitter, numerical semantics or boundary-suite change is included.
Prepared literals, actual kernel/event-program linkage, accepted output/mode
frames, finite-arithmetic coverage and complete source histories remain open.
K02–K05, native correspondence and MISRA still block grammar expansion.

**Step argument rejection (full gate passed):**

The tensor and constant step contracts now require `inputRejected` and
`outputsRejected`. Each product has silent, logged and missing-logger cases
under arbitrary checked error contexts. Missing outputs reach failure before
clock or buffer access; invalid raw point/step arguments first initialize the
outputs, then terminate the instance. Callbacks receive that exact heap and
retain every represented event/outcome and the no-outcome `.wrong []` case.
Missing logging needs no logging-flag or callback-environment cell.

Shared finite-prefix and guard theorems supply both profiles; the existing
scalar prefix statements are preserved and their proof bodies now use the same
mechanisms. No grammar, emitter, numerical semantics or boundary suite changes
in this increment. Draft checks and independent semantic review passed before
promotion; owning-package validation passed all 4,045 jobs in
`build/step-argument-contract-package.log` (exit 0), including the 21 added audit
roots and retained roots. No warnings were reported from the changed shared
prefix/error modules. The required full gate passed on 2026-09-21 (exit 0) in
`build/step-argument-contract-full-gate.log`, with unchanged implementation
fingerprints. All three production FMI matrices passed 75/75 functions and 526
cells with zero discrepancies; scalar/tensor eFMI actual-artifact and mutation
checks passed. Retained FMU source-build audits use only the three permitted
axioms. Evidence and artifact hashes are in
`build/step-argument-contract-checkpoint.md`.
The lifecycle/logger full-gate pass
below predates these new mandatory fields and is not their artifact validation.
Prepared-literal and pointer-emission repair drafts remain outside production.
Full step coverage, native correspondence, MISRA and K02–K05 remain open.

**Tensor and constant step lifecycle rejection (full gate passed):**

The mandatory `TensorDoStep.Contract` and `ConstantDoStep.Contract` now include
disallowed-state rejection with logging suppressed and enabled. Their universal
whole-call proofs instantiate `GuardedCalls`: suppressed logging returns
`fmi3Error` and writes only the selected instance's terminated mode; enabled
logging passes that updated heap to the actual failure callback and retains its
events and heap effects. Absence of a represented callback outcome is exposed as
`.wrong []`. Caller output buffers need no validity premise on these paths,
because the lifecycle guard runs before their access.

The existing adapter contracts include these strengthened products, and the fixed
tensor/constant source-build checkers require them for the actual adapter bytes.
Shapes, instance kinds/modes, argument bits, heaps and callback outcomes remain
universally quantified. The original accepted, null and discard fields remain.
The initial proof-only targeted tensor and constant audits passed
(`build/tensor-lifecycle-package.log`, `build/constant-lifecycle-package.log`).
The preliminary required full gate in `build/step-lifecycle-full-gate.log` was
deliberately stopped (exit 143) to integrate review follow-ups; it is partial
evidence, not a full-gate pass. The combined change explicitly compares the
logger with a null pointer before testing the logging flag. Shared C lemmas
preserve short-circuit evaluation, including an unevaluated right operand.
Missing-callback rejection is mandatory even without a valid logging-flag cell.
The adapter contracts bind the step and failure-helper definitions, and the
rendered step fragment, to the same signature list. The compiler certificates
check exact step-signature membership with a kernel-checked structural proof. Literal bindings and
external callback assumptions remain explicit. Instantiating the step theorem
still requires linking the event program to that certified definition table.
The combined targeted checks
passed (`build/logger-null-integration.log`, `build/logger-contract-package-v2.log`),
including the strengthened contract audits and compiler certificate modules.
The existing native FMI matrix now includes missing-callback lifecycle rejection
with null output pointers for both interfaces and logging settings. A fresh full
artifact gate in `build/logger-contract-full-gate.log` failed at the tensor FMI
certificate: the generated membership tactic attempted `decide` without a
decidable-equality instance for signatures. The axiom audit rejected the failed
elaboration. The tactic now uses the scalar certificate's structural proof.
The repaired tensor and constant actual-artifact checks passed and produced
`build/tensor-fmi/logger-repair.fmu` and `constant-logger-repair.fmu`; each retained
source-build audit contains only the three permitted axioms. Each existing native
matrix passed all 75 functions and 526 behavior cells with zero discrepancies
(`build/logger-tensor-native-matrix.log`, `build/logger-constant-native-matrix.log`).
The required `nix develop .#verification --command lake test` passed on
2026-09-21 (exit 0; `build/logger-contract-full-gate-v2.log`). The implementation
diff fingerprint stayed unchanged throughout that run. All three production FMI
matrices passed 75/75 functions and 526 cells with zero discrepancies; the retained
source-build audits use only the three permitted axioms. Scalar and tensor eFMI
publication, actual-file, archive and mutation checks also passed. Existing
warnings remain, but none were reported on this increment's changed Lean lines.
The earlier failed run remains retained. K02–K05,
remaining argument/numeric rejections, native correspondence and MISRA findings
continue to block grammar expansion.

**Initialization from checked controls (full gate passed):**

The private interference frame now follows from current C destinations on the
same coupled history. Permissions distinguish caller objects outside the pool,
the executing invocation's borrowed record, and its own private reservation.
Invocation identity derives separation from every other private initializer,
including nested members and tensor offsets. Intermediate activity and private
reservation retention follow from the ledger and actual history.

Actual initializer controls establish their write destinations and exclude new
foreign calls. Atomic exchange and clear frames follow from their modeled
prototype conversions and one-cell updates. Actual public entry preserves all
current control permissions: the new internal call has no write or foreign
effect, and entering one resource cannot revoke another active borrow. Observing
a real return also preserves the remaining controls: only that original
invocation can return its borrow; successful publication cannot overwrite an
occupied resource; another call cannot publish a retained private reservation.

The source theorem retains the actual source/C/adapter/metadata/program and
earlier release, initialization and resource-history contracts. Its additional
controlled-initialization contract derives the private frame, initialized
record, returned handle and current publication from that same prefix. It does
not replace the existing general initialization contract or narrow production
source acceptance. Current foreign effects and importer-memory ownership remain
explicit; complete method control invariants and caller-buffer validity still
need to establish those permissions throughout every public lifecycle.

The owning-package checks passed at 03:38:56 UTC on 2026-09-16.
The required `nix develop .#verification --command lake test` passed at
04:26:45 UTC on 2026-09-16, with 1267 unchanged inputs and all
577 selected roots (29 new, 548 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft, dependency-isolation and semantic-review evidence is in
`build/c-private-retention/`: `completion-controls-v3.json`,
`controls-promotion-v3.json`, `controls-review-v3.md`,
`controls-extracted-v3.json`, `controls-extracted-fmi-v3.json` and
`controls-extracted-c-v2.json`. Integration, package, full-gate,
standards/upstream review and retained artifacts are under
`build/c-controlled-initialization/`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. Full public-control/lifecycle admission, importer and
callback effects, caller-buffer validity, native C11/static layout/ABI/fenv,
provenance, transitive allocation, MISRA and existing MLS/FMI/eFMI findings remain
open. K02–K05 still block grammar expansion and a complete assurance claim.

**Private reservation retention and initialization (full gate passed):**

A still-active original invocation now retains its private reservation through
the coupled history. Claims preserve occupied slots; release authority cannot
clear a private slot; another completion cannot publish it under the original
serial. The ledger derives intermediate descriptor retention even with thread
reuse. Starting from claimed-initializer control and the initial private entry,
the same framed history derives the final reservation, initialized record,
returned handle and current importer resource. These facts discharge this
factory completion's publication boundary. Its completion is outside the
prefix, so the proof does not assume the result it establishes. The source
theorem retains the actual C/adapter/metadata/program and preceding contracts.

The C write footprint now covers every supported internal transition, including
loop bodies, indirect call entry and saved return assignments. It resolves the
current destination without evaluating the RHS or enumerating tensor elements.
Actual execution preserves every other cell. Current resource authority then
derives separation from private initializer records, including nested members
and tensor offsets. Eventful and concurrent frames use the current shared heap;
foreign effects remain explicit. Complete method destination confinement and
caller-buffer separation are still needed to discharge the initialization
theorem's private interference premise for the whole public protocol.

The owning-package checks passed at 02:47:13 UTC on 2026-09-16.
The required `nix develop .#verification --command lake test` passed at
03:34:37 UTC on 2026-09-16, with 1260 unchanged inputs and all
548 selected roots (26 new, 522 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft, dependency-isolation and semantic-review evidence is in
`build/c-resource-histories/`: `source-retention-v2.json`,
`retention-promotion-v2.json`, `retention-review-v1.md`,
`retention-extracted-v1.json`, `retention-extracted-fmi-v1.json`,
`retention-c-reuse-v1.json`, `owned-write-frame-v1.json`,
`writes-extracted-v1.json`, `writes-c-reuse-v1.json` and `writes-review-v1.md`.
Integration, package, full-gate, standards/upstream review and retained
artifacts are under `build/c-private-retention/`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. Starting typed storage, complete admitted public
histories, destination/buffer/callback confinement, native C11/static
initialization/ABI/fenv correspondence, provenance, transitive allocation,
MISRA and existing MLS/FMI/eFMI findings remain open. K02–K05 still block grammar
expansion and a complete assurance claim.

**Resource origins and release histories (full gate passed):**

Resource updates now follow actual recorded C/host actions. The original ledger
computes fresh invocation identities, and each ordinary-use or release ticket
retains its exact public API and original instance argument. Ordinary completion
returns only its own resource. The actual captured clear consumes the release
resource; a history theorem proves that subsequent calls, thread reuse and slot
reuse cannot recreate the retired ticket. Its delayed void completion leaves
the current resource map, publication map and heap unchanged.

One coupled history projects to the same resource and computed publication
histories. Every later resource link and API origin follows from the initial
invariant. Starting with an empty host ledger, each usable handle has an actual
observed factory return with that slot and original serial. A successful factory
observation must still retain its private reservation; this boundary remains
explicit. The source theorem uses the same checked source, numerical C, adapter,
metadata and logged program, retaining its captured-release contract.

The owning-package checks passed at 01:57:44 UTC on 2026-09-16.
The required `nix develop .#verification --command lake test` passed at
02:44:19 UTC on 2026-09-16, with 1252 unchanged inputs and all
522 selected roots (57 new, 465 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft, dependency-isolation and semantic-review evidence is in
`build/c-instance-authority/`: `source-resources-v2.json`,
`resource-promotion-v2.json`, `resource-review-v2.md`,
`resource-extracted-v2.json`, `resource-extracted-fmi-v2.json` and
`resource-c-reuse-v2.json`. Integration, package, full-gate, standards/upstream
review and retained artifacts are under `build/c-resource-histories/`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. Complete public-call/lifecycle admission, private-value,
buffer/saved-destination and callback frames, private-reservation retention,
native C11/static initialization/ABI/fenv correspondence, provenance, transitive
allocation, MISRA and the existing MLS/FMI/eFMI findings remain open. Logical
resources are a verification design, not native generation tags. K02–K05 still
block grammar expansion and a complete assurance claim.

**Current handle authority and captured release (full gate passed):**

Logical handles retain the original observed factory serial and bounded slot;
the emitted C pointer is unchanged. Resource borrowing excludes overlapping
use of one instance and rejects stale generations, while other slots remain
independent. Actual successful initialization and factory completion issue the
resource for that initialized record; an unpublished reservation has no client
authority. Actual public release entry uses the invocation ledger's next serial.

Current releasing authority supplies the unchanged lease-checked release rule.
The actual atomic clear consumes that resource and reservation together, updates
computed publication, and leaves a heap-independent void-return suffix. A
reusable current-control footprint theorem preserves the original invocation
through host histories. Its release instantiation protects metadata only until
operand capture; later atomic/return states have an empty footprint. The actual
entry and history derive the pending clear arguments and saved continuation.

The source theorem binds this release contract to the actual numerical C,
adapter, metadata, literal preparation and logged runtime. Current resource
retention, flag representation and the prefix interference frame remain legal
caller obligations. The theorem does not infer authority from pointer bits or
claim arbitrary raw importer histories are valid.

The owning-package checks passed at 01:07:23 UTC on 2026-09-16.
The required `nix develop .#verification --command lake test` passed at
01:55:22 UTC on 2026-09-16, with 1238 unchanged inputs and all
465 selected roots (34 new, 431 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft, dependency-isolation and semantic-review evidence is in
`build/c-publication-history/`: `source-authority-v1.json`,
`authority-promotion-v2.json`, `authority-review-v2.md`,
`authority-extracted-v2.json`, `authority-extracted-fmi-v2.json` and
`authority-c-reuse-v2.json`. Integration, package, full-gate, standards review
and retained artifacts are under `build/c-instance-authority/`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. Complete caller/resource histories, private-value and
buffer/callback frames, native C11/static initialization/ABI/fenv correspondence,
provenance, transitive allocation, MISRA and remaining MLS/FMI/eFMI findings
stay open. K02–K05 still block grammar growth and a complete assurance claim.

**Computed publication and release completion (full gate passed):**

Publication now extends the same actual reservation history with computed
private/published phases. Claims, clears, observed returns, bounded addresses
and original invocation serials determine the transitions. Its projection
preserves the exact physical leases and flag representation. Every current
publication has an actual matching factory-completion event. Forward transition
proofs also show that matching completion really publishes.

The source theorem retains the actual C/adapter/metadata and prepared-runtime
contracts. The initialization bridge proves that the same actual completion
returns the initialized record and publishes its retained reservation. Typed
initial storage, private-record interference and retention remain explicit
premises for the complete legal lifetime protocol to establish. Observation
does not establish a caller's authority to use or release the handle.

A further source theorem starts from the authored static declaration
initialization and derives writable storage at every reached reservation.
Callbacks and host memory actions must preserve object descriptors; numerical
values remain mutable. The original heap must provide fresh static blocks.
No reached writable-pool premise or successful initializer run is supplied.
A combined source theorem connects static storage, the exact physical and
publication histories, and successful initialization under one program and
invocation ledger. Native static initialization remains a separate
correspondence obligation.

After the emitted release's real atomic clear, its remaining instructions are
enabled, silent, preserve the entire current heap and decrease an own-step
count. The generic suffix remains valid under admitted interference without
a metadata frame. Its original invocation returns void even if another factory
has reused the storage. That delayed completion cannot alter publication of a
new lease. Existing lease-checked release rules are unchanged.

The owning-package checks passed at 00:17:00 UTC on 2026-09-16.
The required `nix develop .#verification --command lake test` passed at
01:05:09 UTC on 2026-09-16, with 1230 unchanged inputs and all
431 selected roots (49 new, 382 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft and dependency-isolation evidence is in `build/c-private-initialization/`:
`initialized-publication-v3.json`, `release-tail-v2.json`,
`source-static-initialization-v1.json`, `source-creation-histories-v1.json`, `publication-promotion-v3.json`,
`publication-review-v3.md`, `publication-c-reuse-v2.json` and
`publication-extracted-fmi-v2.json`, `publication-extracted-all-v3.json` and
`publication-dependency-reuse-v3.json`. Integration, package, full-gate,
standards/upstream review and retained artifact records are under
`build/c-publication-history/`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. The complete legal host/callback/buffer protocol,
current lifetime authority, native C11/static initialization/ABI, fenv,
provenance, transitive allocation, MISRA and remaining MLS/FMI/eFMI findings
stay open. K02–K05 still block grammar expansion and a complete assurance claim.

**Concurrent initialization through host observation (full gate passed):**

The source-bound theorem now connects the checked source, numerical C,
prepared runtime and actual public history to successful reservation,
initialization and host-observed return. The raw history derives the original
factory arguments and saved caller. Its actual exchange supplies the index,
observation, event, new heap and successful continuation. The real helper
return, capacity guard and instance selection derive initializer entry.

The initializer runs its emitted metadata, prepared Solve state, clock,
lifecycle and callback stores. A reference execution stays related to the
current heap only on its private record. Its actual internal steps are enabled,
silent, preserve the exterior and reduce a control-derived remaining-step
count. Zero means actual root halting. The returned handle, initialized values,
writable storage and slot metadata are proved at host-observed completion.
Scheduler fairness is not asserted.

Shared-history invariants use the current heap and original invocation serial.
Thread reuse cannot reuse that identity. A distinct initializer's actual C
steps preserve every member of this record, without enumerating array elements.
The complete successful factory continuation derives its exterior frame,
including helper return, guard and selection; the successful scan preserves
the whole shared heap.

Typed pool storage at the reached exchange and private-record interference
remain explicit premises. The complete legal host/callback/buffer protocol must
establish them and connect actual completion to live-handle authority and
authorized release. The physical reservation registry remains a separate
proved component; pointer bits or a busy flag do not establish caller authority.
The source theorem does not yet combine these into one complete lifetime rule.

The owning-package checks passed at 23:23:46 UTC on 2026-09-15.
The required `nix develop .#verification --command lake test` passed at
00:13:37 UTC on 2026-09-16, with 1217 unchanged inputs and all
382 selected roots (33 new, 349 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft and dependency-isolation evidence is in `build/c-reservation-registry/`:
`source-initialization-v3.json`, `initialization-promotion-v2.json`,
`initialization-review-v2.md` and
`initialization-extracted-c-v1.json` plus
`initialization-extracted-{fmi,all}-v2.json`. Integration, package, full-gate,
standards/upstream review and retained artifact records are under
`build/c-private-initialization/`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. Native static initialization/C11/ABI, callback/fenv
correspondence, provenance, transitive allocation, MISRA and remaining
MLS/FMI/eFMI findings stay open. K02–K05 continue to block grammar growth and
a complete assurance claim.

**Computed reservation histories through actual claims (full gate passed):**

The source-bound theorem now derives current reservation/flag representation
from the typed C pool's initially free flags and the raw public host history.
Actual selected controls, operands and recorded invocations compute each
registry update. Successful exchanges record the enclosing factory's serial;
busy exchanges retain the previous reservation. Actual false stores clear only
the addressed slot, leaving this pool unchanged when the address is outside it.
No next-map, owner, observation or per-step atomic annotation is supplied.

Invocation replay proves that recordings of the same raw actions have the same
ledger. The same derived registry therefore supplies actual factory claims,
original arguments, bounded indices and saved continuations. Successful claims
exclude any later reservation by that invocation, including after helper return
and across thread reuse. Event tags need not be injective.

The actual generated program proves clear-call operands and ordinary flag
frames. Importer memory and logger effects must preserve atomic cells; these
are explicit foreign-boundary contracts. Original factory inputs must satisfy
the represented ABI profile. Neither valid identity strings nor supported CS
requests are required; rejection paths remain covered.

Additional C proofs use mathlib's `Set.EqOn` to transport actual typed stores
and assignments across interference outside their symbolic address region.
They preserve values, not merely cell types and permissions, and retain the
other heap's exterior. Conservative operand certificates cover the body and
loop evaluators. Every actual initializer store, including slot metadata and
nested Solve state, satisfies the selected-record footprint. These lemmas
supply the memory component; complete concurrent initialization remains open.
The combined checked draft is `build/c-factory-history/initialization-footprint-v1.json`.

This is a physical reservation registry. It records a clear even when the
caller lacks release authority. The existing lease-checked release semantics
are unchanged. Private initialization, actual handle publication, legal later
metadata/buffer and release authority, and stale/reused handle safety remain
open. A reservation or pointer alone is not published live-instance authority.

The owning-package checks passed at 22:33:31 UTC on 2026-09-15.
The required `nix develop .#verification --command lake test` passed at
23:21:32 UTC on 2026-09-15, with 1204 unchanged inputs and all
349 selected roots (39 new, 310 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft and dependency-isolation evidence is in `build/c-factory-history/`:
`source-registry-v4.json`, `initialization-footprint-v1.json`,
`registry-promotion-v2.json`, `registry-review-v2.md` and
`registry-extracted-{c,fmi,all}-v2.json`. Integration, package, full-gate,
standards/upstream review and retained artifact records are under
`build/c-reservation-registry/`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. The initial flags belong to the authored typed C
semantics; native static initialization/C11/ABI, callback/fenv correspondence,
provenance, transitive allocation, MISRA and remaining MLS/FMI/eFMI findings stay
open. K02–K05 continue to block grammar growth and a complete assurance claim.

**Public factory histories through slot claims (full gate passed):**

The source-bound claim theorem now starts with the raw public host history.
It derives the original ME/CS factory arguments, the exact saved reservation
continuation, the prepared flag-array pointer and the bounded exchange index.
It no longer requires a separately supplied helper-entry interval. That same
actual C step supplies its event, observation, recorded invocation and slot
ownership transition. A successful helper continuation remains silent and
returns the selected index. The same factory invocation cannot reserve again
anywhere in its remaining host history, including after the helper returns.
Later calls on a reused thread receive new invocation identities.

The factory control proof covers supported and rejected CS requests, both
identity outcomes, optional rejection logging, reservation, and the closed
post-scan suffix. An unconditional return makes rejected creation code
unreachable. Generic context lemmas preserve the literal saved caller and
exclude premature local halting. Host histories include other invocations,
completions and admitted heap changes, as well as C execution.

The original factory call must satisfy the represented ABI argument profile
(`AdmitsFactories`). It need not contain valid identity strings or request
supported CS capabilities. Current owner/flag representation remains an
explicit heap premise. Ownership at the successful atomic result does not
establish its preservation under arbitrary later changes. Concurrent private
initialization, actual live-handle publication and subsequent legal lifetime,
metadata/buffer and release authority remain open.

The owning-package checks passed at 21:40:48 UTC on 2026-09-15.
The required `nix develop .#verification --command lake test` passed at
22:31:16 UTC on 2026-09-15, with 1192 unchanged inputs and all
310 selected roots (30 new, 280 retained). No unexpected axioms, changed-module
warnings or source drift were found. Root counts do not measure semantic
coverage; all previously selected roots remain in the same three audits.

Draft and dependency-isolation evidence is in `build/c-scan-context/`:
`factory-history-promotion-v3.json`, `factory-history-review-v2.md`,
`fmi3-factory-once-v1.json` and `factory-extracted-{c,fmi,all}-v3.json`.
Integration, package, full-gate, standards/upstream review and retained artifact
records are under `build/c-factory-history/`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

No grammar, source/IR semantics, C emission, solver or interface policy changed;
no test suite was added. Native C11/ABI, callback/fenv correspondence, provenance,
transitive allocation, MISRA and remaining MLS/FMI/eFMI findings stay open.
K02–K05 continue to block grammar growth and a complete assurance claim.

**Slot claims and suspended callers (full gate passed):**

Actual reservation uses the computed enclosing factory invocation serial as
its slot lease and as the origin of the same recorded C step. Starting at the
real helper entry, its atomic operation supplies the bounded slot, observation
and ownership transition. On success, subsequent helper steps are silent,
schedule no further calls and return that index under finite interleavings.
The actual factory suffix cannot reserve again after the helper returns,
including its exhaustion branch. Source theorems retain the same actual pool,
header, table, numerical C, adapter and metadata contracts.

Generic continuation proofs give exact C step correspondence in both directions
beneath a suspended caller, preserving events and heap. The root-return boundary
is explicit. Actual shared-history invariants retain the literal caller and
derive each reached nested call's context. A source-bound helper-domain theorem
uses this to exclude reservation inside identity validation without requiring
the suspended factory's reservation suffix to satisfy that helper policy.

The complete factory prefix must still derive helper-entry/return intervals
from its raw host history. Current flag/owner representation, concurrent private
initialization, live-handle publication and later legal lease/interference
histories remain open. Control preservation does not assert ownership survives
arbitrary future heap changes. No progress/fairness or native C11 claim is added.

The owning-package checks passed at 20:49:47 UTC on 2026-09-15.
The required `nix develop .#verification --command lake test` passed at
21:38:47 UTC on 2026-09-15, with 1179 unchanged inputs and all
280 selected roots (36 new, 244 retained). No unexpected axioms, changed-module
warnings or source drift were found. The three existing audits retain every
previous root; no unit test suite was added. Root counts do not measure semantic
coverage.

Draft review and dependency-isolation evidence remains in
`build/c-host-boundary/`: `scan-claim-promotion-v2.json`,
`context-promotion-v1.json`, `scan-claim-review-v2.md`, `context-review-v1.md`
and `claims-context-extracted-v1.json`. Integration, package, full-gate,
standards/upstream review and retained artifact records are under
`build/c-scan-context/`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and public interface emission are
unchanged. Existing artifact, native and mutation checks pass. Only these three
evidence documents change after the frozen gate.

Factory identity-resumption follow-ups remain drafts outside this checkpoint.
Native ABI/C11, callback/fenv correspondence, provenance, transitive allocation,
MISRA and remaining MLS/FMI/eFMI findings stay open. K02–K05 block grammar growth.

**Host histories and reservation origins (full gate passed):**

The host boundary executes the existing C scheduler, admits calls through the
actual public table, observes their halted results and permits repeated calls.
Host memory changes have an explicit policy relation. Computed invocation
records retain the original thread, function and arguments; issued serials
form a strictly increasing interval and are not recycled at completion.

Existing typed C executions embed with exact events, values and output heaps.
The source-bound initial factory/release contract assigns the factory's
invocation serial as its lease and passes its actual returned pointer to release.
Release gets a new invocation serial while using the original factory lease.
These complete calls have matching intermediate states for sequential
composition; they do not establish arbitrary concurrent lifecycle histories.

The actual generated bodies prove a closed non-factory call domain. Generic C
step equivalence and control invariants tied to each recorded invocation derive
the enclosing ME/CS factory for every reached reservation helper or exchange.
The raw host history supplies the descriptor, fresh serial and prior invocation
witness; no later factory or owner annotation is assumed. Successful claim
handoff, concurrent initialization, live-handle publication and later legal
ownership/frame histories remain open.

This checkpoint also includes the release-origin and ordinary flag-frame
proofs described below. The combined package checks passed at
19:55:20 UTC on 2026-09-15. The required
`nix develop .#verification --command lake test` passed at 20:46:20 UTC
on 2026-09-15, with 1166 unchanged inputs and all 244 selected roots
(78 new, 166 retained). No unexpected axioms, changed-module warnings or source
drift were found. The three existing audits retain every earlier root; no
unit test suite was added. A root count is not a measure of semantic coverage.

Evidence is in `build/c-host-boundary/`: `integration-v1.json`, `package-v1.*`,
`full-gate-v1.*`, `standards-review-v1.json`, `upstream-review-v1.json` and
`artifacts-v1.*`. The earlier release/frame evidence remains in
`build/c-release-frames/`. The combined gate covers its pre-publication EOF
cleanup as well as all new host/recording/origin modules.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and public interface emission are
unchanged. Existing artifact, native and mutation checks pass. Only these
three evidence documents change after the frozen gate.

Further scan-claim work remains an ignored draft under `build/`; it is not
part of this checkpoint. Complete legal histories, native C11/ABI and
callback/fenv correspondence, provenance, transitive allocation, MISRA and the
remaining MLS/FMI/eFMI findings remain open. K02–K05 block grammar expansion.

**Release origins and ordinary flag frames (full gate passed):**

Generic C proofs classify real shared steps as ordinary frame-preserving work
or exceptional foreign calls. Prepared string and math bindings retain atomic
flag values. Under an explicit logger flag-preservation contract, only atomic
operations may change them. Without that contract, a flag-changing step is
attributed to an actual atomic or canonical importer logger call. Source binding
supplies the actual adapter table, types and library; no per-step ordinary
annotation is assumed.

Atomic exchange/store preserve successfully loaded ordinary cells. Their cell
types prove non-aliasing without an extra address-inequality premise. A generic
heap-dependent invocation rule separates own execution from other-thread
interference. Actual public release preserves its slot metadata through entry,
parameters, local initialization, the null guard, store and void return. Null
release requires no metadata cell.

The source release theorem supplies the actual function, header and 32-slot
pool. Valid original metadata and an explicit other-thread metadata frame
determine its release address. A represented current lease supplies the enabled
unique atomic step, ownership update, exact event and return continuation.
Successful release, converted arguments and next-state annotations are not
premises. Complete legal histories must still derive interference and current
lease conditions; original metadata alone does not authorize a stale or
duplicate release.

The affected package checks passed at 18:59:11 UTC on
2026-09-15. The required
`nix develop .#verification --command lake test` passed at 19:48:41 UTC
on 2026-09-15, with 1151 unchanged inputs and all 191 selected roots
(25 new, 166 retained). No unexpected axioms, changed-module warnings or source
drift were found. The three existing audits retain all previous roots; no test
suite was added. Evidence is in `build/c-release-frames/`:
`integration-v1.json`, `package-v1.*`, `full-gate-v1.*`,
`standards-review-v1.json`, `upstream-review-v1.json` and `artifacts-v1.*`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and public interface emission are
unchanged. Existing artifact, native and mutation checks pass. Three evidence documents were updated after that frozen gate. A later
pre-publication EOF cleanup is included in the combined gate above.

The host-boundary and recorded reservation-origin follow-ups are integrated
in the combined checkpoint above. Complete legal histories and live-lease
handoff, native C11/ABI/fenv/callback correspondence, provenance, transitive
allocation, MISRA and remaining MLS/FMI/eFMI findings stay open. K02–K05
continue to block grammar expansion.

**Reservation bounds and actual atomic operations (full gate passed):**

The shared C invocation invariant covers actual helper entry, parameter binding,
local initialization and every scan-loop prefix under shared-heap interleavings.
It retains the original flag pointer and bounded index until the original caller
resumes. The source theorem derives the actual helper, header types and emitted
32-slot pool from the same source/adapter contract. The validated factory suffix
obtains its helper arguments from fresh locals and concrete globals.

Represented current flags supply an enabled, unique actual reservation step and
its lease annotation, with the busy result, exact event, ownership update and
other-thread control frame. Neither successful reservation nor argument
conversion or a next-state annotation is a premise. Complete public factory
entry, release authorization, fresh lease assignment and ordinary/logger flag
frames remain open. An unsuccessful concurrent scan does not prove that all
slots were busy at one instant.

The separate generated-call proof derives Boolean conversion and actual atomic
memory effects after finite shared executions from public entries. It retains
exact events and return continuations without extra conversion or value-policy
premises. Its unrestricted atomic pointers do not establish release authority.

The affected package checks passed at 18:09:27 UTC on
2026-09-15. The required
`nix develop .#verification --command lake test` passed at 18:57:47 UTC
on 2026-09-15, with 1142 unchanged inputs and all 166 selected roots
(27 new, 139 retained). No unexpected axioms, changed-module warnings or source
drift were found. The existing three audits retain all previous roots; no test
suite was added. Evidence is in `build/c-reservation-bounds/`:
`integration-v1.json`, `package-v1.*`, `full-gate-v1.*`,
`standards-review-v1.json` and `artifacts-v1.*`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and public interface emission are
unchanged. Existing artifact, native and mutation checks pass. Only these
three evidence documents change after the frozen gate.

The ordinary flag-frame and callback-attribution follow-up remains a checked
draft under `build/`, separate from this checkpoint. Native C11/ABI, full legal
histories, provenance, transitive no-allocation, MISRA and remaining MLS/FMI/eFMI
findings stay open. K02–K05 continue to block grammar expansion.

**Concurrent slot histories and atomic-call values (full gate passed):**

Reusable C proofs characterize actual shared-heap scheduler steps and preserve
operand restrictions through calls, returns and finite interleavings. The direct
Boolean checker is equivalent to the structural predicate. FMI derives
reservation=true and release=false from the generated trees and actual argument
evaluation. Its linked address map excludes indirect atomic aliases. The source
theorem supplies this invariant from the actual adapter/header contract and
ordinary public invocations, without later-call annotations or an extra atomic
argument policy.

The separate ownership simulation derives atomic steps from represented flag
memory and connects annotated C histories to independent lease transitions.
An owned slot cannot be successfully reclaimed without its prior lease being
released. Source binding supplies the generated table, library bindings and
emitted 32-slot pool. Complete factory-path classification still needs valid
flag-address origins, release authorization and atomic-value frames for other
effects; these obligations are not assumed away by the call-value proof.

The affected package checks passed at 17:16:36 UTC on
2026-09-15. The required
`nix develop .#verification --command lake test` passed at 18:07:31 UTC
on 2026-09-15, with 1133 unchanged inputs and all 139 selected roots
(45 new, 94 retained). No unexpected axioms, changed-module warnings or source
drift were found. No test suite was added. Evidence is in
`build/c-concurrent-slots/`: `integration-v1.json`, `package-v1.*`,
`full-gate-v1.*`, `standards-review-v1.json`, `upstream-review-v1.json`
and `artifacts-v1.*`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and interface emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

The atomic-operation, reservation-bound and flag-frame follow-ups are checked
drafts under `build/`; they are not integrated at this checkpoint. Native atomics/ABI, full legal histories,
provenance, transitive no-allocation, MISRA and remaining MLS/FMI/eFMI findings
stay open. K02–K05 still block grammar expansion.

**Runtime storage and state-setter permissions (full gate passed):**

Generic C proofs lift store-stable heap relations through foreign calls and
modeled thread interleavings. The selected string, atomic and math bindings
preserve object existence, types and permissions. The source-bound prepared
runtime combines this with the call-depth bound under an explicit logger storage
contract. Without that contract, any observed storage change is attributed to
an actual logger execution, with its arguments and trace position. These are
modeled storage properties; native/transient allocation and race freedom remain
separate obligations.

The state-setter policy identifies continuous states through the actual XML's
ModelStructure derivative links. Initialization and reinitialization attributes
determine the phase permissions. Lean proves exact correspondence with the
existing guard for every accepted XML witness and connects it to the actual
source/setter contract. The ME interpretation follows accepted FMI clarification
#1956; the Table 17 editorial conflict remains explicit in the standards review.

The affected package checks passed at 16:16:22 UTC on
2026-09-15. The required
`nix develop .#verification --command lake test` passed at 17:12:17 UTC
on 2026-09-15, with 1125 unchanged inputs and all 94 selected roots
(32 new, 62 retained). No unexpected axioms, changed-module warnings or source
drift were found. The existing separate audits retain every prior root; no
test suite was added. Evidence is in `build/c-runtime-resources/`:
`integration-v1.json`, `package-v1.*`, `full-gate-v1.*`,
`standards-review-v1.json` and `artifacts-v1.*`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and public-call emission are unchanged.
Existing artifact, native and mutation checks pass. Only these three evidence
documents change after the frozen gate.

The annotated concurrent lease-history and atomic-call-value follow-up proofs
are checked drafts under `build/`; they are not integrated at this checkpoint. Complete factory-path
classification, native/ABI, full legal histories, provenance, transitive
no-allocation and MISRA obligations remain open. K02–K05 and the remaining
MLS/FMI/eFMI findings still block grammar expansion.

**Source-bound runtime and call depth (full gate passed):**

One prepared environment contains the actual generated function table,
string/atomic/math bindings and an arbitrary logger effect. Generic linking
preserves existing bindings and registers function addresses only for imported
entries. The C rank invariant survives every internal step, return and returning
foreign choice. Every finite execution prefix in this FMI environment has at
most three modeled continuation frames, without assuming successful termination.
The source theorem derives the literal pool, public printer coverage and
concrete object/fenv interface from the actual adapter contract. It uses the
emitted 32-slot configuration, with no separate type, pointer-policy or rank
premise. Native layout, library/callback internals, native stack bytes and
transitive allocation remain outside this bound.

The affected package checks passed at 15:17:26 UTC on
2026-09-15. The required
`nix develop .#verification --command lake test` passed at 16:14:54 UTC
on 2026-09-15, with 1119 unchanged inputs and all 62 selected roots
(29 new). No unexpected axioms, changed-module warnings or source drift were
found. The existing separate package audits retain every prior root. Evidence
is in `build/c-call-depth/`: `integration-v1.json`, `package-v1.*`,
`full-gate-v1.*`, `upstream-review-v2.json` and `artifacts-v1.*`.

Every FMU member is unchanged from the previous checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC, Production C, grammars, metadata and public-call emission are unchanged.
The existing artifact, native and mutation checks pass; no test suite was added.
Only these three evidence documents change after the frozen gate.

This accepts the modeled execution-depth and source linkage increment.
The storage and state-setter follow-up proofs remain checked drafts under
`build/`; they are not accepted package/artifact results at this checkpoint.
Native resource, ABI, complete legal-history, provenance and MISRA obligations
remain open. K02–K05 and the whole-subset standards findings still block grammar
expansion; no full standards or CompCert-level whole-compiler claim follows.

**Generated call policy (full gate passed):**

The shared C package has a complete structural call inventory and an independent
admission predicate. Its executable checker walks the tree directly; Lean
proves exact Boolean equivalence to checking the full inventory for every
predicate and function. FMI classifies generated helpers, library routines and
importer callbacks. Checked ranks exclude cycles in the complete prepared
direct-call graph, including numerical definitions. The shared resolver connects
named calls to that graph, and numerical-kernel execution is proved unable to
issue a scheduler call. The source consequence derives the policy from the
mandatory actual adapter/header contract without an extra rank assumption.

The shared C package additionally has a reusable decidable no-heap and acyclic
policy (`RumocaC/NoHeapPolicy.lean`) over a list of function definitions and a
named external boundary set. `NoHeap` requires every callee name in every body
to be a defined function, a declared kernel entry, a header-declared FMI
function or a named external, and never one of the explicitly listed allocation
entry points (`malloc`, `calloc`, `realloc`, `free`, `aligned_alloc` and the
others); `Acyclic` states the direct-call relation among defined functions has
no cycle, discharged by a decidable topological rank. `noHeap_no_alloc_call`
proves that a call actually scheduled by the shared eventful resolver from a
policy-checked body names no allocation entry point, stated over the machine's
own call step rather than a text search, and `noHeap_execution_no_alloc` lifts
this across the body's reachable loop states. The scalar adapter function list
is proved to obey both policies (`CallPolicy.unit_no_heap`/`unit_acyclic`), with
the named boundary set `CallPolicy.bUnit`: the generated helpers `fail`,
`model_rhs`, `model_advance`, `rumoca_valid_identity`, `rumoca_reserve_slot`;
the declared kernel entries `rumoca_rhs`, `rumoca_step`, `rumoca_sample`; the
library externals `isfinite`, `floor`, `fegetround`, `strlen`, `strspn`,
`strcmp`, `atomic_exchange`, `atomic_store`; and the importer logger callback
`logMessage`. This is carried as the `no_heap_acyclic` conjunct of
`FMI3.SourceBuildContract`, a proved consequence of the mandatory adapter
contract required on the actual bytes. The same policy is instantiated for the
tensor adapter function list (`TensorFunctions.functions`): its 19 shape-dependent
bodies, reused static-factory/release helpers and scalar fallback bodies are
proved to obey both policies (`TensorCallPolicy.tensor_no_heap`/`tensor_acyclic`)
universally in the tensor shape, scalar witness model and header signature list,
with the boundary set `TensorCallPolicy.bTensor` (the scalar externals plus the
second prepared kernel entry `rumoca_square_jacobian_diag`). This is carried as
the `no_heap_acyclic` conjunct of `Rumoca.TensorSourceBuildContract`, a proved
consequence of the mandatory tensor adapter contract on the actual bytes. The
static-declaration layout/size/alignment binding to bytes and the numerical
kernel body-level discharge remain open.

The affected package checks passed at 14:22:06 UTC on 2026-09-15. The required
`nix develop .#verification --command lake test` passed at 15:09:42 UTC
on 2026-09-15, with 1114 unchanged inputs and all 33 selected roots.
No unexpected axioms, changed-module warnings or source drift were found.
The policy audits have separate modules in the existing package check libraries;
unrelated audits retain Lake's normal cache. Evidence is in
`build/c-call-policy/`: `integration-v3.json`, `package-v3.*`,
`full-gate-v1.*`, `upstream-review-v2.json` and `artifacts-v1.*`.

Every FMU member, including its native library, is unchanged from the previous checkpoint.
The eFMU changes only generation identities and dependent references/checksums
in three manifests. Numerical C, GALEC, Production C, grammars, solver policy,
metadata and lifecycle emission are unchanged. The existing artifact, native
and mutation checks pass; no test suite was added. Only these three evidence
documents change after the frozen gate.

This accepts call classification and direct-call graph ranking. Complete
execution/continuation composition, native/transitive no-allocation, callback
reentry, layout, concurrency and MISRA remain open. K02–K05 still block grammar
expansion; this is not a full standards or CompCert-level whole-compiler claim.

**SR09 empty-setter correction and public-export coverage (full gate passed):**

Empty Float64 and absent-type setters now use the general setter endpoint
rule. Terminated instances reject them; CS Step Mode retains empty calls.
The nonempty Float64 validation domain is unchanged. Complete success and
lifecycle/count rejection contracts preserve every modeled callback outcome,
prepared diagnostics, raw arguments and source/history composition.

Every emitted header signature now has mandatory coverage by a named public
execution/printer contract. The fixed actual-file checker supplies this witness
for the same adapter table and literal pool. The general C return-continuation
law proves unused caller suffixes cannot change the modeled call behavior;
it does not weaken the C machine or the previous behavior contracts.

The combined core/C/FMI/compiler checks passed at 13:01:38 UTC. The required
`nix develop .#verification --command lake test` passed at 13:52:47 UTC on
2026-09-15 with 1107 unchanged inputs and all 436 selected roots. There were
no unexpected axioms, changed-module warnings or input drift. Evidence is in
`build/c-factory/setter-endpoints/`: `package-v3.*`, `full-gate-v1.*`,
`integration-v3.json`, `standards-review-v1.json`, `upstream-review-v1.json`
and `artifacts-v1.*`.

The actual FMU changes exactly 13 setter guard lines and its native library;
every other member is byte-identical to the previous checkpoint's retained FMU. The eFMU
changes only generation identities and dependent references/checksums in three
manifests. Numerical C, GALEC, Production C and metadata behavior are unchanged.
The existing native boundary check now includes terminated empty setters for
both interfaces; no test suite or grammar was added. Only these three evidence
documents change after the frozen gate.

This accepts the empty-setter repair and complete raw-call contracts. The
separate nonempty local-state setter wording review, complete legal-history
correspondence, native/ABI, provenance, concurrency, no-heap and MISRA obligations
remain open. K02–K05 still block grammar expansion; this is not a full FMI/eFMI
conformance or CompCert-level whole-compiler claim.

**Unsupported public FMI calls (2026-09-15, full gate passed):**

The mandatory adapter proposition includes all 25 existing generic rejection
APIs and the separate Scheduled Execution creation rejection. Shared proofs
derive typed call entry, null/quiet/logged behavior, every modeled callback
return and the blocked alternative. Prepared contracts construct the diagnostic
pool and preserve readonly strings. Exact signatures, printers and fragments
use the existing C printer certificates. The fixed actual-file checker derives
membership in the same header signature list before constructing the contract.

Two source consequences connect the same compiled source, numerical C, XML
capability/declaration omissions, adapter bytes, prepared table and literal
pool. They require no extra adapter assumption. The three affected existing
source/history consumers retain their theorem statements. Six backend modules
and one compiler proof module add 35 audit registrations; none are removed.

The owning core/C/FMI/compiler checks passed at 11:19:44 UTC; the required
`nix develop .#verification --command lake test` passed at 12:06:06 UTC on
1103 unchanged inputs. All 418 selected roots passed without unexpected axioms,
changed-module warnings or input drift. Evidence is in
`build/c-factory/public-api-inventory/`: `package-v1.*`, `full-gate-v1.*`,
`integration-v1.json`, `review-v5.json` and `artifacts-v1.*`.

Every retained FMU member, including the native library, is unchanged. The
eFMU changes only generation identities and dependent references/checksums in
three manifests. Numerical C, GALEC and Production C remain unchanged. Existing
artifact/native/rejection checks passed; no grammar, runtime emitter, solver,
metadata behavior or test suite changed. Only these three evidence documents
change after the frozen gate.

These are raw execution contracts. XML omissions do not establish that every
empty Clock, interval or output-derivative request must be rejected. Those
standards findings and complete legal-history correspondence remain open,
together with native/ABI, full provenance, concurrency and MISRA obligations.
K02–K05 still block grammar expansion. No full FMI/eFMI conformance or
CompCert-level whole-compiler claim follows from this increment.

This checkpoint exposed SR09's empty-setter endpoint defect. Its original
review witnesses remain in `empty-setter-review-v1.*` and
`public-coverage-review-v2.json`; the accepted correction and full artifact
evidence are recorded in the SR09 section.

**Absent-variable initialization histories (2026-09-15, full gate passed):**

The initialization protocol includes all 24 existing absent-variable accessors.
Empty calls preserve the heap; rejected counts derive Error and retain every
modeled logger return or blocked outcome. Source-bound creation, initialization,
simulation, reset and release compose through recurring ME/CS histories,
including interrupted prefixes. Caller storage, readonly diagnostics, ownership,
logging configuration and numerical source observations are retained.

The owning core/C/FMI/compiler checks passed at 10:19:29 UTC; the required
`nix develop .#verification --command lake test` passed at 11:05:22 UTC on
1096 unchanged inputs. All 194 selected roots passed without unexpected axioms,
changed-module warnings or input drift. Six new audit registrations retain all
previous roots. Evidence is in `build/c-factory/accessor-histories/`:
`package-v1.*`, `full-gate-v1.*`, `integration-v1.json`,
`standards-review-v1.json` and `artifacts-v1.*`. The existing mandatory adapter
field supplies every prepared accessor from the same source artifact.

Every retained FMU member, including the native library, is unchanged. The
eFMU changes only generation identities and dependent references/checksums in
three manifests. Numerical C, GALEC and Production C remain unchanged. Existing
artifact/native/rejection checks passed; no grammar, emitter, solver, metadata
or test behavior changed. Only these three evidence documents change after
the frozen gate.

These are raw execution histories. They do not license null arguments,
terminated-state setters or unrestricted CS getter/setter ordering. Complete
legal-history correspondence, remaining public APIs, native/ABI and provenance,
concurrency and MISRA obligations remain open. K02–K05 still block grammar
expansion; no full FMI/eFMI or CompCert-level compiler claim follows.

**Absent-variable accessors (2026-09-15, full gate passed):**

A shared contract covers all 24 emitted Get/Set functions for Float32,
integer, Boolean, String and Binary types absent from the current model.
Empty calls preserve the whole heap. Null/nonempty rejection and every modeled
logger outcome use the actual function table and prepared diagnostic pool.
Binary's separate size array is retained. The actual XML proof also excludes
Enumeration, which shares the Int64 APIs; valid typed selections and consistent
counts derive the successful call without assuming its returned result.

The mandatory adapter contract and fixed checker bind every exact signature,
printed function and runtime contract to the same compiled source, numerical C
and XML. Existing source/history theorem statements remain intact. The owning
core/C/FMI/compiler checks passed at 09:27:21 UTC; the required
`nix develop .#verification --command lake test` passed at 10:12:18 UTC on
1094 unchanged inputs. All 188 selected roots passed without unexpected axioms,
changed-module warnings or input drift. The audit adds 27 registrations and
removes none. The initial failed build and unchanged-statement fixes remain
recorded in `package-v1.*` and `additional-consumers-v1.json`. Evidence is in `build/c-factory/empty-access/`: `package-v2.*`,
`full-gate-v1.*`, `integration-v2.json`, `review-v4.json` and `artifacts-v1.*`.

Every retained FMU member, including the native library, is unchanged. The
eFMU changes only generation identities and dependent references/checksums in
three manifests. Numerical C, GALEC and Production C remain unchanged. Existing
artifact/native/rejection checks passed; no emitter, solver, source grammar or
test suite changed. Only these three evidence documents change after the gate.

This accepts the raw public-call and same-source artifact contracts. It does
not authorize null arguments, setters after termination or arbitrary importer
histories. CS getter-after-setter ordering, complete history composition and
standards correspondence remain open, together with native/ABI, provenance,
concurrency and MISRA obligations. K02–K05 still block grammar expansion.

**Evaluation during initialization histories (2026-09-15, full gate passed):**

Evaluation success and rejection now compose through the initialization
protocol, reset/retry, post-exit ME operation and recurring ME/CS runs. The
classifier covers every represented interface/mode pair. The same public C
function derives returned status and memory effects, including every modeled
logger return and the blocked alternative. Original caller/borrowed storage,
ownership, source checkpoints and completed/stopped observations compose from
actual creation through final release.

The common bundle reuses its existing ME evaluation contract. Successful
evaluation preserves state and cannot replace the required discrete update.
The owning core/C/FMI/compiler checks passed at 08:23:37 UTC; the required
`nix develop .#verification --command lake test` passed at 09:17:17 UTC on
1087 unchanged inputs. All 150 selected roots passed without unexpected axioms,
changed-module warnings or input drift. Five new audit registrations supplement
the retained source/history roots. Evidence is in
`build/c-factory/evaluation-initialization/`: `package-v1.*`, `full-gate-v1.*`,
`integration-v1.json`, `standards-review-v1.json` and `artifacts-v1.*`.

Every retained FMU member, including the native library, is byte-identical to
the accepted discrete-evaluation checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC and Production C are unchanged. Existing artifact/native/rejection checks
passed; no grammar, solver, emitter, metadata or test suite was added.
Only these three evidence documents change after the frozen gate.

This closes evaluation interleavings in the represented initialization and
recurring protocols. Remaining public capability/type-access calls, unrestricted
host/callback/concurrent behavior, complete native/ABI and artifact provenance,
MISRA and whole-subset standards obligations remain open. K02–K05 still block
grammar expansion; this is not a full FMI-conformance claim.

**Discrete evaluation (2026-09-15, full gate passed):**

The existing evaluation call now accepts only ME Event Mode in this profile.
The actual XML omits the capability, whose reviewed default is false; successful
evaluation preserves the whole heap. It does not complete event iteration.
Null/rejected calls retain every modeled status and logger alternative. The
mandatory adapter/checker binds the exact printed function and common prepared
table/literal pool; the source theorem retains the same numerical C and XML.
ME control and rejection histories, storage frames, creation/release and the
numerical/recurring source consumers carry the strengthened contract.

The owning core/C/FMI/compiler checks passed at 07:31:36 UTC; the required
`nix develop .#verification --command lake test` passed at 08:15:06 UTC on
1085 unchanged inputs. All 133 selected roots passed without unexpected axioms,
changed-module warnings or input drift. The audit adds 21 registrations and
retains all prior roots. Evidence is in `build/c-factory/discrete-evaluation/`:
`package-v1.*`, `full-gate-v1.*`, `integration-v1.json` and `artifacts-v1.*`.

The retained FMU changes only the evaluation guard in `sources/fmi3.c` and its
native library. The eFMU changes only generation identities and dependent
references/checksums in three manifests. Numerical C, GALEC and Production C
remain unchanged. The existing ME native lifecycle check now exercises
Initialization rejection and Event no-op; no new test suite was added.
Only these three evidence documents change after the frozen gate.

This accepts the corrected call and represented ME control/rejection history
composition. It does not close the remaining initialization/public-call
interleavings, unrestricted host/callback behavior, complete native/ABI and
artifact provenance, or MISRA and whole-subset standards obligations.
K02–K05 remain open; no grammar expansion or full FMI-conformance claim.

**Event-indicator histories (2026-09-15, full gate passed):** The
existing initialization and mixed ME histories now include empty event queries.
Raw target executions determine status, observations, reference transitions and
completed/stopped prefixes. Original borrowed inputs, logging configuration,
ownership and reset/source initialization checkpoints compose through the same
history relations. Source-bound creation/release, resource handoff and recurring
ME/CS bundle consumers retain their numerical and memory obligations.

The owning C/FMI/compiler checks passed at 06:36:55 UTC; the required
`nix develop .#verification --command lake test` passed at 07:20:04 UTC on
1079 unchanged inputs. All 63 selected roots passed without unexpected axioms,
changed-module warnings or input drift. Three new audit registrations supplement
the retained history/source roots. Evidence is in
`build/c-factory/event-histories/package-v1.*`, `full-gate-v1.*` and
`integration-v1.json`.

Every retained FMU member, including the native library, is byte-identical to
the accepted zero-event getter checkpoint. The eFMU changes only generation
identities and dependent references/checksums in three manifests; numerical C,
GALEC and Production C are unchanged. See
`build/c-factory/event-histories/artifacts-v1/` and its JSON record.
The existing artifact, importer, native and mutation checks passed; no test
suite was added. Only these three evidence documents change after the frozen gate.

The next discrete-evaluation review found an overbroad lifecycle predicate:
`fmi3EvaluateDiscreteStates` was admitted during Initialization, although the
pinned FMI 3.0.2 call table lists it in Event Mode. Its false capability default
requires an ignored operation there, so generic capability rejection is not
the replacement. An Event-only policy correction and complete no-op call,
metadata, source and control-history drafts are in
`build/c-factory/discrete-evaluation/`; combined production and artifact
acceptance remain pending. No new grammar or numerical capability is admitted.
K02–K05 and the recurring whole-subset standards review remain open.

**Zero-event getter (2026-09-15, full gate passed):** The mandatory
adapter proposition and fixed checker require the printed/prepared
`fmi3GetEventIndicators` contract. Its source theorem joins the actual C file,
XML zero-event count and the same Solve product. Success preserves the whole
heap; rejection retains every modeled logger return and no-return alternative.
The ME call theorem derives the numerical/caller memory frame under the
existing universal callback policy.

The owning C/FMI/compiler checks passed at 05:43:02 UTC; the required
`nix develop .#verification --command lake test` passed at 06:26:27 UTC on
1078 unchanged inputs. All 40 selected roots passed without unexpected axioms,
changed-module warnings or input drift. Six existing consumers were updated to
unpack the strengthened adapter conjunction; their statements and audit roots
are preserved. Failed integration evidence remains in `package-v1.*`.
Accepted evidence is in `build/c-factory/event-indicators/package-v2.*`,
`full-gate-v1.*` and `integration-fixes-v1.json`.

Every retained FMU member, including the native library, is byte-identical to
the accepted CS checkpoint. Only generation identities and dependent
references/checksums in three eFMU manifests change. Numerical C, GALEC and
Production C are unchanged. See `build/c-factory/event-indicators/artifacts-v1/`
and its JSON record. The existing artifact, importer, native and mutation
checks passed; no test suite was added. Only these three evidence documents
change after the frozen gate.

The later event-history checkpoint above accepts initialization and mixed
ME composition together with its own package and actual-artifact evidence.
The standards review distinguishes normative valid calls from the body's
additional null-pointer tolerance. No grammar, numerical lowering or emitter
change is admitted. Native/ABI correspondence, remaining public calls,
reset-policy review and K02–K05 remain open.

**CS simulation logging (2026-09-15, full gate passed):** The recurring
CS protocol and initialization-access/protocol continuations now use one mixed
numerical/logging history. Source-bound creation, initialization, simulation,
reset and release retain the last successful logging update, raw call returns,
numerical source observations and stopped prefixes. The numerical call proofs
remain shared components; the two fixed-logging restart wrappers are replaced
by one theorem over the mixed history.

Original borrowed category arrays and strings are carried through preceding
calls. Their write separation and universal callback policies remain explicit
host-profile conditions, including while logging is disabled. Expected return
statuses and final flags are derived from actual executions. No future readable
heap or selected callback result replaces that derivation. Shared initialization
retention/configuration facts now live in the common access storage module.

The owning C/FMI/compiler checks passed at 04:46:54 UTC. The required
`nix develop .#verification --command lake test` passed at 05:28:57 UTC on
1071 unchanged inputs. All 69 selected audit roots passed, with no unexpected
axioms, changed-module warnings or input drift. Earlier failed package attempts
are retained; missing direct imports and an extra namespace terminator were
fixed. The five original CS numerical interruption roots remain registered,
and the generalized handoff/restart roots replace their former wrappers
without weakening the contracts or axiom whitelist. Evidence is in
`build/c-factory/cs-simulation-logging/package-v4.*` and `full-gate-v1.*`.
Only the three evidence documents change after the frozen full gate.

Every retained FMU member, including the native library, is byte-identical to
the accepted ME checkpoint. The eFMU changes only generation identities and
dependent references/checksums in three manifests. Numerical C, GALEC and
Production C are unchanged. Archives and comparisons are in
`build/c-factory/cs-simulation-logging/artifacts-v1/` and its adjacent JSON
record. Existing artifact, importer, native and mutation checks passed; no
test suite was added. Reset logging policy, remaining public calls, native/ABI
correspondence and K02–K05 retain their stated review limits. This acceptance
adds no grammar or emitter change and does not establish full conformance.

**ME simulation logging (2026-09-15, full gate passed):** The existing ME
history implementation now includes initialization-access and protocol continuations,
restart, source observations, stopped-prefix flags and recurring source-bound
creation/initialization/simulation/reset/release. The shared initialization
bundle supplies the prepared logging contract from the same emitted table.
The affected CS bundle consumer retains its previous guarantee.

The package split separates shared callback effects, ME/CS memory invariants
and prepared call contracts. A generic C storage theorem derives atomic-cell
unreadability after tracing storage descriptions back through creation. Original
borrowed inputs and universal callback frames remain explicit conditions.
The owning C/FMI/compiler package checks passed at 03:24:08 UTC. The required
`nix develop .#verification --command lake test` passed at 04:09:01 UTC on
1062 unchanged inputs. All 89 selected audit roots passed, with no unexpected
axioms, changed-module warnings or input drift. Evidence is in
`build/c-factory/simulation-logging/package-v4.*` and `full-gate-v1.*`.
The earlier package failures exposed missing imports and a stale audit name;
the relocated retained-field theorem has the same statement. Its registration
is preserved under its new name, without weakening the audit or contract.
Only the three evidence documents change after the frozen full gate.

Every retained FMU member, including the native library, is byte-identical to
the initialization checkpoint. The eFMU changes only generation identities
and dependent references/checksums in three manifests. Numerical C, GALEC and
Production C are unchanged. Archives and comparisons are in
`build/c-factory/simulation-logging/artifacts-v1/` and its adjacent JSON record.
The existing artifact, importer, native and mutation checks passed; no test
suite was added. The CS checkpoint above accepts the later mixed CS histories;
K02–K05 remain open. No grammar or emitter changed. Reset logging policy and native/ABI correspondence retain
their stated review limits; this acceptance is not full standards conformance.

**Mutable logging during initialization (2026-09-15, full gate passed):**
The existing initialization protocol now admits public logging actions and
records their exact effect on the logging cell. A failed request retains the
old flag and enters the failed phase; a successful request changes the flag
without changing the source IVP. Original borrowed category arrays and strings
are preserved through preceding calls under explicit read/write separation
and callback-frame conditions. They may be writable; no future readable heap
is an external premise of the composed initialization theorem.

`InitializationProtocol.runtime_source` now includes the actual XML logging
category and the prepared public setter. Its callback capability retains the
original binding and universal memory policy while disabled. This is a
stronger history precondition than a suppression-only fact; the latter does
not imply a valid callable pointer. The separate low-level suppressed-call
contracts remain available. The read-bank borrowing guards are a modeled host
discipline, not an FMI standard requirement or a claim of unrestricted host
trace coverage.

Creation now derives the original-to-created read-bank frame from the actual
factory execution: ordinary category reads, including string terminators,
cannot alias atomic reservation flags. The source-bound creation/release,
reset/initialization and stopped-prefix theorems carry the same bank. ME/CS
handoffs use the exact final flag selected by initialization, instead of
assuming it still equals the factory argument.

CS simulation now preserves exact borrowed contents, alongside existing typed
storage. Its `Logger.FramePolicy` is a universal callback obligation, and
`LoggedTrace.frame` derives the frame for every actual returned branch. The
actual prepared `cs_execution` supplies the new persistent read-bank frame
under explicit separation from instance/output writes. These guards describe
a borrowing profile; they do not establish unrestricted importer behavior.

ME now has the same exact-content guarantee for count, nominal, numerical,
rejection and reset calls. Its actual mixed-history proof derives the borrowed
input frame using the original callback policy and explicit separation from
writes. Both recurring source-bound runtime theorems now carry this bank from
actual creation through initialization/simulation cycles, stopped prefixes,
resets and release. Their postconditions compose the exact logging update
across all initialization segments. The suppressed CS call certificate also
retains its exact output/instance frame, so restart helpers derive later inputs.

The owning C/FMI/compiler package checks passed at 01:38:40 UTC. The required
`nix develop .#verification --command lake test` then passed at 02:22:20 UTC,
on 1056 unchanged inputs. All 173 selected roots passed, including 68 newly
registered roots, with no unexpected axioms, changed-module warnings or input
drift. Evidence is in `build/c-factory/logging-history/package-v1.*` and
`full-gate-v1.*`. Only the three evidence documents change after the frozen
full gate.

Every retained FMU member, including the native library, is byte-identical to
the public-setter checkpoint. The eFMU changes only generation identities and
dependent references/checksums in three manifests. Numerical C, GALEC and eFMI
Production C are unchanged. The checked archives and comparisons are in
`build/c-factory/logging-history/artifacts-v1/` and its adjacent JSON record.
Existing artifact, importer, native-interface and mutation checks passed;
no new test suite was added.

The subsequent ME checkpoint above accepts logging interleavings during ME
simulation, including exact flags after completed and stopped prefixes and
recurring source-bound lifetimes. The CS checkpoint above supplies the later
CS source/lifetime composition and artifact acceptance. K02–K05 still block
grammar expansion.

**Public logging configuration (full gate passed):**
The emitted `fmi3SetDebugLogging` now uses an explicit `strcmp` result before
checking each selected category. The shared C machine models every permitted
comparison result; the validation loop checks arbitrary finite category arrays
and writes the logging flag only after the entire array succeeds. This adds
no allocation or numerical lowering to the FMI backend.

The mandatory adapter proposition includes `DebugLogging.FunctionContract`:
the actual function tree, certified printer, declared XML category and a
prepared runtime contract. Its success, suppressed-error and logged-error
branches derive the failure helper from the actual definition table and the
immutable literal pool. Every modeled callback return and the no-return
alternative remain explicit. Legal requests derive the requested flag and
preserve every other memory cell, storage and immutable-memory guarantees.

The owning C/FMI/compiler package gate passed on 1040 unchanged inputs,
covering 58 new and five affected audit roots. The first attempt exposed
missing direct unfolding in two existing structural proofs; those proofs were
repaired without weakening their statements. The required
`nix develop .#verification --command lake test` then passed on
2026-09-15 at 00:18:22 UTC, with all 63 required roots, no unexpected axioms
and no changed-module warnings or input drift. Evidence is in
`build/c-factory/debug-logging/package-v2.*` and `full-gate-v1.*`.
Only the three evidence documents change after the frozen full gate.

The retained FMU changes only `sources/fmi3.c`, specifically the public logging
setter; all other members, including the native library, are byte-identical
to the preceding nominal-history artifact. The eFMU changes only generation
identities and dependent references/checksums in three manifests. Numerical C,
GALEC and eFMI Production C are unchanged. Retained archives and member hashes
are in `build/c-factory/debug-logging/artifacts-v1/` and its adjacent JSON record.
The existing native FMI check covers the string-array ABI and the original
logging policy on rejection; no new test suite was added.

The initialization-history checkpoint above now composes the public setter
with creation, initialization, ME/CS handoffs and recurring release. Logging
changes during CS simulation, remaining public calls, native/ABI correspondence
and K02–K05 remain open.

**Nominal observations in complete histories (2026-09-14, full gate passed):**
The nominal function contract now supplies the actual shared runtime on later
literal-preserving heaps, including suppressed logging and all modeled logger
outcomes. Original typed caller storage supports nominal reads throughout
initialization, ME simulation/control histories and resets. Compatible public
Float64 output buffers may alias; private instance and flag storage remains
separate. Expected statuses and values are derived from raw C executions.

Source-bound creation, restart, recurring ME/CS initialization and recurring
ME simulation/release retain the same XML nominal ordering and positive
default-one witness. The existing C machine and emitters are unchanged.
`Nominals.FunctionContract.runtime` strengthens the mandatory actual adapter
proposition; this increment requires its own full artifact acceptance.

The final 80-module draft and 56 selected roots passed ordinary Lean checking
in `build/c-factory/nominal-initialization-source-draft-v6.log`, with no unexpected
axioms or Lean warnings. The owning FMI/compiler package gate then passed at
22:10:56 UTC on 1022 unchanged inputs in
`build/c-factory/nominal-history-package-v2.log`: 25 new and 31 affected roots,
with no unexpected axioms or changed-module warnings. The first package attempt
exposed a missing direct import; its failed log is retained and the import is
fixed without changing a proof statement. The required
`nix develop .#verification --command lake test` then passed at 22:56:23 UTC
on 1022 unchanged inputs, with all 56 required roots and no unexpected axioms
or changed-module warnings. Evidence is in
`build/c-factory/nominal-history-full-gate-v1.log` and its JSON record. Only the
three evidence documents change after that frozen full gate.

Retained artifacts and comparisons are in
`build/c-factory/nominal-history-artifacts-v1/` and adjacent JSON records. Every
FMU member, including its native library, is unchanged from the preceding
ME-count artifact. The eFMU changes only generation identities and dependent
references/checksums in three manifests. Numerical C, GALEC and eFMI Production
C remain unchanged. Logging configuration, remaining public calls, native/ABI
correspondence and K02–K05 still block grammar expansion.

**Counts in ME simulation histories (2026-09-14, full gate passed):**
The mixed ME relation now includes successful and rejected count calls between
simulation/control actions and resets. Raw execution admits arbitrary returned
statuses, events and heaps; complete prepared C contracts derive the Solve
count, lifecycle result, source observation and preserved storage. A blocked
call is retained in its actual source-bearing prefix without assuming a
callback return.

The caller supplies typed count cells in the original heap. The existing
universal callback storage policy and history induction derive each later
precondition. The source-bound creation, initialization, recurring ME plans
and release theorems retain these observations alongside actual XML counts.
ME importer trial states still carry no external-integrator correctness claim.

The owning FMI/compiler package gate passed at 21:15:09 UTC. The required
`nix develop .#verification --command lake test` then passed at 22:01:57 UTC
on 1015 unchanged inputs, including nine new and eighteen affected audit
roots, with no unexpected axioms or changed-module warnings. Evidence is in
`build/c-factory/me-count-full-gate-v1.log` and its JSON record. Only the three
verification/roadmap documents change after the frozen full gate.

Retained artifacts and comparisons are in `build/c-factory/me-count-artifacts-v1/`
and adjacent JSON records. Every FMU member, including the native library, is
unchanged from the preceding initialization-count artifact. The eFMU changes
only generation identities and dependent references/checksums in three
manifests. Numerical C, GALEC and eFMI Production C are unchanged.
Source/GALEC grammars, numerical/C machine semantics, emitters, metadata and
mandatory artifact propositions are unchanged. Nominal queries, remaining
public calls, native/ABI correspondence and K02–K05 continue to block growth.

**Count observations in initialization histories (2026-09-14, full gate passed):**
The existing initialization protocol now includes both count queries. Successful
observations report the prepared Solve state volume or zero event indicators;
rejections use the existing mode/pointer priority, Error transition and logger
contracts. The raw execution still admits arbitrary returned statuses, events
and heaps. The call proofs derive the expected observations and recovery state.

Caller `size_t` cells are supplied once in the original heap. Storage
preservation carries their types and permissions through preceding calls,
callbacks and resets. Successful writes preserve the model, initialization
configuration and reservation map; rejected calls preserve the protected
caller/instance region under the existing universal logger policy. Callback
return and a valid future heap are not assumptions.

The composed initialization, creation/release and recurring ME/CS source
theorems now retain these initialization observations and explicitly bind the
same Solve counts to actual XML metadata. This includes ME Instantiated and
post-exit Event Mode observations, and rejected attempts in the other phases
represented by initialization. The numerical C and both interfaces' runtime
emitters are unchanged. The required
`nix develop .#verification --command lake test` passed at 21:05:03 UTC on
1012 unchanged inputs. Eight new and twelve affected audit roots passed with
no unexpected axioms or changed-module warnings. Evidence is in
`build/c-factory/count-history-full-gate-v2.log` and its JSON record; the earlier
failed attempt is retained separately. Only the three verification/roadmap
documents change after this frozen gate.

Retained archives and comparisons are in
`build/c-factory/count-history-artifacts-v1/` and adjacent JSON records. Every
FMU member, including the native library, is unchanged from the prior retained
count-runtime artifact. The eFMU changes only generation identities and their
dependent references/checksums in three manifests. Numerical C, GALEC and
eFMI Production C are unchanged.

This initialization checkpoint alone excludes later ME simulation/control
interleavings; the accepted extension above supplies them. Nominal queries,
logging configuration, remaining public calls,
native/ABI correspondence and K02–K05 also remain open. Grammar expansion is
blocked.

**Count-query repair and shared runtime (2026-09-14, full gate passed):**
The count queries now use the FMI 3.0.2 call-table restriction to ME
Instantiated and Event Mode. The earlier predicate and emitted guard also
accepted Initialization, Continuous-Time and Terminated; the old
`terminated_me_queries` theorem incorrectly grouped counts with final-value
accessors. Both the reference predicate and generated policy are corrected,
with an explicit rejection theorem and an update to the existing native check.
This is a standards-driven behavior correction, not a grammar expansion.

`CountQueries.FunctionContract.prepared` strengthens the mandatory adapter
proposition with success/null and suppressed/enabled logging contracts in the
shared creation/lifecycle interface. It uses the existing C machine, interface
transport and failure-helper proofs. The actual function table and pool supply
the contract for every later literal-preserving heap. Returning logger effects
may branch; no returning outcome is modeled as a blocked call, without assuming
native callback termination. `QuietContract.returned` derives the status,
Solve state volume or zero event count, and output-only frame from an arbitrary
returned execution. `counts_runtime_source` binds these contracts to actual
numerical C, adapter fragments and XML metadata.

The required `nix develop .#verification --command lake test` passed at
19:55:08 UTC on 1009 unchanged inputs, including the actual FMU/eFMU contracts
and existing importer, ABI, native and rejection checks. Nine new and ten
affected audit roots passed with no unexpected axioms or changed-module
warnings. Evidence is in `build/c-factory/count-runtime-full-gate-v1.log` and
its JSON record. Only the three verification/roadmap documents change after
that frozen gate.

Retained archives and comparisons are in
`build/c-factory/count-runtime-artifacts-v1/` and adjacent JSON records. Relative
to the previous retained CS artifacts, the FMU changes only the two count guards
in `sources/fmi3.c` and the rebuilt shared library. The eFMU changes only fresh
generation identities and their dependent references/checksums in three
manifests. Numerical C, GALEC and eFMI Production C are unchanged. Count
observations still need integration into the recurring source-bound histories.
Remaining public calls, native/ABI correspondence and K02–K05 keep expansion
blocked.

**Source-bound recurring ME protocols (2026-09-14):**
`MEProtocol.runtime_create_release` now composes actual creation, repeated
initialization/simulation/reset segments and final release in one source-bound
printed/prepared program and literal pool. The factory supplies the handle,
finite Solve default and reservation. Original caller storage and the universal
logger policy supply every later handoff; no future valid heap, successful call
or callback return is a premise.

Each completed cycle retains initialization readbacks, unique source IVPs at
actual exits, ME derivative observations and every internal restart checkpoint.
`SourceTrace` keeps earlier cycles when later resets overwrite runtime state.
`Contract.released` derives mode-appropriate termination/free calls and the
creation theorem restores the original owner map and protected-memory frame.
ME trial states and clocks remain importer-selected; the source theorem does
not prove the correctness of an external integration algorithm.

Raw completed/stopped plans sequence the existing initialization and ME
execution relations. Between-cycle reset results remain unrestricted in that
raw relation; complete C call contracts derive their successful status and heap
and exclude a blocked reset. `interrupted_iff` proves equivalence of the stopped
and recorded-prefix views. `interrupted_correct` preserves source observations
before every modeled blocked initialization or simulation call, including all
earlier cycles. No returned value, checkpoint or release is attributed to the
pending call. `progress_source` exposes both source-bearing alternatives without
assuming logger totality. Native callback termination is outside this model.

The generic initialization-prefix definition and proof now live in their own
compiler module. Both interfaces reuse it; the CS theorem retains its statement.
The new plan/cycle structures belong to the FMI backend and compose existing
call semantics rather than introduce a second C or numerical machine.

Twenty new and six affected roots passed the FMI/compiler package gate on
1007 unchanged inputs at 18:37:14 UTC in
`build/c-factory/me-cycles-package-v1.log`, with no unexpected axioms or
changed-module warnings. Only the three verification/roadmap documents change
after the frozen gate. Grammars, source/Solve/C machine semantics, emitters,
mandatory artifact propositions and boundary tests are unchanged.
[GitHub run 34871354671](https://github.com/CogniPilot/rumoca_lean/actions/runs/34871354671)
passed the full `lake test` gate for the earlier the previous checkpoint revision at 18:15:01
UTC. This increment still needs its own full-artifact acceptance. Remaining
public-call coverage, native/concurrent correspondence and K02–K05 prevent a
whole-compiler or full-standard claim; grammar expansion remains blocked.

**Source-bound CS completed and stopped observations (2026-09-14):**
`CSProtocol.runtime_create_release` connects actual source-bound static creation,
recurring initialization/simulation/reset segments and final release. Its
completed source trace now retains every intermediate DoStep record and every
internal restart's three public call records, alongside explicit initialization
checkpoints and segment-final samples. Later resets do not erase earlier
observations. Original storage and the universal external-effect policy supply
every handoff; no later valid heap, successful call or callback return is a
host premise.

`CSRun.Recorded` exposes actual return statuses, events and heaps.
`recorded_iff` proves that adding these records neither adds nor excludes an
existing raw completed execution. Raw statuses remain unrestricted by expected
outcomes. `SemanticTrace` annotates those exact records with the existing
reference transitions under the same fixed floating-environment header.
Both quiet and branching logger contracts derive this annotation universally.
The raw definitions moved to an independent module and now support arbitrary
event types; no second C or numerical execution semantics was introduced.

`SemanticTrace.source_observations` supplies a unique source Real IVP and the
existing numerical/clock error bound at every completed step's stored state.
Successful steps retain all four public outputs. Failed output buffers are not
claimed to contain valid source observations. Each internal restart derives
all three successful statuses and its initialization-exit source checkpoint.
`CSExecution`, recurring cycle evidence and the actual-source-bound release
theorem carry these stronger conclusions with their original ownership,
caller-storage and memory-frame guarantees.

`CSProtocol.interrupted_correct` now proves source correspondence for every
modeled stopped prefix of an admitted CS plan. Raw `Interrupted` views for
initialization, simulation and recurring plans are equivalent to their existing
`Stopped` relations. They retain actual completed observations and the pending
call, with an explicit decomposition of the original script. Completed-prefix
certificates supply initialization readbacks/checkpoints and each CS step's
source sample, error bound and successful outputs. Earlier cycles retain their
complete evidence. No later execution or callback return is assumed.

The stop record's heap precedes the pending action; it is not a returned heap.
No returned status, numerical output, exit checkpoint or release is attributed
to that blocked action. `ActionContract.faulted_step` excludes partially
completed internal restarts, and the reset call contract excludes a blocked
between-cycle reset. These are conclusions about the existing C/effect model,
not native callback termination or a native hang trace. The source-bound
creation theorem now supplies this stronger `Contract`; `stopped_source` and
`progress_source` expose its stopped and completed source alternatives.

ME's recurring composition and stopped-source correspondence, remaining public
calls, native/concurrent correspondence and K02–K05 remain unfinished. This
does not establish full CompCert-level coverage or permit grammar expansion.

Nineteen new and eight affected roots passed the existing FMI/compiler package
gate on 998 unchanged inputs in
`build/c-factory/stopped-source-package-v1.log`, with no unexpected axioms or
warnings in new/changed modules. Publication subsequently changes only the
three verification/roadmap documents. The admitted grammars, source/Solve/C
machine semantics, emitters, mandatory artifact propositions and boundary tests
are unchanged. [GitHub run 34868166166](https://github.com/CogniPilot/rumoca_lean/actions/runs/34868166166)
passed `nix develop .#verification --command lake test` for the previous checkpoint at
17:24:44 UTC. That full artifact result belongs to an earlier revision; this
package pass is not a new full-artifact acceptance.

**CS raw restart outcomes and history progress (2026-09-14):**
Review found that `CSRun.Performed.restart` required all three return codes
to be zero. Earlier claims that raw CS histories derive arbitrary returned
statuses were therefore too broad for that macro. The raw relation now admits
arbitrary integer codes for reset, initialization entry and initialization
exit. `ActionContract.restart_returned` proves that each is zero from the
complete C call contracts, and the existing history/status/source theorems
retain their conclusions for the enlarged relation.

`CSRun.ActionContract.performed_iff` and `.faulted_iff` characterize both the
returning and blocked alternatives. `Faulted` retains intermediate calls when
a restart stops; `Stopped` retains the actually executed script prefix.
`LoggedTrace.progress` proves that every finite certified script has a
completed execution or an actual blocked prefix. It assumes neither callback
return nor determinism. Blocking is in the existing external-effect/C machine
model; this is not a theorem about native callback termination.

`adapter_logged_cs_run_history` now exposes that progress result and accepts
arbitrary observed status lists, deriving their equality to the reference
list alongside the source Real IVP and numerical error bound. Its original
storage, ownership, bindings and universal callback frame remain explicit.

Six new roots and seven affected roots passed the existing FMI/compiler
package gate on 985 unchanged inputs in
`build/c-factory/cs-raw-progress-package-v1.log`; all required audit roots were
present, with no unexpected axioms or warnings in the changed modules.
Source/Solve and C machine semantics, emitters, mandatory artifact propositions
and boundary tests are unchanged. The raw CS history relation is broader.
This package pass is distinct from the retained full-artifact results.
Repeated initialization/simulation/release composition and K02–K05 remain
open; grammar expansion is still blocked.

**Simulation storage and source-bound restart protocols (2026-09-14):**
`InitializationProtocol.runtime_restart_source` binds actual reset and the
existing initialization protocol to compiled source, numerical C, XML metadata
and one printed/prepared adapter table and pool. Reset obtains the Solve default
and initialization invariant from the current writable runtime storage and
represented kind/mode; no future finite payload or valid initialization heap
is assumed. The original source theorem now exposes its already-proved
lifecycle environment for reuse.

`RestartSourceContract.progress` and `.completed` reuse `Completed`/`Stopped`
with a leading reset action. They derive the raw reset status/events, subsequent
accepted/rejected access observations, actual exit/source-IVP checkpoints,
ownership, caller storage and memory frames. The protocol can reset and fail
again. A non-returning logger retains a real blocked-call prefix.

ME and CS simulation certificates now retain arbitrary caller object regions
under a universal logger storage policy. This preserves domains, types and
permissions, so initialization reference/value buffers can survive simulation.
The existing callback frame still protects instance values and public outputs;
the additional policy assumes neither return nor determinism. Suppressed CS
call certificates also retain their already-derived storage, atomic and field
frames. Typed output-list updates permit compatible aliases, and both
interfaces reuse one reset/entry/exit storage proof.

`restart_after_me`, `restart_after_cs_logged` and
`restart_after_cs_suppressed` derive reset/reinitialization premises from actual
completed simulation histories and original resources. Their initialization
compiler argument is the universal source contract supplied by `runtime_source`;
it is not a host assertion about a selected future heap or successful call.
The existing numerical/source/status guarantees remain in the same histories.

All 33 new roots and affected existing roots passed
`lake build check-c check-fmi3 check-compiler` on 984 unchanged inputs in
`build/c-factory/simulation-restart-package-v1.log`. No new-module warnings or
unexpected axioms were reported. Source/runtime semantics, emitters, mandatory
artifact propositions and boundary tests are unchanged; derived certificates
were strengthened. The package gate is distinct from the retained 869-input
local full gate. GitHub run `34856771664` passed the complete gate for the previous checkpoint
at 15:47:48 UTC; that is a separate revision, not full acceptance of this change.

A single source-bound theorem still needs to compose repeated simulation and
initialization segments through final release, using the existing handoffs and
raw relations. Other public calls, native/concurrent correspondence, complete
artifacts/provenance and standards/MISRA closure remain open. K02–K05 are not
closed and grammar expansion remains blocked.

**Created initialization protocols through ME/CS simulation (2026-09-14):**
`InitializationProtocol.runtime_create_release` now derives the reusable
initialization protocol from actual source-bound static creation. The factory
supplies the handle, finite Solve default, typed storage and reservation. The
same printed/prepared adapter table and pool supply creation, access, lifecycle,
ME and CS contracts. Original caller resources and logger effects remain
explicit; no future heap, field value or successful call is a premise.

The derived memory invariant now preserves protected cell domains, types and
permissions, including scalar simulation outputs as well as array buffers.
The previous writable-array consequences follow from that stronger invariant.
Completed initialization histories retain the unique source Real IVP at each
exit, actual statuses/readbacks, logger configuration and original ownership.
Initialized or failed histories compose with mode-appropriate release.

`CreatedSourceContract.me_continuation` and `.cs_continuation` carry an actual
initialized history into the existing mixed simulation relations. ME derives
Event Mode, initial event-iteration readiness, selected state, clock and stop
bound. CS derives the selected numerical seed and initial step state. Both
transport output storage from the pre-creation heap and retain the existing
suppressed/enabled logger contracts and all modeled returning outcomes.
Completed ME runs retain source derivative observations and reset checkpoints;
CS retains its source epoch and numerical/clock error bound. Release restores
the original owner map and frames protected memory through the entire prefix,
including the ranges used by rejected initialization requests.

All 23 new roots and affected existing roots passed
`lake build check-c check-fmi3 check-compiler` on 977 unchanged inputs in
`build/c-factory/created-protocol-package-v1.log`. The axiom whitelist is
unchanged and the new modules have no warnings. Source/runtime semantics,
emitters, mandatory artifact propositions and boundary tests are unchanged;
only derived storage contracts were strengthened. This package pass is
distinct from the retained 869-input local full-artifact gate and successful
GitHub run `34853259941` for the previous checkpoint; it is not a new full-gate result.

Later simulation restarts still use contiguous reset/enter/exit calls and the
Solve default. Access interleavings at those restarts, remaining public calls,
native/concurrent correspondence, complete artifacts/provenance and the open
standards/MISRA findings remain required. K02–K05 are not closed and grammar
expansion remains blocked.

**Repeated initialization protocols (2026-09-14):**
`InitializationProtocol.runtime_source` binds a reusable initialization
subprotocol to actual source compilation, numerical C, XML state/reference
metadata and one printed/prepared adapter table and pool. Accepted Float64
accesses, rejected accesses, initialization entry/exit and reset are individual
actions. Failed attempts can reset, accept further accesses and fail again;
the history is no longer limited to one contiguous recovery macro.

`Completed.correct` derives successful statuses/readbacks, rejected statuses,
finite instance state, initialization clock/stop configuration, ownership,
read-only memory and protected caller storage from the original invariant.
Every request uses actual typed host stores and the existing C call machine.
Rejection retains arbitrary raw IEEE inputs and the original guard predicates.
The logger policy admits suppressed/missing logging or a bound external effect
with a universal frame; it assumes neither a return nor determinism. `progress`
constructs a completed script or an actual prefix ending at a blocked call.
Detailed callback event alternatives remain in the reused accessor contracts;
the combined observation relation proves statuses and successful readbacks.

Each initialization exit records its actual heap. `Checkpoints.source_ivps`
proves its unique source Real IVP, preserving earlier checkpoints across later
resets. Failed outputs have no numerical observation. `Stored.created` obtains
the initial invariant from the existing factory's initialized-object result;
`Completed.release` derives mode-appropriate release from completed histories
ending initialized or failed. The new source theorem still starts with a valid
instance and caller/logger resources. Composition with the actual source-bound
factory, later ME/CS simulation and repeated simulation restarts remains open.

All 35 new roots passed `lake build check-fmi3 check-compiler` on 970 unchanged
inputs in `build/c-factory/initialization-protocol-package-v1.log`. Its review
record corrects the wrapper's expectation of quoted audit names; the existing
Lean audit reports bare names and checks every required root. No Lean rerun or
axiom-policy change was needed. Only derived proofs/audit imports were added;
semantics, emission, mandatory artifact propositions and boundary tests retain
the distinct 869-input local full gate. GitHub run `34853259941` passed the full
gate for the previous checkpoint, a distinct revision. This is not a new full-artifact result.
K02–K05 and the remaining standards/MISRA findings still block grammar growth.

**Rejected Float64 calls and recovery initialization (2026-09-14):**
`Float64Rejection.runtime_source` supplies the new rejection/runtime and
recovery consequences from actual source compilation, numerical C, XML
numeric/writable-state metadata, accessor function contracts and one prepared
table/pool. It retains the source Real derivative equation. No source case,
runtime policy, emitter or mandatory artifact proposition changes.

`Request.prepare_correct` constructs raw input snapshots through existing
typed caller stores. Arbitrary IEEE encodings include non-finite rejected
writes. Lifecycle/array guard failures need no array transfers or readability
premises; entry checks retain the existing short-circuit read conditions.
Transfer permissions, typed storage, read-only cells and atomic reservations
are preserved. Independent guard predicates still determine the rejection.

`Request.RuntimeContract` combines those transfers with the actual accessor
machine. Suppressed or missing logging has a unique Error result. Enabled
logging retains every modeled returning effect and the blocked alternative.
Each completed raw call determines its actual status/events and establishes
`Returned`: finite instance state/time, recovery storage, ownership, read-only
memory, protected caller storage and the precise memory frame. Original valid
instance/reset storage is explicit; no future heap or successful call is a
premise. The callback contract always protects all instance slots and flags,
and quantifies the additional caller region needed by later operations.

`InitializationAccess.Recovery` reuses reset and the existing accepted
initialization-access certificate. Both ME and CS can perform finite writes
and batched queries before entry and during the new initialization. Raw reset
and access statuses/readbacks are derived; completed recovery determines the
unique source Real IVP at actual exit. `Returned.source_recovery` obtains its
caller storage from the original heap, including buffers reused by the rejected
request. Failed-call output values are not treated as valid model observations.
Reset starts from the Solve default; later finite writes select the new IVP.
The common reset record-frame lemma moved to `ResetStorage` without changing
its statement, and shared reset/mode-write preservation is proved.

The 31 new roots and existing affected roots passed
`lake build check-fmi3 check-compiler` on 963 unchanged inputs in
`build/c-factory/float64-rejection-package-v2.log`; the axiom whitelist is
unchanged. Existing semantics, emission, mandatory artifact propositions and
boundary tests retain the separate 869-input local full gate. GitHub run
`34848939187` passed the full gate for the previous checkpoint, a distinct revision. Neither
is a new full-gate result for these additions. No tests were added.

The new rejection/recovery operations still need integration into the created
initialization and repeating mixed ME/CS histories, including further rejected
accesses during recovery and final release. Other public interactions,
concurrent/native correspondence, complete artifacts/provenance and K02–K05
standards/MISRA closure remain open. Grammar expansion remains blocked.

**Initialization access through mixed ME execution (2026-09-14):**
`InitializationAccess.runtime_create_me_histories` connects actual source-bound
creation and accepted initialization accesses to the existing mixed ME history
and release contracts. The source theorem retains numerical C, XML numeric,
writable-state and derivative metadata, function printing and one prepared
table/pool. The original factory supplies the handle, finite Solve default,
typed storage and reservation. Accepted host writes determine the actual
initialization-exit value and its unique source Real IVP.

`Certificate.me_storage` derives Event Mode, the required initial event
iteration, selected state, initial clock/stop bound and original caller buffers.
`Certificate.configuration` carries the original logger configuration across
initialization accesses. Shared lifecycle and reset-storage proofs now have
common modules; the existing CS handoff and theorem statements are retained.

`Certificate.me_continuation` reuses `MEMixedRun.Trace` and its raw `Completed`
relation. The contract retains the existing suppressed/missing and enabled
logger configurations, returning branches and blocked alternative. Every
completed history derives the actual statuses/query observations, source
derivative equations and source initialization at each reset checkpoint.
Release restores the original owner map. The memory frame reaches the
pre-creation heap for protected cells outside the instance, history outputs,
initialization-access ranges and released flag. The external callback frame
remains explicit. Importer trial-state writes are not claimed to solve the
initial source IVP, and later restarts retain their contiguous reset/enter/exit
protocol and Solve default.

Six new roots and the affected existing roots passed
`lake build check-fmi3 check-compiler` on 955 unchanged inputs in
`build/c-factory/initialization-me-run-package-v2.log`. The first package attempt
identified a missing direct storage-proof import after the module split; that
import was fixed before the passing run. The axiom whitelist is unchanged.
Existing semantics, emission, mandatory artifact propositions and boundary
tests retain the separate 869-input local full-gate evidence. This package pass
is not a new full-gate result. No grammar or test suite was added.

Rejected initialization accesses, access interleavings at later restarts and
other public interactions remain open. K02–K05, including concurrent/native
correspondence, complete artifacts/provenance and standards/MISRA closure, are
not closed. Grammar expansion remains blocked.

**Initialization access through mixed CS execution (2026-09-14):**
`InitializationAccess.runtime_create_cs_histories` connects actual source-bound
creation and accepted initialization accesses to the existing mixed CS histories.
Both suppressed logging (disabled or missing logger) and callback-enabled
histories are covered. The source theorem retains numerical C, XML reference and
writable-state metadata, function printing, one prepared table/pool and original
storage/ownership. The earlier creation theorem now also exposes its storage
frame and common prepared stepping/lifecycle context for reuse.

The actual initialized state supplies the initial run seed. Recovery storage,
logger configuration, clock, stop bound, literals and ownership are derived at
the handoff. Successful/rejected steps and reset/reinitialization then reuse
`CSRun.ReferenceTrace`, `Calls`, `LoggedTrace` and `Completed`; no parallel
simulation relation or new runtime policy was introduced. Later reset still
selects the Solve default and performs contiguous reset/enter/exit calls.

For suppressed logging the theorem constructs a completed script and proves
its raw status list, empty event list and final heap. For enabled callbacks it
retains every modeled returning branch and the existing blocked alternative;
no callback return is presumed. Every completed history retains a readable
finite numerical sample, the source epoch and existing numerical/clock error
bound. Mode-appropriate release and `RunOutcome.restored` restore the original
owner map. The combined frame reaches the pre-creation heap for protected
cells outside the instance, initialization-access ranges and step outputs.
Private logger memory is governed by the explicit external frame contract.

Ten new roots and the strengthened creation root passed
`lake build check-fmi3 check-compiler` on 951 unchanged inputs in
`build/c-factory/initialization-cs-run-package-v1.log`. Existing semantics,
emission, mandatory artifact contracts and boundary tests are unchanged;
their separate 869-input local full gate is retained. GitHub run `34842923078`
also passed the full gate for the previous checkpoint, a distinct earlier revision. Neither
result is a new full-gate pass for these additions. No grammar or test suite
was added. Rejected initialization accesses, ME continuation, interleaved
accesses at later restarts and other public interactions remain open, alongside
K02–K05 and native/concurrent/standards correspondence. Grammar remains frozen.

**Creation through initialization access and release (2026-09-14):**
`InitializationAccess.runtime_create_release` now derives the original handle,
finite Solve default and access-history storage from the actual source-bound
static factory. The same header/object/literal environment and prepared function
table supply creation, accepted Float64 accesses, initialization and release for
both ME and CS. Identity/library bindings, available original typed storage,
valid caller buffers and admitted finite requests remain explicit premises.

Every accepted initialization script is constructed; every completed raw script
determines its statuses/readbacks, selected source Real IVP and unique solution.
State writes before and during initialization supply the actual exit value.
The strengthened certificate preserves typed storage and atomic reservation
cells. Ordinary checked stores cannot change atomic cells, so retaining leases
does not require new caller-buffer separation from the reservation block.
Mode-appropriate termination and release restore the original owners and retain
the combined frame outside the instance, caller ranges and released flag.

`Certificate.cs_storage` establishes the existing executable CS invariant using
the final overridden state as its seed, start clock, configured stop bound and
original step-output storage. It is a proved handoff; later CS step histories
have not yet been composed with this initialization-access prefix. Rejected
accesses, modeled logging/recovery, later ME/CS simulation and other public
interactions also remain to be composed. No concurrent-host or native ABI claim
is added, and K02–K05 remain open.

The 15 new roots and affected existing roots passed
`lake build check-c check-fmi3 check-compiler` on 947 unchanged inputs in
`build/c-factory/created-access-package-v1.log`. Existing semantics, emission,
mandatory artifact contracts and boundary tests are unchanged and retain their
separate 869-input full-gate evidence. This is not a new full-gate pass. No
grammar case or test suite was added; grammar expansion remains blocked.

**Accepted initialization access histories (2026-09-14):**
`InitializationAccess.runtime_source` binds accepted batched Float64 histories
to actual source compilation, numerical C, XML reference/writable-state metadata,
function-section tokenization and one prepared runtime table/pool. Both ME and CS
are covered. Original typed instance/caller storage, disjoint buffer blocks,
representable request counts and admissible initialization arguments are explicit.

Before initialization entry, histories admit state start-value reads and finite
state writes. During initialization, queries may mix/repeat time, state and
derivative references. Typed host stores construct each reference/value buffer;
later contents or successful target executions are not premises. Empty batches
are included. Shapes describe host access batches without admitting tensor source
models or enumerating source operations during lowering.

`Float64Access.Calls.execution_iff` and
`InitializationAccess.Certificate.execution_iff` prove existence and uniqueness
of the completed raw script, including every returned event, status and bounded
readback. Each constituent call also retains its all-behavior contract.
`Certificate.completed_source` proves that the actual exit state selects a unique
source Real IVP. Finite writes before and during initialization determine that
state; the proof does not reuse the earlier contiguous entry/exit heap. Clock
storage, caller storage, read-only diagnostics and memory outside the written
ranges/fields persist. The certificate retains exact named fields before entry
and at exit, including stop-time and instance-metadata evidence for later histories.

All 41 roots passed `lake build check-fmi3 check-compiler` on 942 unchanged
inputs in `build/c-factory/initialization-access-package-v2.log`. Only the three
status documents changed afterward. Existing semantics, emission, mandatory
contracts and tests retain the separate 869-input full artifact gate; no new
full-gate pass is claimed. Actual creation, rejected accesses/logging/recovery,
later simulation/release and K02–K05 still need composition/closure. No grammar
case or test suite was added, and grammar expansion remains blocked.

**Initialization-history prerequisites (2026-09-14):**
`InitializationEnvironment.quiet_correct` supplies the existing successful/null
entry and exit contract in the shared runtime. Exit applies independently to
the current heap with its kind and writable initialization-mode cell; it no
longer needs to follow entry immediately. The theorem derives complete call
behavior from the actual definitions, without assuming a successful execution.

`CMemory.ArrayStore` proves indexed caller-buffer preparation through ordinary
typed stores. Original writable cells and conversion identities establish exact
readback; every successful transfer preserves the storage domain, types,
permissions and read-only contents. A separate frame covers all other cells.
These are host memory operations, not emitted tensor lowering or new grammar.

The six roots passed `lake build check-c check-fmi3 check-compiler` on 937
unchanged inputs in `build/c-factory/initialization-prerequisites-package-v1.log`.
Only the three status documents changed afterward. Existing semantics, emission,
mandatory contracts and tests retain their separate 869-input full artifact
gate; this package pass is not a new full-gate result. Interleaved initialization
histories must still derive every later buffer/heap and the source IVP at actual
exit. No K02–K05 item or grammar-expansion gate is closed by these prerequisites.

**Float64 reads and writes share the runtime (2026-09-14):**
`float64_runtime_source` binds both actual accessors and the RHS helper to one
compiled source, numerical C program, XML reference/writable-state metadata,
function-section tokenization and prepared table/pool. It derives the getter's
new `Float64Environment.PreparedContract` alongside the existing setter runtime
contract, for the same header/object/literal environment and later heaps.

The getter retains arbitrary represented batch lengths, mixed/repeated numeric
references, validation before output writes and exact time/state/derivative
readback in request order. Original input/output storage, finite state/time and
the existing separation conditions are explicit. Derivative queries execute
`model_rhs` and the actual numerical RHS without advancing the solver. The
existing `get_refines` consequence preserves state/time and frames every cell
outside the output range.

Empty and failure prefixes use only the accessor definition. They do not acquire
numerical/helper bindings, finite-state or writable-output premises merely to
transport their proofs. Null calls and existing array/reference rejections are
retained. Disabled/missing logging and all modeled enabled-callback outcomes,
including no return, use the actual runtime error helper. Callback read-only
preservation is explicit; protected-instance ownership frames belong to history
composition.

All nine roots passed `lake build check-fmi3 check-compiler` on 935 unchanged
inputs in `build/c-factory/float64-environment-package-v1.log`. Only the three
status documents changed afterward. Earlier semantics, emission, mandatory
contracts and tests retain the separate 869-input full artifact gate and
unchanged archives; no new full-gate pass is claimed. Initialization histories
must still derive the selected source IVP from the actual state at exit and
distinguish start-value reads from initialization evaluation. K02–K05 and grammar
expansion remain open/blocked. No source case or test suite was added.

**Float64 setter in the shared runtime (2026-09-14):**
`float64_set_runtime_source` connects actual source compilation, numerical C,
writable-state metadata, function-section tokenization and the emitted setter
to `Float64SetEnvironment.PreparedContract`. The existing complete setter
contract now holds in the header/object/literal interface used by creation and
lifecycle calls, including later heaps preserving the installed diagnostic pool.

The successful contract retains arbitrary representable batch lengths, the
original tensor-shaped input snapshot, validation before writes, exact finite
payloads and the final-request state update. Empty and null calls and all
existing lifecycle/array/entry rejection cases are preserved. Suppression covers
both a disabled flag and a missing logger. Enabled logging retains every modeled
returning effect, its actual invocation and the no-return alternative; only the
effect's read-only frame is imposed here. Ownership and protected instance frames
must still be supplied when composing histories.

The shared `internal_reaches_interface` theorem transports internal prefixes,
including loops and kernel calls, into a larger runtime with agreeing types,
literals, used syntax, numerical kernel, address table and existing definitions.
Additional target functions and callbacks are unrestricted. The proof fragment's
absent externals are used only for silent prefixes; the complete failure suffix
uses the actual target callbacks. No successful target execution is a premise.

All ten roots passed `lake build check-c check-fmi3 check-compiler` on 933
unchanged inputs in `build/c-factory/float64-set-environment-package-v1.log`.
Only the three status documents changed afterward. Earlier semantics, emission,
mandatory contracts and tests retain the separate 869-input full artifact gate
and unchanged archives; no new full-gate pass is claimed. Getter integration,
intervening initialization histories and K02–K05 remain open. No source case or
test suite was added.

**Created mixed ME lifetime (2026-09-14):**
`MEMixedRun.runtime_create_release` derives actual creation, initialization,
mixed numerical/control/error/reset histories and final release from original
static storage and owners. The factory supplies the handle, finite Solve default
and lease before the importer selects its history. Caller buffers belong to the
pre-creation heap; logger configuration follows the original factory arguments.
Subsequent storage, configuration, slot metadata and ownership are derived.

Every completed actual history retains source derivative observations and the
source initialization/uniqueness of every actual restart checkpoint. The initial
checkpoint also satisfies source initialization with the created finite default.
The full branching certificate retains suppressed, missing and enabled logger
paths, every modeled returning effect and the no-return alternative. The
universal external frame remains explicit, with no presumed callback return.

`LifecycleRelease.finish_correct` supplies a common interface-level suffix:
active states terminate before release; an Error/Terminated state releases
directly. The actual release restores the original owner map and preserves
protected unrelated memory. It grants no future validity to the released handle.
The source, numerical C, function-section tokenization and derivative/state
metadata remain bound to the same compiled artifact.

All seven added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-mixed-lifetime-package-v2.log` on 930 unchanged inputs.
The first package attempt exposed a missing direct import of an existing storage
lemma; the import was corrected without changing a proof body. Only the three
status documents changed after acceptance. Earlier semantics, emission, mandatory
contracts and tests retain the separate 869-input full artifact gate and unchanged
archives; no new full-gate pass is claimed. Intervening initialization accesses,
remaining public APIs, concurrent ownership, complete artifact/native correspondence
and standards/MISRA closure keep K02–K05 open. No grammar or test suite was added.

**Mixed ME rejection/recovery histories (2026-09-14):**
`MEMixedRun.runtime_history` derives a branching certificate for finite admitted
mixtures of numerical/control calls, rejected requests and reset/reinitialization.
The same compiled table, diagnostic pool, numerical C and derivative/state
metadata supply every call. Rejection selection uses reference state, raw
arguments and clock bounds. Optional importer stores preserve all IEEE bit
patterns, including non-finite setter inputs; later buffer contents are derived.

`ActionContract.returned` and `ActionContract.realizes` connect every returning
alternative to actual target calls in both directions. Enabled logging retains
all modeled effect outcomes and the no-return alternative. No returning logger
or final heap is presumed. Disabled logging and a missing logger are covered by
the same history construction. Logger configuration remains fixed, with a
universal external frame protecting instance/reservation storage and reusable
caller buffers; private logger storage may change.

For every completed raw script, `Trace.completed` derives final numerical/reset
storage, ownership, diagnostic preservation and the protected memory frame.
`Trace.source` derives success/Error statuses, source Real agreement for every
successful derivative query, and source initialization/uniqueness at each actual
restart checkpoint. Failed-call outputs receive no numerical guarantee. Importer
trial states and debugging getters after Error do not authorize continuation of
the original simulation or establish an IVP trajectory.

All 15 added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-mixed-run-package-v1.log` on 927 unchanged inputs. Only the
three status documents changed afterward. Earlier semantics, emission, mandatory
contracts and tests retain the separate 869-input full artifact gate and unchanged
archives; no new full-gate pass is claimed. Original valid non-null instance and
caller storage remain premises. Creation/release composition for these histories,
intervening initialization accesses, remaining public interactions and K02–K05
remain open. No grammar case or test suite was added.

**ME rejection and recovery (2026-09-14):** `MEFailure.Request.prepared`
unifies the existing rejection contracts for state/derivative access, time,
event/continuous entry, integrator completion and discrete updates. The request
retains actual arguments and the corresponding admission predicate. Window
rejections require bounds represented by the instance's memory. The same compiled
table and literal pool provide suppressed and enabled-logging contracts.

`MEFailure.runtime_recovery` binds these contracts to source compilation,
numerical C, function-section tokenization and derivative/state metadata. For
every completed covered error call on a valid non-null instance, it derives the
Error status, callback arguments, retained storage, diagnostic preservation and
ownership. The enabled case retains all modeled returning effects and the
no-return alternative. A universal external frame protects the instance pool,
reservation storage and caller buffers while permitting private logger effects.
Native callback execution remains an external boundary.

Each returned branch supplies complete reset/entry/exit calls and source
initialization at the new requested time. `Recovery.executed_source` derives all
three raw statuses and source validity at the actual initialization checkpoint.
Retained storage gives no numerical meaning to the failed call's output arguments.
Original typed instance/caller storage, recovery permissions and represented
owners remain premises. Arbitrary mixed accepted/rejected histories and their
creation/release composition remain open.

All 15 added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-failure-recovery-package-v1.log` on 923 unchanged inputs.
Only the three status documents changed afterward. Earlier semantics, emission,
mandatory contracts and tests retain the separate 869-input full artifact gate
and unchanged archives; no new full-gate pass is claimed. No grammar case or
test suite was added. K02–K05 still block grammar expansion.

**Created ME numerical/reset lifetime (2026-09-14):**
`runtime_create_me_run_release` derives actual creation, initialization, finite
interleavings of accepted ME control/state/derivative operations and repeated
reset/reinitialization, then termination and atomic release. Original available
storage supplies the handle, finite Solve default and lease before the importer
chooses its history. Caller buffers belong to the pre-creation heap; subsequent
storage, slot metadata and ownership are derived. Release restores the original
owner map and preserves unrelated memory.

Each restart expands to three observable calls: reset, initialization entry and
initialization exit. `Executed` records arbitrary statuses and intermediate heaps;
`Calls.determines` derives all statuses, query results, final memory and the exact
initialization checkpoints. Every actual checkpoint satisfies source Real
initialization with its unique selected trajectory at the requested restart
time. Every derivative query agrees with the source equation. Later importer
trial states are not asserted to follow those trajectories. The same source
artifact supplies numerical C, function-section tokenization and derivative/state
metadata. Accepted calls do not invoke the configured logger.

All 17 added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-numerical-run-package-v1.log` on 919 unchanged inputs.
Only the three status documents changed afterward. Earlier semantics, emission,
mandatory contracts and tests retain the separate 869-input full artifact gate
and unchanged archives; no new full-gate pass is claimed. Original typed storage,
caller-buffer separation, admitted host protocol and explicit external C/library
bindings remain premises. The restart sequence is contiguous; intervening
initialization accesses, rejected calls and enabled-callback histories still need
composition. Remaining public interactions, concurrent ownership and complete
artifact/native correspondence are open. K02–K05 still block grammar expansion.

**Mixed ME numerical histories (2026-09-14):** `adapter_me_environment`
supplies control, state and derivative contracts from one compiled table and
literal pool, retaining independent function-section tokenization and the full
prepared failure/logging contracts. `MENumericalHistory` composes every finite
admitted interleaving of ME controls, importer state updates, state readback and
derivative queries. Caller input stores, later writable storage, control outputs,
intermediate states, read-only diagnostics and memory frames are derived.

The target `Executed` relation records arbitrary statuses, events and raw query
values. It requires neither expected control flags nor finite/correct results.
`Calls.determines` derives the observed list and final heap. The compiler theorem
`runtime_me_numerical_history` retains source compilation, numerical C and
derivative/state metadata and proves source Real equation agreement for every
returned derivative query. Importer trial states are not asserted to lie on an
original-IVP trajectory.

All 24 added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-numerical-history-package-v1.log` on 910 unchanged inputs.
Only the three status documents changed afterward. Earlier semantics, emission,
mandatory contracts and tests retain the separate 869-input full artifact gate
and unchanged archives; no new full-gate pass is claimed. Valid initial instance
storage and separate typed caller buffers remain premises. Creation,
initialization, reset, rejected histories, callbacks and release still need
composition around these mixed histories. K02–K05 and grammar expansion remain
open and blocked, respectively.

**ME control runtime bridge (2026-09-14):** `MEControlEnvironment`
derives complete event/continuous entry, integrator-completion and discrete-update
calls in the explicit header/object/literal runtime used by state and derivative
access. Time-call rejection/logging also uses this runtime; its quiet-call
contract was already available. Existing body execution and failure-prefix
proofs supply the result. Null, rejected, suppressed-logger and all modeled
enabled-callback outcomes retain the existing contract types.

The 21 added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-controls-environment-package-v1.log` on 904 unchanged inputs.
Only the three status documents changed afterward. Earlier semantics, emission,
mandatory contracts and tests retain the separate 869-input full artifact gate
and unchanged archives; no new full-gate pass is claimed. This bridge still
requires actual definitions, typed storage and diagnostic bindings. Supplying
all control/numerical contracts from one compiled table/pool and composing mixed
ME histories remain next. K02–K05 and grammar expansion remain open/blocked.

**ME derivative runtime and source correspondence (2026-09-14):**
`adapter_me_numerical_environment` supplies state getter/setter and derivative
getter contracts from one actual table and literal pool. Their actual accessor
and helper fragments and existing mandatory contracts are retained.
`ModelRhsRuntime` proves the helper under explicit type/symbol bindings;
`DerivativeEnvironment` follows public entry through `model_rhs`, the numerical
C kernel, the caller output write and the returned status in the shared runtime.

`runtime_derivative_source` connects actual source compilation, numerical C and
derivative/state metadata to this call. It derives the returned finite value's
equality to Solve's derivative, its equivalence to the source Real equation
through the existing lowering theorems, and the output memory frame. No getter
execution or post-call heap is an input premise. The current unit RHS is state
independent; arbitrary host trial states do not establish an IVP trajectory.

Null, lifecycle/access rejection and disabled, missing or enabled logger cases
are retained. Later failures require preserved read-only diagnostics. The full
enabled callback contract includes every modeled returning effect and its
no-return alternative; native callback behavior is still an external boundary.

All eleven added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-derivative-environment-package-v1.log` on 903 unchanged inputs.
Only the three status documents changed afterward. Earlier semantics, emission,
mandatory contracts and tests retain the separate 869-input full artifact gate
and archives; no new full-gate pass is claimed. ME control/state/derivative
histories, creation/release composition for those histories and K02–K05 remain
open. Grammar expansion is still blocked.

**ME state-access runtime bridge (2026-09-14):**
`adapter_state_environment` derives getter/setter contracts in the same explicit
header/object/literal interface as creation and lifecycle histories. Both actual
accessor fragments, their existing mandatory contracts and the prepared literal
pool belong to the same compiled source and Solve product. Successful and null
calls work on arbitrary heaps satisfying their typed storage premises. Rejected
calls work on every later heap preserving the pool's read-only cells.

`StateEnvironment` retains lifecycle, pointer/count and non-finite rejection,
both disabled and missing logger paths, and the existing complete enabled-callback
contract. Every modeled returning effect and the no-return alternative remain.
No future successful call or callback execution is supplied as a premise. The
existing getter/setter refinement theorems now apply in this shared environment;
a host trial-state write does not establish an original-IVP trajectory.

The six added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-state-environment-package-v1.log`, with all 900 inputs unchanged.
Only the three status documents changed afterward. Earlier semantics, emitters,
mandatory contracts and tests are unchanged, retaining the separate 869-input
full artifact gate and its archives. No new full-gate pass is claimed. Derivative
query transport, ME numerical/history composition, remaining public interactions
and K02–K05 remain open; this does not authorize grammar expansion.

**Created callback-enabled CS lifetime (2026-09-14):**
`adapter_create_logged_cs_release` now derives actual source-bound creation,
initialization and the branching mixed step/rejection/reset history from
original available static storage and matching logger configuration. The actual
factory supplies the handle, finite Solve default and lease. Every completed
actual history admits termination/release according to its final mode, restores
the original owner map, and retains the source IVP and numerical/clock error.
There is no assumed post-creation or post-callback heap or lease.

The new `ActionContract.performed_status` and `LoggedTrace.statuses_eq` prove
that observed return statuses equal the reference statuses. The lifetime theorem
quantifies over arbitrary observed status lists and derives this equality;
it does not assume expected statuses when selecting completed executions.
The full branching certificate remains in the conclusion, including each
modeled callback alternative and the no-return case. A completed final heap
is not existentially promised if the logger has no returning outcome.

The universal callback frame remains explicit. It protects the instance pool,
reservation storage and caller outputs while allowing private logger effects.
The final lifetime frame covers protected cells outside the selected instance,
caller outputs and released flag. The theorem grants no future-call validity
to a released handle and no new getter contract after an error.

All three added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/cs-logged-lifetime-package-v1.log`, with all 898 inputs unchanged.
Only the three status documents changed afterward. Earlier semantics, emission,
mandatory contracts and tests are unchanged; their separate 869-input full
artifact gate and retained archives remain the evidence. No new full-gate pass
is claimed for these derived proofs. Remaining public interactions, ME numerical
histories, concurrency, complete artifact/native correspondence and standards/
MISRA review keep K02–K05 and the grammar expansion gate open.

**Callback-enabled mixed CS histories (2026-09-14):**
`adapter_logged_cs_run_history` derives a branching contract for accepted and
rejected steps interleaved with reset/reinitialization. `ActionContract` retains
complete actual calls, callback names/arguments and every modeled returning
outcome. If the returning-effect relation has no outcome, the existing authored
semantics exposes `wrong`; no successful callback or continuation is invented.
`LoggedTrace` supplies a continuation for every returned branch, preserving
intermediate finite state, successful outputs, logger configuration and owners.

The external `Logger.Respects` premise universally preserves the FMU instance
pool, reservation block and caller outputs. It permits effects on other private
storage, including private atomics, and requires neither determinism nor a
return. This is an explicit external memory contract, not a proof of arbitrary
native logger code. `Performed` and `Completed` specify actual C-machine call
sequences without source/Solve invariants. Their preservation theorem derives
final storage, ownership and protected memory frames; the compiler consequence
retains the source IVP and numerical/clock error bound for every completed
script. The source index is explicitly shared with Solve.

All 11 added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/cs-run-logging-package-v1.log`, with all 896 inputs unchanged.
Only the three status documents changed afterward. Earlier semantic definitions,
emission, mandatory contracts and tests are unchanged; the separate 869-input
full artifact gate and retained archives remain their evidence. No new full-gate
pass or example suite is claimed for this derived increment.

Actual creation/release composition for these enabled-logging histories,
remaining public interactions, ME numerical histories, concurrent hosts and
native ABI/floating-environment correspondence remain open. The existing
returning-effect model does not prove native callback divergence or reentry;
FMI prohibits log callbacks from calling back into the FMU. Broader single-call
contracts are retained. K02–K05 remain open and grammar expansion stays blocked.

**Created mixed CS lifetime follow-up (2026-09-14):**
`adapter_create_cs_run_release` derives actual source-bound creation,
initialization, mixed accepted/rejected steps, repeated reset/reinitialization
and release from the original available static storage and owner map.
The selected handle, initial finite Solve default, every subsequent heap,
successful outputs and final release ownership are derived. Each reset starts
a new source IVP; the final readable state retains its source-solution
numerical/clock error bound. No post-creation or future-call storage/lease is
supplied by the host.

`CSRun.trace_framed` preserves cells outside the selected instance and caller
outputs. `ReferenceTrace.can_finish` derives that the final mode is Step or
Terminated. `finish_correct` terminates Step before release and releases an
already terminated error path directly. The composed frame covers creation through release, and
release restores the original owner map. The theorem grants no subsequent
validity to a released handle. A stored-value error bound after a rejected call
does not authorize continued simulation or assert a new public getter contract.

The 16 added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/cs-run-lifecycle-package-v1.log`, with all 893 inputs unchanged.
Only the three status documents changed afterward. Existing semantic
definitions, emission, mandatory contracts and tests are unchanged; their
artifact evidence remains the 869-input full gate and retained archives below.
No new full-gate pass is claimed for this derived-proof increment.
Suppressed logging, the explicit library profile and fixed typed caller buffers
remain premises. Callback-enabled histories, ME numerical interactions,
concurrency, complete artifact/native correspondence and standards/MISRA
closure remain open. K02–K05 and the grammar expansion gate remain open.

**Mixed CS run follow-up (2026-09-14):** `adapter_cs_run_history` now derives
arbitrary finite interleavings of accepted steps, rejected calls and repeated
reset/reinitialization from the actual adapter certificate, original valid
storage and suppressed logger configuration. `CSRun.Change` and
`CSRun.ReferenceTrace` specify lifecycle and source-epoch progression without
C execution. Every subsequent heap and writable caller/instance premise is
derived. `CSRun.Calls` retains each actual call, intermediate finite state and
explicit successful outputs, including `lastSuccessfulTime`. Error/discard
outputs are not assigned a standards-level value by the observation relation.

The persistent invariant includes the reset-only writable cells, so a rejected
call does not lose the storage needed for recovery. Reset selects the Solve
default and a new source time origin. `SourceEpoch` states the source IVP and
selected initial value; its unique Real solution and the existing
numerical/clock error bound apply to the actual readable sample. The source
observation explicitly uses the same AST index as Solve. Control fields,
read-only diagnostics and all existing atomic reservations are retained.

The 25 added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/cs-run-package-v2.log`, with all 890 inputs unchanged. Only
the three status documents changed afterward. Earlier semantics, emission,
mandatory contracts and tests are unchanged, retaining the 869-input full
artifact gate and archives below; no new full-gate pass is claimed. These
histories use a fixed typed caller-buffer bank or omitted output pointers,
the explicit nearest-rounding/floor library profile, and logging suppressed
by a missing logger or disabled configuration. Callback-enabled mixed traces,
creation/release composition for this new trace, ME numerical interactions,
concurrency and native correspondence remain open. K02–K05 and the grammar
expansion gate remain open. Earlier records retain their original scopes.

**CS recovery follow-up (2026-09-14):** `adapter_suppressed_recovery` and
`adapter_logged_recovery` connect the mandatory CS rejection contract to actual
reset and both initialization calls in the same header/object/literal interface.
They derive the later writable storage from the original heap. `Restarted`
records complete call behaviors, each intermediate heap, the Solve default and
the unique source IVP at the new requested start time. Reset selects positive
zero for this admitted profile; the previous simulation's initial condition
is not carried into the new source trajectory.

The suppressed path preserves atomic reservations, the original owner map
and slot metadata. The logged theorem retains every modeled returning callback
outcome and the case with no returning outcome. It derives recovery for each
returning outcome that preserves the entire instance record. This is an
explicit external frame premise, not a proof of native callback behavior or
global lease preservation by callbacks. Mixed simulation/recovery/release
histories, callback reentry and concurrent hosts remain open.

The 16 new audit roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/cs-recovery-package-v1.log`, with all 885 inputs unchanged.
Only the three status documents changed afterward. Earlier semantic
definitions, emission, mandatory contracts and tests are unchanged, retaining
the 869-input full artifact gate and archives described below. No new full-gate
pass is claimed for these derived proofs. K02–K05 remain open; grammar expansion
is still blocked. The following records retain their original evidence scope.

**Latest CS checkpoint (2026-09-14):** the actual adapter certificate now
requires `StepCalls.FunctionContract`, composing exhaustive raw-input admission
with complete successful, null, error and discard calls and optional logging.
`adapter_cs_calls` extracts the rendered function and its prepared contract from
that certificate. No successful target execution is supplied as its premise.
The 18 added audit roots passed the full required artifact gate in
`build/c-factory/cs-contract-full-gate-v1.log`, with all 869 inputs unchanged.
The actual FMU/eFMU are retained in `build/c-factory/cs-contract-artifacts-v1/`.
All FMU member contents are unchanged from the preceding CS artifacts. Only
three eFMU manifests differ, in fresh generation identities and dependent
references/checksums; numerical C, GALEC and Production C are unchanged.

Twenty-four subsequent derived roots prove initialized accepted CS lifetimes.
`CSHistory.trace_frame` derives every call and later storage from initial
storage and a separately defined finite reference request history.
`adapter_initialize_cs_release` composes actual initialization, those steps,
termination and atomic release in one prepared program and object interface.
The original lease supplies release ownership; no post-initialization or
post-simulation heap/lease is a host premise. The theorem retains the unique
source IVP and exact finite Solve state. Its source error bound separates
accumulated numerical error from the difference between the reported rounded
clock and the initial time plus elapsed solver duration. It does not assert
exact Real integration at the rounded clock.

The derived roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/cs-history-package-v1.log`, with all 877 inputs unchanged.
They change no preceding semantic definition, emitter or mandatory contract,
so the 869-input full artifact evidence is retained for those components;
the full gate was not rerun for the derived additions. No grammar, existing
test or axiom-policy change is introduced. Original valid storage/ownership,
the explicit target header, ordinary library calls and atomic external
semantics remain premises. At that checkpoint, creation, mixed
error/discard/logging/reset histories, concurrent hosts and native ABI/profile
correspondence remained open.
Released handles are not promised valid for subsequent calls. K02–K05 remain
open, and this checkpoint does not authorize grammar expansion. The following
chronological records retain their original scope and acceptance snapshots.

**CS creation follow-up (2026-09-14):** `adapter_create_cs_release` now composes
the actual source-bound factory with initialization, accepted CS stepping,
termination and release. It starts from available static storage, readable
identity buffers, supported capabilities and the original owner map. The actual
bounded reservation and initializer derive the handle, finite Solve default,
typed writable state/caller storage and lease. No created or initialized heap
is an input premise. The result retains the source IVP and numerical/clock error
bound, all represented call behaviors, bounded reservation trace, memory frame
and restoration of the original owner map after release.

`FactoryEnvironment` instantiates the existing factory proofs in the same
explicit header/object/literal interface used by stepping. The reusable backend
`CSHistory.initialize_release` supplies the shared lifetime composition;
`adapter_initialize_cs_release` retains its exact theorem statement and now
uses that result. Nine new roots passed the FMI/compiler package audit in
`build/c-factory/cs-created-lifetime-package-v1.log`, with all 881 inputs
unchanged. Only the three status documents changed afterward. Earlier semantic
definitions, emission, mandatory artifact contracts and existing tests are
unchanged, retaining the 869-input full artifact gate and its actual archives;
no additional full-gate pass is claimed for this derived-proof follow-up.
Mixed error/discard/logging/reset histories, ME numerical interactions,
concurrent hosts and native profile/layout remain open. This is a sequential
created-instance lifetime, not a whole FMI/eFMI conformance claim or permission
to grow the grammar. The explicit external library/header/atomic boundaries
are retained; the theorem grants no future-call validity to released handles.

**Static storage foundation (2026-09-13):** this working source emits 32
permanent, shared ME/CS instance slots with bounded atomic reservation and
release. Its mandatory adapter contract now includes declaration syntax,
record interpretation, capacity bounds, initial creation/release execution
and consistent foreign bindings. The full artifact gate passed for the
793-input static-runtime snapshot in `build/c-factory/static-runtime-full-gate-v1.log`.
The retained FMU/eFMU and source/member comparisons are under
`build/c-factory/static-runtime-artifacts-v1/` and the adjacent review files.

Thirteen subsequent derived theorems connect the actual source token, literal
pool and function table to creation, exhaustion, input rejection, optional
logging, immediate release/reuse and the stored Solve/source initial value.
Their package audits passed in `static-creation-consequences-packages-v1.log`
and `static-public-consequences-packages-v1.log` under `build/c-factory/`.
The latter check covered 798 unchanged inputs; the full artifact gate was not
rerun for these proof-only additions. Every earlier emitter, semantic
definition and mandatory contract field was retained. The earlier published
the previous checkpoint checkpoint used the allocating emitter.

Seventeen further audit roots now connect creation to both complete public
initialization calls in the same execution interface. A shared body
bisimulation proves that changing unused global bindings preserves all body
behaviors; it does not assume agreement for unrelated factory definitions.
The actual adapter supplies function membership and definitions. Creation
supplies writable storage, initial mode and the finite Solve default; the
composed theorem retains the exact intermediate heaps, initialized clock,
ME Event/CS Step mode, slot metadata and ownership, and the unique completed
source solution. Successful and null initialization calls are covered;
invalid subsequent calls and arbitrary host histories remain open.
`static-initialization-packages-v1.log` passed C/FMI/compiler checks for 801
unchanged inputs, and `static-initialization-packages-v2.log` passed the
strengthened compiler consequence. These logs are under `build/c-factory/`.
No earlier emitter, semantic definition, mandatory contract or audit root
changed. The full main-workspace gate then passed in
`build/c-factory/static-integration-full-gate-v1.log`, with all 801
integration inputs unchanged. Both actual FMU interfaces and the eFMU
passed their existing artifact/native/rejection checks. The adjacent
`static-integration-artifacts-v1/` retains the checked archives; member
comparisons confirm unchanged numerical C, FMI metadata, GALEC and eFMI
Production C. The status-document reconciliation after this gate changes
only these three documentation files; code and audit inputs are identical.

Twenty-two subsequent derived audit roots connect complete initialization
error paths to the same static object environment and actual function table.
They preserve all represented callback outcomes, immutable diagnostic bytes,
and the path with no returning callback outcome. A review found an omitted
case in the earlier error contract: logging enabled with no logger. The new
suppressed contracts cover a missing logger or disabled logging; a theorem
proves that these cases and an enabled supplied logger exhaust the represented
domain. The generated C already handled this case, so no emission changed.
`build/c-factory/static-error-package-gate-v2.log` passed the FMI/compiler
package audits with all 804 draft inputs and all 801 main gate inputs unchanged.
The full artifact result belongs to the preceding 801-input snapshot; these
new derived consequences have separate package evidence. Existing emitters,
semantics, mandatory artifact contracts and audit roots were retained. No new
test suite was added. See `build/c-factory/static-error-review-v1.md`.

Reset now uses this same object interface too. Fifteen further derived audit
roots cover complete successful/null calls and reset followed by both public
initialization calls. Every intermediate heap is explicit; reset supplies the
new initialization storage, restores the Solve default and establishes the
corresponding source IVP. Frame proofs preserve lease flags, slot metadata and
arbitrary nested fields of other instances in the same array. The FMI/compiler
package audits passed in `build/c-factory/static-reset-package-gate-v1.log`
with all 806 inputs unchanged. This adds proofs only: earlier semantics,
emitters, mandatory artifact contracts and audit roots are retained. The
previous full artifact gate still supplies the unchanged C/archive evidence;
it was not rerun for these derived consequences. No new test suite was added.

Termination's complete call contract is now mandatory in
`AdapterContract`. It retains every previous conjunct and adds the exact public
signature, independent tokenization, successful/null behavior, suppressed and
logged errors, and prepared diagnostic storage in the static object interface.
Fifteen new roots also compose initialization through termination with exact
heaps, unchanged finite state/clock, the source IVP and outside-record frames.
The strengthened actual-artifact contract passed the full required gate in
`build/c-factory/termination-full-gate-v1.log`, with all 809 inputs unchanged.
Both checked archives are retained in `build/c-factory/termination-artifacts-v1/`.
C, headers, GALEC and FMI XML are byte-identical to the preceding static-runtime
artifacts. The three eFMI manifests differ only in fresh generation identities
and their dependent references/checksums; exact comparisons and hashes are
recorded beside the archives.

Four further derived roots compose termination with the actual public release
call. Termination preserves slot metadata and ownership flags, supplying the
later release premises from the original host lease. The result discharges
that lease and changes only the selected mode and reservation flag. Both calls
use the same actual definition table and object interface; atomic-store
semantics and valid host ownership remain explicit. The FMI/compiler package
audit passed in `build/c-factory/termination-release-package-gate-v1.log` with
all 811 inputs unchanged. This follow-up changes no emitter or mandatory
contract and retains the preceding full artifact evidence. Released handles
are not declared valid for subsequent FMI calls. No new test suite was added.

The time-call checkpoint also makes `TimeCalls.FunctionContract`
mandatory in the actual adapter certificate, retaining every earlier conjunct.
Twenty-five added audit roots cover the exact `fmi3SetTime` signature and
tokenization, complete successful/null/rejected calls in the static interface,
and suppressed or supplied logging. Admission is defined independently over
finite binary64 values and the reference history window; all raw argument bits
and declared lifecycle modes are classified. The history consequence preserves
model state, bounds, other cells and the source initialization relation. It
does not assert that an unchanged state solves the ODE at a new trial time:
ME integration belongs to the importer.

The FMI/compiler package checks passed in
`build/c-factory/time-package-gate-v1.log` with all 815 inputs unchanged.
The strengthened actual-artifact contract passed the full required gate in
`build/c-factory/time-full-gate-v1.log`, with all 815 inputs unchanged.
Both checked archives are retained in `build/c-factory/time-artifacts-v1/`.
C/header/GALEC and FMI XML bytes match the termination checkpoint; the three
eFMI manifests differ only in fresh generation identities and their dependent
references/checksums. Exact archive/member hashes are recorded beside the
archives. Only these three status documents changed after the full gate;
all code and audit inputs retain its exact checked bytes. No emitter, grammar,
numerical semantics, native test or axiom policy changed.
Valid prior instance/history storage is explicit; arbitrary host histories
remain open.

The ME control checkpoint also requires exact signatures, tokenization
and complete static-interface contracts for event entry, continuous entry,
completed integrator steps and discrete-state updates. Success, null, lifecycle
rejection, missing output buffers and both logging paths are covered. The
generic C output-assignment and pointer-guard proofs live in backend-c; FMI
history and protocol proofs live in backend-fmi3. No emitted code changed.

`MEHistory.trace_frame` composes finite quiescent time/control histories with
every intermediate heap and output value. A discrete update must establish
event-iteration readiness before continuous entry. The trace starts from valid
instance/history storage and a reusable caller buffer bank outside the instance
block; it derives their continued validity, including compatible aliases.
`adapter_me_history` obtains the call contracts from the actual adapter and
retains the source initialization relation and other memory cells. This is a
control-history theorem: state setters, derivative queries, importer integration,
creation-to-operation composition, errors between successful calls and concurrent
hosts still require composition. An unchanged state is not claimed to solve
the ODE at a new trial time.

The 92 added roots passed the C/FMI/compiler package audit in
`build/c-factory/me-package-gate-v5.log`, with all 829 inputs unchanged. The
strengthened actual-artifact contract passed the full required gate in
`build/c-factory/me-full-gate-v1.log`, also with all 829 inputs unchanged.
Both checked archives are retained in `build/c-factory/me-artifacts-v1/`.
C/header/GALEC and FMI XML bytes match the time checkpoint; the three eFMI
manifests differ only in fresh generation identities and their dependent
references/checksums. Exact archive/member hashes are recorded beside the
archives. Only these three status documents changed after the full gate.
No earlier contract/audit root, grammar, numerical semantics, native check or
axiom policy was removed or weakened; no test suite was added.

A derived lifecycle follow-up now composes both initialization calls, finite
ME control histories, termination and release in one actual adapter interface.
Initialization marks the first event iteration incomplete and establishes the
caller-buffer invariant. Typed ordinary writes preserve every existing atomic reservation;
the trace derives the surviving lease instead of requiring it again at release.
The compiler consequence retains the selected source IVP and its uniqueness,
all intermediate calls and outputs, the discharged lease and the final memory
frame. Creation, importer integration, interspersed failures and concurrent
hosts remain outside this history. Released handles gain no future-call validity.
The 19 added roots are integrated into six owning modules. The C/FMI/compiler
package audit passed in `build/c-factory/me-lifecycle-package-gate-v1.log`,
with all 835 inputs unchanged. Earlier emitters, semantics, mandatory contracts
and audit roots are unchanged, so the preceding full gate remains the
actual-artifact evidence. The full gate was not rerun for these derived proofs;
their package snapshot is recorded separately. No test suite was added.

The next derived consequence connects that lifecycle to the actual public
factory. From an available slot, it derives the created handle, initialized
source value, caller-buffer validity and original lease. The same program then
executes initialization, the admitted ME controls, termination and release,
restoring the original owners and preserving cells outside the instance,
outputs and selected reservation. The five new roots are integrated into
three owning modules. The FMI/compiler audit passed in
`build/c-factory/me-creation-package-gate-v1.log` with all 838 inputs unchanged.
Existing emitters, semantics, mandatory contracts and audit roots are unchanged;
the preceding full gate supplies artifact evidence, with this derived-proof
package snapshot recorded separately. The history still
omits importer state/numerical interactions, interspersed failures, reset and
concurrent hosts; this does not assert validity of a released handle.

The C conversion checkpoint replaces the special cases for integer `0`/`1`
with exact binary64 conversion for every integer of magnitude below `2^53`.
Finite binary64-to-size conversion now truncates toward zero and checks the
selected 64-bit unsigned range, rejecting nonfinite/out-of-range inputs without
modulo. Core proofs connect the computed encodings and integer-unit division
to real values and mathlib's floor/ceiling; shared C proofs cover conversion and
actual cast-expression evaluation. Its 32 new roots passed the core/C/FMI/eFMI/compiler
audit in `build/c-factory/c-integer-package-gate-v3.log`, with all 840 inputs
unchanged. The renewed full artifact gate passed in
`build/c-factory/c-integer-full-gate-v1.log`, also with all 840 inputs unchanged.
Both checked archives are retained under `build/c-factory/c-integer-artifacts-v1/`.
C/header/GALEC and FMI XML bytes match the ME checkpoint; the three eFMI
manifests differ only in fresh generation identities and dependent references/checksums.
Only these three status documents changed after the full gate. Emitted code,
grammar and mandatory contracts are unchanged. This is a prerequisite for
complete CS stepping, not a complete `fmi3DoStep` or native-cast guarantee.

The C body semantics also evaluate a decimal floating-constant expression node.
Its value is the round-to-nearest-even of the literal's exact base-ten content
(`(if negative then -1 else 1) * mantissa * 10 ^ exponent`) on the finite
binary64 grid, defined through the shared scaled-rounding specification, so
evaluation is total, deterministic and always finite: the grid holds no
infinities, and an out-of-range magnitude saturates to the nearest finite value.
The magnitude prints as a single C11 6.4.4.2 floating constant
(`<mantissa>e<exponent>`, the exponent carrying its own sign) and a negative
constant prints as its parenthesized unary negation, because C has no negative
literal tokens. Trusted boundary: a conforming C11 translator converts each such
floating constant to this same correctly rounded binary64 value; this rounding
assumption was already implicit for the integer `0`/`1` casts that print `1.0`,
and is now stated explicitly for decimal literals. No further floating
arithmetic is added to the body machine; `isfinite` remains its only intrinsic.

A derived stepping prerequisite now adds computed floor for all finite
binary64 encodings, including negative zero, and ordinary typed external-call
contracts for finite `floor` and a supplied int32 `fegetround` observation.
The latter is not a proof that the host uses nearest rounding; native library,
fenv/header correspondence and floating exception flags remain explicit
boundaries. The actual `model_advance` helper executes through the shared
event scheduler, deriving its nested kernel call, return and single state write
without a successful-execution premise. The adapter consequence retains its
actual fragment, tokenization, function bindings, memory frame and source error.
Solve composition and reported-time lemmas keep cumulative solver duration
separate from the communication clock. They do not establish the clock trace.
The 27 added roots are integrated into five owning modules. The core/C/FMI/eFMI/compiler
audit passed in `build/c-factory/cs-prerequisites-package-gate-v1.log`, with all
845 inputs unchanged. Previous semantic definitions, emitters and mandatory
contracts are unchanged, so the preceding full gate retains the actual-artifact
evidence; it was not rerun for these derived proofs. Only the three status
documents changed after package acceptance. No new test suite was added.
Complete public `fmi3DoStep` remains open.

The C arithmetic checkpoint replaces the finite-addition overflow failure
with an encoded signed-infinity result. `Binary64.Adds` independently states
the Real overflow thresholds and finite nearest/even/signed-zero conditions;
existence, uniqueness and complete result correspondence are proved.
`CArithmetic.add_correct` relates actual C result values to that relation.
Member-read and prepared-register expression proofs use the same `CLoops`
arithmetic rule. The original `floatAdd_finite` statement and all unit-kernel
claims are retained. This admits no new source syntax or nonfinite operand;
multiplication still rejects overflow. NaN encoding is canonicalized only by
the new result encoder; raw input payload decoding remains unchanged, and
finite addition is proved never to produce NaN.

Its 21 added roots passed the core/C/FMI/eFMI/compiler audit in
`build/c-factory/finite-addition-package-gate-v1.log` with all 847 inputs
unchanged. The renewed full artifact gate passed in
`build/c-factory/finite-addition-full-gate-v1.log` with all 847 inputs unchanged.
Both checked archives and exact member comparisons are retained under
`build/c-factory/finite-addition-artifacts-v1/` and adjacent review files.
C/header/GALEC and FMI XML match the preceding artifacts; the three eFMI
manifests change only their generation identities and dependent checksums.
The existing native FMI test passed overflow calls with and without a stop
bound. Only these three status documents changed after full acceptance.
No new test suite or emitted-code change was made.
Floating status flags, traps, target-header/fenv correspondence and the complete
public CS call remain outside these result proofs.

A derived-proof follow-up adds 14 roots in the shared C and FMI packages.
`CallDeclarationPrefix` composes a determinate ordinary external call with its
typed local declaration while leaving future behavior unrestricted. `MathCalls`
applies this to floor and the supplied rounding observation. `StepAdmission`
connects the C comparisons to positive integral durations bounded by one
million, proves the unique counter and its C conversion, and separates finite
clock addition from strict clock progress. `StepAdvance` executes the actual
final solver/time/output suffix, deriving the conversion from mathematical
duration and the nested helper execution from the program definitions. Exact
written values and the memory frame are proved under explicit storage premises.
The earlier successful-conversion premise is unnecessary in this suffix proof.

The core/C/FMI/eFMI/compiler package audit passed in
`build/c-factory/cs-duration-package-gate-v2.log` with all 850 inputs unchanged.
Only these three status documents changed afterward. Earlier definitions,
emitters and mandatory artifact contracts are retained, with their preceding
847-input full gate evidence; the full gate was not rerun for these derived
proofs. These are derived consequences, not the complete
public `fmi3DoStep` contract; initial output writes, input/lifecycle checks,
rounding-header correspondence, rejection/logging and histories still require
composition. No test suite or source case is added.

The next environment increment adds 14 roots. Shared C `CFenv.Header` represents
an explicit nonnegative signed-32-bit `FE_TONEAREST` value; it supplies that
binding while retaining the base types and literal addresses. No default
numeric macro value is selected. The rounding-declaration/branch proof covers
every supplied int32 observation, including negative failure, and retains all
later rejection behavior. Declaration-free rejection blocks are explicit in
the current C scope profile. `BodyCallInterface` transfers a closed-body call
proof using local syntax/type/literal agreement, without assuming agreement on
unrelated functions in the actual table.

`RuntimeEnvironment` combines that header with the existing static objects
and literal pool. Its admitted/null ME time-call and numerical-helper proofs
share this interface. Two compiler consequences obtain the same function table
and pool from the actual adapter certificate for every supplied header, retain
the helper/source error bound, and transfer the ME time-history/source frame.
The signatures and pool are chosen before quantifying over header values.

The core/C/FMI/eFMI/compiler package audit passed in
`build/c-factory/rounding-environment-package-gate-v1.log`, with all 854 inputs
unchanged. Only the three status documents changed afterward; the full artifact
gate was not rerun for these derived proofs. Earlier definitions, emitters and
mandatory artifact contracts are unchanged; their 847-input full artifact evidence is
retained. These consequences do not provide a complete public `fmi3DoStep`
contract or certify native headers, floating-environment observations,
mode stability, flags/traps/restoration or arbitrary surrounding histories.
The base FMI constant dictionary remains a partial proof context; the new
runtime environment supplies the library macro explicitly. No source case or
new test suite is added.

The ordinary-CS-call increment changes generated C: `fegetround` and `floor`
now initialize fresh function-scope `int`/`double` locals. Named sections retain
the existing rounding, addition, optional stop, finite-progress and unit-grid
order. `StepGuards` characterizes stop/progress/duration comparisons using Real
values and the decoded overflow domain. Its rounding, clock and grid prefixes
cover every represented observation or finite input, preserving the heap and
all behavior of the chosen rejection continuation. The clock proof includes
both signed overflow outcomes and does not skip a rejected sum.

`StepGuards.accepted_execution` composes these prefixes with the actual solver
and output suffix. It derives a positive bounded count from duration admission,
then proves all behaviors terminate with the computed state, rounded clock and
last-successful-time write. `actual_sections` identifies this code in the emitted
`doStep` body; the retained `StepAdvance.actual_tail` index changes from 13 to 16
for the three added declarations/branches. This is execution after the first
nine statements and their public input checks, not a complete public-call theorem. The ordinary
external observations, declared C profile, valid storage and stop/progress
conditions are explicit. Input/output setup, errors/logging, histories and
native floating-environment correspondence remain open.

Eight new audit roots passed the core/C/FMI/eFMI/compiler package audit in
`build/c-factory/cs-ordinary-package-v1.log`, with all 855 inputs unchanged.
The renewed full artifact gate passed in
`build/c-factory/cs-ordinary-full-gate-v1.log`, with the same 855 inputs
unchanged, including both actual archives and all 13 existing native FMI checks.
The retained archives and exact member comparisons are under
`build/c-factory/cs-ordinary-artifacts-v1/`. Only the reviewed FMI adapter
source changes and its rebuilt binary differ from the previous FMU; numerical
C, headers, FMI metadata, GALEC and eFMI Production C are unchanged. The eFMI
manifests have fresh generation identities and dependent checksums only.
Only the three status documents changed after that full gate. Existing
mandatory artifact contracts and all earlier audit roots are retained; shared
numerical semantics and the grammar are unchanged. No new test suite is added.

`StepEntry` subsequently extends the public CS proof boundary. Its independent
`InputsValid` predicate uses finite decoded values, numerical point/clock equality
and positive duration. `input_condition_all` proves the emitted input guard for
every pair of raw 64-bit encodings, including nonfinite values and both signed
zeros. `prefix_run` connects the actual first nine statements to admission or
the input-failure statement and records the precise initialized output heap.
The earlier finite-input helpers now follow from these general proofs.

`accepted_call` starts at public typed parameter binding and derives all successful
call behavior through the ordinary library calls, guards and numerical helper.
The solver count, final state, rounded clock, last-successful-time and three
false Boolean outputs are derived, with an exact other-memory frame. Boolean
outputs may alias; incompatibility with Float64 cells follows from the typed
heap rather than a separate pairwise-address assumption. `null_call` covers
all raw arguments and nullable output pointers without instance/buffer-storage
premises. Type/header bindings, the ordinary external-call relations, valid
nonnull storage and mathematical stop/progress conditions remain explicit.
The raw-bit theorem models values, not signaling-NaN traps or floating flags.

These sixteen added roots passed the FMI/compiler package audit in
`build/c-factory/cs-entry-package-v1.log` with all 856 inputs unchanged.
Only the three status documents changed afterward. Earlier semantic definitions,
emitters, mandatory artifact contracts and tests are unchanged, so the preceding
855-input full gate retains their artifact evidence; the full gate was not rerun
for these derived proofs. The new public-call consequences are not yet mandatory
in `AdapterContract`. Complete rejected/logged calls, repeated histories and
actual-artifact composition remain required. No new test suite is added.

`ErrorContext` subsequently makes the error helper's local interface
requirements explicit: type/literal agreement, agreement on its actual syntax,
the Error binding and the ordinary `fail` name. The static-object constructor
and rounding-header extension prove these requirements. Neither construction
assumes successful execution or agreement on unrelated public functions.
Fourteen existing `StaticErrors` roots are generalized to this context; sixteen
existing caller sites instantiate the static constructor while retaining their
public theorem statements. The new statement contracts retain enabled,
suppressed and absent-outcome callback behavior, and can compose after ordinary
library calls. Existing complete failure-call proofs reuse them.

`StepErrors.lifecycle_prefix`, `lifecycle_suppressed` and `lifecycle_logged`
cover complete public CS lifecycle rejection under every constructed context.
The independent `Reference.Allowed` predicate selects forbidden kinds/modes.
All raw numerical arguments and nullable output pointers are covered, with no
output-buffer storage requirement. The suppressed case returns Error after
the Terminated write; the enabled case retains the callback's exact represented
trace, result heap and no-returning-outcome case. Native callback execution,
reentry and ownership/frame assumptions remain separate obligations.

The FMI/compiler package audit passed in
`build/c-factory/cs-errors-package-v1.log`, with all 858 inputs unchanged,
eleven new roots and no removed audit roots. Only the three status documents
changed afterward. Earlier semantic definitions, emitters, mandatory artifact
contracts and tests remain unchanged; the retained 855-input full artifact gate
continues to apply to their unchanged products. The full gate was not rerun
for this proof refactor and its derived call results. Missing-output, input,
rounding, stop and discard calls, repeated histories and mandatory public-CS
artifact composition remain open. No grammar or test suite is added.

`StepArguments` then closes complete missing-output and invalid-numerical-input
calls under the same checked error contexts. Missing outputs are rejected
before any output access, without output/time/state storage premises. For
invalid raw point/step encodings, the proof derives the initialized output heap
and the helper's storage premises from the original caller buffers. Boolean
outputs may alias; writable typed storage and separation from the instance
block are explicit. The suppressed error preserves every instance field except
mode, including the numerical state and clock. Enabled logging retains every
represented callback outcome and the absence-of-outcome case, without assuming
a callback memory frame or certifying native callback internals/reentry.

Two reusable direct-prefix bridges compose prefixes already proved in the target
interface with the existing failure-statement contracts. Earlier transferred
failure calls and CS lifecycle proofs reuse them with unchanged propositions.
Twelve added roots passed the FMI/compiler package audit in
`build/c-factory/cs-arguments-package-v1.log`, with all 859 inputs unchanged.
Only the three status documents changed afterward. No earlier semantic
definition, emitter, mandatory artifact contract, test or axiom policy changed;
the retained 855-input full gate still supplies their unchanged artifact evidence.
The full gate was not rerun for this derived-proof increment. Rounding/stop/
discard calls, repeated histories and mandatory public-CS artifact composition
remain open. No grammar or test suite is added.

`StepFailures` subsequently composes public admission with the ordinary rounding
observation and the stop guard. Rounding rejection covers every supplied int32
observation unequal to the explicit header's nearest value, including negative
failure observations, after valid raw input admission. Stop rejection covers
finite duration encodings and the rounded clock sum, including overflow. It
precedes progress and unit-grid rejection. Both paths retain exact output
initialization and return Error through the actual helper; enabled logging
retains every represented callback outcome and the absent-outcome case.

The shared `StepArguments.ready_prefix` derives the public state after output
writes from the original heap. `StaticErrors.FailurePath` also permits ordinary
calls in a derived prefix, and its complete behavior theorems reuse the existing
error-statement contracts. The core silent-prefix theorem obtains absence of
divergence from that complete suffix contract; it does not postulate native
callback termination. No successful C execution is a premise of the public
rounding or stop theorems. Header/library bindings, valid caller storage and
the established finite clock remain explicit.

Eleven added roots passed the core/C/FMI/eFMI/compiler package audit in
`build/c-factory/cs-failures-package-v1.log` with all 860 inputs unchanged.
Every earlier declaration, emitter, mandatory artifact contract and test is
retained. Only the three status documents changed afterward. The preceding
855-input full artifact evidence is retained; the full gate was not rerun for
these derived proofs. Discard calls, mandatory public-CS artifact composition,
repeated histories and native floating-environment correspondence remain open.
No grammar, test suite or axiom-policy change is introduced.

`StepDiscard` now supplies complete public discard behavior after valid input
and nearest-rounding admission. The optional stop guard runs first. A rounded
clock that cannot advance reaches discard without calling `floor`; otherwise
the duration guard can reject after the ordinary floor call. Both routes avoid
the solver. Suppressed logging returns Discard with the exact initialized caller
outputs and every instance cell unchanged. Logged execution retains all foreign
outcomes and the no-outcome case; preservation after a foreign callback requires
its frame, rather than following from the FMU's own absence of writes.

`StepCases.partition` proves exhaustive, unique classification for every raw
request across null, lifecycle, output, input, rounding, stop, discard and
accepted cases. The reusable `Float64.finite_encoding` theorem preserves the
original finite bits, including signed zero. Accepted cases derive finite
values, duration admission, a progressing rounded clock and the inclusive stop
bound. This reference partition does not itself prove execution or conformance;
the latest CS checkpoint above composes it with the public call proofs in the
mandatory artifact contract.

Sixteen added roots passed the core/C/FMI/eFMI/compiler package audit in
`build/c-factory/cs-cases-package-v1.log`, with all 863 inputs unchanged.
The preceding discard-only FMI/compiler audit passed with 861 unchanged inputs.
Only three status documents changed after final package acceptance. Every
earlier declaration, emitter, mandatory contract and test is retained. The
855-input full artifact evidence therefore remains applicable to those unchanged
components; the full gate was not rerun for these derived-proof additions.
No grammar, test suite or axiom-policy change is introduced.

This does not close K02–K05. Remaining public calls must be composed in the same
object-aware execution interface; actual concurrent histories, callback
frames, a transitive no-heap/call-graph policy, native ABI/profile and MISRA
correspondence remain open. The production grammar is unchanged. Earlier
paragraphs below record historical checkpoints, including the former
allocating implementation; they do not supersede the latest CS/storage status.

**Current claim boundary:** the numerical source-to-C core is formally
checked. The whole FMI/eFMI compiler is not yet fully verified, even for the
unit grammar subset, because the adapter/artifact/compliance obligations
below remain open. Completing this stage requires one composed guarantee for
the actual compiler and production artifacts, with every pass and admitted
interface behavior covered. Individual theorem or CI checkpoints are partial
progress and do not authorize grammar or product-scope expansion.

Before every spiral-stage grammar expansion, the admitted subset must also
complete a recorded review against MLS 3.7, FMI 3 ME/CS, and eFMI Algorithm and
Production Code, using the [recurring stage checklist](../dev/standards-review.md#required-review-at-every-spiral-stage).
That review maps normative clauses to the authored semantics,
pass/target proofs, actual-artifact contracts and explicit external assumptions.
Open compliance findings block expansion. Kernel checking proves the authored
propositions; review against the prose standards is a separate obligation.

The production end-to-end theorem covers one Modelica `Real` state and `der(state)=1`.
The source equation is over mathematical reals. Generated C uses finite
IEEE754 binary64 values and nearest-even addition. The numerical theorem takes
a supplied finite `x(0)`; samples remain at integer times. There is no initialization syntax, variable
time step, event handling or general solver. All compiler code, EBNF tooling,
semantics and proofs are Lean. No Rocq dependency or cross-prover assumption
is used.

The default IVP now has an explicit checked initialization plan. The source
relation remains underdetermined: `der(x)=1` does not imply `x(0)=0`. Preparation
selects the Real fallback zero and records both fallback and unfixed-start
selection notices. Scalar Flat/DAE/Solve models require exact occurrence origins
and preserve those settings; CLI and LSP notices identify the declaration.
The shared C initializer proves its write and memory frame, and FMI emits it
on instance activation and reset. Whole FMI storage/lifecycle/host-set and
artifact composition remain open.

`EFMIInitializationProofs` derives the completed source trajectory from the
finite state actually loaded after Production C Startup. For every admitted
entry heap, `ArchiveStartupContract` binds the exact archive member and its
independently denoted C tree, proves termination and characterizes all Startup
behaviors. The actual archive checker now requires this consequence together
with its prior contract. Entry storage, public ABI and later machine compilation
remain explicit boundaries. The final required gate passed in
`build/initialization-provenance/full-gate.log`, with its source inventory
unchanged throughout the run. See
[initialization.md](../dev/initialization.md) for remaining SR08 obligations.

GALEC and Solve Algorithm models now also require complete origin traces.
Independent rule/parent requirements identify initialization, sampling policy,
methods, state accesses and assignments. The composed lowering theorem
preserves both lifecycle values and every operation/operand origin event,
without enumerating tensor elements. Sixteen added roots retain the existing
axiom policy; the required full gate passed in
`build/algorithm-provenance/full-gate.log`, including both target archives.
At that checkpoint tensor/FMI operation origins and actual emitted-byte source
maps remained open; this does not close the whole-adapter/compliance contract.

The subsequent unit FMI preparation now requires complete indexed origins too.
`FMI3Model.preparation_preserves` connects the actual tensor IVP's initial value,
RHS and observation to its stored Solve model, and proves exact source lookup,
generated-role ancestry and an independent contract for the attached operation
annotations. Nineteen new roots and the downstream package gate pass in
`build/literal-call-worktree/build/fmi-origins-trace-gate.log`. The required full
main-workspace gate also passed in `build/fmi-provenance/full-gate.log`, including
both actual target archives with the input inventory unchanged throughout.
Development tensor/AD provenance, actual C/GALEC/XML byte maps and complete
adapter/artifact composition remain open. No source grammar case is added.

The next increment strengthens the actual GALEC annotation contract and adds
required origins to shared C initialization emission. `GALEC.Model.TraceCorrect`
inspects the annotations on the actual block; Solve Algorithm lowering now
preserves this contract alongside its existing values and origin events.
`CInitialization.Emission.preserves` combines the actual initializer's annotation
contract, declaration ancestry and all terminating C-body behaviors. It assumes
the supplied target denotes writable binary64 storage and the interface binds
`double` accordingly. FMI creation/reset use this checked emission. Allocation,
the enclosing public functions and emitted-byte source maps still require
separate composition. Its 25 added audit roots and downstream package checks
passed in `build/literal-call-worktree/build/c-initial-provenance-package-gate.log`;
the required main-workspace artifact gate also passed in
`build/c-initial-provenance/full-gate.log`, including both actual target archives
and the existing boundary/mutation checks. All 510 inventoried inputs remained
unchanged throughout the run.

The following shared-initializer map increment proves exact correspondence
between its required origins and the existing statement printer's UTF-8 bytes.
`CInitialization.Emission.printed_preserves` combines the execution contract
with annotation correctness, ancestry of every collected map entry, complete
range membership and exact byte extraction. Generic expression mapping preserves
the existing printer and every annotated origin; a single array collector uses
cached document lengths. These 25 new audit roots and all downstream package
checks passed in
`build/literal-call-worktree/build/c-mapped-initialization-package-gate.log`.
Its required main-workspace artifact gate also passed in
`build/c-mapped-initialization/full-gate.log`, with all 513 inventoried inputs
unchanged and both actual target archives checked. This is a fragment map:
whole-function/file maps, original-to-staged input identities and archive-member
map binding remain open, along with the adapter obligations above.

The next increment adds complete annotations and mapped printing for the
existing C statement, parameter, signature and function syntax. It proves exact
printer-byte equality, range extraction and preservation/reflection of predicates
on supplied origin references. The initializer now derives a complete statement
trace and uses this shared mapper; its earlier map and execution contracts are
retained. Twenty-four additional audit roots and downstream package checks pass
in `build/literal-call-worktree/build/c-statement-function-map-package-gate.log`.
The required main-workspace artifact gate passed in
`build/c-statement-function-map/full-gate.log`, with all 517 inventoried inputs
unchanged and both actual target archives checked. These generic maps do not
establish correct source/rule attachment in every production function, arbitrary
C-tree validity, whole-file/archive map binding or full adapter execution.

The next eFMI increment connects those maps to the actual Production C Startup
emitter. Required annotations come from prepared Solve operations and operands;
independent predicates inspect every Startup annotation and its generating
rule/parents. The state default traces to the declaration, while the generated
sampling period traces to the model policy. `ProductionContract.startup_map`
requires the exact file bytes, complete Startup map ranges, source ancestry and
all Startup behaviors in one witness. Both production and archive generation
consume the mapped renderer; `StartupMap.render_unchanged` preserves the earlier
C text and execution contracts. All package checks and 22 new audit roots pass
in `build/literal-call-worktree/build/efmi-startup-map-package-gate.log`.
The required main-workspace artifact gate passed in
`build/efmi-startup-map/full-gate.log`, with all 522 inventoried inputs unchanged
and both actual target archives checked. This certifies a computed
Startup map against the supplied input and complete C member, not a serialized
archive map. Header/other-method maps, original-to-staged input identity and
the remaining adapter/standards obligations are still open.

The current FMI reset increment has package-checked complete-call, frame,
independent function-syntax and source-initialization proofs. Its strengthened
actual-file contract binds the complete adapter renderer to the file and the
same definition table used by the reset theorem. The fixed actual-file check
passes in `build/fmi-reset/actual-file.log` under the unchanged axiom policy;
the required root gate also passed in `build/fmi-reset/full-gate.log`, including
both actual target archives with all 529 inventoried inputs unchanged. This
does not close other adapter bodies, allocation,
whole-C/preprocessing or ABI obligations; see
[the reset contract](../dev/fmi3/contracts.md#reset-and-complete-adapter-bytes).

The shared CTree printer now proves character stability under trigraph
replacement and line splicing for every expression, statement and function.
Its FMI instantiation covers the complete adapter renderer. The strengthened
`FMI3.AdapterContract` requires this guarantee for the actual file, deriving
model-name safety from source lexing and checking signature spellings in the
kernel. All 35 new roots and affected package audits pass in
`build/source-cutover/build/c-printer/composed-package-audit.log`; the fixed
checker also passes on the retained FMU files in its `actual-fmi.log`.
The required main artifact gate passed in `build/c-printer/full-gate.log`, with
all 596 inventoried inputs unchanged and both actual archives checked. Exact
archives and hashes are retained in `build/c-printer/artifacts/`.
This does not establish C tokenization, macro/header interpretation, remaining
public-call behavior or whole FMI/eFMI compliance. See
[the printer roadmap](../dev/c-printer.md).

The follow-on shared printer now derives the independent token/precedence
grammar of every admissible CTree expression, block item and complete function.
Names, typedef spellings and postfix restrictions are explicit premises;
indentation, nested statements and call/parameter lists are universally
quantified. The actual reset contract additionally requires this generic
text/tree judgment, and `adapter_reset_syntax` binds its fragment to the complete
adapter file. Existing execution, memory and character-rewrite contracts remain
required. This is not a full C tokenization theorem: cross-category maximality,
adjacent-string concatenation, macros/headers and other public calls remain
open. All 85 added roots and affected packages pass
`build/c-token/final-package-audit.log`. The required actual-artifact gate passed
in `build/c-token/full-gate.log`, with all 613 inputs unchanged and both actual
archives checked. Exact artifacts and hashes are retained in
`build/c-token/artifacts/`. No grammar or emitted
C bytes change. See [the exact scope](../dev/c-printer.md).

The next lexical increment now proves cross-category maximality for the
compositional token judgments against an independent normal-context candidate
envelope. It checks identifier/number competition, literal encoding prefixes,
all punctuators and comment openers against the actual continuation. The
independent function grammar separates ordinary literals, so no phase-six
concatenation changes its tokens. `FunctionDenotes.tokenization` composes these
results using one token witness, and the actual reset contract now requires
this consequence alongside its prior syntax, call and memory contracts.
`adapter_reset_tokenization` locates that certified fragment in the complete
adapter file. All 67 added audit roots and affected packages pass
`build/c-lexical/composed-audit.log`. The required full gate passed in
`build/c-lexical/full-gate.log`, with all 621 inputs unchanged and both actual
archives checked. Exact archives and hashes are retained in
`build/c-lexical/artifacts/`.
No C bytes or grammar cases change. This is an ordinary-code contract;
header-name/directive contexts, macro expansion, actual typedef meanings,
scope/type constraints and remaining public-call behavior stay open.

The following increment requires the independent shared grammar for the
complete actual FMI function section. `function_sequence_tokenization`
composes arbitrary lists with their real lexical continuations, and
`RuntimePrinter` instantiates it for all runtime bodies and helpers.
`AdapterContract` retains every prior field and additionally binds that section
to the exact adapter bytes and prepared definition table. The fixed checker
kernel-checks type/name proofs for its collected signatures; it does not assume
the header collector is correct. `adapter_reset_source` now retains this
grammar witness alongside the reset execution/source consequence for the same
table. Nine new roots and the affected packages pass
`build/fmi-functions/package-audit-v2.log`. The fixed actual-file checker passes
in `build/fmi-functions/actual-fmi.log`. The required full gate passed in
`build/fmi-functions/full-gate.log`, with all 625 inventoried inputs unchanged
and both actual archives checked. Exact archives and hashes are retained in
`build/fmi-functions/artifacts/`. Typedef meanings, headers/macros, declarations,
scope/type constraints and other public-call execution remain open. No runtime
or source grammar changes. At that checkpoint, 57 of the 75 collected API signatures
contained an adjusted parameter type absent from its execution dictionary;
the new grammar contract does not supply those missing conversions. See the
[concrete F03 review](../dev/fmi3/contracts.md#reset-and-complete-adapter-bytes).

The current call-entry increment addresses those missing parameter bindings.
`CallSignature.call_entry` derives a fresh coherent scope from per-parameter
conversion, while `arguments_exist` establishes a nonempty argument domain.
`CUnsigned` proves modular integer conversion, uniqueness and BitVec agreement;
FMI selects 32 bits for value references. `AdapterContract` retains its previous
fields and requires known parameter/return types and unique parameter names for
every actual helper/API function. `adapter_call_entry` binds their entry theorem
to the same actual bytes and grammar witness. This does not establish body
termination/effects, pointee storage, callback execution or native header/ABI
correspondence. All 26 new roots and affected packages pass
`build/fmi-types/package-audit-v2.log`. The strengthened actual-file checker
passes in `build/fmi-types/actual-fmi.log`. The required full gate passed in
`build/fmi-types/full-gate.log`, with all 629 inventoried inputs unchanged and
both actual archives checked. Exact archives and hashes are retained in
`build/fmi-types/artifacts/`; their C and GALEC members match the previous checkpoint. No source
grammar or runtime emitter changes.

The next count-query increment requires complete calls for both existing ME
count getters in `AdapterContract`, together with successful literal-pool
construction. The actual `SourceBuildContract` now binds the complete metadata
tree through `XML.Document`, in addition to its prior identifier contract.
`counts_source` joins actual C grammar, complete successful-call behavior,
returned counts, Solve state volume and an independent scalar-reference count
relation for the actual XML. Null instances are covered too. Invalid lifecycle
and missing-output calls have complete Error/Terminated results with logging
disabled; `counts_failure_source` constructs their collected literal addresses
and immutable objects and proves their heap frame. Enabled callbacks, native
allocation/header/ABI meanings, other public calls and full FMI conformance
remain open. No source grammar or emitted C/GALEC changes. All 28 added roots
and affected package checks pass
`build/fmi-counts/package-audit-v2.log`. The strengthened actual-file checker
passes in `build/fmi-counts/actual-fmi-v2.log`. The required full gate passed in
`build/fmi-counts/full-gate.log`, with all 634
inventoried inputs unchanged and both actual target archives checked. Exact
archives and hashes are retained in `build/fmi-counts/artifacts/`; their C and
GALEC members match the previous checkpoint (`code-member-comparison.log`).

The version-query increment now requires the actual `fmi3GetVersion` function's
grammar, constructed static storage and complete behavior in `AdapterContract`.
`version_source` connects its immutable, zero-terminated `3.0` result and
unchanged heap to the version fields of both actual XML documents. No instance
or lifecycle premise is needed. This uses the authored C interface; native
header/ABI interpretation and the remaining public functions stay open.
All 11 new audit roots and affected packages pass
`build/fmi-version/package-audit.log`. The required full gate passed in
`build/fmi-version/full-gate.log`, with all 637
inventoried inputs unchanged and both actual target archives checked. Exact
archives and hashes are retained in `build/fmi-version/artifacts/`; their C and
GALEC members match the previous checkpoint (`code-member-comparison.log`).

The callback increment uses a shared `Typed.nextWith` scheduler and labeled
execution with finite/infinite histories. Existing internal-call, literal and
read-only proofs remain required. The actual adapter contract now also requires
`Logging.FunctionContract`: `logging_source` binds the emitted failure helper,
its prepared function table, constructed `logStatus` bytes and actual XML
category. Enabled calls emit the importer symbol and converted environment,
Error status, category and message pointers, then return Error with the host's
permitted writable effects. Immutable category/message storage survives.

This is conditional on the explicit symbolic callback binding, the pinned
prototype and an invocation-local returning host effect. It does not establish
arbitrary callback termination, native function-pointer ABI, allocation,
reentrancy or complete public-call/FMI conformance. At this checkpoint,
named-literal lowering retained its internal-machine contract; the eventful
extension was still separate from the emitted-helper proof. No source grammar,
renderer or boundary test suite is added. All 58 new audit roots and affected
packages pass `build/c-events/package-audit-v1.log`. The required full gate
passed in `build/c-events/full-gate.log`, with all 646 inventoried inputs
unchanged and both actual target archives checked. Exact archives and hashes
are retained in `build/c-events/artifacts/`; their C, header and GALEC members
match the previous checkpoint (`code-member-comparison.log`).

The subsequent eventful literal pass preserves and reflects every authored C
behavior, including callback arguments/effects, faults and finite or infinite
event histories during divergence. Both interface extension and syntax lowering
instantiate labeled bisimulation; ordinary and eventful calls share scheduler
proofs. `AdapterContract` now requires `LiteralPreparation.EventContract` for
its actual function table and separately requires successful pool preparation.
`literal_events_source` and the strengthened `logging_source` retain the actual
file/table/pool witnesses. Foreign relations are unchanged; the pass adds no
callback determinacy or successful-return premise. This does not model execution
inside a nonreturning foreign call or establish native header/ABI correspondence.
All 37 new audit roots and affected package checks pass in
`build/c-events/literal-package-audit-v1.log`. The required full artifact gate
passed in `build/c-literal-events/full-gate.log`, with all 651 inputs unchanged
throughout the run. Both target archives are retained in its `artifacts/`
directory; their C, header and GALEC members match the previous checkpoint
(`code-member-comparison.log`). See
[the pass contract](../dev/fmi3/contracts.md#eventful-literal-lowering).

The all-outcome helper increment strengthens the mandatory logging contract
with both `AllPreparedContract` and `SilentPreparedContract`. Enabled logging
characterizes every represented returning host effect without a supplied
successful outcome or determinacy premise; absence is explicitly stuck in the
atomic external machine. Disabled logging proves no callback events and exactly
the mode write. The same actual-file/table/pool/XML witnesses and eventful
literal-lowering contract remain required. Shared silent-prefix and external
choice theorems support the actual helper's dispatch and return continuation;
earlier determined guarantees are retained as consequences.

Compiler composition builds in `build/c-logging-choices/promotion-v2.log`.
All 21 new roots and affected package checks pass in
`build/c-logging-choices/package-audit.log`; every earlier audit root is retained.
The required full artifact gate passed in
`build/c-logging-choices/full-gate.log`, with all 654 inputs unchanged and both
actual archives checked. Retained archives and hashes are in
`build/c-logging-choices/artifacts/`; their C, header and GALEC members match
the previous checkpoint (`artifact-retention.log`). This does not prove execution
inside host calls, native ABI, allocation, host ownership or all public entries.
FMI's prohibition on log-callback reentry is an admissible-host obligation at
that boundary. See [the exact contract](../dev/fmi3/contracts.md#all-failure-helper-outcomes).
Grammar and generated artifacts are unchanged; the stage remains open.

The next nominal-query integration adds a mandatory complete public-call
contract for the actual emitted fragment/table/pool, alongside every earlier
adapter field and eventful literal-lowering guarantee. Successful storage and
the independently interpreted ordered XML state agree on the positive decoded
default 1; null, rejected lifecycle and invalid access cases include both
logging settings. The fixed checker kernel-proves actual signature membership.
All 33 new audit roots and affected packages pass in
`build/c-nominals/package-v2.log`; the required full `lake test` gate passed in
`build/c-nominals/full-gate.log`, with all 660 inventoried inputs unchanged.
Both actual archives are retained in `build/c-nominals/artifacts/`; their C,
header and GALEC members match the previous checkpoint. Valid memory, host
bindings, native ABI, allocation and remaining public-call obligations remain
explicit. See [the exact scope](../dev/fmi3/contracts.md#complete-nominal-queries).

The next state-access increment requires both actual getter/setter fragments,
their complete call behaviors and independent XML state ordering for the same
compiled Solve model and literal pool. It proves exact finite read/write values,
Model Exchange state refinement and memory frames, including all represented
error callback outcomes. Shared prefix and finite-domain lemmas support later
API proofs. All 39 additional roots and affected packages pass in
`build/c-state-calls/package-v1.log`; the required full artifact gate passed in
`build/c-state-calls/full-gate.log`, with all 667 inventoried inputs unchanged.
Both actual archives are retained in `build/c-state-calls/artifacts/`; their
C, header and GALEC members match the previous checkpoint. Native storage/ABI, initialization
and remaining adapter obligations are still open. See
[the state contract](../dev/fmi3/contracts.md#continuous-state-getter-and-setter).

The derivative getter increment now requires its actual public and `model_rhs`
helper fragments, complete call contracts and independent XML derivative order.
The helper executes the existing numerical C statements of the same Solve model;
no derivative callback is assumed. `derivative_value_source` composes the existing
Flat/DAE/Solve relations to the exact Real derivative, and `derivative_source`
retains the actual numerical C contract alongside the adapter and literal pool.
Success, null handles, lifecycle/count/buffer errors and represented logging
outcomes are covered. The fixed checker proves numerical-name freshness for its
actual header candidates. All 41 added roots and affected packages pass in
`build/c-derivatives/package-v1.log`; the required full artifact gate passed in
`build/c-derivatives/full-gate.log`, with all 675 inventoried inputs unchanged.
Both actual archives are retained in `build/c-derivatives/artifacts/`; their C,
header and GALEC members match the previous checkpoint.
No grammar, emitter or solver policy changes. See
[the derivative contract](../dev/fmi3/contracts.md#complete-continuous-state-derivative-query).

The Float64 getter increment requires the actual public fragment and helper,
independent XML numeric-reference lookup and complete prepared-call contracts.
The two counted loops validate all references before output writes and preserve
request order and duplicates. Nested derivative queries execute the same Solve
numerical C statements. Empty calls permit null arrays; invalid lengths/pointers
and references reach the actual error/log helper. Output and model-memory frames
are explicit. The request buffer reuses the tensor-memory specification without
adding array variables to the production grammar. All 58 added roots and affected
package checks pass in `build/c-float64-get/package-v2.log`. The required full
artifact gate passed in `build/c-float64-get/full-gate.log`, with all 686 inputs
unchanged. Both actual archives are retained in its `artifacts/` directory;
all C/H/ALG members match the previous checkpoint. Current state/time representation, complete initialization,
native ABI and remaining public APIs retain their existing open boundaries. See
[the Float64 getter contract](../dev/fmi3/contracts.md#complete-float64-getter).

The Float64 setter increment requires complete nonempty, empty and null calls,
all validation/lifecycle failures and represented logger outcomes. Every input
is validated before state writes; accepted binary64 payload bits are retained
exactly. A finite snapshot derived from original input storage connects the
last request to the semantic ME state update and a full memory frame.
Independent XML reference interpretation follows ModelStructure and the
derivative attribute to the same scalar local continuous state, with
initial=exact and reinit=false metadata. The fixed actual-file checker now
requires the printed setter and its one-table/pool contract alongside all
prior fields. All 51 new roots and affected package checks pass in
`build/c-float64-set/package-v1.log`. The required full artifact gate passed in
`build/c-float64-set/full-gate.log`, with all 694 source inputs unchanged.
Both actual archives are retained in `build/c-float64-set/artifacts/`; all C,
header and GALEC members match the published the previous checkpoint outputs.
Initialization histories, native ABI,
ownership and remaining APIs keep the whole-stage claim open. See
[the setter contract](../dev/fmi3/contracts.md#complete-float64-setter).

The initialization increment changes the reviewed unit admission policy to a
finite start and an optional finite inclusive stop. Tolerance is unused by this
profile. The mandatory `InitializationCalls.FunctionContract` binds both actual
entry/exit fragments, typed complete-call behaviors, all represented failure
logging outcomes and their shared table/literal pool. Successful entry needs
writable clock storage, not initialized old clock values. The source consequence
uses the finite model value actually stored by default initialization or a host
setter and proves the unique Real trajectory at the supplied time origin.
Composition builds in `build/c-initialization/composition-v2.log`; all 51 added
roots and affected package checks pass in `build/c-initialization/package-v1.log`.
The required full artifact gate passed in `build/c-initialization/full-gate.log`,
with all 706 inventoried source inputs and the complete file set unchanged.
Both actual archives are retained in `build/c-initialization/artifacts/`.
Compared with the previous checkpoint, only the initialization-entry body in `sources/fmi3.c`
changed; every other C/header/GALEC member is identical. The inclusive `atLeast_iff`
replaces the retired strict-order policy root; every other earlier root and the
axiom whitelist are retained. No source grammar is added. Allocation, arbitrary
host/lifecycle histories, remaining APIs and complete standards/ABI coverage
keep the stage open. See [the initialization contract](../dev/fmi3/contracts.md#complete-initialization-calls).

At the initial no-heap/RTOS review, the FMI emitter still used `calloc`/`free`.
The static-runtime checkpoint at the top of this document supersedes that
implementation: permanent multi-instance storage is now emitted. Complete
execution/ownership and transitive allocation contracts remain open; neither
initialization alone nor internal heap-frame invariants close them. MISRA C:2025 with the C11 profile has been
reviewed for initial findings; the 223-entry enforcement matrix is open.
Essential types, pointer guards, allocation and concurrency require
further proof and artifact coverage. Rule 15.5 is Disapplied; C11 is supported.
No MISRA compliance or approved deviations are claimed.
See [the rule review](../dev/standards-review.md#misra-c2025-and-static-storage-review)
and [K02–K05].

The explicit-null increment supplies shared C null equality/inequality semantics
and independently checked printing for `((void *)0)`. It changes the actual
shared FMI instance guard and proves equivalence to its former implicit test
for every represented pointer. Literal-pool and interface-extension proofs
retain the distinction between a zero literal and an integer variable holding
zero. Comparisons between two non-null symbolic pointers remain unsupported.
Existing actual-function and artifact contracts remain required. The 44 new
roots retain every earlier root and the unchanged axiom policy. The required
full gate passed in `build/c-static-storage/full-gate.log`, including both
actual target archives with all 710 inventoried inputs unchanged. Only the
70 shared instance guards in the FMI adapter differ from the previous checkpoint; every
other C/header/GALEC byte is unchanged. Exact archives are retained in
`build/c-static-storage/artifacts/`. Other implicit pointer tests and whole
MISRA/adapter compliance remain open.

Its storage prerequisites prove preservation of supplied cell domains, types
and permissions through internal C execution, and bounded serial reservation,
exclusion and reuse of fixed slots. They do not establish a no-heap generated
product, native atomics, caller ownership or layout. At that checkpoint,
nested array/member addressing also required a structural correction before
the planned static instance array could support tensor fields; see MC10 in the
[standards review](../dev/standards-review.md#misra-c2025-and-static-storage-review).

The following subobject correction retains the containing array index at each
member selection and resets the selected member's local offset. Ten added
roots prove exact recovery of both index levels and the field name, tensor
region separation, arbitrary member-depth isolation and the actual typed
store's frame for a different record. All existing memory/call contracts and
affected C/FMI/eFMI/compiler package checks pass in
`build/c-static-storage/address-package-v3.log`. The required main artifact
gate passed in `build/c-subobjects/full-gate.log`, including both actual
target archives with all 711 inventoried inputs unchanged. Every C/header/GALEC
member is byte-identical to the previous checkpoint; exact archives are retained in
`build/c-subobjects/artifacts/`. The ten new roots retain all earlier roots
and the unchanged axiom policy. No source grammar or Solve operation changes.
These are structural cell facts; native bounds, layout, effective types,
lifetimes and concurrent ownership require separate contracts. In particular,
they do not establish native pointer inequality for all different paths or
implement the planned static instance storage.

The next storage increment adds atomic Boolean cells whose ordinary heap
loads/stores are rejected. Their value conversion uses the existing Boolean
semantics; selected sequentially consistent exchange/store calls supply their
indivisible access rules. The bounded C reservation helper now has complete
fresh-parameter, initialization, loop, return and caller-continuation proofs.
Admitted entry cells imply termination and an exact sequential trace/result,
with bounded exchanges, memory frames and storage preservation. Its printed
function has the shared independent token/tree contract, including `_Bool`
and `volatile` type syntax. Successful scans refine the independent FMI slot
reservation; sequential exhaustion characterizes the supplied snapshot.
All affected packages and 38 added audit roots pass in
`build/c-atomics/package-check.log`; all earlier roots and the axiom policy are
retained. The required main artifact gate passed in
`build/c-atomics/full-gate.log`, with all 720 source inputs unchanged,
both actual target archives checked and every C/header/GALEC member
unchanged from the previous checkpoint. Exact archives and the comparison evidence are
retained under `build/c-atomics/`. Production still uses
`calloc`/`free`: the helper is not yet emitted into the FMI adapter. Native
atomic/header bindings, declarations, overlapping calls, ownership, reuse
initialization and complete factory/artifact composition remain open. These
proofs do not claim a globally full snapshot after a concurrent failed scan
or bounded native atomic latency. No source grammar or numerical IR changes.

The following identity increment replaces the factory's nested string-call
condition with an explicitly sequenced private helper. Null pointers reject
before any string access. With valid null-terminated buffers and the selected
library bindings, every helper call preserves memory and returns the independent
nonblank-name/token-equality predicate. The proof preserves arbitrary caller
observations and every sign-correct `strcmp` result. Its mandatory
`Identity.FunctionContract` binds the exact printed fragment, independent
tokenization and execution to the adapter's actual definition table. The fixed
checker also proves library-name freshness, and a consistent library environment
is constructed rather than assumed to exist. All earlier adapter fields remain
required. All affected package checks pass in
`build/c-factory/identity-packages-v1.log`, with 60 added audit roots and the
unchanged axiom policy. The required full artifact gate passed in
`build/c-factory/identity-full-gate.log`, including both actual archives and
the existing mutation/native boundary checks, with all 743 inputs unchanged.
The retained code-member comparison under `build/c-factory/identity-artifacts/`
shows only the new helper and its two factory call sites in FMI `sources/fmi3.c`;
numerical C and eFMI C/GALEC are unchanged from the previous checkpoint.

This increment also includes checked storage-frame and interleaving foundations
for the planned static instance slots. These describe the authored C scheduler
and an explicit ownership protocol; they do not establish a native scheduler,
weak-memory model or complete factory/history refinement. Production still
uses `calloc`/`free`. Native headers, libc implementation and hidden allocation,
caller-buffer validity, storage declarations, reuse initialization and the
complete creation/release calls remain open. No source grammar or numerical
IR case is added, and no whole MISRA/FMI/eFMI compliance claim is made.

The next factory-admission contract covers both public ME/CS entry points.
Parameter conversion constructs a fresh coherent environment; CS's unsupported
event/intermediate-variable guard runs before identity validation. Null identity
pointers need no string-storage/library premise. For valid caller buffers, the
independent nonblank-name/token-equality predicate selects the actual rejection
or creation suffix with unchanged memory and arbitrary later observations.
Rejection logging retains every represented foreign result, trace and writable
effect, including the no-outcome stuck case; disabled logging returns null with
the heap unchanged. The actual pool constructs all five identity/diagnostic
strings, whose readonly storage survives represented callback writes.

`FactoryAdmission.FunctionContract` is now mandatory in `AdapterContract`.
It binds both exact public signatures, independent function tokenization,
located fragments and prepared execution to the same emitted definition table.
The fixed checker kernel-proves signature membership. The actual-file source
consequence derives complete expected-token bytes from parsed identifiers,
without assuming a successful factory execution or a supplied local environment.
The C/FMI/eFMI/compiler package checks pass in
`build/c-factory/factory-contract-packages-v1.log`, with 50 added roots and no
removed roots or axiom-policy changes. The required full artifact gate passed
in `build/c-factory/factory-full-gate-v2.log`, with all 760 source inputs and the
complete file set unchanged. Both archives are retained under
`build/c-factory/factory-artifacts/`; their C/header/GALEC members match the previous checkpoint.
The first gate attempt rejected a failed signature-membership elaboration;
structural membership proofs fixed it without changing the contract or audit.
No emitter, source grammar, numerical IR or capability changes. Successful
creation, static-slot lifetime/reuse/release, private writable-cell callback
frames, native reentrancy/divergence, headers/ABI and MISRA closure remain open;
production still uses `calloc`/`free`.

The user-authorized driven input/state profile is being developed separately.
Its generated grammar, parser actions, tensor equation/initialization lowering
and mathlib matrix/storage bridge are checked, but it has no completed target
or actual-FMU certificate yet. The production compiler rejects it. The shared
tensor types preserve rank and shape, with array-backed storage; the original
unit-only register program remains a regression path. See the
[IR review](../dev/ir-review.md) for exact correspondence and remaining work.

The newly authorized array/AD slice has shape-preserving pointwise addition
and multiplication with array-evaluation proofs. `Tensor.Differentiation`
connects their JVP rules to mathlib `HasFDerivAt`, proves the VJP dual-pairing
identity, and proves the accumulated pullback and diagonal Jacobian of a
shared-input square. These mathematical Real operator proofs pass the core
axiom audit (`build/tensor-ad-package.log`). The array development frontend now
parses fixed `[2]` input/state arrays, `[2,2]` Jacobian outputs, one `.*` product
and ordinary two-argument calls. Decoder soundness/completeness, generated
recognition, name checks and exact call/operand source ranges pass the parser
audit (`build/tensor-parser-audit.log`). `jacobian` is selected by resolution,
not reserved by the lexer. `Array.Builtin` defines its mathematical meaning by
the derivative's action on every tangent, proves the matrix is unique, and
proves the diagonal result correct for the actual resolved square call at
every shape (`build/tensor-builtin-audit.log`). Typed Solve programs now contain
pointwise arithmetic. Their forward transformation preserves primal values and
computes a true Fréchet derivative; reverse execution retains forward values
and accumulates cotangents, with an adjoint theorem for the same derivative.
`Program.forward_derivative` and `Program.reverse_derivative` quantify over
arbitrary programs, shapes and differentiable entry-register functions. All
twelve new roots pass the unchanged axiom audit (`build/tensor-program-audit.log`).
The forward transform emits ordinary Solve instructions; the reverse evaluator
currently returns a saved pullback closure, not a statically lowered target
program. The array source now has separate Flat and DAE equation/initialization
semantics and lowering proofs. The actual partial residual solver is sound,
and complete for the two admitted development forms. Its prepared IVP executes
the RHS and initialization, with an optional dense Jacobian generated by
forward AD and a mathlib diagonal materializer. `ArrayProfile.lowering_chain_correct`
and `initialization_chain_correct` compose these edges over mathematical Real
values. `ArrayCompiler.prepare_correct` also binds the stored kernel to the
actual parsed source, its EBNF membership and its complete source equations.
The source-to-Solve checkpoint passed the complete local gate in
`build/array-source-full-gate.log` and
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34462561010).
The next numerical increment now specifies exact binary64 product rounding,
overflow rejection and signed underflow. `Solve.Tensor.Finite.executes_iff`
characterizes ordered finite program execution, including every intermediate
instruction. `Array.Finite` proves nearest-value bounds for the actual square
RHS and AD-generated Jacobian coefficients against their mathematical Real
values. These 26 new roots pass the core audit in `build/finite-array-audit.log`,
and the checkpoint passed [the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34465555340).
The next C increment proves the complete counted helper bodies for addition
and multiplication over arbitrary tensor shapes. `CTensor.artifact_correct`
binds independently specified C tokens to all body behaviors, finite Solve
results and the whole-heap frame. Its eleven new roots pass the unchanged
axiom audit in `build/c-tensor-audit.log`. These helpers require finite inputs,
in-domain operations, valid readable input ranges, a separate writable output
range and a count fitting the authored 64-bit `size_t`. They do not prove
function-call ABI binding, scratch allocation, overflow/error paths or FMI
interaction. Static reverse transformation, whole-program C simulation and
tensor FMU/eFMU artifact certificates remain open;
[tensor-ad.md](../dev/tensor-ad.md) fixes the small scope. These development
parsers do not enlarge the production compiler's admitted source language.

The helper actual-file gate passed in `build/c-tensor-artifact-gate.log`.
`build/tensor-c/add-contract.log` and `mul-contract.log` audit the exact
file-literal contracts. The gate also rejects a changed loop bound and checks
native shared-input execution, output boundaries, signed underflow and empty
execution. It runs as `lake run tensor-c-test` and is included in `lake test`.
The complete gate passed in
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34469374951).
These helper certificates do not establish the remaining tensor FMU/eFMU chain.

The finite arithmetic now covers all four field operators. Alongside
round-to-nearest-even addition and multiplication, `Binary64.roundedSub` and
`Binary64.roundedDiv` specify subtraction and division on the same
integer-unit grid through the shared scaled-rounding machinery.
`roundedSub_eq_add_negate` proves rounded subtraction equals rounded addition
of the exact negation, since negation is a sign flip with no rounding; its only
negative-zero result is `(-0) - (+0)`. `roundedDiv` scales the exact quotient
`value a / value b` by the divisor's magnitude and sign, rounds it, and rejects
a zero or non-finite divisor and overflow through `finiteQuotient`;
`roundedDiv_nearest` gives the nearest-value error bound where the divisor is
nonzero. Determinism, uniqueness and the nearest/even/signed-zero relations are
proved for both, mirroring the addition and multiplication contracts.
`Solve.Tensor.Finite` executes the four operators over arbitrary tensor shapes,
and the counted C helpers `rumoca_tensor_sub` and `rumoca_tensor_div` carry the
same per-element finite-arithmetic contract as `rumoca_tensor_add` and
`rumoca_tensor_mul`. Because division is not differentiable at a zero divisor,
the tensor forward and reverse derivative theorems that assert a Fréchet
derivative record a nonzero-divisor regularity premise for division nodes,
while the smooth operators impose nothing; the executable Jacobian-vector and
adjoint rules and finite execution remain unconditional.

The subsequent call/fill increment strengthens the actual-file checker to
`CTensor.CallArtifactContract` for add/multiply and `CTensor.Fill.ArtifactContract`
for fill. It executes parameter conversions, fresh callee scopes, the actual
counted bodies and ordinary returns. `invoke_reaches` restores the exact caller
locals/types with the updated heap. A supplied definition-table binding and
header dictionary remain explicit; native linkage/ABI is not proved. Fill
preserves the exact finite value, including signed zero, and `solve_fill_correct`
identifies its result with the existing Solve initialization/seed program.
The three helper files passed `build/c-tensor-call-fill-gate.log`; all 21 new
roots pass `build/c-tensor-call-fill-audit.log` with the unchanged axiom policy.
The prior add/multiply body, finite and frame contracts remain conjuncts of the
stronger file proposition. The body-only limits above describe the earlier
checkpoint; ordinary calls are now covered, while whole-program allocation,
result storage, error policy and source-to-FMU composition remain open.
The required full gate for the call/fill increment passed locally in
`build/c-tensor-call-fill-full-gate.log` and in
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34471779750).

The complete prepared-program increment introduces a shape-indexed storage
plan with one destination per tensor instruction. `CTensor.Lowering.emit_refines`
proves all behaviors of its actual sequence of C calls against independent
`Finite.Executes`, including intermediate operations, the exact result buffer
and preservation of every cell outside the planned destinations. Initial
storage must provide disjoint writable destinations, readable finite inputs,
stable pointer/count bindings and the explicit helper/header definitions.
Intermediate storage validity is derived by the proof, not assumed separately
for each call. `emit_code_count` proves one emitted call per instruction,
independent of tensor volume. The theorem starts at function-body entry;
allocation, the outer wrapper's argument binding and native linkage remain
separate obligations. This does not admit array models into production.

`TensorProgramSyntax` independently specifies scoped pointer/count parameters
and fill/binary calls. `render_denotes` structurally certifies the printer for
arbitrary valid names and instruction lists. `Lowering.ArtifactContract` binds
that complete text to the emitted body and its finite execution theorem.
The fixed development file adapter checks the actual AD-generated square
coefficient program, universally over tensor shapes, with an explicit result
parameter. Its exact root passes `build/tensor-c/program-contract.log`; all 22
added audit roots and the actual-file/native gate pass in
`build/c-tensor-program-gate.log`. A changed add-to-multiply call is rejected.
The native check additionally requires external helper declarations; header
preprocessing and native linkage are still boundary checks. The full repository
gate for this increment passed in `build/c-tensor-program-full-gate.log` and in
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34476481293).

The next increment closes the authored outer-function entry and return:
`Lowering.program_call_refines` proves every complete call behavior against
`Finite.Executes`, with exact result storage and the whole memory frame.
Parameter conversions and fresh scope binding are derived from the independent
signature validity rules. `Lowering.CallArtifactContract` adds this guarantee
to the existing text/body proposition. The fixed program-file checker also
requires `ProgramFixture.Entry.StorageContract`: for the actual square
coefficient program, named input and scratch objects establish all required
readability, writability and separation invariants. It quantifies over arbitrary
shapes and finite input values, subject to the count bound and ordered finite
execution. The symbolic initial heap is supplied storage, not a verified
allocator or native ABI layout. External helper/header definitions remain
explicit. These call/storage proofs do not establish tensor FMI admission,
overflow/error handling or complete source-to-FMU composition.

All 34 added call/storage roots pass the unchanged axiom audit in
`build/c-tensor-entry-gate.log`. That gate also passes the stronger actual-file
certificate, operator-mutation rejection and the existing native boundary check.
`build/tensor-c/program-contract.log` audits the exact file theorem with only
`propext`, `Quot.sound` and `Classical.choice`. The required full gate for this
increment passed in `build/c-tensor-entry-full-gate.log` and in
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34479402664).

The diagonal output helper now has `CTensor.Diagonal.ArtifactContract`. It binds
the complete actual C text to ordinary call entry, the existing zero-fill call,
every diagonal copy and return. `ExecutionContract` requires exact coefficient
bit patterns on the diagonal, positive zeros elsewhere, and preservation of
every cell outside the output matrix. `SolveContract` identifies the result
with the prepared `Solve.Tensor.DiagonalProgram` after its coefficient program
has executed. All statements quantify over arbitrary tensor shapes, including
empty ones, with separate readable coefficients and a writable matrix range.
The matrix cell count must fit the authored 64-bit `size_t`; the dimension,
stride and every unsigned update are proved to fit from that single bound.
The unsigned-addition rule follows C11 N1570 §6.2.5's modulo semantics.

All 35 added roots and the actual-file/native gate pass in
`build/c-diagonal-gate.log`. `build/tensor-c/diagonal-contract.log` audits the
exact file theorem. One assertion group extends the existing native AD fixture
to its dense matrix output; no additional example model or rejection matrix
was added. The full gate passed in `build/c-diagonal-full-gate.log` and in
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34483284726).
This helper checkpoint does not compose coefficient production and diagonal
output into the actual whole model function. FMI storage/metadata/lifecycle binding,
overflow/error policy and tensor source-to-archive certificates remain open.
External header/linkage and valid object-storage assumptions remain explicit;
there is no new allocation or native ABI theorem.

The composed Jacobian function now has `Lowering.DiagonalArtifactContract`.
`emitDiagonal_correct` composes the coefficient program with its prepared
diagonal output; `diagonal_call_refines` covers every complete function-call
behavior. The result contains the exact finite Solve matrix and preserves the
coefficient buffer and every cell outside the combined destinations. Reserved
matrix storage remains writable throughout coefficient execution. The printer
supports the explicit diagonal call through independent token rules, and
`emitDiagonal_code_count` retains one call per prepared tensor operation.

`ProgramFixture.DiagonalEntry.StorageContract` discharges the generic storage
premises for the existing square/Jacobian example, universally over shapes,
finite inputs and backing heaps. Its complete-file contract replaces the
coefficient-only development artifact; no new source model or grammar case is
admitted. Ordered finite coefficient execution, a matrix count fitting `size_t`,
supplied object storage and external helper/header bindings remain explicit.
This proves the Jacobian function, not the complete IVP or FMI lifecycle.
Its 23 added roots and the actual-file/native gate pass in
`build/c-diagonal-model-gate.log`. The exact file theorem is audited in
`build/tensor-c/program-contract.log`; the required full gate passed in
`build/c-diagonal-model-full-gate.log` and in
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34487668082).

The next increment constructs C functions through `Lowering.Named` and groups
them in `PointwisePlan`, indexed by one prepared `Solve.PointwiseIVP`.
`Named.emit_correct` proves structural correspondence to the existing emitter,
including the result buffer. `PointwisePlan.correct` composes the complete-call
and independent printer contracts for initialization, RHS and the optional
diagonal observation. It requires unique entry names and excludes helper-name
collisions. Shape/count metadata remains attached to the target buffer plan;
no tensor coordinates, differentiation decisions or solver policy are introduced.

The fixed IVP artifact adapter reads all three actual C members of the existing
square/Jacobian example. Its proposition retains the complete Jacobian storage
contract and adds initializer/RHS storage contracts over arbitrary shapes,
heaps and finite input values. These derive argument binding and the lowerer's
storage predicates from readable input and writable output ranges. Initialization
produces the prepared IVP's exact zero state; RHS execution yields the independent
finite Solve result. Each call preserves every cell outside its output range.
All 22 added roots and the actual-file/native gate pass in `build/c-ivp-gate.log`.
`build/tensor-c/ivp-contract.log` audits the exact three-file theorem. The
required full gate passed in `build/c-ivp-full-gate.log` and in
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34491283172).

`CCalls.Typed` now executes the same typed tensor loop bodies with ordinary
return values, saved local types and call destinations. `loop_step` and
`loop_reaches` embed successful `CLoops.Calls` executions into this machine.
`append_reaches` carries a closed execution into an arbitrary caller context;
only the old terminal step becomes a zero-step transition. `CallResult`
requires both contextual completion and an exact standalone behavior, excluding
stuck or divergent outcomes under the existing finite-execution premises.
`invoke_return_reaches` composes the actual call statement with its caller's
return expression and conversion. It does not assign a meaning to an FMI name.

`ProgramEntry.Contract` and `DiagonalEntry.Contract` retain their previous
printer/call/storage contracts and additionally require `TypedCallCorrect` and
`TypedDiagonalCallCorrect`. The fixed three-file IVP checker therefore certifies
the emitted functions under the typed, value-returning machine too. These
theorems preserve the exact finite Solve result and whole-heap frame for all
shapes, with the same explicit storage and header/definition-table premises.
The call contracts additionally conclude that the emitted program's output
region remains writable in the returned heap whenever it was writable at entry;
this conjunct is additive and is what lets a caller iterate the prepared entry.
All 22 added roots, the stronger actual-file certificate, mutation rejection and
the existing native boundary check pass in `build/c-typed-gate.log`. The exact
file root is audited in `build/tensor-c/ivp-contract.log`; the package build
passes in `build/c-typed-package.log`. No new source model or native test matrix
is introduced. The required full gate passed in `build/c-typed-full-gate.log`
and in [the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34494402729).

These remain instantaneous C contracts. The existing FMI body proofs must still
be connected to the typed machine's statement/scope rules and composed with
the actual tensor wrappers. Instance storage/metadata, overflow/error policy,
lifecycle/time behavior and source-to-FMU/eFMU composition remain open. There
is no allocator, native ABI or machine-code theorem. Production source admission
and the README are unchanged.

`Source.Solves` is the ideal continuous reference ODE over mathematical reals,
not a complete operational interpretation of the predefined Modelica Real
class. MLS 3.7 §4.9.1 requires finite stored Real values; this implementation's
stored-value contract is the separate binary64 numerical profile. Refinement
to an unbounded ideal trajectory does not claim that such a trajectory is
itself a sequence of valid stored Real values.

For the tracked path beyond this baseline, see [the roadmap].
The newly authorized eFMI unit profile and its standards review are tracked
in [the eFMI roadmap](../dev/efmi.md). Its DAE-derived GALEC product and tensor
Solve algorithm are separate from the numerical IVP path. The Algorithm Code
contract binds actual `.alg` and both EBNF files to the source/DAE and Solve
refinement proofs. `ProductionContract` extends this with the actual complete
C member, its object-memory execution and legal serial interaction traces.
`ManifestContract` extends the code contract to the three actual XML documents,
their checked identity fields, checksum/reference construction, and decoded
mappings to C execution.
`ArchiveContract` composes the manifest contract with the complete stored-ZIP
byte grammar for the same five code/XML strings and all 45 pinned schema
resources. `compile_archive_verified` proves this contract for every successful
compiler/`Artifact.efmuArchive` result. The fixed actual-file checker constructs
`Rumoca.CheckedEFMIFiles.source_to_archive` from the complete archive bytes,
source and both grammars. Its full gate passed in
`build/efmi-archive-full-gate.log`, with only the usual three axioms. These
contracts do not certify a physical lifecycle scheduler or full eFMI standards
conformance.
The schema/text discrepancies in the pinned
eFMI 1.0.0 Beta 1 draft remain explicit review items.
The source parser and EBNF tooling live in the independent
[parser package](../packages/parser/README.md); compiler and target proofs
depend on its public runtime and proof modules. Shared IR and arithmetic live
in [core](../packages/core/README.md); C generation and target contracts live
in [backend-c](../packages/backend-c/README.md), with FMI interfaces in their
respective backend packages. The
[compiler package](../packages/compiler/README.md) composes their proofs.

## Required gate and actual-file binding

Actual-artifact certificates are native Lake build products. The fixed checking
entry points, theorem schemas and axiom whitelist are unchanged. Reuse
requires matching actual input bytes, original source identity, checker/import
dependencies, build coordination and Lean toolchain; changed or missing inputs
fail or rebuild. Cache hits also compare actual bytes and source identity with
the retained input snapshots. A freshness hash alone cannot establish that
binding. The product is the kernel-checked `.olean`, input snapshots and audit report,
not a producer-supplied proof or cached test status. Original source names are
preserved across temporary staging locations and remain part of the proposition.
File I/O, this dependency inventory and the integrity of imported build products
belong to the same explicit build trust boundary. See
[artifact certificate caching](development.md#cached-artifact-certificates).
Each certificate is a directory
`packages/compiler/.lake/build/certificates/<kind>/<trace-hash>/` holding the
kernel-checked `.olean`, the audit report, the certified identity, the freshness
trace and one input snapshot per read file; the snapshots let `--check-only`
reconfirm that the actual inputs still equal the certified bytes. The root Lake
file is part of every trace, so any input, checker or Lake-file edit adds a new
trace-hash directory and never deletes the old one. `lake run certificate-usage`
reports per-kind counts and sizes, and `lake run prune-certificates [KEEP]`
keeps the `KEEP` most-recently-used directories per kind (default two) and
removes the rest; last use is stamped on reuse as well as on build, and the
verification gate never prunes. Pruning only reclaims disk: a kept certificate
still reuses under `--check-only`, and a removed one rebuilds to the same
directory on its next use, under the same checker and axiom whitelist.
Fresh eFMU identities and timestamps remain checked against their complete new
XML and ZIP bytes. Native compilation and external compliance remain separate.
The `tensor-fmi3` certificate kind binds the same five staged files
for the pointwise tensor profile: it compiles the source with `compileTensor`,
kernel-checks the actual `model.c` against the certified tensor kernel text and
the actual `fmi3.c` against the rendered tensor adapter, and emits
`Rumoca.CheckedTensorFMI3Files.source_to_build` under the same axiom whitelist;
it caches with the same inputs as `fmi3`. The pointwise tensor array profile
(`examples/TensorSquare.mo`) is now admitted to production FMI 3 FMU output
through this certificate: the array profile gained the total located-parse
constructor `ParserActions.Parsed.parseLocated_eq` (the reusable mechanism the
unit profile uses in `LocatedTotal`), so the certificate emits the existential
`∃ a, compileTensor input = .ok a ∧ TensorSourceBuildContract a …` exactly like
the scalar `fmi3` theorem, without kernel-evaluating the LR parser on the source
text. The default `rumoca` CLI dispatches an array-profile source to
`compileTensor` and the tensor source-build path, whose publication gate is this
certificate; complete tensor eFMU (`.efmu`) output is admitted through its own
`tensor-efmi-archive` certificate (below), and only tensor C emission on stdout
stays rejected with a diagnostic, and the scalar driven profile
`examples/DrivenIntegrator.mo` stays rejected. Tensor rank and extents remain symbolic; no tensor element is
enumerated during lowering. `jacobian` is an identified language extension. The
enlarged admitted subset is recorded in the recurring standards review.

The `constant-fmi3` certificate kind binds the same five staged files for the
constant-rate profile: it compiles the source with `compileConstant`,
kernel-checks the actual `model.c` against the certified constant kernel text
(the preamble and the three rendered `rumoca_constant_*` entries) and the actual
`fmi3.c` against the rendered constant adapter, and emits
`Rumoca.CheckedConstantFMI3Files.source_to_build` under the same axiom
whitelist; it caches with the same inputs as `fmi3`. The constant-rate profile
(`examples/ConstantRates.mo`) is now admitted to production FMI 3 FMU output
through this certificate: the constant profile uses the same total located-parse
constructor `ParserActions.Parsed.located`, so the certificate emits the
existential `∃ a, compileConstant input = .ok a ∧ ConstantSourceBuildContract a …`
exactly like the scalar `fmi3` and the `tensor-fmi3` theorems, without
kernel-evaluating the LR parser on the source text. The default `rumoca` CLI
dispatches a constant-profile source to `compileConstant` and the constant
source-build path, whose publication gate is this certificate; constant eFMI
export and constant C emission stay rejected with a diagnostic. The state count
stays symbolic in the model's shape parameter; no rate coordinate is enumerated
during lowering. The pinned certificate binds the two-state `ConstantRates`
instance, so a constant source of a different state count or rate fails the
fixed checker before any FMU is produced. The enlarged admitted subset is
recorded in the recurring standards review.


Run `nix develop .#verification --command lake test`. This checks Lean proofs,
grammar freshness, axiom dependencies, actual source/C contracts, mutation
rejection and native C execution. `lake build audit` alone is insufficient.

For development, each package has a separate cached check library; see
[incremental checks](development.md). The `#audit axioms` command rejects
unapproved dependencies during Lean elaboration. Lake reuses that checked
module only while its source and import dependency traces remain current.
The complete gate retains all former audit roots and actual-file checks;
reusing package proofs does not cache a certificate for different artifact bytes.

The independent [SHA-1](../packages/sha1/README.md) and
[XML](../packages/xml/README.md) packages own their implementations, proofs and
axiom audits. They use Lean's standard library, with the local verification
tooling for their checks. The backends own model-specific documents and the
compiler composes actual-file certificates. Extracting these packages does
not extend the manifest/archive contract or establish full standards compliance.

Prioritize general formal theorems over accumulating example tests. Keep a
small set of integration checks for the trusted file adapters, external format
compatibility and native compilation. Do not add case matrices that merely
repeat behavior already quantified over by a theorem. These boundary checks
support the proof infrastructure; their count is not a measure of verification.

To verify another source within the same grammar:

```sh
nix develop .#verification
lake build
bash scripts/verify-artifact.sh path/to/Model.mo build/checked-model
```

The output directory contains a source snapshot, emitted C, a fixed checking
entry point (`Artifact.lean`), a readable producer-supplied `Candidate.lean`,
an axiom report and a SHA-256 manifest. Hashing records files; it is not a proof.
`Rumoca.ArtifactCheck` independently reads the actual source and C files,
quotes them as Lean literals and constructs the fixed proposition:

```lean
Generated.source = actualEbnf ∧
  ∃ a : Artifact source, compile source = .ok a ∧ ArtifactContract a emitted
```

The kernel checks this proposition; the adapter audits the dependencies of
that exact theorem. It never executes producer-supplied Lean commands or
accepts their theorem statements or audit text as authority. `Candidate.lean`
is for inspection/export only. The small file-to-proposition adapter, file I/O
and fixed checking entry point are explicitly trusted infrastructure. To run
that entry point directly, set `RUMOCA_SOURCE` and `RUMOCA_C` to the actual files.
It also reads the actual EBNF file (`packages/modelica-parser/grammar/Modelica.ebnf` by default, or
`RUMOCA_GRAMMAR`) and kernel-checks equality to the certified grammar source.
An early native comparison rejects a mismatched grammar; it cannot authorize
an artifact. The successful certificate proves equality of the actual and
embedded literals by kernel reflexivity, avoiding redundant UTF-8 evaluation.

## Parser and pass contracts

The new located frontend adds source-indexed UTF-8 spans without admitting
grammar cases. `Aligned` checks exact token slices, all trivia gaps, order
and disjointness. Generic LALR annotation preserves terminal/production
identity, covers children including epsilon nodes, and checks leaf ranges
against the input. `LocatedParsed.erases` retains the production parse result.
`Source.attach_complete` now proves completeness from an independent token
spelling/trivia relation, using Lean's standard UTF-8 cursor and iterator
libraries. `Rumoca.Lexes.spelled` discharges that relation for the actual
Modelica lexer. `Parsed.parseLocated_eq` and `parseLocated_complete` identify
the total located frontend with the same accepted source syntax. `Artifact`
requires a located parse; the compiler's retained `compile_complete` has no
extra location-success premise. The actual-file certificate adapters use the
same total construction. These 14 new roots pass the existing package audits
in `build/located-provenance/package-gate.log`; the required complete gate
passed in `build/located-provenance/full-gate.log`, including actual C, FMU and
eFMU certificates and existing boundary checks.
The subsequent generic LALR annotation completeness proof is described below;
origin preservation through the complete IR/printer pipeline remains open. See
[the provenance contract and roadmap](../dev/provenance.md).

The next provenance foundation adds a generic checked origin array, mandatory
nonempty parent records and a proof that every origin reaches a source leaf.
The fixed Modelica field table has exact file/AST-field lookup and production
boundary proofs; configurable-scanner attachment completeness is instantiated
for GALEC as well. These 23 new roots pass the package audit in
`build/origin-tables/package-gate.log`; the required full gate passed in
`build/origin-tables/full-gate.log`, including both actual target archives.
The source table is not yet required in every semantic IR, and no emitted-byte
origin map is certified by this increment.

`Parallel.map_eq` proves equality to sequential mapping for every pure analysis
function, input list and job budget, using Lean's standard logical `Task`
semantics. Batch results retain file identity, source snapshots and input
order. Native task scheduling and file reads are infrastructure, not a proved
OS concurrency implementation. The CLI's file reads are currently sequential.
The separate LSP reuses structured source diagnostics and converts their ranges
to UTF-16 with Lean's library. Terminal context rendering, LSP transport and
file-map conversions are tested presentation/infrastructure boundaries.

Name-resolution errors carry a primary span plus a related declaration span
in the same immutable source. `LocatedParsed.resolve_error_locations` proves
that each failing resolution points to the actual erroneous occurrence and
its declaration, with the exact AST-field text at both ranges. End-name errors
retain precedence over derivative-name errors. `resolve_complete` proves that
the enriched diagnostics retain every successful resolution. CLI JSON, context
notes and LSP related information consume this same data. The LSP respects
the client's related-information capability; `diagnostics_without_related`
proves those extra locations are omitted when support is disabled. The three
new roots pass the unchanged axiom audit, and the existing real LSP/parallel
frontend checks pass in `build/diagnostic-locations-frontend.log`.
The required full local gate passed at the previous checkpoint in
`build/diagnostic-locations-full-gate.log`, including FMI ME/CS and the complete
eFMU artifact gate. This is evidence for the unchanged authored contracts.
Compiler failure-only reparsing has now been removed: the driver returns
structured located diagnostics directly. Later IR/printer provenance remains
open; these diagnostic theorems do not close those obligations.

The [airborne assurance plan](../dev/airborne-assurance.md) records additional
requirements, traceability, independent review, target integration and tool
credit work. No current theorem establishes DO-178C compliance.

The independent `Lexes` relation specifies maximal-munch Modelica lexing.
`lex_correct` proves soundness and completeness. Source length plus one is
sufficient fuel. The token parser is sound and complete for the exact 16-token
model form. `Parsed` binds an AST to the source characters with erased proofs.
`compile_complete` proves successful compilation for every syntactically valid,
resolved tiny model.

The source frontends now use the same generated LALR parser. The old DFA
runtime, regular-expression expander, duplicated runtime tables and generator
have been removed. Successful source EBNF lowering is checked against independent
recursive expression semantics. Alphabet reflection includes unknown symbols,
which encode outside the terminal range and distinctly from EOF.

The EBNF reader accepts comma/equal and selected Rumoca/parol-style colon
notation, single/double quoted literals and implicit sequences. The embedded
reader result is kernel checked and actual grammar files must match the embedded
source. Independent character and token relations now specify this dialect;
`EBNF.parse_iff` proves exact agreement with the public text reader, including
its actual input-size budgets. `parse_rejected_iff` characterizes all rejected
source strings. Forty added generic roots pass the parser package audit in
`build/source-cutover/build/ebnf-reader/parser-package.log`. The generated
ordinary and located parser contracts now include independent source notation.
`Frontend.compile_correct` also composes that notation with CFG preservation.
Both language package audits and existing integration checks pass in the same
directory's `language-packages.log` and `integration.log`. The required main
artifact gate for P02 passed in `build/ebnf-reader/full-gate.log`, with all 591
inventoried inputs unchanged. Both actual target archives and their hashes are
retained in `build/ebnf-reader/artifacts/`. No full ISO 14977 theorem or exact
error-message contract is claimed.

The in-tree `Parser.LALR` candidate generator implements
canonical LR(1) construction and LR(0) kernel merging. `LALR.parse_sound` proves
that every successful checked parse tree derives the exact input in mathlib's
CFG semantics, universally over tables and fuel. `LALR.RuntimeProofs.run_checked`
also proves that raw execution preserves valid trees and the exact input word,
so a returned tree cannot fail the public parser's final check.

`LALR.Safety.validated_parse_safe` proves that tables passing the independent
finite structural validator cannot produce internal table or tree errors, for
any input and fuel. Checked edge annotations cover every actual shift and goto;
a backwards calculation verifies reductions for every represented stack path,
including unbounded recursive paths. The generated Lean module contains the
actual tables, edge annotations, a kernel-checked `safety_checked` proof and its
universal `execution_safe` consequence. Candidate generation is not assumed
correct. Shared reduction/acceptance summaries avoid recomputing them for each
table entry; `validate_iff` connects the implementation to its obligations.
The emitter checks each reduction summary in its own theorem and substitutes
the proved array equalities into this unchanged validator. Private proof-only
snapshot definitions add no runtime parser storage. Both emitted language
instances and the existing corruption controls pass
`build/tensor-sharded-lalr-gate.log`; this changes certificate evaluation, not
the parser's semantic contract.

`LALR.FirstCheck.validate` independently checks nullable/FIRST closure for every
grammar production. `FirstProofs.nullable_complete` and `first_complete` prove
that those facts cover every empty derivation and every derivable leading
terminal in mathlib's CFG semantics. `lookahead_complete` covers the actual
lookahead calculation used by LR closure, including a caller's lookahead after
an empty suffix. These results do not assume that the generator's fixed-point
search is correct. `lalrgen` emits the actual fact array, a kernel-checked
`first_checked` proof, and universal `nullable_coverage`/`lookahead_coverage`
corollaries. The certificate uses Lean's proof-producing `cbv` normalizer for
standard-library sorting equations; its terms are kernel checked and axiom
audited. No native-reduction axiom is introduced.

The facts may conservatively include extra nullable marks or terminals, so this
is a coverage contract, not an exact FIRST-set computation theorem. Regressions
reject missing direct/transitive predictions and nullable marks, wrong array
sizes and EOF in the grammar's terminal sets. Another regression permits a
conservative summary while proving that its nullable mark does not imply the
grammar accepts the empty word.

`LALR.ItemCheck` now checks the initial augmented item, closure, advances through
actual shifts/gotos, completed reductions and EOF acceptance. For every grammar
and table instance satisfying that validator, `Completeness.accepts_iff_parse`
proves CFG acceptance iff the actual parser accepts at some finite fuel.
`Grammar.accepts_tree` constructs the existential derivation tree from mathlib's
semantics; `Completeness.parse_tree` follows it with exactly one interpreter
transition per tree constructor plus EOF acceptance. These are universal
theorems, independent of the generator and frontend. The package proof/audit
gate passes in `build/lalr-cutover/build/completeness-audit.log`.

`LALR.Fuel` and `LALR.Progress` additionally validate grammar/state credits and
prove a strict potential decrease on every interpreter transition. Their
linear input-size bound guarantees that every word finishes with either a
correct tree or syntax rejection. Grammar membership is equivalent to success
at that same bound, and malformed inputs cannot cause internal errors or
exhaustion. The complete parser package audit passes in
`build/lalr-production/progress-audit.log`, under the unchanged axiom policy.
Both emitted grammar instances and the existing recursive/mutation controls
pass in `build/lalr-production/resource-integration.log`.
The generated entry-point and exact returned-tree contracts also pass the GALEC
audit in `build/lalr-production/entry-contract.log`. The required full root
artifact gate passed in `build/lalr-production/full-gate.log`, including both
actual target archives and the existing rejection/native controls. All 578
inventoried inputs remained unchanged throughout the run. State/item credit
arrays are proof-only; runtime fuel uses two scalar coefficients. These results
do not prove candidate-search convergence for every conflict-free LR grammar,
or wall-clock/heap performance.

The EBNF preservation increment adds independent recursive expression
semantics and a finite structural lowering certificate. Universal soundness
and completeness connect those semantics to mathlib CFG derivations, including
empty forms, named recursion and finite alphabet reflection. The public
`Frontend.lower_correct` and `compile_correct` cover successful preprocessing;
the latter binds the exact reader result. Generated `source_parse_correct`
combines a kernel-checked read of the embedded EBNF text, its expression-to-CFG
witness, acceptance equivalence and all-input bounded LR termination. The
proof-only witness is not retained by runtime token parsing.

The 19 added generic audit roots and parser packages pass in
`build/ebnf-stage/build/ebnf-package-staged.log` (796 jobs). Actual Modelica,
GALEC and recursive certificates and the existing mutation controls pass in
`build/ebnf-stage/build/ebnf-integration-staged.log`. Source-reader checking
reuses the exact character-view certificate and separately checks lexing and
expression parsing. The EBNF increment's required main artifact gate passed in
`build/ebnf-preservation/full-gate.log`, with all 584 recorded inputs unchanged
and both actual target archives retained under its `artifacts/` directory.

The subsequent source cutover supplies `LALR.TokenParser.Actions`: builders
receive the actual concrete tree and original token payloads, and specify an
independent relation between tokens and their chosen AST. The generic
`parseWith_iff` proves soundness and completeness for that relation;
`parseWith_execution` retains the actual LR result and checked tree. It neither
requires a grammar-shaped AST nor requires every AST to reconstruct a unique
token spelling. The current language-owned exact-token decoders instantiate
this interface without becoming the generic parser.

Generated one-step named-rule equations let Modelica and GALEC prove AST token
membership directly in EBNF semantics. Unit, driven and array cases use these
derivations, not execution of empty-name token patterns. GALEC also uses the
certified generated bound instead of its former fixed fuel expression. Modelica's
`parseTokens_iff`, character binding, located-source and compiler completeness
contracts are retained. Actual-artifact source membership now names independent
`EBNF.Accepts sourceGrammar`; all numerical and emitted-file fields remain.

The initial Modelica parser/action modules pass in
`build/source-cutover/build/modelica-actions.log` (770 jobs), and the GALEC package
passes in `build/source-cutover/build/galec-cutover.log` (780 jobs). The final parser package gate passed in
`build/source-cutover/build/parser-cutover-gate.log` (1525 generic/generator jobs,
806 language jobs). The downstream package audits, freshness, LALR corruption
controls, native compiler/C execution and LSP/parallel boundaries passed in
`build/source-cutover/build/downstream-cutover-v2.log`. This also fixes an
import-related Lean keyword collision by renaming an internal eFMI metadata
list; emitted manifest values are unchanged. The direct actual-source/C contract also passed in
`build/source-cutover/build/actual-c-cutover.log`. The required complete
actual-artifact gate passed in `build/lalr-source-cutover/full-gate.log`, with
all 581 recorded inputs unchanged throughout the run. Actual FMU/eFMU archives
and their hashes are retained in its `artifacts/` directory. This covers the
existing actual-source/C, FMI ME/CS, GALEC, complete eFMU and rejection/native
boundaries. These are implementation checkpoints, not a completed compiler
or FMI/eFMI compliance claim. Richer LR rejection reporting and generator
success/cost proofs remain open;
see [LR01–LR07](../dev/lalr-parser.md).

`LALR.LocatedCompleteness` now proves exact token/span preservation for arbitrary
tree fragments, including nullable nodes. Every successful raw parse has a
located result for the same tree. `parseLocated_erases` preserves the exact
success/error result; `parseLocated_correct` composes table and progress
certificates into complete located parsing at the same bound. Generated entries
choose that bound automatically and compose EBNF membership and reader-result
binding. A shared scalar `fuelForLength` avoids mapping a list solely for its
length. Spelling/trivia remains the frontend lexer's responsibility.
Eight generic and six emitted Modelica/GALEC roots pass the unchanged axiom
policy in `build/source-cutover/build/lalr-locations/language-packages-v2.log`.
Freshness and existing recursive/mutation checks pass in its `integration.log`.
The required main artifact gate for this span increment passed in
`build/lalr-located/full-gate.log`, with all 582 inventoried inputs unchanged.
Both actual target archives and their hashes are retained in
`build/lalr-located/artifacts/`; the existing C, FMI ME/CS, GALEC and eFMU
boundary and mutation checks passed.
No grammar or numerical behavior is added.

Source-indexed IRs retain their predecessors. State/register indices cannot
refer to absent values. The public per-pass contracts in `packages/compiler/Rumoca/Lowering.lean`,
`packages/backend-c/RumocaC/Lowering.lean` and the target semantics are:

| Pass | Theorem | Meaning |
| --- | --- | --- |
| AST → Flat | `Flat.lower_correct` | Equivalence of the named source equation and indexed flat equation |
| Flat → DAE | `DAE.lower_correct` | Equation holds iff its residual is zero |
| DAE → Solve | `Solve.lower_correct` | Residual is zero iff the derivative equals the solved RHS |
| Solve → C expressions | `C.lower_correct`, `C.lower_binary64_correct` | Ideal RHS preservation and exact rounded step preservation |
| C program → text | `CSyntax.module_render`, `lower_correct` | Rendered text denotes the target in an independent grammar |
| Solve → C statements | `CStatements.lower_correct`, `lower_behavior_correct` | Statement execution and all observable behaviors preserve finite Solve/source-profile semantics |

`lowering_chain_correct` explicitly composes the first four contracts.
The numerical policy and callable vocabulary live in shared `RumocaCore.Profile`;
`Rumoca.Source` imports no backend. `Profile.AdmitsUnit` requires the complete
derivative solution set to be `{1}` before licensing the fixed unit-step policy.
`Profile.behavior_congr` transports this condition and relational rounding
through equation equivalence. `Flat.behavior_correct`, `DAE.behavior_correct`
and `Solve.behavior_correct` lift each real pass;
`CStatements.solve_behavior_correct` supplies the target execution edge.
`CStatements.lower_behavior_correct` composes these in the artifact and driver
theorem. This is a policy for the frozen equation, not an arbitrary ODE solver
or general partial-pass simulation framework.
`Solve.lower_samples_correct` connects execution of the actual register
program to the independent relational source sampling policy. Proof-carrying
IR invariants are checked by the kernel; they are not added axioms.

## Shared C package and header bindings

`packages/backend-c` owns numerical C emission, the structured C tree,
object-memory and call semantics, the finite-addition extension, and thin
emission of tensor Solve algorithm instructions. It depends on core and the
proof audit tooling, with no dependency on either FMI backend or the compiler.
Both FMI backends depend on it and keep their respective wrappers, metadata
and complete-output contracts.

The routes remain DAE → GALEC → Solve → C for eFMI and DAE → Solve → C for
FMI 3. GALEC text branches from the same checked GALEC IR that is refined into
Solve. The existing tiny numerical and algorithm Solve representations are
still distinct; a shared package is not a proof that they are interchangeable.
The backend does not read GALEC text, redo DAE lowering or select a solver.

`CInterface` supplies named constants and declared C types to `CBody`,
`CCalls` and `CArithmetic`. Shared proofs quantify over this dictionary.
Each adapter installs a private local instance of its concrete header bindings;
imports install no global default. The actual compiler contracts select those
concrete bindings. eFMI type aliases are looked up in the rendered header's
declaration nodes. `CHeader.interface_alias` and `interface_return` prove the
shared interpreter's alias and return conversion agree with those declarations
for every scalar/value. These facts are fields of the actual header contract.
The meanings of primitive C types and the physical ABI retain the existing
reviewed platform boundary.

## C syntax and statement execution

`CSyntax.Denotes` specifies the emitted declarations, expressions, loop guard,
assignment and unsigned decrement through independent lexical/token rules.
`expression_render` is structural over arbitrary expressions; `module_render`
proves text denotation for every module in this syntax profile. It composes
lexical constructors directly, without executing a C reader. `denotes_unique`
proves that the same text cannot denote two different target programs.
The actual-file certificate still requires exact equality to the rendered
bytes. The header is an exact prefix; preprocessing and standard headers
remain reviewed infrastructure rather than implemented C semantics.

`CStatements` is the target semantics used by the high-level theorem. It has
statement constructors for assignment, unsigned decrement, sequencing, while
and return, with explicit local bindings, call entry and a continuation of
remaining statements. Each assignment, decrement and control operation takes
a separate transition. A missing binding is stuck: `rhs(void)` has no `x`
parameter. `lower_scoped` proves compiled bodies use only bound variables.
`denotes_statements` relates emitted characters to the statement AST's independent
token grammar. Expressions have no side effects, so evaluation order has no
observable effect in this profile.

The countdown is `Fin (2^64)` and unsigned decrement is modular subtraction.
`decrement_positive` proves it equals natural subtraction when positive; the
loop proof applies it after the nonzero guard. Every local counter is in range
by its type. The earlier `CExecution` whole-iteration machine remains with its
own execution proofs for existing contracts; it is no longer the final
operational boundary. No simulation between these two machines is currently
proved. Retiring it or proving that relation is tracked as C02.

`Transition.Machine.Behaves` distinguishes returned results, infinite execution
and stuck execution. `CStatements.behaviors_correct` proves every behavior of
each exported function is the exact finite Solve result. `all_terminate`
excludes infinite reductions. `all_complete` shows every reachable state can
finish with that result. These functions have no external calls, pointers,
volatile accesses or I/O, so observable behavior consists of termination and
the returned encoding, without an external-event trace.

## Whole-compiler theorem

`compiler_semantic_preservation` quantifies over successful compilation,
actual emitted bytes, every finite IEEE bit pattern, every uint64 count,
every exported function and every behavior. It proves the emitted text denotes
a scoped target whose behaviors are equivalent to the independent relational
`Source.SampledBehavior` semantics:

```text
compile source = ok artifact → artifact.cSource = emitted →
  ∃ targetC, Denotes emitted targetC ∧ WellScoped targetC ∧
    ∀ function bits count behavior,
      CBehaves targetC (call function bits count) behavior ↔
      SourceSampledBehavior artifact.source function bits count behavior
```

Consequently every target behavior is an allowed source-profile behavior,
and neither divergence nor stuck execution is possible. This is behavioral
preservation at the C boundary. The proof uses deterministic finite execution
and relational composition, not CompCert's general small-step simulation
framework for an optimizing C-to-assembly compiler.

`compile_verified` supplies the source/byte contract, behavior equivalence,
scoped statement syntax, termination/completion of every call,
original-symbol EBNF membership and refinement against any real source
solution. The actual-file checker checks the whole `ArtifactContract`.

Exact preservation is against the explicitly rounded numerical profile.
It would be false to claim binary64 results always equal the mathematical
real trajectory. Numerical refinement is a separate theorem.

`compiler_preserves_property` transfers any predicate of source-profile
observations to every behavior of the actual parsed output. It is derived
from `compiler_semantic_preservation`; it does not require a separate
assumption about target behavior.

The initial ME-within-CS internal contract lives in
`RumocaCore.Solve.ModelExchange`. The ME kernel owns continuous state and
derivative evaluation; `UnitSolver` consumes it; `CoSimulation.State` contains
the ME state and an exact count of completed unit steps. `run_model_correct`
and `run_progress` relate repeated solver calls to finite Solve execution and
the time grid. `ArtifactContract.model_exchange` and `co_simulation` bind the
current scalar C exports to those internal model/solver semantics.
They do **not** assert an FMI ABI, Float64 communication-time semantics,
instance-memory/lifecycle correctness or an FMU package. Those proof obligations
remain F01–F04 in the roadmap.

## FMI archive and runner

The unit profile now has a Lean FMU producer and a separate Lean runner
package reusing FMPy. `rumoca MODEL.mo -o MODEL.fmu` emits model/build XML,
an internally linked numerical `sources/model.c`, a structured C ABI adapter in
`sources/fmi3.c`, and a host Linux shared library exposing ME and CS. Before
native compilation it invokes the fixed actual-file checker on the staged
Modelica source, current EBNF, numerical kernel, adapter and both XML files, then audits
the result.
ZIP and FMPy validation run before an atomic publication rename. Failure
leaves a previously published FMU intact. Toolchain I/O and publication are
tested infrastructure, not verified filesystem operations.

`Build.recipe` supplies both the native compiler invocation and the source-build
XML for Linux x86_64/aarch64 GCC. `Build.ArtifactContract` requires valid XML
characters, a uniquely decoded recipe for each platform, the explicit C11 and
floating-point options, the single compiled `fmi3.c` source and the environment's math library.
That translation unit includes the private numerical `model.c`.
The independent `RequiredInvocation` also checks the producer's argument list,
universally over its path arguments. `FMI3.SourceBuildContract` composes this
with the unchanged numerical `ArtifactContract`. The fixed
`CheckFMI3Build.lean` adapter reads actual files from a single supplied directory
and reuses the XML package's compositional character certificates. A missing
declared library is rejected before native compilation.

Six new roots pass the unchanged axiom audit in `build/fmi-build-package.log`.
The actual-file, schema, native and mutation gate passes in
`build/fmi-build-artifact-gate.log`; the packaged `kernel-audit.log` contains
the fixed `Rumoca.CheckedFMI3Files.source_to_build` root.
The existing source-rebuild check validates the official build-description XSD,
reads compiler/options/sources/libraries from that XML, and resolves the resulting
binary in a fresh loader process. This prevents Python's already-loaded math
library from concealing a missing dependency. These are build-recipe and file
proofs plus a native boundary check; they do not prove GCC, linking, runtime
floating-point settings, the actual FMI adapter/model-description XML or the
complete FMU ZIP. The required full gate passed in `build/fmi-build-full-gate.log`.
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34502115582)
also passed.

The SR02 linkage increment generalizes the existing complete numerical
`ArtifactContract` over external or `static inline` declaration tokens, without
changing its source, execution, behavior or rounding obligations. The FMI
profile selects internal linkage and a single compiled adapter translation
unit. `modelIdentifier` is `Rumoca_` followed by the parsed model name. Source
lexical proofs establish a valid C identifier and XML text; distinct model
names have distinct identifiers. Repeated instances share an identifier, and
unrelated artifacts with the same name are not guaranteed distinct namespaces.

`FMI3.SourceBuildContract` also requires decoded modelName/ME/CS identifiers in
the actual model-description XML and the exact source prefix/include fragment
in the actual adapter. The remainder of that adapter is unconstrained by this
fragment proposition. It does not prove full preprocessing, linking, metadata
semantics or whole-adapter behavior. The native binary build uses the official
header's `FMI3_OVERRIDE_FUNCTION_PREFIX`; ordinary source composition retains
the declared prefix. The fixed reader quotes the full adapter as bounded
character blocks and uses `String.ofList` in the proposition; this avoids
kernel reduction of a large UTF-8 builder. `sourcePrefix_of_chars` derives the
same string decomposition from that input's checked character prefix. As with
literal quotation, file reading and faithful input encoding remain part of the
small trusted adapter. The certificate passes in `build/fmi-prefix-certificate.log`.
Thirteen new roots and the generalized existing roots pass
`build/fmi-linkage-package.log`. The targeted artifact/importer/source-link gate
passes in `build/fmi-linkage-artifact-gate.log`, retaining thirteen native test
groups and adding one prefix mutation. Both source FMUs compile from their own
XML recipes, link together and expose only their declared FMI APIs. Failed
native builds preserve earlier FMUs. The required full local gate passed in
`build/fmi-linkage-full-gate.log` at the previous checkpoint;
[CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34509004071) also passed.

`Solve.FMI3Model` carries the original Solve model, source names and a prepared
scalar tensor IVP. Its numerical policy remains unit Euler; default start is
zero and the unit source contract permits a finite host override. Both FMI
interfaces use the same local state and constant derivative. A CS instance
contains the ME model data and calls the existing numerical kernel directly;
it never calls ME-only FMI functions on a CS handle. Positive integer
communication steps run that many internal unit steps, with a limit of one
million per call. Unsupported/nonprogressing steps return Discard without
advancing; invalid arguments and calls return Error and enter Terminated.
Final values remain readable there; reset is required before restarting
simulation in this profile.

`Rumoca.FMI3.allowed_correct` in `RumocaCore.FMI3.Lifecycle` checks the mode table against
separately written reference predicates. `Rumoca.FMI3.guard_reference` in `RumocaFMI3.GuardProofs`
proves the constructed C integer/Boolean guard AST accepts exactly those
predicates for every command, interface kind and mode. The reference covers
the selected event-free profile, not the entire FMI standard. It must still
be reviewed against the prose and tables. These theorems **do not** establish
the function-body, memory, printer, callback, Float64 time or lifetime bridge.
`metadata_name` and the prepared-Solve projections are limited metadata facts,
not an XML schema or complete correlated-metadata theorem.

`RumocaC.Memory`, `Body` and `RumocaFMI3.StateProofs` add an object-level memory
and small-step body contract. Cells have declared types, writable permissions
and optional initialized contents. Loads reject missing, uninitialized or
ill-typed contents; stores require a writable existing cell and a supported
type conversion. Float64 contents are actual `BitVec 64` payloads, with finite
values connected to the existing binary64 encoding bijection. Addresses use
block identity, struct-member paths and array offsets; byte layout and the
native pointer ABI are not formalized by this representation.

`RumocaFMI3.LifecycleGuard.reference` connects the generated guard to those
same reference predicates in `CBody.eval`, using the actual symbolic heap.
`require_run` executes the complete three-step instance/lifecycle prefix for
every existing command, interface kind and represented mode. It preserves the
entire heap and selects either the remaining body or the emitted failure call.
The premises supply the instance binding, a fresh local `m`, and readable
kind/mode fields. `reject_prefix` stops at the failure helper; it does not
claim that logging or the final Error return has been executed.

`LifecycleBodies.terminate_correct` proves every behavior of the successful
ME/CS termination body: OK status, Terminated mode, and model/history
preservation. Its general mode-write frame protects all other cells.
`failure_mode_run` executes the actual error helper's first write and reaches
its logger; it is not a complete failed-call theorem. The state and derivative
getter proofs now cover Terminated through the common guard theorem, matching
the final-query requirement in FMI 3.0.2 §2.3.8. Core/C/FMI checks passed in
`build/fmi-termination-package.log`. The actual combined FMU, independent ME/CS
importers, native ABI and runner passed in `build/fmi-termination-artifact.log`.
The complete cross-package gate remains required. No additional source grammar
or solver is admitted by this correction.

The event/completed-step prefix and both successful initialization bodies now
use this shared guard theorem. `CBody.run_add` composes blocks through their
exact intermediate machine state. Their existing all-behavior, frame and
history/model theorems retain their statements. The shared C and FMI audits
passed in `build/fmi-lifecycle-guard-package.log`; no runtime or grammar case
changed, and these package checks do not replace the actual-artifact gate.

`StateProofs.get_behaviors` proves every behavior of the actual generated
`fmi3GetContinuousStates` body returns OK and copies the model's exact finite
encoding to the caller buffer in each permitted ME mode. `set_behaviors`
proves the corresponding `fmi3SetContinuousStates` body implements the shared
ME state update in Continuous-Time Mode. Their observations include the full
final heap. Frame theorems preserve every other address and other instance
blocks. The caller must provide correctly typed, accessible storage; separate
blocks justify ownership claims. `null_instance_behaviors` proves the common
prefix returns Error without changing memory when given a null handle.

These proofs evaluate the existing generated statement trees with independent
rules for declarations, branches, loads, stores and returns. They do not
replace FMI calls by their intended results. The pure `isfinite` intrinsic
uses the encoding's finite-range predicate.

`RumocaC.Calls` extends the memory machine with fresh parameter scopes,
checked arity and conversions, call frames and converted returns. Successful
memory transitions lift unchanged (`body_step`, `body_reaches`), and
`body_behaviors` lifts the existing terminating body contracts when the
declared return conversion succeeds. This is a successful-execution extension,
not equivalence for old stuck states: ordinary calls can now execute.
The linked program selects the actual `Runtime.helpers` trees and the existing
`CStatements` numerical program. Every numerical statement executes with the
caller heap carried unchanged; `kernel_correct` proves that bridge. Dispatch
never supplies a numerical result merely because of a function's name.

`CallProofs.model_rhs_reaches` follows the model helper into the numerical RHS.
`model_advance_behaviors` covers every finite state and uint64 count: the helper
loads state, calls the numerical sampler, writes its exact encoding and returns
void. Its final heap agrees with shared `CoSimulation.run` model state; other
addresses are unchanged by the existing frame theorem. This proves the internal
helper, not the public `fmi3DoStep` time, status and admissibility logic.
`DerivativeProofs.get_behaviors` covers the actual generated ME derivative getter
in initialization, event and continuous modes. It follows both helper calls and
returns OK with the shared ME derivative in a valid writable output cell.
Its all-behavior conclusion excludes divergence and stuck execution and includes
the full final heap. As with state access, entry bindings and accessible typed
storage are explicit premises; this is not a byte-layout or public ABI theorem.

`RumocaCore.Real.Comparison` classifies actual binary64 encodings as finite,
positive/negative infinity or NaN. Finite comparisons reuse the encoding
bijection and exact integer units. `test_finite` proves all six comparison
results agree with mathematical real order; signed zeros compare equal.
`decode_nan` and the unordered theorems cover every NaN payload. The C-tree
interpreter uses these comparisons, including its existing supported conversions
of integer zero and one. General integer-to-double conversion remains unsupported.
Comparison results do not model floating exception flags or signaling traps.
This distinction matters under the C floating environment; see
[C11 draft N1570 §§7.12.14 and F.9.3](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).

`RumocaCore.FMI3.Time.Window` independently states the ME time-history lower
bounds from [FMI 3.0.2 §3.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3SetTime):
start time, the second-last completed step and last event-mode entry. The
runtime's optional experiment stop adds an upper bound. `TimeProofs.guard_reference`
proves the actual generated validation expression accepts exactly this window
for finite inputs, assuming `timeMin` represents the maximum of those history
bounds and the stop fields represent the optional stop. `guard_nonfinite`
proves rejection before either bound is read. `set_behaviors` proves every
successful generated `fmi3SetTime` body returns OK, stores the exact input
encoding and preserves all other cells, including the shared ME model state.
The existing call-machine lifting supplies the all-behavior result.

`RumocaCore.FMI3.History` relates a positional reference history to the compact
runtime clock. Its invariant retains the experiment/event floor separately
from completion history; no monotonic-completion premise is introduced.
`trace_represents` proves preservation over every admitted reference sequence
of time updates, completions and event entries. The generated runtime now
stores `eventTime`, initialized with `startTime`, and recomputes `timeMin`
from that event floor and the previous `lastCompleted` at each completion.
This drops obsolete completion bounds. The old running maximum over-rejected
`SetTime(1.5)` after completions at `1, 2, 1, 2` even though each time query
satisfies the reference interval. Event entry preserves both the event floor
and the still-applicable second-last-completion bound.

`HistoryProofs.initial_correct`, `event_correct` and `completed_correct`
execute the actual generated history blocks under the independent C-tree
small-step rules, prove their final heaps represent the corresponding
reference updates, and preserve an arbitrary code continuation. Separate
frame theorems preserve every cell outside each block's writes. The field
comparison and conditional store are proved for all finite encodings, with
typed writable storage as a premise. `stored_guard_reference` connects the
maintained clock representation to the existing SetTime guard theorem.

`HistoryBodies.event_correct` and `completed_correct` now compose the complete
successful public `fmi3EnterEventMode` and `fmi3CompletedIntegratorStep` bodies
with the reference history, reference lifecycle mode and shared Solve/ME state.
The execution includes the instance and lifecycle guards, output-pointer guards,
both Boolean output writes, the history blocks, the event-mode write and OK
return as applicable. Every behavior terminates with the specified full heap;
divergence and stuck behavior are excluded under the stated entry conditions.
The call-machine lifting also accepts compositional reachability proofs through
`body_behaviors_of_reaches`, without changing the interpreter.

The instance clock fields must be finite, typed and writable; the event-mode
cell must be writable for event entry. Completion outputs require writable
Boolean cells and may be uninitialized or alias each other. Their storage
blocks are separate from the instance. The frame theorems preserve every cell
outside the actual write addresses; preserving another instance also requires
its storage to be separate from caller output writes. The model-state
corollaries preserve its exact Float64 encoding. These are symbolic-memory
body contracts with supplied parameter bindings, not byte-layout or public ABI
entry theorems.

Kernel mutation controls distinguish a missing event-mode write and a changed
output value from the correct successful bodies. They also check uninitialized,
missing and read-only output storage. Native tests cover aliased/distinct
outputs, both values of the unused FMU-state flag, signed-zero model state and
instance isolation.

`InitializationBodies.exit_correct` covers every behavior of the complete
successful `fmi3ExitInitializationMode` body for both ME and CS. It proves
termination with OK, agreement with the reference lifecycle transition, and
preservation of the shared model state and clock history. `exit_frame`
preserves every cell except the instance mode. The premises supply the
instance parameter, its interface kind, and a typed writable mode cell in
Initialization Mode. The existing event-free profile moves ME to Event Mode
and CS to Step Mode. This is a symbolic-memory body theorem; ABI entry,
rejected calls and printed-adapter binding remain separate obligations.
All seven new roots passed the unchanged axiom audit with
`lake build check-fmi3` in `build/fmi-initialization-exit-package.log`.
The aggregate `lake build audit` also passed in
`build/fmi-initialization-exit-audit.log`. No emitter or grammar changed in
this proof increment; these checks do not replace the required artifact gate.

`RumocaCore.FMI3.Initialization` now states the corrected unit admission profile
independently of C: start is finite and an enabled stop is finite and no earlier
than start. The unused tolerance and undefined stop retain arbitrary bits,
including NaNs. `atLeast_iff` connects its executable bit comparison to inclusive
Real order through the finite encoding bijection. The earlier finite-start body
proofs remain checked under this policy; the complete raw-argument classification
also covers nonfinite starts and rejection before any clock/state write.

`InitializationEntry.correct` covers every behavior of the complete successful
`fmi3EnterInitializationMode` body for both ME and CS. It executes the instance,
lifecycle and argument guards, four clock writes, stop/flag writes, mode change
and OK return. The final heap preserves the shared model state, represents the
initial reference history, and discharges the representation premises of the
existing `SetTime` guard theorem, including its optional stop. A full-heap frame
preserves all cells outside these seven writes. Stop and flag storage may be
uninitialized; the pre-existing clock cells must represent a finite writable
clock. Supplied entry bindings, a valid kind and a writable Instantiated mode
cell remain premises. This does not yet prove allocation establishes them.
The package audit passed in `build/fmi-initialization-entry-package.log`.
`then_exit` composes the complete entry and exit body contracts through the
same intermediate heap, retaining model state, initialized history and the
reference final mode. The aggregate audit, including this composition, passed
in `build/fmi-initialization-entry-audit.log`. This proof-only increment changes
no emitted code or grammar; its audits supplement the passing publication gate.

Those earlier body-only checkpoints used the strict policy at their recorded
revisions. The new `InitializationCalls`/`InitializationExit` contracts cover
ordinary typed public entry and return, null calls, lifecycle and raw-argument
failures, disabled logging and all represented returning logger outcomes. The
mandatory actual-file contract includes both printed fragments and their exact
function table. `QuietExecutionContract.initialize` composes entry/exit through
one intermediate heap without assuming a finite old clock; its source contract
derives the unique IVP from actual finite state storage. The corresponding
required artifact gate passed in `build/c-initialization/full-gate.log`.
General host/lifecycle histories, instance storage,
lifetime, complete CS execution and native ABI correspondence remain open.

The SR04 correction removes nominal-state queries from Instantiated after
independent review of FMI 3.0.2 §2.3.2. `ErrorBodies.nominals_reject_run` proves
the actual generated query reaches its failure call with the whole heap intact;
it requires no output-pointer premise because rejection precedes output access.
`nominals_reject_reaches` embeds this prefix in the typed tensor-call machine.
`failure_dispatch_run` covers both logging settings and `failure_log_arguments`
identifies the actual callback arguments. `failure_silent_correct` proves all
typed body-entry behaviors return Error and change only the mode cell when
logging is disabled. Enabled callback execution, string parameter binding and
the actual printed query/helper are outside those statements. This does not
yet close the failed-call or entire-FMU contract.

`RumocaC.BodyEmbedding` proves that successful `CBody` evaluation, steps and
finite runs are preserved by `CLoops`, carrying the same code, values and heap
with local type bindings. It then derives ordinary typed returns and all-body
behavior equivalence. `RumocaFMI3.BodyEmbedding` applies that bridge to the
generated runtime bodies and reuses the complete termination proof. The initial
scope premise excluded SetFloat64: its empty-array branch declared a local
variable, which the typed model rejects without block-scope semantics.
This limitation was found by attempting the universal scope proof, rather than
assuming every existing body embeds. It is not a defect in C's block semantics.
Sixteen added roots pass `build/fmi-error-embedding-audit.log`. The lifecycle
check rejects the old FMU, and the corrected artifact passes all thirteen native
groups plus the actual-file/source-link/mutation gate in
`build/fmi-nominals-artifact-gate.log`. The required full gate passed in
`build/fmi-nominals-full-gate.log` and in
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34512618273).
Production language acceptance is unchanged.

The subsequent setter refactor hoists the instance declaration and shares the
mode guard, preserving all checks and the existing value-validation/write
suffix. `SetterScope.nonnull_equivalent` and `null_equivalent` preserve every
`CCalls` behavior for arbitrary suffixes, programs and caller continuations.
They use a general finite-prefix equivalence theorem in `Transition.Prefix`;
no successful termination assumption hides wrong or divergent outcomes.
`emitted` binds the actual setter to that form. `empty_behaviors` and
`null_behaviors` prove complete typed body-entry termination with unchanged
heap, and `entry_reaches` covers the nonempty lifecycle prefix before its value
operations or failure call. `BodyEmbedding.body_closed` now quantifies over
all generated FMI bodies, with no setter exclusion and the unchanged nested
declaration restriction. Nine new roots pass `build/fmi-setter-scope-audit.log`;
all thirteen existing native groups and the actual-file/source-link/mutation
gate pass in `build/fmi-setter-scope-artifact-gate.log`. The required full gate
passed in `build/fmi-setter-scope-full-gate.log` at the previous checkpoint, and
[its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34516914151)
passed. That full run's FMU has SHA-256
`765662ef91d429089b4a22fd12dd29ec885f375a39a173c02bd4c8c35343a56f`.

The next increment adds the unsized-array parameter adjustment from
[C11 N1570 §6.7.6.3 paragraph 7](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
`CCalls.parameterType` preserves the declared pointee spelling, including
`const`, and requires the adjusted pointer type to resolve in the explicit
header dictionary. Binding still rejects unknown types, duplicate names,
wrong arity and unsupported conversions. `CallParameters.parameters_typed`
derives the matching local type environment and conversion-stable values from
successful binding; `parameters_length` and `parameters_unknown` prove the
arity and unknown-type obligations. `BodyEmbedding.typed_call_reaches` and
`typed_call_behaviors` lift a checked body run through ordinary function entry
and return, without assuming prebound locals or an arbitrary type environment.

`StateCalls.get_behaviors` and `set_behaviors` apply that bridge to complete ME
continuous-state calls. They execute the same function constructor used by
`Runtime.render`, preserving exact binary64 values and the whole-heap frame
of the existing Solve ME observation/update proofs. Only the required Float64
pointer spellings were added to the FMI type dictionary. These calls require
the explicit function-table binding, valid caller/instance storage and the
stated lifecycle preconditions. Official-header parsing, actual adapter text,
native ABI/linkage, other public signatures and rejected-call execution remain
separate obligations. All twelve added roots and the full package audit pass
in `build/fmi-array-call-audit.log`, with the unchanged axiom whitelist. The
FMI actual-file/source-build/mutation gate and all thirteen existing native
groups also pass in `build/fmi-array-call-full-gate.log`. That required full
local run passed at the previous checkpoint, including the complete GALEC/eFMU archive,
extracted-manifest and mutation checks;
[its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34521375057)
also passed. Its FMU has SHA-256
`782bc82fa92e2149c531d0ee53e1f9eb7a4760f6b54223f28093c541130d7ae2`.
No new Modelica source case is admitted.

Ordinary calls are supported as entire assignment, declaration, return or
discard operands; their arguments are pure expressions. The typed tensor-call
machine additionally supports declared-local writes and its selected arithmetic
operators; the original memory-body machine does not. Function pointers,
remaining parameter forms and typedefs, nested effectful expressions, block scopes,
allocation/free, callbacks, general C arithmetic and remaining FMI bodies need
additional rules and proofs. The selected generated assignments call pure
numerical functions or the read-only RHS helper, so evaluating their lvalues
after the call cannot observe a callee memory change. General C evaluation-order
correspondence remains part of the target review. Unsupported operations are
stuck. The successful-body results do not prove the non-null logging/error
paths, connect body trees to the actual printed adapter bytes, or extend
`ArtifactContract` to the whole FMU.

The additional kernel-checked negative controls distinguish a constant-valued
copy from the correct state copy, expose aliasing into another instance,
and reject missing storage and unsupported calls in the base memory machine.
Call regressions additionally detect a changed helper return and an unbound
numerical RHS; reject bad arity, duplicate parameters and unknown symbols;
and reject nonfinite numerical input and an out-of-range counter. Time controls
cover signed zeros, adjacent/subnormal values, infinities, quiet/signaling NaN
encodings, valid backtracking, absent stop storage, both interval boundaries
and a mutated time write. These are authored-model regressions, alongside
independent native ABI tests for the same time and state boundaries.

The required gate now also validates the actual ZIP/XML with FMPy and runs
ME/CS simulations, raw ABI lifecycle/error/time/binary64 regressions and an
independent C source rebuild. Runner CSVs and nonzero failure propagation are
checked. FMPy, its ME Euler solver, the native ABI adapter and packaging are
outside the whole-compiler theorem. The included kernel audit log records a
check performed during creation; it is not a standalone proof or signature
authenticating all members of an arbitrary archive. Full actual-FMU binding
and the public FMI conformance capstone remain open.

## Tiny eFMI Algorithm Code

`rumoca MODEL.mo -o MODEL.alg` emits the checked unit integrator's GALEC block.
It selects zero initialization and a fixed one-second period within the
existing host-initialized source profile. This does not add Modelica syntax.
Names in the emitted block are canonical; the checked product retains its
original source-indexed DAE. The authority and Beta 1 draft discrepancies are
recorded in [the eFMI review](../dev/efmi.md).

`GALEC.lower_equation_correct` checks admission of the unit DAE.
`GALEC.lower_step_correct` compares the projected method with the existing
finite numerical profile. The executable Algorithm Code refinement itself
comes from `Solve.Algorithm.lower`, without reconstructing DAE or repeating
the numerical IVP lowering. Its register references retain tensor shapes;
`lowerExpr_correct` preserves the expression interpretation for every shape
and arithmetic operation. `UnitProfile.lower_correct` additionally includes
the explicit clock-initialization program, not a backend-chosen literal.

`GALEC.Protocol.lower_trace_correct` transports every trace of the restricted
lifecycle reference. Entering and completing a method are separate events;
only idle permits output reads or another method entry. A sampling tick enters
DoStep once, and shutdown is terminal. This proves the connection between two
formal block interpreters under the authored protocol. It does not verify
concurrent host scheduling, C instance memory or an ABI implementation.

The independent GALEC scanner, named action checks and shared LR engine bind
emitted characters to the admitted block. A checked profile-specific input
bound covers the fixed token skeleton with arbitrary lexically admitted names.
`GALEC.Generated.grammar_processed` checks processing of the actual embedded
EBNF into its CFG. These facts do not establish general LR table completeness
or conformance of the EBNF reader to ISO 14977.

`EFMI.AlgorithmContract` combines source lexing/grammar membership, concrete
GALEC grammar processing, parsing/denotation of the actual `.alg` bytes, DAE
admission, binary64 methods/samples and full state/lifecycle refinement to
Solve. `EFMIArtifactCheck` independently reads the Modelica input, both EBNFs
and the actual `.alg` file. Its fixed proposition includes the two grammar
equalities and successful compilation with this contract. It audits that
theorem's dependencies before publication; producer-supplied proofs are not
executed. File I/O, the file-to-proposition adapter and atomic publication have
the same trusted-infrastructure status as the existing C artifact checker.

Use `rumoca verify-algorithm MODEL.alg --source MODEL.mo` for a standalone
member, or `rumoca verify-efmi INPUT --source MODEL.mo` for the prepared tiny
directory or complete `.efmu` archive. The CLI uses the pinned `lean4-cli` dependency and passes explicit
process arguments to fixed checking entry points. It does not generate Lean
commands from user text. The original source remains an explicit input; the
workspace determines the default grammar files. No eFMI input environment
variables are needed. The adapters share one read of each code/source file
when composing their theorems.

The directory adapter fixes the current emitted layout: `__content.xml`,
`AlgorithmCode/{manifest.xml,model.alg}` and
`ProductionCode/{manifest.xml,production.c}`. A restricted root-header reader
extracts candidate IDs and the generation time from the actual manifests.
It does not authorize XML acceptance: the manifest certificate still requires
the complete actual strings to equal the prepared trees and checks the
independent XML output grammar. The reader proposes identity strings; a separate
kernel decision proves their required identity profile. It is not a general
XML parser. Directory checking covers the five code/XML files. Archive checking
additionally binds the complete ZIP structure and all pinned resources; neither
path imports arbitrary eFMI representation layouts.

The full gate audits these roots and checks grammar/namespace reuse, source
acceptance/rejection, and mutations of arithmetic, clock initialization and
both actual grammars. The manifest checker composes the XML/reference/checksum
correlation with that same code contract. The `.efmu` output path uses the pure
`Artifact.efmuArchive` generator, checks the staged source and complete archive,
audits the fixed theorem, and then renames the checked file into place. A checked
`.alg` member alone does not supply this archive contract.

Candidate identities come from `IO.getRandomBytes` with the UUIDv4 layout
described in [RFC 9562 §5.4](https://www.rfc-editor.org/rfc/rfc9562.html#section-5.4).
The timestamp comes from `Std.Time.Timestamp.now`, formatted in UTC. The existing
manifest and actual-file contracts check whole-string identity validity, calendar
validity and distinctness within this archive. They do not assume the producer's
native decisions are proofs, nor establish entropy quality, global uniqueness
or clock accuracy. No identity work is added to DAE or Solve IR. Staging in the
destination directory permits a same-filesystem rename; file I/O, process
execution and publication remain tested infrastructure.

## Tiny eFMI Production C

The [standards review](../dev/standards-review.md) found that the previous
status-zero proof did not connect the C result to the manifest's error anchor.
The correction now declares an `EfmiStatus errorSignalStatus` instance field.
Every unit method clears it on entry and returns its stored value. Startup
accepts allocated, writable but uninitialized state, clock and status cells;
later methods require finite state/clock cells and writable status storage.
The previous status bits are arbitrary. Complete method execution still
preserves the exact numerical Solve result and every cell outside the three
declared instance fields; other instances are unchanged.

`Manifest.MappedStatus` requires a unique decoded mapping from the actual
Algorithm Code error anchor and C formal parameter to a declared status field.
`mapped_status` and `mapped_startup_status` connect that field to the actual
returned value, including uninitialized Startup storage. Both are conjuncts
of `ManifestContract`; `ManifestContract.status_observations` exposes their
composition with the actual XML/C members. `ArchiveContract` therefore also
requires them. The certified C printer's independent tokens include the
status store and return; the header contract describes all three fields.
Nine new roots pass the unchanged axiom audit in `build/efmi-status-package.log`.
The required complete artifact gate passed in `build/efmi-status-full-gate.log`,
including the actual archive theorem and redirected-status rejection.
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34499145712)
also passed.
The unit profile still has no exposed error signals. This correction neither
adds general GALEC error handling nor establishes full eFMI standards compliance.

`Solve.Algorithm.Model` retains the GALEC product and the proof that its block
is the actual algorithm lowering. `Production.lower` reads only that block.
It emits a fresh C local for each fill/add instruction and stores the return
register in the appropriate instance field. Startup explicitly executes the
clock program as well as the state program. Unsupported non-scalar storage
is rejected without enumerating tensor coordinates.

The three generated functions use a caller-owned `Model *` with separate
binary64 `x` and `samplePeriod` subobjects. `Production.method_correct` checks
every behavior of each method: it returns status zero with the exact Solve result,
preserves the clock except during Startup, and preserves unrelated memory.
Startup also has a separate theorem for allocated but uninitialized storage.
Typed parameter binding, initialized finite storage for subsequent calls, and
serialized host use are explicit preconditions. The tiny API does not contain
runtime checks for invalid pointers or host lifecycle misuse.

The interface declares `EfmiReal` as `double` and `EfmiStatus` as `int32_t`.
The structure fields use `EfmiReal`; all entry points return `EfmiStatus`.
`CHeader.header_declares` checks the header against an independent fixed token
grammar for these typedefs and fields. `Production.return_checked` checks the
returned zero against the actual declared return type. This avoids the Beta 1
prose/schema disagreement about return metadata for void functions. The status
reports successful completion under the existing preconditions; no additional
GALEC error modes or source cases have been introduced.

`CProtocol.trace_sound` and `trace_complete` connect legal serial interactions
of these actual C bodies to the Solve protocol, including output state and the
number of completed sampling calls. Method execution uses the target machine,
not a function-name lookup returning the intended value. These traces compose
with the existing GALEC/Solve theorem; they do not prove physical scheduling.

`EFMI.CSyntax.Denotes` specifies declarations, pointer-member accesses, finite
constants, additions, assignments and function headers using an independent
maximal-munch token grammar. `EFMI.CSyntax.program_render` proves that every
valid program in this syntax profile renders with the same execution-tree
denotation. Its component proofs quantify over names, expressions, statement
lists, indentation and lexical continuations. The compiler contract composes
this structural printer theorem with method execution and protocol preservation;
there is no executable Production C reader. The fixed preamble is checked as a
prefix, including the storage declaration and binary64 preprocessor guards.
Its correspondence to object layout and preprocessing remains reviewed
infrastructure. The separate fixed-header certificate still uses the shared scanner soundness
theorem. These printer theorems cover the tiny numerical and straight-line
eFMI function profiles, not the entire FMI 3 adapter or arbitrary ISO C.

The required full gate passed after the printer migration with exit status zero
in `build/c-printer-full-gate.log`. The actual source/C and combined eFMI
contract audits are preserved in `build/c-printer-artifact-contract.log` and
`build/c-printer-efmi-artifact-contract.log`. No new axiom or source-language
case was introduced.

The shared `CTree` string-expression printer now also has an independent
literal contract in `RumocaC.StringLiteral`. `CString.render_correct` proves
for every Lean string that the printed C literal uniquely denotes its UTF-8
payload followed by zero, including empty strings and embedded zero bytes.
It also proves that the modeled trigraph and line-splice rewrites cannot
change the emitted characters. The actual emitter escapes question marks;
three-digit octal escapes prevent following digits from changing a byte.
The selected rules follow [C11 N1570 §§5.1.1.2, 5.2.1.1, 6.4.4.4 and 6.4.5](https://www9.open-std.org/JTC1/SC22/WG14/www/docs/n1570.pdf)
under an explicit eight-bit ASCII source/execution profile.

Four new public roots pass the unchanged axiom audit in
`build/c-string-printer-audit.log`. A disposable native boundary reproduction
uses the actual expression printer on the formerly corrupted `??/n` payload
and passes strict C11 compilation and byte observation in
`build/c-string-trigraph-after.log`. The required full local gate passed at
the previous checkpoint in `build/c-string-printer-full-gate.log`, including both artifact
paths; [its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34527453846)
also passed. The decoder in the proof module is not a compiler pass.
The proposition describes literal object bytes, not allocation,
static lifetime, pointer decay, header binding, logger execution or surrounding
adapter syntax. Those obligations and the full FMI artifact contract remain
open; this repair admits no new grammar case.

The next storage increment uses Std's `UInt8`/`Int8` conversions in
`CCharacter`. It proves byte/value round trips for unsigned or two's-complement
signed eight-bit characters; the inverse for integer inputs requires a
representable value. `CMemory.convert` accepts only representable character
values. This is a partial conversion profile, not a claim about arbitrary C
casts or every implementation-defined signed representation.

`CReadOnly.typed_reaches` proves that all existing read-only cells survive
every reachable prefix of the authored typed-call machine, including its
ordinary returns. The analogous body/loop invariants and a load-preservation
corollary are also proved. `CLiteral.installed` constructs symbolic storage
for every UTF-8 payload and terminating zero; fresh-block installation preserves
previously supplied objects. `CLiteral.rendered_memory` binds decoded bytes of
the actual expression printer to loads from these typed character objects,
and `Stored.after_steps` preserves that storage through modeled calls.

Nine new audit roots pass in `build/c-literal-storage-audit.log` under the
unchanged axiom policy. The required full gate passed in
`build/c-literal-storage-full-gate.log`, including both target artifacts and
their existing boundary checks. There is no new unit-test suite.
The construction establishes a possible symbolic initial heap, not native
allocation, static lifetime or a global literal-address environment. It does
not require separate addresses for distinct literal texts; C permits literal
storage sharing. That checkpoint retained abstract string expression values;
the next increment below connects their evaluation to pointers. Neither
checkpoint admits a new source case.

`CInterface` now supplies an explicit static literal-address map. `CBody.eval`
decays a supported literal expression to its supplied first-element pointer;
a missing binding rejects evaluation. The abstract `CMemory.Value.string`
constructor is removed. `CLiteral.rendered_pointer` connects the actual
printer's bytes, evaluated pointer and typed character loads under the supplied
storage contract, and `Valid.after_steps` preserves that contract through
modeled calls. The selected map uses one address per literal text and allows
compatible storage sharing; it does not model every native compiler's
per-occurrence allocation. Resolving that representation against actual
adapter globals and native storage remains an explicit obligation.

FMI body proofs now quantify over supplied literal maps while retaining the
same concrete header constants/types. The dictionary additionally resolves
`const char *` and the pinned `fmi3String` pointer alias. `ErrorCalls` proves
ordinary entry and return for the actual failure helper and supplies a shared
theorem for every emitted `return fail(m, message)` statement with logging
disabled. `nominal_reject_correct` composes actual public parameter binding,
the Instantiated guard, literal evaluation, helper execution and return. Every
behavior returns Error and changes only the instance mode to Terminated;
supplied immutable literal storage survives. It covers either interface kind,
all UInt64 counts and arbitrary output pointers, including null, without an
output-dereference premise. An output address that aliases the mode cell is
subject to the stated mode-cell exception in the frame.

All twelve added roots and the existing C/FMI/eFMI/compiler package audits
passed during isolated preparation in `build/c-literal-call-package-audit.log`.
The required full root gate passed in `build/c-literal-call-full-gate.log`,
including both FMI interfaces and the actual eFMU archive/mutation gate.
The [standards review](../dev/standards-review.md#c-literal-pointer-and-rejected-call-increment-standards-impact)
records this run's retained artifact hashes and unchanged grammar identities.
These are function-tree and storage proofs with explicit signature/definition
and literal-binding premises. Complete adapter bytes, static object setup and
lifetime, enabled external callbacks and whole FMI conformance remain open.
No native compiler/ABI proof or new unit-test suite is introduced.

`CLiteral.Lowering` prepares explicit named string storage without changing the
production renderer. Its transformation replaces registered string expressions
with data identifiers and retains unregistered literals. `expression_correct`
preserves value/lvalue evaluation, including failure, and `arguments_correct`
preserves evaluated argument lists. Both sides use the same supplied C interface;
the named identifiers must resolve to the literal pointers and must not collide
with the recognized `isfinite` intrinsic.

`body_behaviors` preserves and reflects every observation of the memory-body
machine: exact returned values and heaps, stuck execution, and divergence.
Freshness of declarations prevents local capture, and the proof preserves that
invariant through branches and loops. It uses the reusable
`Transition.FunctionalBisimulation.behaviors` theorem, whose step reflection and
final-state correspondence do not assume successful termination.
At that checkpoint the theorem covered the memory-body machine. Constructing the
global dictionary, proving freshness against existing identifiers and headers,
printing/initializing static arrays, and binding those declarations to the actual
adapter are still required before the production renderer can use this pass.
The seven new audit roots and core/C package checks pass in
`build/c-literal-lowering-package-audit.log`. The required complete root gate
passed in `build/c-literal-lowering-full-gate.log`; the recurring standards
review records both retained artifact hashes. No new tests or production
language cases were added.

`LiteralLoopLowering` and `LiteralCallLowering` now extend that transformation
to the typed loop and ordinary-call machines. `loop_behaviors` preserves and
reflects their exact returned values/heaps, stuck execution and divergence.
`call_behaviors` composes parameter conversion, fresh callee scopes, loop/body
steps, continuation frames and ordinary returns for arbitrary programs,
including recursive calls. `invocation_behaviors` specializes this result to
public entry with an empty continuation; it does not assume termination.

The proofs require a supplied global dictionary, names fresh against local
parameters/declarations/writes, and structural exclusion of string literals
as direct callees. Both machines still use the same interface. This does not
prove that adding named globals preserves every existing source lookup, nor
construct or print those globals. External callbacks, native storage/ABI and
the complete emitted adapter remain outside this increment. The thirteen new
roots pass the unchanged axiom audit in `build/c-literal-loop-call-package-audit.log`.
The required full gate passed in `build/c-literal-loop-call-full-gate.log`,
including both target artifacts and their existing boundary checks. The
recurring standards review records the exact artifact hashes. No production
renderer, grammar case or test suite is added; the stage remains open.

`LiteralInterface` and `LiteralInterfaceCalls` now prove that extending a
global dictionary preserves all typed-call observations when the original
program's identifier lookups are unchanged. `LiteralPool` constructs checked
named-object candidates with distinct names, texts and block slots. Validation
checks ASCII C identifiers, reserved-name exclusion and a 63-character name
bound. `make_coverage` proves that a successful construction binds exactly the
requested texts, including duplicate requests; name collisions can reject
construction. This is partial correctness, not an unchecked name-generation
totality claim.

`LiteralPoolStorage.storage_valid` derives the literal-byte storage contract
from a concrete symbolic heap construction. Fresh pool blocks preserve every
existing cell, and `storage_after_steps` retains the literal bytes after every
typed-call execution prefix. `LiteralPoolLowering` collects identifiers read,
declared and written by the original code, including function and parameter
names. Its `Pool.invocation_behaviors` composes interface extension and literal
lowering, preserving exact return/heap, failure and divergence observations
between the original and named interfaces. The collected names establish local
freshness and lookup agreement; checked entries establish global bindings.

Header name exclusion, the connection between the function list and definition
table, and structural exclusion of direct string callees remain explicit.
Both interfaces use the constructed pool's literal addresses; no equivalence
to an arbitrary earlier literal-address assignment is claimed. This is still
the authored symbolic C machine: native storage/layout, external calls,
declaration printing and actual adapter binding are not established by these
theorems. The production renderer does not yet use the transformation.
The 27 added roots pass the unchanged C package axiom audit in
`build/c-literal-pool-package-audit.log`. The required full local gate passed
in `build/c-literal-pool-full-gate.log`. The recurring
[standards record](../dev/standards-review.md#checked-literal-pool-and-interface-extension-standards-impact)
tracks the required full gate and the unchanged MLS/FMI/eFMI obligations.

`LiteralDeclaration` and `LiteralDeclarationBlock` add independent syntax for
static character-array declarations. The printer theorem characterizes the
complete ordered sequence of names and initializer bytes, including null
terminators, after every modeled trigraph/splice rewrite. The sequence theorem
also checks physical line boundaries; it does not formalize macro expansion.
`renderBlock_storage` connects independently interpreted declarations to named
lookup and every byte of the constructed immutable symbolic arrays.
`LiteralNames` proves that successful `Pool.make` names use the fixed lowercase
prefix and satisfy the checked identifier/63-character conditions. This is
not a claim about arbitrary unchecked candidates or all native header names.

`LiteralCollection` visits every expression/statement constructor and proves
complete removal of registered string nodes. `FMI3.LiteralPreparation` applies
it to the actual renderer's function list. Its definition table uses that same
list and the prepared numerical kernel, with no supplied tree definitions.
It derives the authored constant-dictionary freshness, helper bindings and
structural call conditions. `lowering_behaviors` then preserves and reflects
every authored-machine observation for successful pool construction, any entry,
arguments and heap. Both sides use the same constructed literal addresses.

These 34 roots extend the package audits; the gate record is in
[the standards review](../dev/standards-review.md#literal-declarations-and-fmi-function-binding-standards-impact).
The renderer still emits its existing C. Full translation-unit syntax,
header/ABI correspondence, actual adapter-byte binding, callbacks and native
allocation/layout remain open. In particular, equality of observations in a
machine with unsupported external calls includes their stuck observations;
it is not a proof that every FMI call executes successfully or conforms.

`FMI3.LiteralRejection.nominal_reject` now composes that preparation with the
complete Instantiated nominal-query rejection, for either interface kind,
arbitrary output pointer/count and disabled logging. It derives the message
address, immutable bytes and helper/function bindings from the checked pool
and renderer's table. All call observations return Error, update only the mode
cell and preserve every literal object's bytes. Successful pool construction,
unique function names, inclusion of the nominal signature and fresh storage
remain explicit. `Header.signatures_unique` proves uniqueness for every
successful header-reader result; helper/public name separation and actual
signature membership are still separate obligations.

The shared scanner now selects a matching configured pair before a single
symbol. `Scanner.lex_disjoint` proves exact results and diagnostic preservation
for the previous disjoint configurations; both GALEC and Production C instantiate
it. `CTree.Syntax` proves lexical prefixes for valid names and printed naturals.
`CDecimal.render_denotes` separately proves canonical digits and their base-10
value, excluding leading-zero octal ambiguity. These are printer prerequisites,
not complete C expression syntax, integer type/range or whole-file guarantees.
The [increment's standards and gate record](../dev/standards-review.md#adapter-call-and-lexical-preparation-standards-impact)
keeps those limitations explicit.

`EFMIProductionArtifactCheck` reads the source, both EBNFs, GALEC and C files
and constructs a fixed existential theorem with one compiler artifact and
`ProductionContract` for both members. The kernel and exact-root axiom audit
authorize acceptance. This contract includes source/DAE admission, algorithm
refinement, actual C text denotation, typed entry, full memory effects and both trace
directions. It does not yet cover serialized XML, checksums or ZIP structure.

The contract also recovers the actual GALEC declaration names and includes
`Metadata.Contract` for the same lowered C module. This checks exported method
signatures, real typedefs and structure fields. `Metadata.execution_preserves`
follows the actual C behavior: reading either logical variable through the
described formal parameter and component observes its exact Solve tensor
value, and the return status is zero. Mapping identifiers are proved unique.
These are the typed mapping obligations. `ManifestContract` binds the serialized
XML and foreign-manifest/checksum construction to the same lowered module.

`EFMIManifestArtifactCheck` constructs and audits the exact
`Rumoca.CheckedEFMIFiles.source_to_manifests` theorem from the actual source,
both grammars, GALEC, C and all three XML files. XML rendering is certified by
composing element character lists, checking their equality to a flat list,
and using the standard library's string/list correspondence. Separate header
and child certificates establish the restricted XML output grammar. SHA-1
certificates check UTF-8 encoding, padding and each compression block. Native
candidate generation supplies no proof authority, and no native-reduction
axiom is used.

Manifest names are supplied from `a.parsed.ast.name`. The backend receives
this prepared metadata explicitly and performs no source name resolution.
`Manifest.prepare_named` proves that all three root attribute lists retain
the supplied name. `ManifestContract.source_name` connects these attributes
to the actual XML strings through the independent `XML.Document` relation.
The actual-file checker constructs a kernel-checked `Parsed` witness for the
source and uses parser determinism to bind its quoted name to the artifact's
AST. A native name comparison alone cannot establish the contract. Canonical
GALEC block and C function identifiers remain part of the existing interface
profile; manifest names describe the originating Modelica model.
The full gate passed with these stronger contracts in
`build/efmi-source-name-full-gate.log`; the exact actual-file root audit and
stale-manifest rejection are retained in `build/efmi-source-name-artifact.log`
and `build/efmi-source-name-rejection.log`.

`ManifestContract.identity_valid` requires whole-string membership in the
brace-delimited 8-4-4-4-12 hexadecimal UUID layout, and distinct IDs after case
normalization. It also requires a `YYYY-MM-DDTHH:MM:SSZ` timestamp with a valid
Gregorian date, reusing `Std.Time` for month lengths and leap years.
`Identity.utc_fields` recovers a checked `Std.Time.PlainDate` with exactly the
digits read from that timestamp. The emitted profile admits years 0001–9999,
hours 00–23, and minutes/seconds 00–59. `prepare_identified` binds these facts
to the root attributes of each actual document. This proves the selected
lexical/calendar profile, not global UUID freshness, wall-clock accuracy, or
acceptance of every alternate `xs:dateTime` representation.

The strengthened actual manifest contract passed the kernel and exact-root
audit in `build/efmi-identity-manifest-contract.log`. The complete required
gate passed with exit status zero in `build/efmi-identity-full-gate.log`,
including rejection of an impossible calendar date despite a consistent
checksum graph. Official XSD validation and independent checksum comparisons
are integration checks; they do not license the Lean theorem.
General XSD semantics remain a review obligation; the current SR06 disposition
below records the checker's format limitation. E05/E06 are incomplete.
The later archive and publication checkpoints extend
this manifest contract. See
[the checkpoint and remaining work](../dev/efmi.md).

The production integration gate tests native Startup/Recalibrate/DoStep,
uninitialized storage, independent instances and binary64 boundary cases.
Actual-file negative controls alter a state reference, initialization, store
target, the GALEC member, and append an extra C function. Host tests support
the authored C/IEEE review; native C compilation is not a proved lowering.

The eFMU transport has a separate `StoredZIP.Format` byte
grammar. Its stored ZIP32 profile fixes local and central records, raw member
bytes and CRCs, offsets, lengths and the final directory record. Names must be
unique ASCII relative paths; encryption, compression, extra fields, directory
entries and comments are excluded. `encode_sound` proves that the tail-recursive
ByteArray writer satisfies this list-based specification. `encode_complete`
proves generation succeeds for every admissible member sequence.

`decode_sound` proves that every accepted archive matches the complete byte
grammar. The cursor reader proposes members; an independent final validator
checks the actual complete bytes. This is a soundness theorem, not yet a
completeness theorem for the cursor reader. `number_value` proves numeric
field decoding for every representable value and width. Member inclusion and
whole-byte uniqueness keep this contract tied to the actual archive, without
assuming checksum collision resistance. Review of the authored format against
[PKWARE APPNOTE](https://pkware.cachefly.net/webdocs/casestudies/APPNOTE.TXT)
and of CRC-32 against its specified recurrence remains part of the standards
boundary. The compiler's `ArchiveContract` composes these transport results
with the correlated eFMI XML graph and existing source/C execution contract.
`archive_code_correct`, `efmu_archive_correct` and `compile_archive_verified`
prove correctness of the pure preparation and archive-generation functions.
The combined source-to-archive actual-file gate passed in
`build/efmi-archive-full-gate.log`. The CLI now stages this complete product and
requires that certificate before publication. The new public path passed the
complete required gate in `build/efmi-publication-full-gate.log`, including
independent extraction, schemas/checksums, native C, mutation rejection and
failure-preserving publication. The retained product is `build/Integrator.efmu`;
`build/efmi-publication-artifact.log` audits its four exact roots. The pinned
official checker rejects these same bytes at its extension/layout checks,
as recorded in `build/efmi-publication-official.log`; no official-checker
conformance pass is claimed.
The current [SR06 disposition](../dev/standards-review.md#sr06--resolved-packaging-question-documented-checker-limitation)
classifies those entry guards as a pinned-tool limitation: Beta 1 Chapter 2
permits the emitted standalone layout. The required gate and artifact contract
are unchanged. General standards correspondence, coding guidelines and the
other release obligations remain open.
No full eFMI conformance claim follows from the authored byte grammar alone.

The array/tensor profile adds tensor eFMI certificate kinds to the required gate.
The `tensor-algorithm` kind is delivered: it reads the Modelica source, both
EBNFs and the Algorithm Code bytes, compiles the source through `compileTensor`,
and emits the axiom-audited `Rumoca.CheckedTensorEFMIFiles.source_to_algorithm`
binding the pinned tensor square Algorithm Code to the compiled tensor artifact.
The CLI stages this member for `-o out.alg` and requires the certificate before
publication; `tests/efmi-algorithm.sh` checks the publication, no-build reuse and
a mutation-rejection control with only the usual three axioms. The tensor Production C
actual-byte checker is also implemented: `EFMITensorProductionArtifactCheck`
binds a read Production C file to the certified translation unit one certified
fragment at a time (via `RumocaEFMI.TensorProduction.render_chars`) and emits
`source_to_production`, validated standalone on the pinned `TensorSquare`
Production C with only the three approved axioms. Both remaining tensor eFMI
certificate kinds are now delivered. The `tensor-efmi-directory` kind
(`EFMITensorManifestArtifactCheck`) reads the three manifests, the Algorithm Code
and the Production C from a directory and composes their XML serialization and
validity and the SHA-1 checksum graph into `source_to_manifests`, gated in
`tests/tensor-c.sh`. The `tensor-efmi-archive` kind
(`EFMITensorArchiveArtifactCheck`) reads the actual `.efmu` bytes, re-derives that
manifest contract and composes it with the stored-ZIP transport over all fifty
members into `source_to_archive`; the tensor archive assembly and its
`TensorArchiveContract` (roster, checksums, container correlation and stored-ZIP
bytes, universal in identity and model name) supply the composition. The default
CLI admits `-o out.efmu` for the fixed tensor square profile through
`EFMIExport.writeTensorArchive` gated on that certificate, exercised in
`tests/tensor-c.sh` and `tests/efmi-production.sh`. The archive certificate peaks
at parity with the scalar eFMU archive certificate the gate already builds and
accepts; the XML serialization certificate was made linear per fragment, but the
archive peak is dominated by the re-derived manifest contract, not by any single
whole-document step; the pinned schema payloads are certified once and reused
by name across the scalar and tensor archives. See [verification performance](../dev/verification-performance.md).

## Binary64 and real refinement

The development tensor profile additionally uses `Real.ScaledRounding`,
`Real.Multiplication` and `Real.Addition`. Product rounding compares exact
integer cross-products on the binary64 grid; it never truncates the product
to an integer before rounding. The nearest/even/canonical relation has a unique
result, and the product relation separately fixes signed zero. `multiply?`
accepts exactly that relation within the strict finite overflow interval.
Its guard is proved equivalent to the Real interval; strict underflow returns
the sign-selected zero. Exactness and half-spacing error bounds are proved.
The scaled rule at denominator one agrees with the original rounding rule.

`Solve.Tensor.Finite` gives an independent execution relation for literals,
addition and multiplication on whole tensors. Execution exists exactly when
every ordered operation is in domain, and its result equals the array evaluator
with the explicit binary64 arithmetic. This includes unused intermediate
instructions: a target may not silently remove their overflow checks. The
actual square program's result is nearest to the Real RHS at every coordinate;
the AD coefficient program's result is nearest to the Real derivative `2*u`.
These are mathematical specifications used in proofs, not an implementation
of native floating-point arithmetic or a derivative of IEEE rounding.
Exception flags, traps, nonfinite inputs and the C/FMI failure policy remain
outside this new numerical contract. The production unit contract below is
unchanged.

`Binary64.Value` contains all finite encodings, including both signed zeros;
NaNs and infinities are outside the input domain. Values decode to signed
integers in units of `2^-1074`, divided by `2^1074` for the real interpretation.
The encoding covers subnormal and normal values with 52 fraction bits and
exponent fields 0 through 2046. `finiteEncodingEquiv` is a proved bijection to
the finite subset of `BitVec 64`; both inverse laws, exponent/fraction decoding
and signed-zero bit patterns are proved in `Real/Encoding.lean`.

`RoundsNearestEven` independently specifies the nearest finite encoding,
even parity on a distance tie, and canonical +0 on the duplicated-zero tie.
`round` is a noncomputable finite minimum with proved existence, specification
and uniqueness. Its kernel-checked opaque witness carries the minimality
proof; opacity prevents accidental enumeration during proof reduction and
introduces no axiom. This specification is never executed by the production
compiler. No property of Lean's opaque native `Float` is assumed.
`round_zero` proves canonical +0. The addition primitive separately retains
-0 for -0 + -0; both signed-zero cases have checked theorems.

`advance_no_overflow` proves every finite `x+1` lies strictly inside the
nearest-rounding overflow thresholds. The compiled expression therefore
never fails its overflow check. `advance_nearest` bounds its error against
any finite candidate. `advance_exact` gives zero error when the exact sum is
representable. `advance_half_spacing` bounds error by half the width of any
representable bracket containing the sum; adjacent brackets give half an ulp.

`run_exact` proves all samples through a horizon are exact whenever the ideal
samples through that horizon are representable. `Source.solution_unique`
proves uniqueness of the real source solution with the supplied initial value.
`CStatements.real_refinement` bounds the result against any such solution.
The global theorem for all finite starts and counts is:

```text
|value(run x n) - (value(x) + n)| ≤ n
```

This conservative bound includes stagnation at large magnitudes. A frozen
sampler can satisfy this bound alone, but cannot satisfy the complete compiler
contract, which requires the exact relational nearest-even result at every
step. The ODE has no discretization error under exact unit increments; the
numerical error here is rounding. The initial real value is the decoded
binary64 input, not an arbitrary decimal string before host conversion.

## Trusted boundary and coverage limits

* Lean 4.29.1's kernel and the audited standard foundations `propext`,
  `Classical.choice`, `Quot.sound`. No new axioms or proof placeholders.
* Review of the authored Modelica grammar/semantics against MLS 3.7, the C
  grammar/statement rules against C, and encoding/rounding against IEEE754.
  Prose standards are not Lean theorems. This is not CompCert Clight or a
  complete formalization of ISO C's memory model.
* Binary64 `double`, nearest-even addition, gradual underflow, standard
  integer/header meanings and the call ABI. The generated preprocessor checks
  radix, precision, exponent and `FLT_EVAL_METHOD == 0`; these do not prove an
  entire IEEE implementation. The host selects nearest rounding. NaN/Inf,
  other rounding modes, flush-to-zero and unsafe optimizations are excluded.
* Later native C compilation, assembler, linker and hardware. GCC execution
  is tested; there is no composed C-to-machine-code theorem.
* The fixed `ArtifactCheck` file-to-proposition adapter, file I/O, source
  encoding, build orchestration, and host decimal parsing and CSV formatting.
  `examples/driver.c` remains tested support code.

The theorem has an explicit all-behavior preservation shape for this tiny
profile. This does not claim CompCert's language coverage, established C
formalization, optimization/linking proofs, machine-code endpoint or maturity.

## Negative controls

The gate reproduces both artifact attacks from the review: a compiler emitting
`2.0` paired with a certificate containing only `True.intro`, and that same
wrong C paired with a valid complete certificate about a separate good C
file. Both must fail the independent actual-file checker and leave no manifest.
The actual source and EBNF files are also checked independently of candidate
literals and native freshness checks.

Other required controls reject corrupted LR tables/source witnesses, changed C
arithmetic, altered embedded Modelica source and an added logical assumption.
The obsolete executable C reader and its parser-only checks have been removed;
structural printer and grammar uniqueness theorems supply the text connection.
Actual-file mutation and forged-producer controls remain. A renamed Modelica
source with mixed admitted whitespace passes. Native tests cover fractional/negative starts,
subnormals, maximum finite values, signed zero, both even-tie directions,
iteration and malformed inputs. Tests exercise infrastructure and examples;
the theorems quantify over all admitted models, finite encodings and counts.
