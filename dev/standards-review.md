# MLS, FMI and eFMI compliance review — 2026-09-10

The current artifacts are **not ready for a full standards-compliance claim**.
This review reproduced two source-FMU integration failures, found an omitted
eFMI error-status mapping and an FMI lifecycle mismatch, and retained two
initialization restrictions as unresolved policy questions. These issues take
priority over the next tensor/FMI implementation round. No grammar, compiler
semantics, proof contract or production artifact was changed for this review.
The original findings below retain their reviewed revision and repair evidence.
The stage checklist and MLS follow-up make this a recurring three-standard
review, rather than a one-time backend inspection.

## Required review at every spiral stage

### Original scalar method semantics — repair increment; stage OPEN

No grammar expansion or new admitted source case. The original scalar parsed
member now has mandatory generic method preparation and independent body
execution in `AlgorithmContract.original_source`; state and clock have proved
whole-value transport across method-role layouts. DoStep retains literal-one
addition, with the finite domain proved only for that instruction. Startup's
non-input writes and later constant-read-only partition are the existing
restricted policies, not a new normative input-initialization resolution.

`ProductionContract.original_methods` connects those body semantics to the
existing authored C result and complete frame under finite represented entry.
The separately required allocated-only Startup branch is retained unchanged.
This improves formal source/C coverage of the frozen scalar subset; it does
not settle native ABI, host scheduling, MISRA or tensor initialization findings.
Owner V1/session91528 passed 3,657 jobs; 63 new roots are registered. Required
full gate V1/session67522 and post-audit V1/session66369 passed `ba091c6`, both
terminal0: 2,654 frozen inputs, 8,719 complete unchanged-whitelist reports, 573
selected roots, four retained actual FMU roots and all three 75-function FMI
matrices with zero discrepancies/unexpected results (526/650/526 cells).
Algorithm/Production members remained byte-identical, while the scalar
actual-file/archive proof contract now includes original-body semantics.
Evidence prefix: `build/scalar-source-`. Fresh-parser scalar composition is
still scratch (62 roots in its combined check), not a production parser cutover.
Only the three ledgers change after the frozen gate. Prior clause mappings and
all unresolved expansion blockers carry forward.

### Scalar compatibility and source-totality repair prerequisites — stage OPEN

No production grammar, source admission, interface policy or artifact changed.
The prospective replacement now preserves every old scalar typed parse's exact
AST and resolution via universal scanner and actual LALR/CST/action proofs
(six scanner roots, 21 compatibility roots; standalone final55002/75411).
The old two-assignment action-only boundary is therefore supplemented by a
successful-source theorem, not retroactively broadened. Reverse-domain and
diagnostic equality, scalar generic lowering/execution, and all product-level
artifact obligations remain separate. The obsolete tensor `.*` language is not
a preservation requirement; the admitted Modelica product and its corrected
Algorithm/Production semantics are. Full independent review read, no substantive
finding; evidence: `build/galec-scalar-{scanner,parser-compat}-draft/`.

The existing source-existence proof also composes into the same-source public
Startup theorem (one root, session75948), removing an external source-execution
premise without assuming initial input/heap representation or weakening the
output/status/input/frame contract. Main independently reviewed it in full.
Candidate tables are still not actual emitted files/archives. These are repair
prerequisites, not a new whole-subset compliance verdict; all ordinary-expansion
blockers remain, except the corrected manifest-cardinality concern below.

### Correction: scalar-encoded array manifest starts are permitted — 2026-09-23 UTC

Main read the complete pinned eFMI Beta1 §3.1.6 variable/start description,
including the text following the row-major example. Extract lines887–897
explicitly permit either a scalar encoding, used uniformly for every element,
or a multi-dimensional encoding with element values. The earlier focused
method-policy review cited only lines873–884 and failed to read this permission.
The extract is unchanged: SHA256
`2e5aff94511f8499d49a12726085335a3b470fe63950dc26ce4b4407f328f4f9`.

Therefore the single `start="0"` values emitted for u[2], x[2] and J[2,2] by
`TensorManifest.algorithmVariable` are **not a manifest cardinality defect**.
No emitter change or element enumeration is required to repair that alleged
defect. This corrects the normative interpretation, not an artifact or full
conformance claim. Source/C initialization correspondence, type/range validity
and method lifecycle retain their own evidence requirements. It does not
authorize scalar-to-array GALEC assignment or resolve initial inputs versus
the TODO assignment ban. Missing production J initialization remains open.
Historical scratch reviews are retained unchanged and superseded on this point.

### Named preparation and restricted initialization policy — stage OPEN

This is an ownership adoption of reviewed repair prerequisites, not a grammar
expansion or new admitted case. Pinned eFMI Beta1 §3.2.3, §3.2.4 S-2.11 and the
TODO input-assignment prohibition remain unresolved as recorded below. The
initialization role permits writes to non-input variables/constants, retaining
read-only inputs; its independent recursive write judgment proves only that
restricted profile, not complete normative Startup legality. Named preparation
proves exact method selection, original declarations/shapes and original-body
execution correspondence. It does not validate other methods or lifecycle order.

Owner V1/session10534 and post-owner V1 passed (2,412 jobs, 1,026 complete
whitelisted reports, 41 roots, seven owner hashes). Full gate27860 and
post-audit74127 subsequently passed `3accd67`: 2,644 frozen inputs, 8,656 complete
whitelisted reports, 510 selected roots and four retained FMU roots; all three
75-function matrices had zero discrepancies/unexpected results, with
526/650/526 cells. Algorithm/Production members stayed byte-identical.
Evidence: `build/named-preparation-adoption/`. Production languages and emitters
are unchanged. The prospective statement-list parser and same-source Startup /
DoStep body certificates now have separate checked receipts and a fully read
independent review (`build/galec-startup-{parser,certificate}-draft/`). These
discharge the supplied-text parsing/preparation step, not public dispatch,
actual-file/archive cutover or sequential lifecycle composition. Old action
compatibility is not a general old-source acceptance theorem. All prior MLS,
FMI, eFMI, initialization-correspondence, numeric/domain, native and MISRA findings remain open;
ordinary expansion remains blocked under the recurring whole-subset checklist.

### Startup initialization prerequisites — 2026-09-22; stage OPEN

The existing method-policy findings below remain authoritative: pinned eFMI
Beta1 §3.2.3 initial block/input values, §3.2.4 S-2.11 initial outputs and §3.1.6
row-major array starts require separate treatment. Core now proves shaped
vector/matrix clears and period-one assignment with independent exact values
and complete frames; generic source lowering preserves their independent
semantics. These are conditional writable-binding/shape facts, not normative
Startup capabilities. The input-initialization/assignment-ban conflict is not
resolved by assuming that input cells already hold values.

Owner V1/session9879 passed 2,406 jobs; post-owner V1/session74549 passed 985
complete whitelisted reports, 29 new roots and nine owner hashes. Main read
independent source review and checked exact owner migrations. Required full
gate V1/session22907 and post-audit V1/session46912 subsequently passed `7cef7b0`,
both terminal0: 2,638 frozen tracked inputs, 8,615 complete whitelisted reports,
all 469 selected roots and four retained FMU roots. Three FMI matrices covered
75 functions each, 526/650/526 cells and zero discrepancies/unexpected results;
actual scalar/tensor Algorithm/Production Code members stayed byte-identical.
Evidence prefix: `build/startup-initialization-`. Independent adoption review confirmed all four
exact migrations and 29 audit registrations; main read it fully. Separate
checked and independently reviewed candidate C/source-C proofs
initialize x/J without old finite reads, but actual public Startup and artifacts
remain unchanged. No initial-output finding closes before complete cutover;
manifest array starts, GJ01/GJ03/N01, all MLS/FMI findings and native/MISRA scope
remain open. This is a repair-prerequisite addendum, not a grammar-stage
expansion or new whole-subset compliance verdict. Evidence:
`build/galec-startup-{core,source,c,link}-draft/`,
`build/galec-startup-adoption/` and `build/startup-core-owner-v1.*`.

### Whole-subset Startup grammar repair review — 2026-09-23 UTC; stage OPEN

Before changing the prospective grammar, main read the complete independent
266-line review `build/galec-startup-grammar-review/review.md`. It inspects
current dispatch, both production grammars, selected actual artifacts and pinned
references at `7cef7b0`, carrying all unresolved findings forward. Its live-gate
observations are historical; the completed gate evidence is recorded above.

| Recurring checklist | Current repair decision and evidence |
| --- | --- |
| Scope and identity | Scalar unit C/FMU/Algorithm/eFMU, fixed extent-two square/Jacobian FMU/Algorithm/eFMU, pinned two-state constant FMU only. No new Modelica case or product. |
| Architecture continuity | Prospective Startup changes only from two fixed assignments to existing statement repetition, through reusable LALR/CST/typed actions; original names/bodies and shaped IR remain. No token matcher, second parse or cell enumeration. |
| Normative baseline | MLS3.7, FMI3.0.2 ME/CS, eFMI1.0Beta1. Review records pinned hashes; TODO-labelled eFMI rules stay labelled. |
| MLS coverage | Existing lexical/AnnexA, declarations/equations, Real/derivative and initialization mappings for all three profiles. Source jacobian remains an extension; S01/SR08 remain open. |
| FMI coverage | All three advertised ME/CS products retain lifecycle, access/counts, metadata/arrays, initialization/reset, prepared solver/time, status/logging, storage and source-build/archive obligations. No FMI behavior change. |
| eFMI coverage | Both eFMUs retain Startup/Recalibrate/DoStep, period, mappings/status and same-container Algorithm/Production correspondence. Beta1 §3.2.4 G-2 uses statement repetition; §3.2.3, S-2.11, §3.1.6 and TODO input-write rules keep initialization/output/start/input-policy obligations open. |
| Proof correspondence | Owned source/core initialization plus checked candidate C are prerequisites. Missing actual parsed Startup, public entry, actual-file/manifest/archive cutover and target-counter/normative permission obligations cannot be replaced by successful examples. |
| Boundary evidence | Completed full-gate records above, actual member/XML inspection in the review, and separate draft checks. Schemas/importers/native success do not establish conformance; official eFMI standalone-checker limitation remains. |
| Decision | Proceed only with the bounded scratch repair under existing user authorization. Ordinary expansion and production promotion remain blocked by unresolved findings. Preserve old scalar Startup AST and all other admitted profiles. |

The new scratch root is `build/galec-startup-parser-draft/`; the older checked
loop draft and all production files remain unchanged. Initial generation
succeeded with 598 canonical/178 LALR states and 21 rules; kernel certificates
and full typed-action/source correspondence still require their own evidence.
The companion restricted initialization policy and declaration/named-Startup/C
chain passed standalone checks with 31 and 38 roots respectively; independent
reviews were read by main (`build/galec-startup-{policy,layout}-draft/`). They
do not resolve the input-initialization conflict, manifest starts, GJ01/GJ03/N01,
source/finite history, native/ABI or MISRA obligations. No finding closes here.

### DoStep write-policy prerequisites — 2026-09-22; stage OPEN

The core now owns exact-occurrence method selection/public-end-name checks and
metadata-derived DoStep capabilities. The applicable pinned eFMI Beta1 anchors
are §3.2.4 S-2.2 (extract1916–1919), the TODO-labelled control-input assignment
prohibition (2893–2895), and §3.2.5 §3's DoStep constant/input discussion (3727).
The independent write condition is variable variability and non-input direction;
proofs trace actual resolved shaped targets and every nested source assignment
to the original declaration metadata. This does not validate arbitrary descriptor
combinations, parameter kinds absent from the IR, ranges/implicit limitation,
read/call effects, Startup or complete method/lifecycle legality.

Reviewed scope/evidence: `build/galec-dostep-capabilities-draft/review.md` and
`build/method-capability-adoption/review.md`, both read fully by main. Combined
parser/core owner passed 2,423 jobs, 1,294 complete whitelisted reports and all
44 new roots. Required full gate V1/session15943 and post-audit V1/session82397
subsequently passed `07e1060`, both terminal0: 2,630 frozen inputs, 8,586 complete
whitelisted reports, all 440 selected roots and four retained actual FMU roots.
Three FMI matrices covered 75 functions each and 526/650/526 behavior cells,
with zero recorded-finding discrepancies/unexpected results. Algorithm Code
and Production C members stayed byte-identical. Evidence prefix:
`build/method-capability-`; this gate excludes subsequent scratch repairs and
does not close any compliance finding.
The independently checked prospective named-source/C and whole-interface-header
certificates remain scratch, not admitted source/artifact evidence. MLS/FMI and
all retained eFMI findings carry forward unchanged; this is a focused repair
addendum, not a new whole-subset compliance decision or grammar expansion.

### Tensor method-policy addendum — 2026-09-22; stage OPEN

Focused independent review is `build/galec-composition-draft/method-policy-review.md`;
main read it fully and independently checked the lifecycle/input-write clauses
and actual tensor Startup/DoStep definitions. This supplements the whole-subset
checklist below; MLS/FMI and other open findings are carried forward, not newly
certified. No grammar, method implementation or numerical policy changes here.

Pinned eFMI Beta1 §3.2.3 §2/§3 (local extract lines1251–1287) requires initial
block-variable values and explicitly discusses initialized inputs. The
TODO-labelled side-effect rule at2893–2895 forbids assignments to control-inputs
without a stated Startup exception. Keep that conflict OPEN: neither blanket
writable Startup inputs nor an unstated external-initialization agreement is
justified. §3.2.4 S-2.11 (2321–2327) requires initial outputs; §3.1.6
(873–897) permits scalar-encoded uniform or row-major array manifest starts,
not scalar assignment broadcast in GALEC (corrected above). Current
`TensorStartup.lean`'s `StartupOutcome` explicitly preserves prior
u/J storage while initializing x and the clock. Therefore initial J is a real
unclosed output-initialization obligation. Scalar-to-array `self.x := 0.0` and
the manifest-to-execution initialization correspondence remain unestablished,
not certified by schemas or the current storage frame proof. Single-value
array manifest starts themselves are explicitly permitted by §3.1.6.

The conservative DoStep configuration (u/constant period read-only; x/J writable)
is supported by the side-effect and limitation clauses (3654–3729), but must
still be derived through method-specific capability validation. Constants being
read-only in DoStep does not prohibit establishing their value in Startup.
Retain the existing scope/namespace and immutable-input obligations.

No tensor eFMI Euler mismatch was found: `TensorProductionCode.doStepFunction`
calls prepared RHS and diagonal entries, agreeing with the current Algorithm
Code's RHS/Jacobian intent. FMI3 CS state-plus-derivative behavior belongs to a
different path. The new source-body proofs must compose with existing eFMI
heap/status/return contracts, not silently add Euler integration. Chapter5
(7776–7777) still requires Production Code to implement the algorithm in the
same container. GJ01/GJ03/N01, Startup, direction syntax, native/ABI and MISRA
findings remain open; ordinary language expansion remains blocked.

### Indexed AST preparation — 2026-09-22; stage OPEN

Generic surface references now retain indices on every component, expressions
represent dimension queries and ordinary callees, and loops retain unresolved
bounds/step/body. The existing grammar/actions still produce only unindexed
profiles. All arbitrary-AST projection exactness/retraction, structural
coverage, word/yield and source-compatibility contracts recheck; indexed paths
and loops cannot leak through the old projections. Owner814jobs/162reports
passes the unchanged whitelist. No admitted source/grammar/emitter/target
contract changes; the whole-subset review below applies unchanged.
The prospective183-state loop grammar now has all split kernel certificates
and24audited roots, but lacks production actions/elaboration/Integer/body/
artifact integration. R1–R5, GJ01/GJ03/N01 and all standards/MISRA/native limits
remain open. Combined full gate V2 is required for these prerequisites; the
stopped V1 and the earlier typed-body artifact gate are not substitutes.

### Lookahead closure normalization — 2026-09-22; stage OPEN

The exact named-repetition kernel fixture failed under the old sorted closure
decider, so the `f33a1eb` full gate V1 was stopped143 with no pass/post-audit claim.
Structural candidates now have universal exact membership in the same sorted
lookahead set and preserve every bounded-forall closure obligation. Only the
decision implementation changes; independent validator propositions, metadata,
parser runtime and all MLS/FMI/eFMI admitted profiles remain unchanged.
Owner1555jobs/315whitelistedreports/all3roots pass; independent review found no
weakening. The unchanged fixture now checks and both production generated
directories remain byte-identical. The larger scratch grammar's item certificate
passes, not yet its complete artifact chain. No standards finding closes;
R1–R5 and the recurring whole-subset review below remain applicable. The
combined required gate is pending, including the upcoming AST-only prerequisite.

### Signed parser resource prerequisite — 2026-09-22; stage OPEN

The generic LALR budget now permits signed nonterminal credits, with the same
independent rule/edge validators and universal valid-tree/all-input bounds.
Three repetition lemmas prove why named repeated bodies require negative
credits. Legacy successful search is preserved; bounded fallback retries both
credit sets and makes no discovery-completeness claim. Owner1553jobs/312reports
and all3roots pass the unchanged whitelist. Actual regeneration leaves both
production grammars' complete generated directories byte-identical. Independent
review's mutation-selector finding is corrected; full integration gate pending.
No source grammar, admission, numerical semantics, emitter or artifact-contract
change; the whole-subset review below remains applicable. The scratch larger
loop grammar has unresolved item-closure certificate normalization, not a new
production guarantee. All R1–R5 and GJ01/GJ03/N01/MISRA/native limits remain.

### Prospective indexed-loop GALEC repair — 2026-09-22; stage OPEN

Adopted from the independently reviewed prospective draft; main checked the
new static-expression, dimension and builtin clauses. This is the authorized
GJ01/GJ03 repair of existing admission, not ordinary language expansion.
The prototype grammar remains scratch-only. Its named statement repetition
exposes a generic parser resource-certificate limitation, to be repaired with
signed credits and unchanged universal safety/completeness/progress obligations.

| Required record | Entire admitted subset, evidence and open obligations |
| --- | --- |
| Scope and identity | Scalar unit: C/FMU/Algorithm Code/eFMU. Fixed extent-two square/Jacobian: FMU/Algorithm Code/eFMU, not standalone C. Pinned two-state ConstantRates: FMU only. Driven sources, other extents/rates, broader development parses and constant eFMI remain outside production admission. |
| Architecture continuity | Reusable in-tree LALR, recursive typed actions, independent word semantics and actual CST consumption once. Generic indexed AST/typed elaboration, not token reconstruction or fixture matching. Core owns shape/AD/prepared realization; no backend inference or compiler-time tensor-cell enumeration. |
| Normative baseline | MLS 3.7, FMI 3.0.2 ME/CS, eFMI 1.0.0 Beta 1; pinned vendor schemas/headers unchanged. MLS syntax annex and retained clause mappings, local FMI/eFMI extracts reviewed. Non-syntax MLS mappings reuse earlier ledger/initialization reviews, not a claimed new complete prose reread. No version migration or schema-only conformance inference. |
| MLS | Preserve lexical §§2.1–2.4/A.1; syntax A.2.1/A.2.2/A.2.4/A.2.6–A.2.7; equations §§8.2–8.3.1; Operator 3.12 `der`; Real §4.9.1; initialization §8.6. Existing fixed-zero, tensor shape/square/AD and constant-rate rounding/permutation contracts remain. Modelica `jacobian` is an explicit extension with an ordinary callee. S01/SR08 and ideal-Real/finite-storage limits remain. |
| FMI | All three FMUs: §§2.2.4 status, 2.3 lifecycle/logging/init/reset, 2.4 metadata, 2.4.7.2 arrays, 2.4.10 builds, 2.5.1.3 source ZIP, 3.2.1 ME, 4.2.1 CS. Preserve actual source-build/adapter/public-call/access/time/storage/lifetime/error obligations. No new capability, solver or numerical policy. Existing finite/history/native limitations remain. |
| eFMI | Both scalar/tensor outputs: §§1.3.1/3.2.3 lifecycle/sample period, 3.2.4 declarations/expressions/statements, 3.2.5 signals, Chapters 2/3/5 containers/Algorithm/Production Code. Replace target `.*` and undefined target `jacobian` with scalar indexed loops, preserving Startup/Recalibrate/DoStep meanings and Production C. Correlated manifests/checksums must bind revised Algorithm Code. N01 and block-direction TODO remain. |
| Formal correspondence | `a7b854a` proves typed whole-body execution iff the original finite square RHS and exact final store; coefficient domains follow from the primal. Signed zeros and unrelated-binding frames remain. This does not yet establish parsed-body/target-Integer/signal/native correspondence. Bind those typed bodies through actual accepted CST and artifact contracts; profile recognition alone is insufficient. |
| Artifact evidence | Required full gate and post-audit for `a7b854a` both exit0:2545unchangedinputs/8184whitelistedreports/all106requiredroots/4retainedFMUroots. Three FMI matrices75functions each,526/650/526cells,zero discrepancies/unexpected. Existing artifact/native/mutation checks pass; actual scalar/tensor Algorithm/ProductionC unchanged. These still contain the old GALEC findings and do not certify future grammar/emission changes. |
| Decision | Proceed only with scoped reusable prerequisites and authorized repair. R1–R5 below block repair completion; all other open findings continue to block ordinary expansion and broad standards/native/MISRA claims. Numerical C is unchanged. |

Applicable eFMI details in local `build/standards-review/efmi.txt`:
G-3.5–G-3.10 (2458–2470) does not list `.*`; unique function lookup (2738)
does not define `jacobian`. §3.2.1(a–c) requires bounded iteration/in-bounds
accesses and preserves multidimensional abstractions. G-3.1–G-3.4/S-3.1
(2411–2439/2502–2504) covers `size(reference,axis)` and static bounds;
§3.2.6 L-2 (5437–5439) retains target-dependent Integer checks. S-2.13/14
(2398–2405) forbids size-derived state dimensions; keep literal extents two.
The statement heading (2741–2742) is TODO-labelled, not finalized G-4.
Reference productions (2825–2836) allow per-component indices; local references
are not dotted state paths. Loops (2879–2889) use start[:step]:end and end with
`end for;`. Mutability rules (2890–2895) forbid input/iterator writes. Avoid
unresolved shadowing by fresh binders. Evaluation-order L-1 (2530) forbids
reassociation; ordinary Real infinity/qNaN propagation (3620–3624) is not an
automatic error signal. Core zero-volume proofs license neither zero-sized
source arrays nor `1:0`; FMI initial dimensions remain positive.

Repair completion obligations:

- R1: Generic indexed paths, size queries, scoped loops, typed Integer/Real
  elaboration and generated LALR certificates. Preserve Token categories and
  universal malformed-input rejection; no special Jacobian parser rule.
- R2: Proved one-based coordinate/rank/axis/range/scoping/target-Integer bridge.
  Matrices use two indices; writes obey mutability. Mathematical Nat bounds
  alone do not establish target representability or error freedom.
- R3: Compose the actual parsed body with prepared square/AD execution and
  immutable-input/output frames. Preserve primal-square finite domain, `u+u`
  order, signed zeros and positive off-diagonal zero; do not replace by `2*u`.
- R4: Replace profile-recognition-only denotation with independent typed body
  execution linked to prepared Solve and existing target execution. No backend AD.
- R5: Bind that correspondence into actual-file/archive contracts and correlated
  manifests; run the required gate for repaired artifacts. Extend existing
  boundaries with independently nonvacuous bound/index/RHS/target mutants and
  obsolete-extension rejection. Byte mismatch alone is not semantic evidence.

Baseline EBNF SHA256: Modelica
`1223b291a24cd5f80dcf3734e403164f00b55e4d25f16a0e198960456eee2907`, GALEC
`15b65a1ba11cbb1a65f92577947b6b47c2d3c9e4deb0424667490fa98b6bab73`.
Extract SHA256: eFMI
`2e5aff94511f8499d49a12726085335a3b470fe63950dc26ce4b4407f328f4f9`, FMI
`6e6f59c2209ca40a6d982a1113a20683ba2ddf7cbeda693432c3d56d9b85c7fe`.
MLS annex: `build/modelica-3.7-syntax-reference.html`. Artifact evidence:
`build/galec-typed-bodies-full-gate-v1.*`, `-post-audit-v1.*`,
`build/galec-typed-bodies-{before,after}-members.sha256`,
`build/galec-typed-bodies-fmu-retained-v1.axioms`, `-archives-v1.sha256`.
GJ01/GJ03/N01, block directions, S01/SR08, K02–K05, remaining histories and
native/ABI/callback/MISRA obligations remain open. No full conformance claim.

### Typed prepared square body — 2026-09-22; stage OPEN

The typed pointwise, rectangular clearing and diagonal-scatter bodies now have
independent execution/store-frame proofs, composed to the original finite
square RHS and exact prepared AD matrix. The source primal domain remains;
this does not add overflow signaling or failure-state behavior. No grammar,
source admission, numerical C, emission or artifact contract changed. Owner V1
passed 2312jobs/584complete whitelisted reports/all62new+44prior roots; independent
review found no issue. The combined full gate remains pending. The prospective
whole-subset checklist must be adopted before any grammar edit; no findings
close from these prerequisites. Exact scope is in dev/galec-realization.md.

### Typed loop/index prerequisite — 2026-09-22; stage OPEN

Generic resolved statements, per-axis indices, row-major coordinates and typed
environment updates are integrated without a grammar/emitter/admission change.
Core owner V1 passed 2,298jobs/522complete whitelisted reports/all44new roots;
independent semantic/adoption review found no issue. This is not the complete
repair gate. The8f9034b full gate below covers the earlier coefficient/iteration
baseline only. `dev/galec-realization.md` records exact semantic limits.
MLS/FMI/eFMI admitted profiles and MISRA/native claims are unchanged. The
prospective134line whole-subset loop-repair review is prepared in
`build/galec-loop-stage-review-draft.md`; main read it and independently checked
the new static-expression/dimension/builtin clauses. Adopt its recurring
checklist before a grammar change; no grammar expansion has yet occurred.
GJ01/GJ03/N01 and all other retained findings stay open.

### GJ01/GJ03 semantic preparation — 2026-09-22; stage OPEN

Implementation `8f9034b` passed the required full gate V1 and post-audit
(both exit0): 2,523 unchanged inputs, 8,078 complete whitelisted reports,
all 66 new roots, four retained FMU roots. All three FMI matrices and existing
artifact/native/mutation checks passed. Actual scalar/tensor Algorithm Code
and Production C members are byte-identical to the prior baseline. Evidence
and exact limits are recorded in `dev/galec-realization.md`. No finding closes
from this prerequisite gate; any future loop grammar/emission repair needs
its own complete proof/artifact chain and recurring review.

New core loop, shaped-write and prepared-coefficient realization proofs are
prerequisites only; see [galec-realization.md](galec-realization.md). MLS 3.7,
FMI 3.0.2 ME/CS and eFMI 1.0.0 Beta 1 admitted profiles, grammar and artifacts
are unchanged. All findings from the last whole-subset review carry forward.
Finite scalar execution retains the source primal-square domain and does not
pretend that ordinary GALEC Real overflow automatically raises a signal.
Mathematical bounds and zero-volume proofs do not settle G-3 surface ranges,
index conversions, Integer representability or zero-extent licensing.
No MISRA or native-machine claim changes; numerical C is not edited.
The full recurring checklist must be completed before the subsequent repair
grammar expansion. GJ01/GJ03/N01 are not closed by these semantic prerequisites.

### GJ02 repair review — 2026-09-22, positional finding closed; stage OPEN

Implementation `4371eb3` passed the required full gate V1 (exit0), with all
2,514 frozen inputs unchanged and all 8,012 complete reports under the unchanged
whitelist. All 18 selected roots (five new) were present; four retained FMU
roots were separately audited. All three FMI matrices passed 75functions and
526/650/526cells, zero discrepancies/unexpected results. Parser, source/C/helper,
FMI/eFMI artifact/native/mutation gates passed, including the three independent
old-order declaration mutations. Owner V3 had passed 2314jobs/456reports, and
bounded independent Astra review found no issue.

Actual `TensorSquare.efmu` Algorithm Code was inspected: `Real u[2]`,
`Real x[2]`, `Real J[2, 2]`. Algorithm member SHA-256:
`69c3fc4e3dd6800a558404f7a5d8d369c2d26d610eec9f7b76d12be47b127b36`;
archive SHA-256:
`f359de826bf6fa468194db794e1d5e6e7490f4bd4554fe48cb69406b85140f5c`.
Scalar Algorithm Code and scalar/tensor Production C member hashes match the
pre-repair archives. Evidence: `build/gj02-full-gate-v1.*`,
`build/gj02-fmu-retained-v1.*`, `build/gj02-{before,after}-{algorithm,production-c}.sha256`
and `build/gj02-efmu-v1.sha256`. GJ02's positional finding is closed. GJ01,
newly confirmed GJ03, N01, block directions and other findings keep the stage
OPEN. The preimplementation scope review (baseline e35c2f9) follows as history;
its prospective boundary/decision rows are superseded only by this evidence.

This is the authorized correction of GALEC declaration dimension placement,
not a new Modelica case or ordinary grammar expansion. Main independently read
the pinned G-2 productions, current CLI dispatch, fixed tensor/constant actual-
file checkers, universal tree/profile contracts and the emitter/refinement
chain. The Astra preparation is `build/gj02-stage-review-draft.md`; its live-
baseline wording is superseded by the completed gate record below.

| Required record | Reviewed scope, evidence and remaining obligation |
| --- | --- |
| Scope and identity | Baseline implementation `acf3046`, evidence `e35c2f9`. CLI admits the scalar unit profile to C/FMU/Algorithm Code/eFMU, the fixed extent-two square/Jacobian profile to FMU/Algorithm Code/eFMU, and the pinned two-state constant-rate profile to FMU only. The fixed tensor and constant file certificates do not admit every source accepted by the broader development grammar. Only the tensor GALEC spelling changes from type/dimensions/name to type/name/dimensions. Modelica EBNF and admission stay unchanged. |
| Architecture continuity | Regenerate in-tree LALR certificates and retain all nine typed actions, exhaustive coverage/licensing, actual-CST conversion, independent word semantics and all-AST projection proofs. No token-pattern parser, second parse or tensor element enumeration. Existing name/extent-separated AST and indexed IR remain unchanged. PA11 helper boundaries remain intact; no new cost-complexity claim. |
| Normative baseline | MLS 3.7, FMI 3.0.2, eFMI 1.0.0 Beta 1. Local `build/standards-review/efmi.txt` lines1878–1898 directly give type, name, optional constant dimensions, semicolon (§3.2.4 G-2). Lines1815–1846 retain the block-state direction TODO. Vendor README/SHA256SUMS pin FMI headers/eFMI schemas; those resources are not conformance proofs. No new MLS/FMI/MISRA interpretation is needed for this positional correction. |
| MLS coverage | Current lexical/resolution/equation/initialization contracts carry forward without source edits. Unit, tensor square and fixed constant-rate source-to-Solve chains must rebuild through the corrected GALEC artifact chain. Preserve raw identifier categories and extents. `jacobian` remains an identified source extension. The existing MLS initialization and finite-real/encoded distinction findings remain open; unchanged source is not new evidence closing them. |
| FMI coverage | Both ME and CS remain advertised for all three FMUs. Metadata, initialization/reset, access/counts, time/solver, errors/logging, storage/lifetime, source builds and ZIP contracts remain in scope, including existing FMI §§2.2.4, 2.4, 2.5.1.3, 3.2.1 and 4.2.1 mappings. No FMI adapter, prepared Solve or emitted C change is planned. Recheck the complete gate and retained certificates, not just GALEC parsing. Existing numerical/history/native findings carry forward. |
| eFMI coverage | Correct tensor declarations under G-2 and preserve Startup/Recalibrate/DoStep, sample-period and numerical policy. Recheck `tensor_lexical`, `tensor_render_parses`, `tensor_render_denotes`, mathematical derivative/Jacobian refinement, target execution and tensor actual-file/manifest/archive contracts. Corrected Algorithm Code changes checksums and archive identities. GJ01's missing `jacobian` definition/interface, N01 signals/error policy and the separate block-direction TODO are not repaired here. |
| Proof correspondence | `ProfileSemantics.tensor_denotes_iff` quantifies over any valid program tree; `ProfileBuild.buildTensor_tokens_iff` binds actual accepted CSTs to the complete token profile; exact projection holds on every AST. Re-elaborate their changed grammar/action/token dependencies and prove old-order rejection universally. Existing source-reference theorems refer to the current grammar/specification, so after correction they must not be described as historical language equality. Shape-parametric mathematics does not enlarge fixed artifact admission. |
| Boundary evidence | Baseline full gate passed, 2,513 frozen inputs, 8,006 reports and four retained FMU roots audited. It does not certify this prospective repair. Required repair evidence: `nix develop .#verification --command lake test`, corrected actual Algorithm Code and archive identities, unchanged whitelist, existing importer/native/schema boundaries and nonvacuous old-order mutations in the existing tensor algorithm boundary. No current corrected artifact or repair pass yet. |
| Decision | OPEN. Proceed only with the authorized GJ02 repair and its entire proof/artifact chain. Close the positional finding only after actual corrected bytes and the required gate; do not claim full declaration or standards conformance. GJ01/N01, S01/SR08 initialization, numerical/CS histories, native/ABI/callback trust, K02–K05 and whole-product MISRA obligations remain separate. Constant eFMI remains rejected; no broader ranks/extents/rates are admitted. Existing later repairs are not reopened by historical ledger wording. |

**GALEC cutover and PA11 repair (2026-09-22; full gate passed):**
Implementation `acf3046` passed the required full gate V2 (exit0). All 2,513
frozen inputs were unchanged; all 8,006 complete printed reports, including
62 cutover and 64 repair roots, passed the unchanged whitelist. Four roots
retained inside the three FMUs were separately audited. All three FMI matrices
passed 75functions and 526/650/526cells, zero recorded-finding discrepancies or
unexpected results. Existing parser/LSP, source/C/helper and scalar/tensor
FMI/eFMI artifact, native and mutation gates passed. Evidence:
`build/galec-cutover-full-gate-v2.*`,
`build/galec-cutover-fmu-retained-v2.*`.
Neither grammar nor admitted subset, emitted model C or normative coverage
changes. This closes the parser cutover's artifact-gate obligation, not
GJ01/GJ02/N01 or any whole-standard/MISRA finding. The recurring stage remains
OPEN; the next authorized positional GALEC repair needs its own reviewed
proof/artifact chain. V1 remains deliberately stopped failed evidence.

**PA11 projection repair (2026-09-22; full gate pending):**
Proof-preserving host compiler repair only; no EBNF, admitted subset, emitted
model C, standards clause coverage or formal contract changes. Compositional
AST checks retain all token categories, names, extents and malformed rejection,
with independent universal exact-image proofs and unchanged public statements.
Owner checks passed 829 jobs / 465 complete audited reports, all 64 added roots;
integrated native projection compilation passed in 2.2s. Bounded independent
Astra draft/integration reviews found no issue. These are not artifact-gate
or conformance evidence. GJ01/GJ02/N01 and the other open findings remain open.
See `docs/verification.md` and PA11 in `dev/performance-audit.md`.

**GALEC structural action cutover (2026-09-22; full gate pending):**
Repair prerequisite only: neither EBNF nor the admitted source subset changes.
Typed rule-table actions now consume the actual accepted CST and preserve the
previous source results/diagnostics. Old canonical-token decoders are retained
only as noncomputable compatibility specifications. Independent token-yield
and arbitrary-tree profile proofs do not import the superseded finite engine.
Owner checks passed 829 jobs and 401 complete reports, including all 62 new
roots, under the unchanged whitelist; no new-module warnings. The full artifact
gate remains pending; see `docs/verification.md` and
`build/galec-cutover-owner-v2.log`.
The pinned MLS/FMI/eFMI clause coverage is unchanged. In particular, ordinary
call AST construction does not supply the missing GALEC `jacobian` definition,
and structural parsing does not repair the existing dimension placement or
numerical-error policy. GJ01/GJ02/N01 and the other open findings still block
ordinary grammar expansion. No conformance or MISRA closure is claimed.

**Fixed-rate Euler interval preflight (2026-09-22; full gate passed):**
No grammar or source-admission expansion. The pinned MLS finite-real/encoded
distinction, FMI 3.0.2 §2.2.4 Discard preservation, eFMI Beta 1 §3.2.5 signal
semantics and MISRA C:2025 Dir 4.15 detection boundary remain applicable.
Universal scalar/tensor finite-prefix and reachable-overflow proofs support a
read-only scalar C interval checker with finite inputs, count < 2^64 and exact
heap preservation. Its mandatory actual-source contract includes independent
numerical meaning, not only equality to an executable classifier. Standalone
staging passed 40 roots, the fixed file adapter, three nonvacuous mutations and
the extended existing native boundary; bounded Astra review found no issue.
Integrated owner checks passed 2,900 jobs and all 2,051 printed reports,
including all 40 new roots, within the unchanged whitelist. Evidence:
`build/euler-preflight-owner-v1.log`. The required full gate passed (exit 0)
with all 2,498 frozen inputs unchanged and all 7,862 printed reports, all 40
new roots, the actual-helper contract and four retained FMU roots within the
unchanged whitelist. Integrated helper mutation/native boundaries and existing
parser/FMI/eFMI gates passed. FMI matrices exercised 75 functions each and
526/650/526 cells with zero discrepancies. Evidence:
`build/euler-preflight-full-gate-v1.log`.
No public CS failure behavior,
clock policy, native correspondence or MISRA closure is established; N01,
GJ01/GJ02 and the previous findings remain open. The authorized GALEC repair
scope does not authorize new Modelica cases or complete this stage review.

**Structural EBNF bridge (2026-09-22; full gate passed):**
Checkpoint `3f413a7` changes generic CST interpretation and certified runtime
metadata, not either EBNF, production frontend action, source admission or C
emission. Its 19 generic and four frontend audit roots passed focused checks;
actual recursive native conversion and metadata mutation controls passed.
The required full gate passed with all 2,485 frozen inputs unchanged, all
7,809 printed axiom reports, all 23 new roots, two recursive fixture roots and
four retained FMU roots within the unchanged whitelist. FMI matrices passed
75 functions each and 526/650/526 cells with zero discrepancies; existing
parser and scalar/tensor FMI/eFMI artifact/native/mutation checks passed.
Evidence: `build/ebnf-structure-full-gate-v2.log`. The original V1 run had no
terminal success evidence and is not counted as a pass.
Pinned MLS/FMI/eFMI coverage is unchanged. Classifier compatibility and frontend
AST cutover remain open; this does not complete the recurring stage review.

### GJ01 — open: undeclared tensor GALEC `jacobian`

The actual tensor Algorithm Code emitted by
`RumocaEFMI/TensorAlgorithmCode.lean` calls
`jacobian(self.u .* self.u, self.u)` without a function declaration. Independent
Astra review inspected the retained `.alg` and `build/TensorSquare.efmu`:
neither the sole GALEC member nor the Algorithm/Production Code manifests
supplies a definition, external wrapper or local-function interface.

Pinned eFMI Beta 1 §1.3.2 identifies §3.2.6 as the supported built-in catalog;
that catalog does not define `jacobian`. §1.3.3 requires a GALEC local function
or C implementation with GALEC wrapper and corresponding manifest interface.
§3.2.4 S-3.TODO (function lookup / Name-analysis) requires a uniquely named
function definition. Local normative evidence:
`build/standards-review/efmi.txt`, lines 199–206 and 2738. This is a name-resolution
finding, not an assertion that ordinary call syntax is itself invalid.

The authored parser resolves this extension internally and the mathematical
derivative proofs remain useful, but neither establishes a normative GALEC
built-in. Closure requires valid lowered GALEC or a conforming definition/
wrapper/interface, preserving mathematical refinement and binding corrected
bytes/interfaces into the actual-artifact contract. Schema, native and internal
parser successes alone do not close GJ01. It blocks further grammar expansion
alongside N01 and the existing open findings. The user explicitly authorized
repair-only GALEC grammar changes for existing undeclared-jacobian and numerical-
error findings. No new Modelica cases are authorized, and no repair is
implemented by this finding.

### GJ02 — closed: GALEC array declaration dimension placement

Pinned eFMI Beta 1 §3.2.4 G-2 declaration productions place optional constant
dimensions after the variable name. Local evidence:
`build/standards-review/efmi.txt`, lines 1878–1898. The pre-repair emitter,
authored grammar and token specification instead placed dimensions before
names. Internal parser/artifact agreement did not establish conformity with
the declaration production.

Implementation `4371eb3` repairs rendering, authored/generated grammar,
typed structural actions and token specifications without changing the AST or
indexed tensor rank/extents. Universal corrected acceptance, arbitrary-tree
profile/build proofs, renderer/refinement and target/artifact contracts passed
the required gate. New universal parser-rejection proofs cover each old slot
and combinations; three nonvacuous actual-file mutants were rejected. The
actual archive and unchanged Production C comparison are recorded above.
No token-pattern parser or decoder fallback was introduced.

Beta 1's block-state direction grammar still contains TODOs. This bounded
positional closure does not establish full declaration conformance. GJ01,
GJ03 and N01 remain separate findings; no failure policy is changed.

### GJ03 — open: nonstandard GALEC pointwise operator spelling

Main independently inspected the pinned Beta 1 §3.2.4 G-3.5–G-3.10 arithmetic
production (`build/standards-review/efmi.txt`, lines2458–2470): its alternatives
are `+`, `-`, `*`, `/`, `^`, not `.*`. Current `GALEC.ebnf`'s `product`,
`StructuralActions.product`, `Syntax.TensorBlock.tokens` and the actual tensor
Algorithm Code still use `self.u .* self.u`. Ordinary dotted state references
do not supply that binary operator. This is a GALEC finding, not a claim that
Modelica's source `.*` operator is invalid.

Closure requires a standard-compatible realization of the already prepared
pointwise operation, preserving tensor shape, exact numerical order/domain and
source meaning, with universal lowering/execution and actual-artifact proofs.
Do not replace the spelling with `*` without establishing its meaning on the
shaped operands. Bounded runtime loops are a candidate that avoids compiler-time
element enumeration; source AD, name resolution and shape inference stay
upstream. Removing the undeclared `jacobian` call alone does not close GJ03.

The GJ01 prepared-diagonal loop proposal is recorded for future review in
`build/gj01-lowering-design-review.md`; it is not implemented or proved. Main
read its full text and independently checked the cited G-3 operators, loop/
indexed-reference grammar and dimension restrictions. No grammar changed for
this finding. N01 detection, block-direction ambiguity, native correspondence
and whole-product MISRA obligations remain separate and open.

**Generic CST payload attachment (2026-09-22; full gate passed):**
This reusable parser prerequisite changes neither language EBNF, production
parser execution, source admission nor artifact emission. The pinned MLS 3.7,
FMI 3.0.2 and eFMI Beta 1 clause coverage carries forward without a new standards
interpretation. Universal proofs preserve exact CST structure and original
payloads, including noninjective encodings and nullable nodes, and establish
total attachment after successful checked parsing. Grammar validity remains an
existing-parser obligation. No language-specific case or token-pattern fallback
is added. Bounded independent Astra review found no issue.

The full required gate passed with all 2,483 frozen inputs unchanged, all 7,758
printed axiom reports, all eight new roots and four retained FMU roots within
the unchanged whitelist. FMI matrices passed 75 functions each and 526/650/526
cells, with zero discrepancies; existing parser and FMI/eFMI artifact/native/
mutation boundaries passed. Evidence: `build/cst-payload-full-gate-v1.log`.
Structural frontend actions, grammar cutover, N01, K02–K05, histories, native
correspondence and MISRA closure remain open. This is not completion of the
recurring stage review and does not authorize grammar growth.

**Tensor FMI derivative numerical Discard (2026-09-22; full gate passed):**
No grammar/admission expansion. The pinned MLS 3.7 real/encoded distinction
and eFMI Beta 1 signal constraints remain unchanged. FMI 3.0.2 §2.2.4
instance-preserving Discard/logging requirements and §3.2.1 derivative numerical
failure guidance now have a production tensor-getter instantiation: finite-input
square overflow is detected before instance or caller-output writes. Lean proves
the exact original heap at logging entry and through suppressed logging;
enabled foreign callbacks retain explicit effects and outcomes, not an invented
heap frame. Finite success retains the previous contracts and aliasing domain.
Prepared message storage, exact function lookup and rendered bytes are mandatory
actual-artifact obligations.

MISRA C:2025 Dir 4.15 motivates the pre-consumer detection boundary. Focused
Rule 10.1 review (printed pp. 98–99) found integer `!valid` inappropriate;
the emitted rejection condition is now `valid == 0`. The first gate was stopped
for this repair and is not pass evidence. This narrow review and the independent
proof/linkage review do not establish all-rule MISRA compliance. The corrected
full gate passed with all 2,482 frozen inputs unchanged, all 7,750 printed axiom
reports, all 34 new roots and four retained FMU roots within the unchanged
whitelist. Matrices passed 75 functions each, 650 TensorSquare cells and 526
cells each for Integrator/ConstantRates, with zero discrepancies. Existing
native checks cover overflow, untouched state/output, logging and recovery;
reset/preflight mutations fail actual certification. Shared-helper and
scalar/tensor eFMI checks also passed. Evidence:
`build/fmi-preflight-full-gate-v2.log`. N01's eFMI detection obligation, CS Euler
overflow, histories, native floating-environment correspondence, K02–K05 and
MISRA closure remain open and continue to block grammar expansion. This is
progress within the frozen subset, not a completed recurring stage review.

**Read-only tensor product preflight (2026-09-22; full gate passed):**
No grammar/admission or production-interface expansion. The N01 review's pinned
MLS finite-real distinction, eFMI Beta 1 overflow/signal constraints, FMI 3.0.2
§2.2.4 instance-preservation requirement and §3.2.1 numerical-failure note,
and MISRA C:2025 Dir 4.15 remain applicable and unresolved. A new shared helper
checks each product before any instance write, using a scalar local and the
existing C arithmetic rules. Its universal call theorem preserves the entire
heap and permits input aliasing and null zero-length inputs. The actual helper
contract includes syntax, execution and independent numerical characterization.
Owner/audit checks and bounded independent review passed. The required full gate
passed with all 2,464 frozen inputs unchanged, all 7,711 permitted printed axiom
reports, all 14 new roots and four permitted retained FMU roots. All three FMI
matrices, helper actual-byte/mutation/native checks and scalar/tensor eFMI checks
passed. Evidence: `build/tensor-preflight-full-gate-v1.log`. A focused check of
MISRA C:2025 Rule 2.2, printed p. 43, Notes 3, confirms that initialization is
excluded from dead-code candidates; the scalar sample initializer alone is not
a new finding under that rule. This is not an all-rule compliance review. This is
a prerequisite for public failure handling, not proof that FMI/eFMI methods
perform detection. All-path detection/consumer composition, logging/status
policy and the other open findings continue to block grammar expansion.

**Total prepared tensor RHS outcomes (2026-09-22; full gate passed):**
No source grammar/admission, emitted C, GALEC text or interface-policy expansion.
The pinned MLS 3.7 finite-real derivative distinction, eFMI Beta 1 §3.2.5 §2
overflow propagation and §1.3/§1.6 signal-interface constraints, FMI 3.0.2
§2.2.4 status/frame obligations and §3.2.1 numerical-failure note, and MISRA
C:2025 Dir 4.15 detection/consumer requirements carry forward from N01. The
new universal proof covers the actual prepared RHS wrapper, not just its
arithmetic helper; overflow remains an encoded numerical outcome, not a real
derivative. Actual FMI/eFMI contracts require this result and its finite
conservativity. Owner/audit builds and actual-wrapper native boundary checks
passed. Final owner/audit checks passed 2,643 jobs, all 24 new roots and 59
permitted printed axiom reports. Independent review's linkage concern was
resolved by explicit file-byte/function-table equality in both outcome fields;
the bounded recheck found no remaining issue. The required full gate passed with
all 2,456 inputs unchanged, all 7,683 permitted printed axiom reports (wrapped
lists included), all 24 new roots and four permitted retained FMU roots. All
three FMI matrices and scalar/tensor eFMI actual-byte, publication/reuse/mutation
and native checks passed. Scanner invocation,
all-path/consumer composition and public failure protocols remain open.
This is progress within the frozen subset, not a completed recurring stage
review or MISRA closure. All unresolved findings continue to block expansion.
Evidence: `build/tensor-rhs-outcomes-checkpoint.md`.

**Runtime tensor finiteness scanner (2026-09-22; full gate passed):**
This is a shared-backend prerequisite within the frozen subset, not a grammar
expansion or completed recurring stage review. The pinned MLS 3.7 source and
real-derivative clause coverage is unchanged. The N01 review's eFMI Beta 1
§3.2.5 §2 propagation and §1.3/§1.6 exposed-signal requirements, FMI 3.0.2
§2.2.4 status/frame distinctions and §3.2.1 numerical-failure note, and MISRA
C:2025 Dir 4.15 detection/consumer obligation carry forward without a new
interpretation. No backend-only status bit or unapproved delayed-detection
assumption is introduced. Formal coverage now includes runtime whole-tensor
scanning, typed canonical calls, exact classifier results and heap preservation.
The fixed actual-helper checker binds those proofs to emitted bytes; independent
review, actual-file certification, detector mutation rejection and the extended
existing native boundary passed. The required full gate passed with all 2,450
inputs unchanged, all 7,640 permitted printed axiom reports (wrapped lists
included), all 16 new roots and four permitted retained FMU roots. All three
FMI matrices and scalar/tensor eFMI actual-byte, publication/reuse/mutation and
native checks passed. Production
methods do not yet invoke the helper, so all-path/consumer composition and
interface failure handling remain open. N01 and every other unresolved finding
continue to block grammar growth and standards-compliance claims. Evidence:
`build/tensor-finite-scan-checkpoint.md`.

**Numerical classification foundation (2026-09-22; full gate passed):**
No grammar, admission, emitted C or interface policy change. The N01 normative
review carries forward: core tensor/bit classification and its actual-helper
heap correspondence do not establish runtime detection. The exact square
finite-execution boundary and real overflow witness are now proved in Lean;
the mandatory helper artifact contract includes classification. Owning modules,
bounded independent review and the affected-package rebuild passed: 4,289 jobs,
all 20 new roots and 5,402 permitted printed axiom reports. The required full
artifact gate passed with all 2,444 inputs unchanged, all 20 new roots, all
7,608 permitted printed axiom reports and four permitted retained FMU roots.
All three FMI matrices and scalar/tensor eFMI actual-byte/reuse/mutation/native
checks passed; evidence is in `build/numerical-detection-checkpoint.md`.
N01 and all other open findings continue to block expansion.

**Numerical error-detection follow-up (2026-09-22; open):**
[N01](numerical-outcomes-review.md) records actual tensor eFMI DoStep returning
zero status with infinite square/Jacobian outputs for finite inputs. The pinned
eFMI ordinary-overflow semantics do not themselves mandate automatic OVERFLOW
signaling; MISRA C:2025 Dir 4.15 independently requires a detection/propagation
argument. The review corrects that ledger paraphrase and records exact artifact
identities, a native observation and closure criteria. No compiler, admission,
artifact or deviation changes; no new full gate or compliance claim. This
finding and the existing open obligations continue to block grammar growth.

**Finite-input multiplication outcomes (2026-09-22; full gate passed):**
No grammar, source admission, emitted C or solver-policy expansion. The existing
pinned MLS/FMI/eFMI clause reviews carry forward; the authored C numerical model
is extended to finite-input multiplication overflow, matching the intended
nearest/even finite/infinite result profile. Exact finite-domain conservativity
is proved, and both actual-byte products require total helper outcomes. This is
not a valid-real-derivative or complete public-method overflow claim. Focused
review and native helper rehearsals passed; the affected package rebuild passed
4,286 jobs, all 32 new roots and 5,382 permitted printed axiom reports.
The required full artifact gate then passed with unchanged inputs, all 32 new
roots, 7,583 permitted printed axiom reports and four permitted retained FMU
roots. All three FMI matrices and eFMI actual-byte/reuse/mutation/native checks
passed; evidence is in `build/multiplication-outcomes-checkpoint.md`.
K02–K05, MISRA and all
unresolved normative/native-correspondence findings remain open.

**Encoded Jacobian helper outcomes (2026-09-22; full gate passed):** No grammar,
source admission, emitted C or solver-policy change. The existing pinned
MLS/FMI/eFMI clause reviews carry forward. Mandatory actual-byte products now
include the helper's finite-input overflow outcomes, without treating infinity
as a valid real derivative or claiming total source/public-method behavior.
Package checks, focused review and the extended existing native driver passed.
The required full artifact gate passed with unchanged inputs, all 24 new roots,
7,530 permitted printed axiom reports and four permitted retained FMU roots.
All three FMI matrices and eFMI actual-byte/reuse/mutation/native checks passed;
see `build/jacobian-overflow-checkpoint.md`. Native overflow checks are only
host-boundary evidence, not MISRA or IEEE-platform correspondence. K02–K05,
remaining arithmetic/size-domain restrictions and normative findings stay open.

**Finite-square derivative premise (2026-09-22; full gate passed):** No grammar,
source admission, emitted C or solver-policy change. Existing pinned MLS/FMI/eFMI
clause reviews carry forward without a new conformance claim. The existing
tensor eFMI actual-byte product is strengthened: finite square RHS execution
now suffices for the exact Jacobian and public DoStep, without an independent
finite-addition premise. This is a universal Lean domain implication, not a
successful-example argument. Package checks, focused independent review and the
required full artifact gate passed with unchanged inputs. All seven new roots,
7,378 printed axiom reports and four retained FMU roots passed the whitelist;
all three FMI matrices and eFMI actual-byte/reuse/mutation/native checks passed.
See `build/finite-square-checkpoint.md`. K02–K05, MISRA and all unresolved
normative findings remain open; native checks do not prove toolchain correspondence.

**Canonical-context integration, full gate passed (2026-09-22):** No grammar/admission, emitted C
or solver-policy expansion is included. The existing MLS/FMI/eFMI clause review
therefore carries forward without new conformance claims. The tensor eFMI fixed
artifact contracts now require public-method execution and source/Jacobian
observations through the common C evaluator; existing finite-arithmetic/storage
and external-call premises remain. The complete isolated consumer closure and
actual tensor archive certificate passed. The required full gate then passed
with unchanged inputs, all 462 new package roots, 7,477 permitted printed axiom
reports, and four permitted retained FMU roots. All three FMI matrices matched
their recorded expectations across 75 functions and 526 cells each. Scalar/tensor
eFMI artifact/reuse/mutation controls and extracted tensor-method finite/signed-zero
native checks passed. These are not a proof of host compilation or ABI correspondence.
Alignment/freshness and guard/range counterexamples are retained as formal
checks, and the tensor output-alias prose is qualified. K02–K05 and all prior
open findings remain; this is not authorization for a grammar expansion.

**Numerical applicability repair (2026-09-21, full gate passed):** The linkage review
proved that the previous standard tensor fenv type dictionary could not supply
the binary helper header/full-library premise: `double *` and `const double *`
were absent, although the numerical C functions use those spellings. Evidence:
`build/kernel-header-gap-diagnostic.log` (two universal Lean diagnostic roots,
permitted axioms only). This is a modeled integration/non-vacuity gap, not a
claimed native or normative FMI violation. The combined repair is promoted:
real header bindings, instruction-restricted numerical proofs, production-owned
IVP/C plans, and mandatory same-source actual-table accepted/rejected execution.
The existing MLS/FMI/eFMI review clauses carry forward: no admission, grammar,
emitted C, solver policy or boundary suite changes. The coherent owning-package
rebuild passed all 4,163 jobs, including all 150 new roots; all 4,857 printed axiom
lists were permitted. The explicit event-type proof repair changed no statement.
The required full artifact gate passed (exit 0, observed 22:12 UTC), with unchanged
inputs and all 150 new roots. All 6,753 printed axiom lists and four retained FMU
source/C/build roots were permitted. All three FMI matrices passed 75/75 functions
and 526 cells with zero discrepancies; scalar/tensor eFMI publication, reuse and
mutation controls passed. The tensor eFMI native boundary is C compilation, not
complete public-method execution. Existing warnings remain. This validates the
repair; K02–K05 and the unresolved normative findings remain open. See
build/numerical-linkage-checkpoint.md. The prior step-composition gate is a
separate historical checkpoint, not this repair's validation.
No grammar expansion or conformance claim follows.

**Public logging configuration: full gate passed.** The focused review of
[FMI 3.0.2 §2.3.1 and §2.4.5](https://fmi-standard.org/docs/3.0.2/) confirms
that a zero-length category list requires `NULL` and applies to all categories;
nonempty selections must use declared names. The actual XML declares only
`logStatus`. `DebugLogging.LegalRequest` states that caller obligation separately
from C validation; `legal_behaviors` and `legal_returned` derive successful
configuration and its exact memory frame. Invalid importer inputs and a missing
callback have separately identified defensive behavior, without classifying
them as legal standard requests.

The emitted validation loop, mandatory function/source-artifact contract and
owning-package audits passed. The required full
`nix develop .#verification --command lake test` passed on
2026-09-15 at 00:18:22 UTC, with 1040 unchanged inputs, all 63 required
roots and no unexpected axioms or changed-module warnings. Evidence is in
`build/c-factory/debug-logging/full-gate-v1.*`. Only the three evidence
documents change after that frozen gate. Existing FMI boundary checks cover
the string-array ABI, both interfaces and rejection before a flag change;
the existing eFMI artifact and mutation controls also passed.

Retained archives are in `build/c-factory/debug-logging/artifacts-v1/`.
Only the FMU's public logging setter in `sources/fmi3.c` changes; the native
library and other members are identical. The eFMU changes only generation
identities and dependent references/checksums in three manifests. There is no
MLS or GALEC grammar, Solve numerical policy or eFMI emission change.
Upstream Rumoca `41477d6f` retains the previously reviewed SPEC_0007, SPEC_0043
and SPEC_0048 ownership rules; their unchanged hashes are recorded in
`build/c-factory/logging-history/standards-review-v1.json`.

The initialization-history follow-up below now accepts creation, handoff and
recurring lifetime composition. The ME follow-up below also accepts simulation
interleavings; the CS follow-up accepts the corresponding CS histories.
Native ABI/stdlib correspondence, MISRA coverage and previous MLS/eFMI findings
remain open. This focused acceptance does not close the recurring whole-subset checklist.
**Stage decision: open; no grammar expansion.**

Before extending the grammar or admitting a development profile to production,
complete the following record for the **entire currently admitted subset**.
Reuse unaffected evidence only after checking its dependencies; review changed
interactions across all three standards even when no grammar file changed.

| Required record | Evidence needed to close the stage |
| --- | --- |
| Scope and identity | Source revision, production entry points, exact source/GALEC EBNFs, admitted and rejected forms, deliberate extensions, and the actual artifacts reviewed. |
| Architecture continuity | Identify the reusable mechanism exercised by the slice, its extension point and its cost model. Small syntax coverage must use the intended compiler architecture. Grammar-specific derivations instantiate general parser/lowering theorems; fixed examples or temporary recognizers cannot replace them. |
| Normative baseline | MLS, FMI and eFMI versions; relevant clauses; pinned header/schema identities. Upstream Rumoca and compliance tools are references, not normative authorities. |
| MLS coverage | Lexical/syntactic admission, resolution, types and shapes, equation meaning, initialization, numeric interpretation and diagnostics. Keep `jacobian` explicitly identified as an extension. |
| FMI coverage | Both advertised ME and CS interfaces: metadata, initialization, legal and rejected calls, time/solver policy, errors/logging, storage/lifetime, source builds and archive contents. |
| eFMI coverage | GALEC semantics and methods, sample-period policy, Production C execution, logical mappings/status, correlated manifests/checksums, archive layout and coding-guideline obligations. |
| Proof correspondence | For each applicable clause: independent specification, lowering/target theorem roots, actual-file/archive proposition and any remaining external assumptions. Inspect elaborated quantifiers and interface instances for accidental specialization to imported constants; an axiom audit does not establish the intended scope. A theorem about an emitter's own policy does not establish that policy's conformance. |
| Boundary evidence | Required `lake test` outcome and artifact identities, plus existing schema/importer/native checks where tools or interfaces lie outside Lean. Record checker limitations explicitly. |
| Decision | Carry forward every open finding with closure criteria. Close applicable findings before growth. Record a reason for each excluded clause; an unproved advertised behavior cannot be marked inapplicable. |

The stage is **open** if any applicable compliance finding or required compiler
proof/artifact obligation remains unresolved. A passing schema, importer or CI
run cannot change that decision by itself. This is a review gate, not an
automated claim that Lean has formalized the prose standards. Use universal
proofs for compiler properties and keep tests to the existing external boundaries.

## Current unit-stage follow-up

### Prepared step composition and accepted observations: full gate passed

This proof-only increment makes successful literal-pool preparation, prepared
logged rejection calls and accepted final output/mode observations mandatory in
the existing tensor/constant contracts. The checked function-list witness is
shared with the actual-byte certifier; diagnostic/category contents are derived
at callback entry. Accepted calls retain three false flags and the selected mode
on the same final heap as state/time/execution. No caller, finite-arithmetic or
runtime-linking premise is added or discharged by these new observations.

The existing FMI 3.0.2 §4.2.1 computation, §2.2.4 status and §2.3.1 logging review
carries forward. No source admission, MLS/GALEC grammar, eFMI emission, solver
policy or native boundary suite changes. Callback effects, literal installation/
initial frames, complete histories and actual numerical linking remain explicit.
No whole MISRA claim follows; residual pointer guards are unchanged.

Independent review, isolated owner compilation and 58 selected axiom audits
passed. The integrated package check passed all 4,055 jobs (exit 0) in
`build/step-composition-package-v3.log`; all 39 new roots were present and the
4,215 printed axiom lists used only permitted axioms. Existing profile warnings
remain. The required full gate passed (exit 0, observed 2026-09-21 at 20:47:09 UTC)
in `build/step-composition-full-gate-v3.log` with unchanged implementation inputs.
All three FMI matrices passed 75/75 functions and 526 cells with zero discrepancies;
scalar/tensor eFMI artifact/mutation controls passed. All 6,525 printed axiom lists
and four retained FMU roots use only permitted axioms. See
`build/step-composition-checkpoint-v3.md`.
The previous numerical checkpoint does not validate these additions. All prior
MLS/FMI/eFMI, finite-arithmetic, native and MISRA findings carry forward.
**Stage decision: open; no grammar expansion.**

### Step numerical rejection: full gate passed

The tensor and constant profiles now require shared whole-call proofs for
non-nearest rounding, stop-limit rejection and both discard causes (nonprogress/
nonfinite next clock, or off-grid/over-bound duration). These cover the existing
guards, not a new solver policy or source case. The FMI 3.0.2 §4.2.1 computation,
§2.2.4 status and §2.3.1 logging review carries forward. Error paths initialize
outputs then terminate the instance; discard preserves the selected instance
before any callback. Enabled logging retains arbitrary represented callback
effects, so post-callback preservation is not inferred. Missing logging needs
no flag/environment binding; floor bindings are conditional on clock progress.

The reusable prefix constructors discharge actual syntax and closure obligations
for both profiles. Existing fields remain mandatory. All 22 new audit roots
passed isolated owner/profile rehearsals and integrated package validation
passed all 3,795 jobs (exit 0) in `build/step-numeric-contract-package.log`.
Independent review confirmed that both fixed actual-source-build paths retain
these mandatory fields, without discharging their explicit program/literal/
external premises. The required full artifact gate passed on 2026-09-21
(exit 0, observed 19:22:37 UTC) in `build/step-numeric-contract-full-gate.log`.
All implementation fingerprints remained unchanged; all three production FMI
matrices passed 75/75 functions and 526 cells with zero discrepancies. The
scalar/tensor eFMI artifact and mutation controls passed. Retained FMU audits and
all 6,485 printed axiom lists use only the permitted axioms; these counts do not
measure semantic coverage. Artifact hashes and evidence are recorded in
`build/step-numeric-contract-checkpoint.md`. The preceding argument checkpoint
predates these fields.
MLS, GALEC/eFMI, rendered C, solver policy and native suites are unchanged.

Accepted-step review still identifies conditional finite-arithmetic premises,
actual tensor-kernel/event-program composition, final Boolean-output/mode frames
and source/Solve clock-history coverage. Scratch Lean proofs establish unit-clock
stagnation at 2^53 even when an aggregate duration-2 addition advances; this is
authored C/IEEE evidence, not a complete source-to-FMU counterexample. The pinned
[FMI 3.0.2 §4.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3DoStep) permits
`lastSuccessfulTime` to differ from the requested endpoint even with `fmi3OK`
and false `earlyReturn`; the mismatch alone is not an established violation.
Solver progress and source-history obligations require their own analysis.
All prior MLS/FMI/eFMI and MISRA findings carry forward.
**Stage decision: open; no grammar expansion.**

### Step argument rejection: full gate passed

The existing tensor and constant profiles now require shared invalid-input and
missing-output `fmi3DoStep` contracts, each including suppressed logging, enabled
logging and missing-callback behavior. This is proof coverage of the existing
FMI 3.0.2 argument guards, not source admission or grammar expansion. Missing
outputs need no clock/buffer storage; invalid numeric arguments retain the
existing finite stored-clock and writable-buffer premises. Precise heap updates,
arbitrary represented callback effects and no-outcome behavior are preserved.
Scalar prefix theorem statements are unchanged and reuse the generic proofs.

MLS, GALEC/eFMI, C emission and solver policy are unchanged. Independent draft
review passed; package checks passed all 4,045 jobs in
`build/step-argument-contract-package.log` (exit 0). The required full gate passed
on 2026-09-21 (exit 0) in `build/step-argument-contract-full-gate.log`, with
unchanged implementation fingerprints. All three production FMI matrices passed
75/75 functions and 526 cells with zero discrepancies. Scalar/tensor eFMI
actual-artifact and mutation checks passed; retained FMU source-build audits
use only the three permitted axioms. Hashes and evidence are recorded in
`build/step-argument-contract-checkpoint.md`. This checkpoint does not validate
later numeric or literal-composition drafts. All compliance findings carry forward.
**Stage decision: open; no grammar expansion.**

### Tensor and constant step lifecycle rejection: full gate passed

The existing tensor and constant source profiles now require silent and logged
disallowed-state `fmi3DoStep` behavior in their adapter contracts. Review follow-ups
also require missing-callback behavior and actual adapter-table bindings.
The shared logger emitter now explicitly compares the callback with a null
pointer before testing the logging flag, addressing its MISRA C:2025 Rule 11.11
pointer operand. Shared C proofs preserve short-circuit evaluation. Source/GALEC
grammars, numerical lowering, metadata and solver policy are unchanged; this is
not a whole-rule MISRA compliance claim.

[FMI 3.0.2 §2.2.4](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions)
requires `fmi3Error` for detected disallowed-state calls. Section 2.3.1 specifies
the logger arguments and respect for configured logging. The new
`TensorDoStep.lifecycle_logged_behaviors` and
`ConstantDoStep.lifecycle_logged_behaviors` instantiate the reusable
`GuardedCalls.rejected_all_behaviors` theorem. Their contracts require both the
existing suppressed behavior and the new enabled behavior. A suppressed call
changes only the selected mode; an enabled callback receives the terminated
instance and its modeled effects are retained. The no-outcome branch is explicit,
so the contract does not assume that an arbitrary external callback returns.

`TensorSourceBuildContract` and `ConstantSourceBuildContract` require these
strengthened adapter contracts through the existing fixed actual-file checkers.
The earlier F1 claims about missing tensor discard/header coverage are stale:
`TensorDoStep.Contract.discarded` and header quantification already supply them.
This increment does not establish all step rejections or remove finite arithmetic,
library, caller-storage, native callback or ABI premises. MLS 3.7 and eFMI Beta 1
coverage are unchanged; all existing compliance findings carry forward.

Boundary evidence: the targeted tensor and constant audits passed in
`build/tensor-lifecycle-package.log` and `build/constant-lifecycle-package.log`.
The preliminary required full gate in `build/step-lifecycle-full-gate.log` was
deliberately stopped (exit 143) for the combined review follow-ups, not passed.
The combined targeted integration and contract/certificate-module checks passed
(`build/logger-null-integration.log`, `build/logger-contract-package-v2.log`).
The full gate in `build/logger-contract-full-gate.log` failed at tensor FMI
certificate elaboration: the new membership tactic required an unavailable
signature equality decision procedure. It has been replaced by the existing
scalar-style structural membership proof. Repaired actual-file checks passed for
both tensor and constant-rate FMUs (`build/logger-tensor-artifact-repair-v2.log`,
`build/logger-constant-artifact-repair.log`), and each existing native matrix passed
75/75 functions and 526 cells with zero discrepancies, including missing-loggers.
The required `nix develop .#verification --command lake test` passed on
2026-09-21 (exit 0; `build/logger-contract-full-gate-v2.log`) with an unchanged
implementation fingerprint. All three production FMI matrices passed 75/75
functions and 526 cells with zero discrepancies. Their retained source-build
audits use only the permitted axioms. The complete scalar/tensor eFMI publication,
archive, manifest and mutation sequence passed, as did the standalone C-object,
parser and native boundary checks. The failed initial run is retained.
Literal bindings remain explicit; missing-callback behavior is a
separately identified defensive case, not a newly admitted legal importer request.
**Stage decision: open; no grammar expansion.**

### G02 rounded subtraction and division for the tensor arithmetic ring: standards impact

The finite binary64 model and the tensor arithmetic IR now provide all four
field operators. `Binary64.roundedSub` and `Binary64.roundedDiv` round the
exact real difference and quotient on the shared integer-unit grid through the
scaled-rounding machinery, with determinism, uniqueness, nearest/even and
signed-zero relations proved in parallel with the addition and multiplication
contracts; `roundedSub_eq_add_negate` records the exact-negation identity, and
`finiteQuotient` rejects a zero or non-finite divisor and overflow. The tensor
IR `BinaryOp` gains `sub` and `div` with their forward (JVP) and reverse (VJP)
rules, finite execution (`Solve.Tensor.Finite`), and Fréchet-derivative
correctness; division's analytic derivative carries an `AD.Regular`
nonzero-divisor premise. The C backend adds the counted helpers
`rumoca_tensor_sub` and `rumoca_tensor_div` with the same per-element finite
contract, printer and actual-file certificate as `rumoca_tensor_add` and
`rumoca_tensor_mul`. This is a package-checked numerical increment only: no new
admitted source syntax, CLI admission or FMU/eFMU artifact.

| Standard | Impact |
| --- | --- |
| MLS 3.7 (operators and expressions, arithmetic operators `+ - * /`) | The finite model and tensor IR now interpret all four arithmetic operators over the element type. Element-wise subtraction and division follow the same round-to-nearest-even numeric interpretation already used for `+` and `*`; the acyclic algebraic-equation grammar for G02 landed separately, and no new source is admitted to production by this increment. |
| IEEE 754-2019 §4.3.1 (roundTiesToEven) and §5.4.1 (arithmetic operations) | Rounded subtraction and division are specified as the correctly rounded (round-to-nearest, ties-to-even) results of the exact real difference and quotient, matching the addition and multiplication specifications. Division excludes a zero or non-finite divisor by the finiteness predicate; subtraction equals addition of the exact negation because negation is a sign flip with no rounding. Exception flags, traps and the host floating environment remain outside the modeled semantics. |
| C11 §6.5.6 (Additive operators) and §6.5.5 (Multiplicative operators), Annex F (IEC 60559 floating-point arithmetic) | The counted C helpers evaluate `left[k] - right[k]` and `left[k] / right[k]` under the authored finite-arithmetic contract, one element per loop iteration, and `floatSub_finite` / `floatDiv_finite` tie the modeled evaluation of the `-` and `/` operators to the finite Solve results. The trusted boundary between the authored C subset and host compilation is unchanged; native ABI, the floating environment and overflow/error paths remain host-tested rather than proved. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

The new roots are registered in the core arithmetic audit
(`Tests/FiniteChecks`, `Tests/TensorChecks`) and the C tensor helper audit.
Static reverse transformation, whole-program C simulation and tensor FMU/eFMU
certificates for the enlarged ring remain open, as for the existing operators.
**Stage decision: open; no grammar expansion by this numerical increment.**

### Stage record: constant-rate profile admitted to FMI 3 FMU output

This record completes the recurring review for the enlarged admitted subset at
the revision that admits the constant-rate profile to production FMU output.

| Required record | Evidence |
| --- | --- |
| Scope and identity | Production entry point: `Rumoca.compileConstant`, dispatched by the `rumoca` CLI after the unit and array profiles reject the source; the FMU publication gate is the `constant-fmi3` certificate kind of `lake run verify-artifact`. Admitted EBNF production: `constant_composition` (two or more scalar `Real` states, each with one `der(state) = literal` equation whose right-hand side is a signed decimal literal). The pinned certificate binds the single admitted development source `examples/ConstantRates.mo` (`der(x) = 2.5`, `der(y) = -1`); a constant source of a different state count or different rates fails the fixed checker before any FMU is produced. Rejected forms: constant sources for eFMI Algorithm Code, eFMU archive or C output (diagnostic, no publication). Reviewed artifact: `build/ConstantRates.fmu` produced by `tests/fmi3.sh`. |
| Architecture continuity | The constant profile uses the shared LALR engine and typed actions, the constant-rate lowering to `ConstantIVP`, the executable constant kernel (`rumoca_constant_rhs`/`rumoca_constant_step`/`rumoca_constant_sample`, universal in the state count and rates), the static instance pool, and the same fixed-checker structure as the unit and array profiles; the state count stays symbolic in the model's shape parameter and no rate coordinate is enumerated during lowering. `ParserActions.Parsed.located` in `ActionsLocatedTotal` lifts the total located-parse construction to the constant actions, so `constantSourceBuild_correct` is existential like the scalar and tensor certificates without kernel-evaluating the parser. |
| Normative baseline | MLS 3.7; FMI 3.0.2 ME and CS with the pinned `fmi3FunctionTypes.h` and the in-tree model-description conventions; eFMI 1.0.0 Beta 1 unchanged (constant eFMI not built). |
| MLS coverage | Real declarations of two or more scalar states, and one `der(state) = signed decimal literal` equation per state whose written order is immaterial (the resolution requires the derivative names to be a permutation of the declared states). Each rate is the round-to-nearest-even of its literal's exact base-ten content. Resolution, equation meaning and initialization are the constant-rate lowering theorems (`ConstantCompiler.prepare_correct`, `equation_correct`, `initialization_correct`, `rate_exact`, `prepare_perm_invariant`); numeric interpretation is the finite binary64 kernel execution with explicit finite-arithmetic premises. |
| FMI coverage | Both interfaces: model description with the state and derivative `Dimension` elements, the two-element state start list, an empty derivative dependency set and identical identifier decoding (`TensorMetadata.constantModelDescription`, `constant_modelIdentifiers_decode`, `constantToken_attribute`); creation, initialization, mode transitions, termination and release over the static constant pool; Float64 access with the value references `0` (time), `1` (the writable state) and `2` (the read-only derivative); continuous-state access, the constant derivative getter calling `rumoca_constant_rhs`, the co-simulation step calling `rumoca_constant_step`, count queries, time and reset; the two capability families for the remaining functions; `ConstantAdapter.Contract` binding the rendered text, whose call graph is checked no-heap and acyclic (`ConstantCallPolicy.constant_no_heap`, `constant_acyclic`); the `constant-fmi3` certificate `Rumoca.CheckedConstantFMI3Files.source_to_build` on the actual bytes. |
| eFMI coverage | Not extended: constant sources are rejected for Algorithm Code and eFMU output with a diagnostic. Open finding CF01 below. |
| Proof correspondence | Per-function contracts in `packages/backend-fmi3/RumocaFMI3/Constant*.lean` and the reused `Tensor*.lean`, the executable kernel contract `Rumoca.CConstant.contract_correct`, and the compiler composition `constantSourceBuild_correct`; roots audited in `Tests/Audit.lean` on the three permitted axioms. Explicit premises retained, as for the scalar and array paths: the modeled round-to-nearest floating-environment constant, kernel entry resolution, and the per-cell finite-addition premises of the Euler step. |
| Boundary evidence | The required `lake test` at this revision; `tests/fmi3.sh` (constant block: CLI publication, constant eFMU rejection, `constant-fmi3` certificate reuse with no build, adapter mutation rejection, the native all-behavior matrix over the constant variable set, and FMPy runs asserting the two states reach `(7.5, -3)` after three unit steps from zero in both interfaces). Native compilation, ZIP transport and the importer remain outside the proof model. |
| Decision | The constant-rate profile is admitted to FMI 3 FMU output. Open findings carried forward with closure criteria: CF01 constant eFMI path (build the constant GALEC/Production Code path with its contracts or keep rejection documented); CF02 general state count and rates in the certificate (the grammar admits any state count, but the fixed checker binds the two-state `ConstantRates` instance; extension needs a source-general constant checker or a per-instance certificate); CF03 Euler-step finite-addition premises are explicit (overflow of the rate accumulation is not modeled); CF04 native ABI, floating-environment and callback correspondence, shared with the unit and array profiles; CF05 MISRA C:2025 inventory for the constant adapter, shared with K05. **Stage decision for further growth: open until K02 to K05 close for the unit profile.** |

### Constant-rate FMI 3 adapter assembly (Stage B4): standards impact

The constant-rate adapter function list, families, call policy, printability and bound
contract are now assembled (`FMI3.ConstantFunctions`, `ConstantFamilyContracts`,
`ConstantCallPolicy`, `ConstantAdapterPrinter`, `ConstantAdapterContract`,
`dev/constant-rates.md` "Constant adapter assembly"). Each pinned header signature
renders a constant-specific body (the Float64 accessors, the derivative getter and the
do-step), a profile-independent tensor body at the constant state shape, or the shared
scalar body, over the reused helper prefix. The declaration preamble carries the
no-input/no-output constant instance record and the three constant kernel prototypes;
no tensor kernel or Jacobian prototype is emitted. The compiler fixture renders the
`ConstantRates` adapter under the function-section grammar check, the native regression
executable ties it to the actual `ConstantCompiler.prepare` kernel and retains the
bytes under `build/constant-fmi/adapter.c`, and `tests/tensor-c.sh` compiles the whole
adapter to a standalone C11 object with zero diagnostics under the strict flags. This is
a package-checked product only: no production artifact, CLI or grammar change, and the
tensor and scalar adapters and every existing contract are unchanged.

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The constant-rate profile remains a development case. |
| FMI 3.0.2 §2.2.2 (source-code FMU, C API and header files) | Every emitted function carries the pinned prototype for its name from the vendored `fmi3FunctionTypes.h` header (`ConstantFunctions.functions_signatures`), one function per pinned signature and per reused helper; the source prefix `#define FMI3_FUNCTION_PREFIX Rumoca_ConstantRates_` precedes the official FMI header selection, and the adapter's function-prefix names exactly the model identifier the model description decodes to (`constant_modelIdentifiers_decode`). The whole translation unit compiles as a standalone C11 object with zero diagnostics under the strict flags, the three `rumoca_constant_*` kernel entries staying undefined externs declared in the preamble. |
| FMI 3.0.2 §2.4.1 (instantiation) and naming | The reserved-record factory validates exactly the token `lean-rumoca-constant-v1:ConstantRates` the constant model description declares as its `instantiationToken` attribute (`ConstantAdapter.Contract` carries `constantToken_attribute`). |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic memory allocation) | The complete constant adapter call graph is checked no-heap against the boundary set `bConstant` (`ConstantCallPolicy.constant_no_heap`): every callee is a defined function, a declared constant kernel entry or a named non-allocating C library / math / atomic external, and no generated call graph reaches an allocation entry point. |
| MISRA C:2025 Rule 17.2 (no recursion) | The complete constant adapter direct-call graph is checked acyclic (`ConstantCallPolicy.constant_acyclic`): the three constant kernel entries are unranked numerical-kernel leaves, the reused helpers precede them and the public functions precede the helpers, so no function calls itself directly or indirectly. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

Every theorem is universal in the state count, the scalar witness model and the header
signature list. Binding the sample entry `rumoca_constant_sample` to its own
observable-machine execution, the FMI 3 artifacts bound to actual bytes, and production
CLI admission remain open. **Stage decision: open; no grammar expansion.**

### FMI 3.0.2 §4.2.1 Computation (`fmi3DoStep`) accepted and discard cases for the constant profile (Stage 3c): standards impact

The constant-rate Co-Simulation `fmi3DoStep` body now runs end to end over the
constant instance record (`FMI3.ConstantDoStep`, `dev/constant-rates.md` "Accepted
and discard do-step execution"). `internalStep_reaches` composes the per-step time
advance with the bridged state-step entry `rumoca_constant_step(&(m->x[0]))`
(`step_writes_events`) as one observable-machine execution; `stepLoop_reaches`
iterates it over the outer unit-grid loop by induction, advancing the state region by
the `N`-fold finite rate sum and the time base by `N`; `solve_reaches` wraps the loop
with the step-count/counter declarations, the last-successful-time publish and the
`fmi3OK` return. The reused model-independent scalar guard prefix (`front_run`, then
the shared `stepRounding`/`stepClock`/`stepGrid` guard sections) composes with the
numerical tail in `accepted_reaches`/`accepted_behaviors`, and the off-grid /
over-bound `fmi3Discard` path reuses the shared `StepDiscard` logging composition
(`discard_prefix`, `discard_suppressed_behaviors`, `discard_logged_behaviors`).
`ConstantDoStep.contract` now bundles the accepted execution (`ExecutionFree`) and
the suppressed/enabled discard behaviors alongside the printed text, closedness,
denotation and null rejection. This is a package-checked product only: no production
artifact, CLI or grammar change, and the tensor and scalar adapters and every
existing contract are unchanged.

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The constant-rate profile remains a development case. |
| FMI 3.0.2 §4.2.1 Computation (`fmi3DoStep`), Co-Simulation accepted step | A communication step that is a positive integer multiple of the internal unit step and at most the scalar bound is accepted: the body initializes the event/terminate/early-return output flags to zero and `*lastSuccessfulTime` to the current time, runs `N` internal steps (each advancing the time base by one and calling `rumoca_constant_step(&(m->x[0]))`, which advances every state cell by the finite binary64 addition of its rate), publishes the advanced time base to `*lastSuccessfulTime` and returns `fmi3OK`. Its sole terminating behavior advances the state region by the `N`-fold finite rate sum, sets the instance time cell and the caller's `lastSuccessfulTime` to the `N`-fold finite time sum, and preserves every other instance (`accepted_reaches`, `accepted_behaviors`, `execution_free`). |
| FMI 3.0.2 §4.2.1 Computation, off-grid / over-bound step (`fmi3Discard`) | A step that makes clock progress inside any stop window but does not lie on the unit internal time grid (off-grid) or exceeds the internal-step bound (over-bound) reaches the shared `Runtime.stepDiscard` block before any numerical declaration, via the reused rounding/clock guard sections and the rejected grid branch. With logging suppressed the call returns `fmi3Discard` leaving the heap unchanged apart from the output-cell initialization (`discard_suppressed_behaviors`); with logging enabled it invokes the logging callback and mirrors every represented callback outcome (`discard_logged_behaviors`). |
| FMI 3.0.2, function-call resolution across the interface | Each internal step enters `rumoca_constant_step` resolved directly by name (the entry is not a bound interface constant); the `resolves` premise records the direct resolution of the nested state-step call, carried uniformly as for the derivative and tensor entries. |
| C11 / interface typing | The proofs run under the header-aware floating-environment interface (`ConstantFenv`: the pinned C interface extended with the header's `FE_TONEAREST` round-to-nearest constant), so the rounding guard and the `fmi3OK` return resolve; the `double *` region-pointer typing the numerical entry needs is carried separately (`ptrTy`), the constant analog of the derivative getter's. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The whole body executes over caller-owned instance regions with no dynamic allocation; the step count and loop counter are ordinary `size_t` locals and the grid loop is a counted `size_t` loop. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

Every theorem is universal in the state shape, the instance index and the heap. The
constant adapter function list assembly with its no-heap and acyclic call-graph
policy, and binding to actual FMU bytes, remain open. **Stage decision: open; no
grammar expansion.**

### Constant-rate kernel bridge, fused derivative getter and step entry (Stage 3): standards impact

The executable constant-rate kernel entries are now bound to the static constant
instance record (`FMI3.ConstantInstanceRhs`, `dev/constant-rates.md` "Constant
kernel bridge and fused derivative getter"). The list-indexed kernel view
(`CConstant.place`/`cells`/`writableN` over the declaration-order rate list) is
matched to the dense tensor view (`Reads`/`Writable`/`Values`), and the proved
loop-call behaviors (`CConstant.rhs_behaves`, `step_behaves`) embed into the
observable call machine through the shared typed-to-observable transfer
(`CCalls.Events.loop_call_reaches_events`). `rhs_writes_events` writes the exactly
rounded rate vector into instance `i`'s derivative region, and `step_writes_events`
advances each state cell by the finite binary64 addition of its rate; each
preserves every other cell of every other instance, universal in the state shape,
the source rates and the pool index. Building on the derivative bridge,
`FMI3.ConstantDerivative.deriv_reaches`/`deriv_behaviors` prove the fused
single-run `fmi3GetContinuousStateDerivatives` over the constant instance record,
and `deriv_contract` bundles it as a consumable contract. These are
package-checked products only: no production artifact, CLI or grammar change, and
the tensor and scalar adapters and every existing contract are unchanged.

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The constant-rate profile remains a development case. |
| FMI 3.0.2, Model Exchange interface, evaluating state derivatives (`fmi3GetContinuousStateDerivatives`) | The constant getter now runs in one observable-machine execution: it guards the handle/lifecycle, checks that `nContinuousStates` equals the symbolic state volume and the buffer is non-null, invokes the constant kernel entry `rumoca_constant_rhs(&(m->dx[0]))` (resolved directly by name) which writes the exactly rounded rate vector into `der(x)`, then copies that region into the caller buffer. Its sole terminating behavior returns `fmi3OK` with the rounded rate vector delivered to the caller buffer, the instance's `der(x)` region holding the same values, and every other cell of every other instance preserved (`deriv_reaches`, `deriv_behaviors`, `deriv_contract`). A null handle returns `fmi3Error` changing nothing (`null_deriv_behaviors`). |
| FMI 3.0.2 §4.2.1 Computation (`fmi3DoStep`) | The Co-Simulation do-step's per-internal-step numerical entry `rumoca_constant_step(&(m->x[0]))` is now bridged over the instance record: `step_writes_events` runs it as one observable-machine execution advancing each state cell by the finite binary64 addition of its rate and preserving every other instance, under the explicit per-cell finite-addition premises. The full accepted `fmi3DoStep` execution over the outer unit-grid loop (the `N`-fold state advance and time advance, the publish tail and the off-grid `fmi3Discard` path) composes this entry with the shared scalar guard prefix and remains an open item; the current `ConstantDoStep.contract` proves the guard prefix, printed text, closedness, denotation, null rejection and lifecycle rejection. |
| FMI 3.0.2, function-call resolution across the interface | The typed and observable call schedulers share the `CCalls.Typed.nextWith` scheduler and differ only in call-site resolution; the transfer lemma (`loop_call_reaches_events`) discharges the difference under `CCalls.Events.Resolves`. The constant kernel bodies contain only assignments and a return with no nested calls, so no reachable loop-call state is poised on an `eval`-call and the premise holds definitionally at every reachable state; it is carried as a hypothesis only to mirror the tensor entry theorems and keep the adapter composition uniform. |
| C11 / interface typing | The numerical entries take `double *` region pointers; the fused derivative getter carries the `double *` header-typing premise the entry needs (`(cInterface ...).types "double *" = some .pointer`), the constant-rate analog of the tensor getter's `Library` premise, satisfied by the eventual adapter's header dictionary rather than the pinned FMI runtime typedefs. The rendered getter prints its intended C token grammar and denotes itself under the shared printer (`derivFunction_denotes`). |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The bridged entries execute over the caller-owned instance regions with no dynamic allocation, and the transfer lemma changes neither machine definition; the fused getter stages each region base pointer and the element count into ordinary locals and copies with a counted `size_t` loop over the static instance pool. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

The theorems hold for arbitrary state shape, instance index, request length and
heap. The full accepted `fmi3DoStep` grid-loop execution, the constant adapter
function list assembly with its no-heap and acyclic call-graph policy, and binding
to actual FMU bytes remain open. **Stage decision: open; no grammar expansion.**

### G01 constant-rate executable kernel program (Stage 2): standards impact

The constant-rate profile's numerical C is now an executable program
(`packages/backend-c/RumocaC/ConstantKernelProgram.lean`, `dev/constant-rates.md`
"Executable kernel program"): `rumoca_constant_rhs`, `rumoca_constant_step` and
`rumoca_constant_sample` are `CTree.Function` definitions over the source rate
list, universal in the number of states and in the rates, executed by the
loop-call machine over the caller-owned array. Each rate emits as a decimal
floating constant whose target binary64 value is the correctly rounded conversion
of its exact base-ten content, and the three loop-machine execution theorems, the
per-rate rounding certificate and the rendered-byte contract are audited to depend
only on the three foundational axioms. The development fixture renders the two-rate
program (`2.5`, `-1`), certifies each function's token grammar, binds the actual
file bytes to the rendered functions, and `tests/tensor-c.sh` compiles and runs the
kernel natively (three unit steps advance the two states from zero to `(7.5, -3)`).

| Standard | Impact |
| --- | --- |
| C11 6.4.4.2 Floating constants | Each rate is a decimal floating constant printed as the significand `<mantissa>e<exponent>` (a single preprocessing number, C11 6.4.4.1); the exponent carries its own sign so the constant closes before it. A negative rate is the unary minus of the unsigned magnitude, since C has no negative literal tokens; the printer parenthesizes it (`(-1e0)`). The target binary64 value is the correctly rounded conversion of the constant's exact base-ten content under the current (round-to-nearest-even) rounding mode, specified by `CBody.decimalValue` and certified per rate by `CConstant.rate_rounds` from `CBody.decimalValue_rounds`; the emitted preamble's `FLT_EVAL_METHOD == 0` guard keeps evaluation at `double`. Each rendered function tokenizes under the shared C scanner to its independent token grammar (`Fixture.rhs_denotes`, `step_denotes`, `sample_denotes`), where `25e-1` lexes as `25e`, `-`, `1`. |
| MLS 3.7 Real literals (unsigned-number / exponent form) | The source rate spellings (`2.5`, `-1`) are MLS 3.7 real literals; `ModelicaParser.Constant.parseDecimal` records their exact base-ten `Decimal` content (`sign`, `mantissa`, `power`), and the executable kernel emits a C floating constant with the same content (`CConstant.rateLit`). Source-to-content fidelity is proved in the compiler package (`Prepared.rate_exact`); the target rounding of that content is the C body contract above, so the source literal and the emitted constant denote the same binary64 rate. |
| MISRA C:2025 Rule 7.1 (octal constants shall not be used) | The printed magnitude is a base-ten significand with a mandatory `e` exponent, so it is a floating constant, never an octal integer constant: a zero magnitude prints as `0e0` (an exponent-bearing floating constant), not a bare leading-zero token, and a non-zero magnitude has no leading zero. No rate literal is an integer constant, so Rules 7.2 (unsigned suffix) and 7.3 (lowercase `l` suffix) do not apply to the emitted constants; the counted sample loop uses the shared unsigned `size_t` counter and bound already covered by the tensor loop review. |

### Constant-rate FMI 3 adapter bodies (Stage B2): standards impact

The constant-rate profile (`G01`) adds its profile-specific FMI 3 adapter bodies
over the no-input, no-output instance record: the `fmi3GetFloat64`/`fmi3SetFloat64`
accessors over value references `0` time, `1` state, `2` derivative
(`FMI3.ConstantFloat64`); the Model Exchange derivative getter calling the
numerical entry `rumoca_constant_rhs(&(m->dx[0]))` (`FMI3.ConstantDerivative`); and
the Co-Simulation `fmi3DoStep` calling `rumoca_constant_step(&(m->x[0]))` per
internal step (`FMI3.ConstantDoStep`). The profile-independent bodies (lifecycle
modes, free, factory over the shared reserved-record initializer, count queries,
time setter, reset, nominals, the state getter/setter and the seven
model-independent behavioral functions) are the shared tensor bodies instantiated
at the constant state shape. This subsection covers the constant-rate profile's ME
and CS interface bodies; their fused numerical-entry execution, the full adapter
assembly, artifacts and production admission remain later increments.

| Standard | Impact |
| --- | --- |
| FMI 3.0.2 §2.4.9 Getting and Setting Variable Values (`fmi3GetFloat64`, `fmi3SetFloat64`) | The accessor bodies denote one array value reference as a whole instance region under the array-access rule: `0` the independent time base (element count 1), `1` the state vector `x`, `2` the derivative `der(x)` (each element count the symbolic state volume). The getter denotes all three references; the setter admits only the state reference `1` (writable) and rejects the derivative reference `2` as read-only, matching the constant-rate model description's `1` state / `2` derivative numbering. A request must name exactly one value reference and non-null arrays, and `nValues` must equal the referenced region's element count; the copy is one counted `size_t` loop over the symbolic count, so no coordinate is enumerated. Each body's printed text denotes its function under the shared C printer and a null handle is rejected with `fmi3Error` (`ConstantFloat64.getBody_closed`, `setBody_closed`, `getFunction_denotes`, `setFunction_denotes`, `null_get_behaviors`, `null_set_behaviors`, `get_contract`, `set_contract`). |
| FMI 3.0.2 §4 Model Exchange, `fmi3GetContinuousStateDerivatives` | The derivative getter guards the handle and lifecycle, checks the count and buffer, calls the numerical entry `rumoca_constant_rhs(&(m->dx[0]))` to write the derivative region, and copies that region into the caller buffer with the shared counted copy suffix. The entry needs no state or input (the rate vector is constant), so it takes only the derivative pointer. The copy suffix delivers whatever the entry wrote, preserving every other instance (`ConstantDerivative.deriv_copy_delivers`, `deriv_instance_delivers`); the printed text denotes, and a null handle is rejected with `fmi3Error` (`derivBody_closed`, `derivFunction_denotes`, `null_deriv_behaviors`, `deriv_contract`). The rounding of each written derivative to nearest-even is the constant-rate kernel contract (`Rumoca.CConstant.contract_correct`); the fused single-run observable execution of the entry is a later increment. |
| FMI 3.0.2 §5 Co-Simulation, `fmi3DoStep` | The Co-Simulation step reuses the model-independent scalar guard prefix of `Runtime.doStep` verbatim (handle/lifecycle guard, output-pointer check and writes, invalid communication-point/step rejection, `stepRounding`, `stepClock`, `stepGrid`): the communication step must be a positive integer multiple of the internal unit step and at most the scalar bound. Each admitted internal step advances the time base by one and calls `rumoca_constant_step(&(m->x[0]))`, which advances every state by one explicit Euler step of its constant rate; the kernel iterates the states internally, so the body needs no elementwise loop. Over `N` accepted internal steps every state advances by the `N`-fold finite rate sum and the time by `N`. The printed text denotes, a null handle is rejected with `fmi3Error`, and a lifecycle-mismatched call is rejected with `fmi3Error` writing the terminated mode (`ConstantDoStep.doStepBody_closed`, `function_denotes`, `null_behaviors`, `lifecycle_behaviors`, `contract`); the accepted end-to-end execution and the off-grid `fmi3Discard` path are later increments. |

### Record profile parameterization and the constant-rate model variables: standards impact

The FMI-visible instance record and the model description are parameterized by a
record profile that records whether the input region `u` and the dense output
region `J` are present. The tensor profile carries both; the constant-rate
profile (`G01`) carries neither, keeping only the time base, the state vector and
its derivative. The current tensor definitions are the input-present, output-present
instance of the generic renderers, recovered by `rfl`, so the rendered adapter
bytes, the tensor model description and every existing tensor theorem are
unchanged (the compiler-rendered `build/tensor-fmi/adapter.c` and
`modelDescription.xml` are byte-identical). This subsection covers only the
constant-rate profile's model variables and value references; its C emission, FMI
lifecycle bodies, artifacts and admission remain later increments.

| Standard | Impact |
| --- | --- |
| FMI 3.0.2 §2.4.7 Definition of Model Variables (`ModelVariables`) | The constant-rate model description declares the independent `time` base and two continuous `Float64` variables: the state `x` and its derivative `der(x)`. No input variable and no output variable are declared, matching the profile's no-input, no-output record. Every variable node passes the in-tree restricted XML validator and the document is a well-formed tree accepted by the renderer/syntax relation (`TensorMetadata.constant_valid`, `constant_document`). |
| FMI 3.0.2 §2.4.7 Dimension (array variables) | The homogeneous scalar-state vector is exposed as one array `Float64` variable `x` of the state shape carrying one `Dimension` per extent (with the extent as a constant `start`), rather than one scalar variable per element. This keeps the state rank and extent symbolic and enumerates no coordinate, matching the record's contiguous state region and the compiler rule against enumerating tensor elements. The `Dimension` starts multiply back to the state element count (`constantStateVar_dim_product`, `constantDerivativeVar_dim_product`), and the fixed-zero `start` list has one value per element per the array `start` rule. |
| FMI 3.0.2 §2.4.7 Value reference (`valueReference`) | Value references are renumbered without the input region: `0` time, `1` state, `2` derivative. They are pairwise distinct (`constantValueReferences_nodup`), and the derivative's `derivative` attribute references the state's value reference (`constant_derivative_references_state`). |
| FMI 3.0.2 §2.4.8 Definition of the Model Structure (`ModelStructure`) | The model structure lists the continuous-state derivative and the initial unknown for `der(x)`. Because `der(x)` is a signed decimal constant, each entry lists an empty dependency set (`constant_structure_dependencies_empty`); every structure entry still references a declared variable's value reference (`constant_structure_references_declared`). |
### G02 expression development profile: standards impact

The `expression_composition` production admits one or more `parameter Real p =
literal;` declarations, one or more `Real` state declarations, zero or more
`Real` algebraic-variable declarations (states and algebraic variables share the
plain `Real` declaration form and are distinguished by name resolution, not
syntax), and an equation section whose equations are `der(state) = expr` or
`alg = expr`. Each right-hand side `expr` is an MLS 3.7 arithmetic expression
restricted to `+ - * /` with unary minus, parentheses, decimal literals and
declared-name references. This increment lands the lexer and the admitted
grammar; the typed frontend, source semantics (including acyclic scheduling of
the algebraic equations), Solve lowering and numerical refinement, C emission,
artifacts and production admission are later slices (see `dev/expressions.md`).
The production compiler still rejects the profile.

| Standard | Impact |
| --- | --- |
| MLS 3.7 Operators (arithmetic `+ - * /`, unary minus) | The source lexer emits `*` and `/` as their own literal terminals and a lone `+`/`-` (a sign with no following digits) as an additive operator literal; a signed decimal spelling with digits stays a single value-erasing number token, so the admitted unit, driven, array and constant profiles lex unchanged (`numberToken`, `scan_sound`, `scan_complete`). The grammar admits only the four arithmetic operators and unary minus; no relational, logical, exponent or function-call forms are in the subset. |
| MLS 3.7 Operator Precedence and Associativity | The expression grammar is stratified into additive (`expr`), multiplicative (`arith_term`) and factor (`arith_factor`) levels, so `*`/`/` bind tighter than `+`/`-` and every binary operator is left associative, matching the standard precedence table; parentheses (`arith_factor : '(' expr ')'`) override precedence. The generated LALR(1) tables (268 canonical, 222 LALR states) recognize the stratified grammar with no shift/reduce or reduce/reduce conflict, and the reusable engine's acceptance and execution certificates are re-established for the extended grammar (`Rumoca.Generated.*`), audited to the three foundational axioms. |
| MLS 3.7 Component Declarations (parameter variability; predefined type `Real`) | A parameter is a `Real` component with a literal binding (`parameter Real p = literal`); states and algebraic variables are unbound `Real` components. The subset admits one variable per clause, `Real` only, with no other prefixes, dimensions or modifiers. The classification of a name as a parameter, state or algebraic variable is a resolution obligation of the later semantics slice. |
| MLS 3.7 Simple Equations; Derivative Operator `der` | Each equation is a scalar simple equation: `der(state) = expr` (a state derivative equation) or `alg = expr` (an algebraic equation defining an algebraic variable). Acyclic scheduling of the algebraic equations and rejection of a cyclic algebraic dependency, an unbound name and a duplicated name are obligations of the later source-semantics slice, not yet built. |

### eFMI 1.0.0 Beta 1 Chapter 2 container and manifests (tensor eFMU archive and Algorithm Code admission): standards impact

Stage 3 of the tensor eFMI path (finding TF01) adds the tensor eFMU archive
assembly with its composed contract, the tensor Algorithm Code actual-file
checker, and CLI admission of tensor eFMI Algorithm Code (`.alg`) output. The
archive reuses the shared stored-ZIP generator over the same fixed member roster
the scalar path uses: the pinned tensor square Algorithm Code, the certified-kernel
tensor Production Code, the three serialized manifests for the model name and
packaging identity, and the pinned vendored schemas (`TensorArtifact.efmiCode`,
`efmuArchive`). `TensorArchiveContract` and `tensor_archive_correct` prove the
member roster, per-member checksums, container-manifest correlation and complete
stored-ZIP bytes, universal in the packaging identity and the model name
(`TensorArchiveContract.roster`, `.code_members`, `.schema_members`). The
`tensor-algorithm` `verify-artifact` kind emits the axiom-audited
`Rumoca.CheckedTensorEFMIFiles.source_to_algorithm` from the independently read
source, EBNFs and Algorithm Code bytes compiled through `compileTensor`, and the
CLI gates `-o out.alg` publication on it (`EFMIExport.writeTensorAlgorithm`,
`tests/efmi-algorithm.sh`). The tensor Production C actual-byte checker is also
implemented (`EFMITensorProductionArtifactCheck`, binding a read Production C file
to the certified translation unit per fragment via `render_chars` and emitting
`source_to_production`, validated standalone with the three approved axioms).

The tensor manifest actual-byte checker now lands: the `tensor-efmi-directory`
`verify-artifact` kind (`EFMITensorManifestArtifactCheck`) reads the three tensor
manifests, the Algorithm Code and the Production C from a directory, and composes
their XML serialization and validity and the SHA-1 checksum graph, binding each
code file and each hashed manifest to the correlated tensor code products, into
the axiom-audited `Rumoca.CheckedTensorEFMIFiles.source_to_manifests`
(`tensor_manifests_correct_of_documents`), gated in `tests/tensor-c.sh`. The 7.4 KB
Production Code manifest made two checksum-certificate costs matter that were
negligible at the scalar sizes: the SHA-1 schedule now reduces through a
structural recurrence over masked `Nat` words rather than an array-and-mutation
`UInt32` loop, and the fixed checking entry points run with the 64 MB thread stack
the `verify-artifact` job already sets. The composed manifest certificate then
certifies the actual bytes within the shared gate's memory budget; see
[verification performance](verification-performance.md).

Complete tensor eFMU (`.efmu`) archive publication now lands. The
`tensor-efmi-archive` checker (`EFMITensorArchiveArtifactCheck`) reads the actual
`.efmu` bytes, re-derives the manifest contract and composes it with the stored-ZIP
transport over all fifty archive members into the axiom-audited
`Rumoca.CheckedTensorEFMIFiles.source_to_archive`. The default CLI admits `-o
out.efmu` for the fixed tensor square profile through
`EFMIExport.writeTensorArchive`, gated on that certificate. The certificate peaks
at parity with the scalar eFMU archive certificate the gate already builds and
accepts (about 12.8 GiB against about 12.3 GiB, both cold): the resident peak is
dominated by the re-derived manifest contract plus the stored-ZIP payload over the
140 KB of archive members (about 130 KB of which are the pinned vendored schemas
the scalar archive also certifies), not by any single whole-document step. The XML
serialization certificate was made linear per fragment (removing the
whole-document decide) but this is not what dominates the archive peak; the earlier
"8 GiB gate budget" figure was inconsistent with the scalar archive certificate and
is withdrawn. See [verification performance](verification-performance.md). The
certificate is gated through the CLI publication in `tests/tensor-c.sh` and
`tests/efmi-production.sh`.

| Standard | Impact |
| --- | --- |
| eFMI 1.0.0 Beta 1, Chapter 2 container manifest (`efmiContainerManifest.xsd`, `__content.xml`) and archive layout (`schemas` at the archive root) | The tensor eFMU is assembled through the shared stored-ZIP generator, so its member roster, `__content.xml` container manifest, stored-ZIP transport and pinned-schema membership are the same authored profile the scalar archive certificate covers, proved for the tensor members universal in identity and model name (`TensorArchiveContract`). The complete archive byte checker and CLI `.efmu` admission that would exercise this against actual archive bytes remain open (the Production C byte certificate is in place; the open work is making the composed manifest/SHA-1/stored-ZIP certificate over the concrete tensor artifacts affordable for the shared gate). |
| eFMI 1.0.0 Beta 1, Algorithm Code manifest and Chapter 2 identities (UUID layout, distinctness, UTC generation time) | The tensor Algorithm Code manifest and the three container identities are the pinned `TensorManifest.prepare` documents for the model name and packaging identity, reused unchanged from Stage 2; the archive contract carries their well-formedness, validity and origin-reference checksum. The `tensor-algorithm` certificate binds the compiled tensor source to the pinned Algorithm Code member bytes, and CLI publication requires it. |
| eFMI 1.0.0 Beta 1, §3.2 Algorithm Code admission through the toolchain | Tensor eFMI Algorithm Code output is admitted through the CLI for the fixed tensor square profile only, gated by the fixed `tensor-algorithm` certificate with the usual three foundational axioms; any Algorithm Code text that is not the pinned tensor square profile is rejected at the checker (`differs from the pinned tensor square profile`), exercised by a mutation control. This is a restriction to the fixed extent `2` square kernel (TF04), not a claim of general eFMI Algorithm Code admission. |

TF01 is closed. The tensor eFMU archive byte checker
(`tensor-efmi-archive`, `Rumoca.CheckedTensorEFMIFiles.source_to_archive`) composes
the manifest XML, validity and SHA-1 checksum graph with the stored-ZIP transport
over all fifty members against the actual archive bytes, and the default CLI admits
complete tensor eFMU output through `EFMIExport.writeTensorArchive` gated on that
certificate, exercised end to end in `tests/tensor-c.sh` and
`tests/efmi-production.sh` (publication, no-build reuse, vendored XSD validation,
checksum correlation and a Production C mutation control). The archive certificate
peaks at parity with the scalar eFMU archive certificate the gate already accepts;
the "8 GiB gate budget" that framed the remaining work was inconsistent with that
scalar baseline and is withdrawn. TF04 (fixed extent `2`, square kernel) remains
open: this is admission of the fixed extent-`2` square profile, not general tensor
rank, extent or eFMI Production Code admission.

### G01 constant-rate development profile: standards impact

The `constant_composition` production admits two or more scalar `Real` state
declarations followed by one `der(state) = literal` equation per state whose
right-hand side is a signed decimal literal. It is a development profile: the
production compiler still rejects it, and only the frontend, source semantics
and Solve lowering are built (see `dev/constant-rates.md`). C emission, FMI/eFMI
artifacts and admission are later increments. Each rate literal is recognized as
a single value-erasing number token and its base-ten content is rounded to the
nearest-even binary64 value.

| Standard | Impact |
| --- | --- |
| MLS 3.7 §2.4.2 Floating Point Numbers (lexical `UNSIGNED-REAL`) | The lexer recognizes the unsigned-real form (digits, an optional fraction, an optional `e`/`E` exponent with an optional sign) together with a leading unary sign, and records the exact base-ten content (`parseDecimal`). The admitted subset restricts a rate to a spelling the lexer distinguishes from a bare digit literal: it carries a sign, a decimal point or an exponent (the fixture uses `2.5` and `-1`). A bare single-digit rate keeps the existing `.literal` class and is not admitted here; a trailing point or a bare exponent is rejected by resolution. No change is made to how the admitted unit and array profiles lex their `'0'`, `'1'` and `'2'` literals. |
| MLS 3.7 §3.7.2 Derivative and Special Purpose Operators (`der`) | Each equation has the form `der(state) = literal`, one per declared state. Resolution binds every `der` reference to a distinct declared state and requires the equation set to be a permutation of the declared states, so an unbound or uncovered state and a duplicate declaration are rejected with diagnostics. The written order of the `der` equations is immaterial (`Model.rateOf_perm`, `Model.lower_rates_perm`). |
| MLS 3.7 §8.3.1 Simple Equations; §8.6 Initialization | The source system is a set of independent constant-rate states, each initialized at `+0` (no start modifier is admitted). The Solve lowering is a multi-state IVP whose per-state rate is the exactly rounded binary64 value of the literal; the lowering chain and initialization are proved (`Model.lowering_chain`, `Model.initialization_chain`), and the rounding is the round-to-nearest-even scaled-rounding spec (`Decimal.rate_rounds`), reusing the unit profile's decimal machinery rather than duplicating it. |
### eFMI 1.0.0 Beta 1 Production Code and manifest array variables (tensor square profile): standards impact

Stage 2 of the tensor eFMI path (finding TF01) adds the eFMI Production Code
translation unit and the Algorithm/Production/container manifests for the fixed
extent array square profile as package products, with no change to CLI admission:
the default CLI still rejects tensor eFMI output, and the array/tensor profile
stays admitted only to FMI 3 FMU output. The Production Code method functions
reuse the certified tensor kernel entries (`rumoca_rhs`,
`rumoca_square_jacobian_diag` and the shared helpers) rather than re-emitting the
numerical bodies; the `Model` record and the manifests describe the logical
variables `u`, `x` and `J` as fixed-extent array members with dimensions. The
derivative method is proved to compute the prepared derivative `u .* u` and the
Jacobian output the doubled input `u + u` (`doStep_derivative_refines`,
`doStep_jacobian_refines`, universal in the state shape); the manifests are proved
well-formed in the in-tree XML output grammar with the checksum and reference
correlations (`documents_valid`, `variable_declared`, `origin_reference`,
`prepare_checksums`, the data/function reference lemmas), and the compiler tie
proves the Production contract and the manifest well-formedness for the pinned
`TensorSquare` fixture (`TensorProductionArtifact.production_correct`,
`TensorProductionArtifact.manifests_correct`, `squareProductionArtifact`). The
emitted manifests are validated against the vendored eFMI XSDs at the boundary,
and the Production C compiles as C11. `dev/efmi.md` documents the products and
their theorems.

| Standard | Impact |
| --- | --- |
| eFMI 1.0.0 Beta 1, Algorithm Code manifest variables (`efmiVariable` with `Dimensions`) | The Algorithm Code manifest declares `u`, `x` and `J` as `RealVariable`s carrying a `Dimensions` child with the fixed one-based `number`/`size` extents, beside the scalar `samplePeriod` clock constant the required `Clock` element references. This is a restriction to fixed extents `2` and `2, 2`; general extents and ranks remain out of profile (TF04). Membership in the vendored `efmiAlgorithmCodeManifest.xsd` is checked at the boundary. |
| eFMI 1.0.0 Beta 1, Production Code manifest typedefs and variables (`efmiTypeDefs` Components with `Dimensions`, `efmiVariables`/`efmiDimensions`) | The Production Code manifest declares the `Model` struct as a `Typedef` whose `Components` carry the same fixed dimensions, the three method `Function`s and the `TargetTypes`/`Typedefs` for the 64-bit real and 32-bit status types. Membership in the vendored `efmiProductionCodeManifest.xsd` is checked at the boundary. |
| eFMI 1.0.0 Beta 1, §5.1.5 (logical data mapping) | Each method's `LogicalData` `DataReference` maps an Algorithm Code variable, and the error anchor, through the method's own instance formal parameter and the named struct component; `FunctionReference`s correlate the block method identifiers with the C function identifiers. The origin `ManifestReference` and the container `ModelRepresentation`s hash the serialized dependency bytes (SHA-1), proved by the checksum-correlation lemmas. |
| MISRA C:2025 Dir 4.12 (no dynamic memory) and Rule 21.3 (no `malloc`/`calloc`/`free`) | The emitted Production C allocates nothing: each method function clears its status word, calls the prepared kernel entries with the `Model` record's array-member pointers and stack-fixed element/cell counts, and returns the status. The kernel entries themselves run counted loops over caller-provided storage. No dynamic allocation and no standard-library memory management appear in the emitted C, which compiles clean under `-std=c11 -Wall -Wextra -Werror -pedantic`. |

### eFMI 1.0.0 Beta 1 GALEC arrays (Algorithm Code for the tensor square profile): standards impact

Stage 1 of the tensor eFMI path (finding TF01) adds the GALEC Algorithm Code for
the fixed extent array square profile as package products, with no change to CLI
admission: the default CLI still rejects tensor eFMI output, and the array/tensor
profile stays admitted only to FMI 3 FMU output. The GALEC grammar gains a
`program` start rule admitting the unchanged scalar unit block and a
`tensor_block` with extent-two array declarations, the elementwise product `.*`
and a Jacobian output; the regenerated LALR table keeps every checked certificate
and the scalar acceptance proof routes through the new alternative. The emitted
derivative and Jacobian text is proved to lex and parse to the resolved tensor
block that denotes the prepared pointwise square kernel
(`Rumoca.EFMI.tensor_render_denotes`), the GALEC elementwise product is proved
equal to the prepared kernel derivative and the Jacobian coefficients to the
doubled-input diagonal (`square_derivative_refines`, `square_jacobian_coefficients`,
universal in the state shape), and the compiler tie proves the pinned
`TensorSquare` prepared kernel is that square kernel (`Rumoca.square_prepared_kernel`,
`TensorAlgorithmArtifact.algorithm_correct`). `dev/efmi.md` documents the product
and its theorems.

| Standard | Impact |
| --- | --- |
| eFMI 1.0.0 Beta 1, §3.2.3 (lifecycle), §3.2.4 G-2 (declarations), G-3 (expressions), G-4 (statements) | The authored GALEC profile admits a tensor block with fixed extent-two `Real[2]` and `Real[2, 2]` declarations, an elementwise-product assignment and a Jacobian call. Correction (GJ01, 2026-09-22): internal resolution does not make `jacobian` a normative GALEC built-in; the emitted call lacks a conforming definition/interface. The previous unqualified restriction-of-the-standard claim is withdrawn. General extents, ranks, statements and expressions remain out of profile (TF04). |
| eFMI 1.0.0 Beta 1, Algorithm Code semantics (method lifecycle, arithmetic) | The GALEC to Solve refinement is universal in rank, extent and arithmetic interpretation: the elementwise product denotes the prepared `PointwiseIVP` derivative and the Jacobian output denotes the prepared diagonal coefficient program (the doubled input). Binary64 is one interpretation, not a claim that eFMI mandates it. The refinement is instantaneous; a sampled method schedule and clock are carried structurally as in the scalar profile. |
| eFMI 1.0.0 Beta 1, artifact conformance (manifests, Production Code, eFMU archive) | Not yet extended: this stage certifies the Algorithm Code product only. Tensor manifests, tensor Production C, the eFMU archive, the checker extension and CLI admission remain open, each blocked on its own contract and actual-artifact evidence. A green parse of the emitted `.alg` bytes in the compiler test executable is boundary evidence for the emitter, not eFMU conformance. |
| eFMI 1.0.0 Beta 1, TF01 closure criteria | TF01 (tensor eFMI path) is closed: the tensor GALEC Algorithm Code, Production Code and container manifests are certified against actual bytes, the complete `.efmu` archive certificate composes them with the stored-ZIP transport, and the default CLI admits tensor Algorithm Code and complete tensor eFMU output gated on those certificates. The archive certificate peaks at parity with the scalar eFMU archive certificate; the "8 GiB gate budget" figure is withdrawn. TF04 (fixed extent `2`, square kernel) is unchanged: this is the fixed square profile, not general tensor rank/extent or eFMI Production Code admission. |
### Conforming tensor `fmi3Reset` lifecycle restoration: standards impact

The tensor adapter's `fmi3Reset` body now restores exactly what the scalar reset
restores, returning the instance to the state directly after `fmi3Instantiate`.
The body (`FMI3.TensorReset.bookkeepingTail`) keeps the symbolic zero-fill of the
state region and additionally resets the time base and the lifecycle bookkeeping
cells `timeMin`, `eventTime`, `lastCompleted`, `stop`, `stopDefined` to zero and
writes the lifecycle `mode` cell to Instantiated, mirroring the scalar
`Reset.tail`. This closes finding F8 in `dev/trust-ledger.md` with proofs and
native evidence; the F8 allowlist entries are removed from `tests/fmi3.py`.

| Standard | Impact |
| --- | --- |
| FMI 3.0.2, `fmi3Reset` (returns the FMU to the state directly after `fmi3Instantiate`) | `FMI3.TensorReset.reset_behaviors` proves the tensor reset runs to the result heap `finalHeap`, and `FMI3.TensorReset.bookkeeping_reaches` discharges the bookkeeping tail universally in the post-fill heap: the time base and the clock/stop bookkeeping cells become `+0`, `stopDefined` false and the lifecycle `mode` cell Instantiated. `reads_initialization` keeps the state region at the prepared fixed-zero fill (`initialization_is_zero`) and `preserves_other_instances` keeps every other pool instance untouched, so the reset returns the instance to the post-instantiation state. |
| FMI 3.0.2, §2.3.1 State Machine of Calling Sequences (Instantiated state; `fmi3EnterInitializationMode` from Instantiated) | `FMI3.TensorReset.reset_mode_instantiated` proves the post-reset `mode` cell reads Instantiated (`Mode.instantiated.code`), which is the guard input `fmi3EnterInitializationMode` requires (its single permitted mode is Instantiated). A reset tensor instance therefore re-enters Initialization Mode and re-initializes exactly as the scalar adapter's does. The `mode`-reads-Instantiated conjunct is carried by `TensorReset.Contract` (`reinitializes`) into `TensorAdapter.Contract`. Native evidence: with the allowlist removed, the all-behavior matrix over the regenerated `TensorSquare.fmu` reports 0 recorded-finding discrepancies and 0 unexpected, and re-initialization plus a step after reset succeed on both adapters. |

### Checked no-heap and acyclic call-graph policy over the generated call graph: standards impact

| Standard | Impact |
| --- | --- |
| MISRA C:2025 Dir 4.12 (no dynamic memory) | The reusable decidable policy `CCallPolicy.NoHeap` (`packages/backend-c/RumocaC/NoHeapPolicy.lean`) requires every callee name in every generated function body to be a defined function, a declared kernel entry, a header-declared FMI function or a named external, and rejects an explicit list of allocation entry points. `noHeap_no_alloc_call` proves, over the shared machine's own scheduled call step, that a call issued from a policy-checked body never names an allocation symbol, and `noHeap_execution_no_alloc` lifts this across the body's reachable loop states. The guarantee is therefore a checked contract, not a `malloc` text search. It is discharged for the scalar adapter (`CallPolicy.unit_no_heap`) and carried as the `no_heap_acyclic` conjunct of `FMI3.SourceBuildContract` on the actual bytes. |
| MISRA C:2025 Rule 21.3 (no `malloc`/`calloc`/`realloc`/`free`) | The named allocation set `CCallPolicy.allocationNames` lists `malloc`, `calloc`, `realloc`, `reallocarray`, `free`, `aligned_alloc`, `posix_memalign`, `memalign`, `valloc`, `pvalloc`, `strdup`, `strndup`; `NoHeap` excludes every one of them from the admitted callees, and the scalar adapter list is proved to satisfy the policy. |
| MISRA C:2025 Rule 17.2 (no direct or indirect recursion) | `CCallPolicy.Acyclic` states that the direct-call relation among defined functions has no cycle; `acyclic_of_ranked` discharges it from a decidable topological rank (`FMI3.CallPolicy.functionRank`), and `CallPolicy.unit_acyclic` proves it for the complete scalar adapter function list. Direct and indirect recursion among the generated defined functions is thereby excluded; indirect calls through a function pointer remain a separate resolution boundary. |
| FMI 3.0.2, §2.2.2 Platform Dependent Definitions | The header-declared FMI functions and the named library/callback externals (`isfinite`, `floor`, `fegetround`, `strlen`, `strspn`, `strcmp`, `atomic_exchange`, `atomic_store`, `logMessage`) are recorded as explicit named boundaries in `CallPolicy.bUnit` rather than resolved to generated bodies; the FMI headers and platform types stay external. The policy classifies these boundaries and asserts nothing about the native implementation of the header-declared routines. |

### Checked no-heap and acyclic call-graph policy over the tensor adapter call graph: standards impact

The same reusable policy is now instantiated for the tensor FMI adapter function list (`FMI3.TensorFunctions.functions`), whose 19 shape-dependent bodies, reused static-factory/release helpers and scalar fallback bodies are checked against the tensor boundary set `FMI3.TensorCallPolicy.bTensor` (`packages/backend-fmi3/RumocaFMI3/TensorCallPolicy.lean`). This closes the tensor share of TF06 for these three rules.

| Standard | Impact |
| --- | --- |
| MISRA C:2025 Dir 4.12 (no dynamic memory) | `FMI3.TensorCallPolicy.tensor_no_heap` proves `CCallPolicy.NoHeap (TensorFunctions.functions model m sigs) bTensor` universally in the tensor shape, the scalar witness model and the header signature list: every callee in every emitted tensor body is a defined function, a declared kernel entry or a named external, and none is an allocation entry point. It reuses `noHeap_no_alloc_call`/`noHeap_execution_no_alloc` over the shared machine and is carried as the `no_heap_acyclic` conjunct of `Rumoca.TensorSourceBuildContract` on the actual tensor adapter bytes. The tensor derivative getter and step call the prepared kernel entries `rumoca_rhs` and `rumoca_square_jacobian_diag` directly; both are named kernel boundaries, not allocation. |
| MISRA C:2025 Rule 21.3 (no `malloc`/`calloc`/`realloc`/`free`) | `bTensor` admits the same generated, library and callback names as the scalar `bUnit` plus the two numerical kernel entries, and `NoHeap` excludes every name in `CCallPolicy.allocationNames`; the complete tensor adapter list is proved to satisfy the policy, so no standard-library memory-management symbol is named in any tensor body. |
| MISRA C:2025 Rule 17.2 (no direct or indirect recursion) | `FMI3.TensorCallPolicy.tensor_acyclic` proves `CCallPolicy.Acyclic (TensorFunctions.functions model m sigs)` from the shared decidable rank `FMI3.CallPolicy.functionRank`: the two kernel entries are unranked leaves outside the list, the reused helpers rank at 1 and the public tensor functions at 2, and no tensor body calls another public function, so the direct-call relation among defined functions has no cycle. Indirect calls through a function pointer (the instance logger record field) remain a separate resolution boundary. |

### Native all-behavior matrix over the 75 common functions: standards impact

`tests/fmi3.py --matrix`, wired into `tests/fmi3.sh` for both `build/Integrator.fmu`
and `build/TensorSquare.fmu`, drives the raw FMI 3 ABI over every one of the 75
emitted public functions and asserts the documented status and logger callbacks
for each behavior class. It instantiates natively, at least once on each adapter,
the classes the trust ledger otherwise recorded as proof-only (findings F2 and
F6). The importer/boundary-evidence rule already stated for this stage still
holds: native compilation, ZIP transport and the FMPy/ctypes importer are
boundaries outside the proof model, and the matrix is native boundary evidence,
not a certificate. It fails the run on any status or callback that regresses from
the proved behavior, and prints (but tolerates) the cells recorded as findings.

| Standard | Impact |
| --- | --- |
| FMI 3.0.2, §2.2.3 Status Returned by Functions; common-function null and unsupported-capability handling | The matrix instantiates, per function, the `fmi3Error` return for a null instance (70 status functions, plus the factory's null-handle creation failure and a safe `fmi3FreeInstance(NULL)`), the 25 capability rejections (`fmi3Error` with the logged message "FMI capability is not supported" when logging is enabled and no callback when disabled), the 24 absent-typed accessors (`fmi3OK` on an empty request and `fmi3Error` with "No variables of this type exist" on a non-empty one), the argument rejections (non-finite set value, unknown value reference, mismatched `nValues`), the off-grid communication-step `fmi3Discard`, `fmi3SetDebugLogging` with valid and invalid category lists, and `fmi3GetVersion`. 75/75 functions and 514 behavior cells are exercised on each adapter. Observed statuses and messages match the proved behavior on both adapters. |
| FMI 3.0.2, §2.3.1 State Machine of Calling Sequences (error state) | A function returning `fmi3Error` moves the instance to the terminal error state, in which only `fmi3FreeInstance` and `fmi3Reset` are permitted and final values remain readable. The matrix confirms this natively (a non-empty absent-typed get returns "No variables of this type exist" and a subsequent set is refused with "Call is not allowed in the current FMI state") and therefore runs each error-inducing cell on a fresh instance so the true first-error message is observed on all 24 absent-typed accessors. |
| FMI 3.0.2, `fmi3Reset` (returns the FMU to the state directly after `fmi3Instantiate`) | Native evidence: the scalar adapter conforms; after a full initialization, `fmi3Reset` returns `fmi3OK` and a subsequent `fmi3EnterInitializationMode` succeeds, so the instance re-initializes and steps. The tensor adapter does not: once initialization has run, `fmi3Reset` returns `fmi3OK` but a following `fmi3EnterInitializationMode` is rejected with "Call is not allowed in the current FMI state", so the reset FMU cannot be re-initialized. This is a genuine conformance divergence, recorded as finding F8 in `dev/trust-ledger.md`; the matrix reports it as a recorded finding rather than a regression. `fmi3Reset` directly after `fmi3Instantiate` (before any initialization) restores the Instantiated state on both adapters. |
| FMI 3.0.2, importer/boundary evidence | The matrix is exercised through `tests/fmi3.sh` on the actual published FMUs (the unit FMU from `Rumoca.compile`, the tensor FMU from the default CLI's `Rumoca.compileTensor` path). It supplements, and does not replace, the existing archive/schema/ABI checks and the FMPy Model Exchange and Co-Simulation runs. Native compilation, ZIP transport and the importer remain outside the proof model. |
### Checked no-heap and acyclic call-graph policy over the generated call graph: standards impact

| Standard | Impact |
| --- | --- |
| MISRA C:2025 Dir 4.12 (no dynamic memory) | The reusable decidable policy `CCallPolicy.NoHeap` (`packages/backend-c/RumocaC/NoHeapPolicy.lean`) requires every callee name in every generated function body to be a defined function, a declared kernel entry, a header-declared FMI function or a named external, and rejects an explicit list of allocation entry points. `noHeap_no_alloc_call` proves, over the shared machine's own scheduled call step, that a call issued from a policy-checked body never names an allocation symbol, and `noHeap_execution_no_alloc` lifts this across the body's reachable loop states. The guarantee is therefore a checked contract, not a `malloc` text search. It is discharged for the scalar adapter (`CallPolicy.unit_no_heap`) and carried as the `no_heap_acyclic` conjunct of `FMI3.SourceBuildContract` on the actual bytes. |
| MISRA C:2025 Rule 21.3 (no `malloc`/`calloc`/`realloc`/`free`) | The named allocation set `CCallPolicy.allocationNames` lists `malloc`, `calloc`, `realloc`, `reallocarray`, `free`, `aligned_alloc`, `posix_memalign`, `memalign`, `valloc`, `pvalloc`, `strdup`, `strndup`; `NoHeap` excludes every one of them from the admitted callees, and the scalar adapter list is proved to satisfy the policy. |
| MISRA C:2025 Rule 17.2 (no direct or indirect recursion) | `CCallPolicy.Acyclic` states that the direct-call relation among defined functions has no cycle; `acyclic_of_ranked` discharges it from a decidable topological rank (`FMI3.CallPolicy.functionRank`), and `CallPolicy.unit_acyclic` proves it for the complete scalar adapter function list. Direct and indirect recursion among the generated defined functions is thereby excluded; indirect calls through a function pointer remain a separate resolution boundary. |
| FMI 3.0.2, §2.2.2 Platform Dependent Definitions | The header-declared FMI functions and the named library/callback externals (`isfinite`, `floor`, `fegetround`, `strlen`, `strspn`, `strcmp`, `atomic_exchange`, `atomic_store`, `logMessage`) are recorded as explicit named boundaries in `CallPolicy.bUnit` rather than resolved to generated bodies; the FMI headers and platform types stay external. The policy classifies these boundaries and asserts nothing about the native implementation of the header-declared routines. |

### Checked no-heap and acyclic call-graph policy over the tensor adapter call graph: standards impact

The same reusable policy is now instantiated for the tensor FMI adapter function list (`FMI3.TensorFunctions.functions`), whose 19 shape-dependent bodies, reused static-factory/release helpers and scalar fallback bodies are checked against the tensor boundary set `FMI3.TensorCallPolicy.bTensor` (`packages/backend-fmi3/RumocaFMI3/TensorCallPolicy.lean`). This closes the tensor share of TF06 for these three rules.

| Standard | Impact |
| --- | --- |
| MISRA C:2025 Dir 4.12 (no dynamic memory) | `FMI3.TensorCallPolicy.tensor_no_heap` proves `CCallPolicy.NoHeap (TensorFunctions.functions model m sigs) bTensor` universally in the tensor shape, the scalar witness model and the header signature list: every callee in every emitted tensor body is a defined function, a declared kernel entry or a named external, and none is an allocation entry point. It reuses `noHeap_no_alloc_call`/`noHeap_execution_no_alloc` over the shared machine and is carried as the `no_heap_acyclic` conjunct of `Rumoca.TensorSourceBuildContract` on the actual tensor adapter bytes. The tensor derivative getter and step call the prepared kernel entries `rumoca_rhs` and `rumoca_square_jacobian_diag` directly; both are named kernel boundaries, not allocation. |
| MISRA C:2025 Rule 21.3 (no `malloc`/`calloc`/`realloc`/`free`) | `bTensor` admits the same generated, library and callback names as the scalar `bUnit` plus the two numerical kernel entries, and `NoHeap` excludes every name in `CCallPolicy.allocationNames`; the complete tensor adapter list is proved to satisfy the policy, so no standard-library memory-management symbol is named in any tensor body. |
| MISRA C:2025 Rule 17.2 (no direct or indirect recursion) | `FMI3.TensorCallPolicy.tensor_acyclic` proves `CCallPolicy.Acyclic (TensorFunctions.functions model m sigs)` from the shared decidable rank `FMI3.CallPolicy.functionRank`: the two kernel entries are unranked leaves outside the list, the reused helpers rank at 1 and the public tensor functions at 2, and no tensor body calls another public function, so the direct-call relation among defined functions has no cycle. Indirect calls through a function pointer (the instance logger record field) remain a separate resolution boundary. |

### Stage record: unit and square Jacobian array profiles admitted to FMI 3 FMU output

This record completes the recurring review for the enlarged admitted subset
at the revision that admits the array profile to production FMU output.

| Required record | Evidence |
| --- | --- |
| Scope and identity | Production entry points: `Rumoca.compile` for the unit profile and `Rumoca.compileTensor` for the array profile, dispatched by the `rumoca` CLI; FMU publication gates are the `fmi3` and `tensor-fmi3` certificate kinds of `lake run verify-artifact`. Admitted EBNF productions: `unit_composition`, and `array_composition` with `jacobian_body` (`input Real u[2]`, `output Real x[2](each start=0, each fixed=true)`, `output Real J[2,2]`, `der(x) = u .* u`, `J = jacobian(u .* u, u)`), with the extent literal fixed to `2` by the grammar. Rejected forms: the driven compositions, any other extent, tensor sources for eFMI or C output (diagnostic, no publication). Reviewed artifacts: `build/Integrator.fmu` and `build/TensorSquare.fmu` produced by `tests/fmi3.sh`. |
| Architecture continuity | The array profile uses the shared LALR engine and typed actions, the Flat/DAE/Solve lowering to `PointwiseIVP`, the prepared tensor kernel product with two entries, the static instance pool, and the same fixed-checker structure as the unit profile; tensor rank and extents stay symbolic in every theorem. `ParserActions.Parsed.located` in `ActionsLocatedTotal` lifts the total located-parse construction to every action profile, so the tensor certificate is existential like the scalar one without kernel-evaluating the parser. |
| Normative baseline | MLS 3.7; FMI 3.0.2 ME and CS with the pinned `fmi3FunctionTypes.h` and the in-tree model-description conventions; eFMI 1.0.0 Beta 1 unchanged (tensor eFMI not built). |
| MLS coverage | Array component declarations with one literal dimension, `each start`/`each fixed` modifications (uniform fixed-zero initialization), the elementwise product `.*`, `der` of an array state, and `jacobian` as an identified extension outside MLS. Resolution, shapes and equation meaning are the array-profile lowering theorems (`ArrayCompiler.prepare_correct`, `square_jacobian_eval`, `lowering_chain_correct`); numeric interpretation is the finite tensor execution with explicit finite-arithmetic premises. |
| FMI coverage | Both interfaces: model description with `Dimension` elements, per-element start lists, explicit dependencies and identical identifier decoding (`TensorMetadata`); creation, initialization, mode transitions, termination and release over the static tensor pool; Float64 access with finiteness validation; continuous-state access, the fused derivative getter, count queries, time, reset, the co-simulation step with grid-policy discard; the two capability families for the remaining forty-nine functions; `TensorAdapter.Contract` binding the rendered text; the `tensor-fmi3` certificate `Rumoca.CheckedTensorFMI3Files.source_to_build` on the actual bytes. |
| eFMI coverage | Not extended: tensor sources are rejected for Algorithm Code and eFMU output with a diagnostic. Open finding TF01 below. |
| Proof correspondence | Per-function contracts in `packages/backend-fmi3/RumocaFMI3/Tensor*.lean` and the compiler composition `tensorSourceBuild_correct`; roots audited in `Tests/FMI3Audit.lean`, `Tests/TensorAudit.lean` and `Tests/Audit.lean` on the three permitted axioms. Explicit premises retained, as for the scalar path: the modeled `fegetround` and `floor` library returns, kernel entry resolution, and finite arithmetic. |
| Boundary evidence | The required `lake test` at this revision; `tests/tensor-c.sh` (certified kernel entries, zero-diagnostic object compile, FMPy runs of the development and production-shaped FMUs with derivatives `(1, 4)`, `x = (3, 12)` at `t = 3`, `J = (2, 0, 0, 4)` in both interfaces); `tests/fmi3.sh` (CLI publication, eFMI rejection, certificate reuse with no build, adapter mutation rejection, importer runs). Native compilation, ZIP transport and the importer remain outside the proof model. |
| Decision | The array profile is admitted to FMI 3 FMU output. Open findings carried forward with closure criteria: TF01 tensor eFMI path (build the tensor GALEC/Production Code path with its contracts or keep rejection documented); TF02 multi-reference Float64 aggregate requests (accepted only as single-reference requests; extension needs the running-offset copy proof); TF03 count negotiation for partial or oversized requests; TF04 general extents and ranks in the grammar (the extent is fixed to `2` and the kernel is the square program); TF05 native ABI, floating-environment and callback correspondence, shared with the unit profile; TF06 MISRA C:2025 inventory for the tensor adapter, shared with K05. **Stage decision for further growth: open until K02 to K05 close for the unit profile.** |

### Tensor artifact compiler path, `writeSources` and the `tensor-fmi3` source-build certificate: standards impact

| Standard | Impact |
| --- | --- |
| FMI 3.0.2, §2.4 Structure of an FMU (FMU archive layout) and §4.2.6 / Annex source-code FMU (`sources/`, `buildDescription.xml`) | The pointwise tensor profile now has a production-shaped source-build path kept out of the CLI's default admission. `Rumoca.compileTensor` parses the array profile through `ArrayProfile.parseLocated`/`ArrayCompiler.prepare` into a `TensorArtifact` owning the executable `Solve.TensorFMI3Model`; a tensor `writeSources` variant emits the same FMU layout the scalar driver does (`sources/model.c`, `sources/fmi3.c`, `sources/buildDescription.xml`, `modelDescription.xml`, `extra/org.cognipilot.rumoca/Source.mo`), with `model.c` the certified tensor kernel text (the helper renders, the pointwise IVP sources and the scratch-free `rumoca_square_jacobian_diag` entry), `fmi3.c` the rendered tensor adapter (`TensorFunctions.render`), and the two XML documents the prepared tensor model description and the shared source-build recipe. The fixed checker branch `verify_tensor_fmi3_build_files` reads the same five actual files, compiles the source with `compileTensor`, kernel-checks the actual `model.c` against the certified kernel text and the actual `fmi3.c` against `TensorFunctions.render` (reusing the per-function tree-equality and tokenization machinery of the scalar adapter certificate, generalized over the tensor function list), checks the build and model-description bytes against the prepared documents, and emits `Rumoca.CheckedTensorFMI3Files.source_to_build : compileTensor input = .ok a → TensorSourceBuildContract a modelC buildXml adapter md` under the same `propext, Classical.choice, Quot.sound` axiom whitelist. It is registered as certificate kind `tensor-fmi3` in the root `verify-artifact`, with the same inputs as `fmi3`, so it caches like the other actual-file certificates. |
| MLS 3.7.2 array-and-record built-ins (`jacobian`), array declarations and `.*` | The array profile remains a development case: the default CLI still rejects `examples/DrivenIntegrator.mo` and the array sources, and this path admits no new production grammar. `TensorSourceBuildContract` composes the already-certified pointwise IVP artifact contract, the tensor adapter contract, the build-description contract, the identifier and instantiation-token agreements and the tensor model-description XML document for the single admitted development source `examples/development/TensorSquare.mo`; tensor rank and extents stay symbolic in the shape parameter and no tensor element is enumerated. |
| FMI 3.0.2, importer/boundary evidence | `tests/tensor-c.sh` now assembles the tensor FMU through `compileTensor` + the tensor `writeSources` + the archive step (the `tensor-fmu` development command, not the default CLI path), runs `lake run verify-artifact tensor-fmi3` on the extracted sources with the certificate's axiom lines required, and drives the FMU in FMPy in Model Exchange and Co-Simulation exactly as the existing boundary run does (`x@t=3 = (3, 12)`, `J = (2, 0, 0, 4)`). Native compilation, ZIP transport and the FMPy importer remain boundaries outside the proof model. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Tensor `fmi3DoStep` floating-environment interface and off-grid `fmi3Discard`: standards impact

| Standard | Impact |
| --- | --- |
| FMI 3.0.2, §4.2.1 Computation (`fmi3DoStep`) and §2.4.4 Status Returned by Functions (`fmi3Discard`) | The whole-call `fmi3Discard` result for a Co-Simulation `fmi3DoStep` whose communication step does not lie on the admitted unit internal time grid (off-grid) or exceeds the internal-step bound (over-bound), while still making clock progress inside any `stopTime` window, is now proved for the tensor adapter: `TensorDoStep.discard_prefix` reaches the shared `Runtime.stepDiscard` block through the reused model-independent guard sections (`StepGuards.rounding_path`/`clock_path` and the rejected `grid_path` branch), before any tensor declaration, and `discard_suppressed_behaviors`/`discard_logged_behaviors` return `fmi3Discard` (status 2) with the heap unchanged apart from the scalar output-cell initialization the prefix documents. This reuses the scalar `StepDiscard` logging-callback composition over the tensor instance record's `logging`/`environment`/`logger` cells, so the discard is reported for both the suppressed and the enabled logging outcomes. Added to `TensorDoStep.Contract` as the `discarded` field alongside the null-handle `rejected` field and the `lifecycle_behaviors` companion, and bound per floating-environment header in `FMI3.TensorAdapter.Contract`. |
| FMI 3.0.2, §2.4.7 Getting and Setting Variable Values (floating environment) and the CS rounding guard | The tensor accepted `fmi3DoStep` execution and its contract no longer assume the `FE_TONEAREST` round-to-nearest constant externally. The tensor Co-Simulation numerical chain and the accepted end-to-end theorems are rebased onto the header-aware interface `fenvInterface header = CFenv.Header.interface header (cInterface static.addresses)`, so the reused rounding guard reads the macro and the numerical tail keeps every pinned type spelling (definitionally unchanged) and helper/status constant. The only remaining external premises are the scalar path's modeled `fegetround` and `floor` platform-library returns; the scalar adapter and unit FMU bytes are unchanged. |
| C11 (ISO/IEC 9899:2011) §7.6 Floating-point environment (`<fenv.h>`) | The round-to-nearest guard models `fegetround()` against the `FE_TONEAREST` macro. The header-aware interface supplies `FE_TONEAREST` as a header-parameterized signed-`int` constant (no native macro value, mode stability or exception-flag restoration is claimed); `fegetround`'s return is the explicit modeled external, exactly as the scalar path carries it. No new floating-environment access is emitted. |
| MISRA C:2025 Dir 4.12 (no dynamic memory) and Rule 21.3 (no `malloc`/`calloc`/`free`) | The discard path allocates nothing: it initializes the fixed output cells and, on the rejected grid branch, invokes the prepared logging callback (when enabled) with stack-fixed arguments before returning `fmi3Discard`. No dynamic allocation and no standard-library memory management appear on the emitted discard path. |
| C11 / native boundary | The emitted `fmi3DoStep` body is unchanged; the development tensor FMU boundary run still reads `x@t=3 = (3, 12)` and `J = (2, 0, 0, 4)` in Model Exchange and Co-Simulation, and the adapter still compiles cleanly as a standalone object and as part of the FMU shared library. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Output-aware tensor `fmi3DoStep` running `rumoca_square_jacobian_diag` per accepted step: standards impact

| Standard | Impact |
| --- | --- |
| FMI 3.0.2, §4.2.1 Computation (`fmi3DoStep`) and §2.4.7 Output | The Co-Simulation half of the square-Jacobian output wiring is now complete: the accepted tensor `fmi3DoStep` runs the prepared square-Jacobian diagonal entry once per accepted internal step, so a Co-Simulation instance's output tensor `J` (value reference 4, declared `J[2,2]` by `TensorMetadata`) is computed by the emitted adapter and read back by `fmi3GetFloat64(J)` after stepping, matching the Model Exchange getter. `TensorDoStep.function`/`doStepBody`/`tensorStepSolve`/`Contract` are parameterized on the output presence exactly as the getter is: `jacobianTail shape false` is the unchanged output-free tail (advanced-time publication then `fmi3OK`), and `jacobianTail shape true` inserts `TensorContinuousStates.jacobianCall` after the outer grid loop and before the publication, emitting `rumoca_square_jacobian_diag(&(m->u[0]), &(m->J[0]), nContinuousStates, cells)` with the argument list `TensorContinuousStates.jacobianEntryArgs`. The output-free body and its theorems (`tensorSolve_reaches`, `accepted_reaches`, `accepted_behaviors`) are identical, taken at `false`. The output-aware run `TensorDoStep.tensorSolveOutput_reaches` threads the outer grid loop (`stepLoopT_reaches`) and then `TensorInstanceJacobian.jacobian_writes_events` on the post-loop heap under the explicit `Resolves`, definition (`SquareDiagonal.function`) and no-overflow (`jacAdds`) premises; `accepted_output_reaches`/`accepted_output_behaviors` add the conjunct `Reads finalHeap (field pool i outputName) (Diagonal.matrix (SquareDiagonal.doubled u))`. `TensorDoStep.Contract shape hasOutput` selects the output execution by `cond hasOutput` over `ExecutionFree`/`ExecutionOutput`; `FMI3.TensorAdapter.Contract` binds `contract shape m.hasOutput`. Post-`fmi3DoStep` output evaluation is a legal Co-Simulation observation: the entry reads the instance's current input region `u`, which the state step leaves unchanged, so the published `J` is `diag(2*u)` at the stepped state. |
| MLS 3.7.2 array-and-record built-ins (`jacobian`) | No admission, grammar, source semantics or provenance change. This increment wires the already-certified square-Jacobian diagonal kernel entry into the emitted Co-Simulation step path for the admitted square kernel `der(x) = u .* u`. No production artifact is emitted and no CLI or grammar case is added. |
| MISRA C:2025 Dir 4.12 (no dynamic memory) and Rule 21.3 (no `malloc`/`calloc`/`free`) | The emitted step allocates nothing new: it calls the prepared kernel entry once with the instance's array-member pointers and the stack-fixed element/cell counts after the counted grid loop. No dynamic allocation and no standard-library memory management appear in the emitted C. |
| FMI 3.0.2, importer/boundary evidence (Co-Simulation) | The development tensor FMU boundary run (`tests/tensor-c.sh`) now reports `fmi3GetFloat64(J) = (2, 0, 0, 4)` in Co-Simulation after three unit `fmi3DoStep` calls with the constant input `u = (1, 2)` (`diag(2*u) = diag(2, 4)`, row-major `(2, 0, 0, 4)`), matching the Model Exchange assertion; the `x = (3, 12)` trajectories in both interfaces are unchanged. The native kernel boundary check and the standalone-object compile stay green. |
| C11 / native boundary | The emitted step body and the second forward prototype are ordinary conforming C; the adapter still compiles cleanly as a standalone object under the strict flags, and `model.c` still compiles cleanly as part of the FMU shared library. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Output-aware tensor derivative getter emitting `rumoca_square_jacobian_diag`: standards impact

| Standard | Impact |
| --- | --- |
| MLS 3.7.2 array-and-record built-ins (`jacobian`) | No admission, grammar, source semantics or provenance change. `jacobian` remains an identified extension, admitted only through complete lowering and an actual-artifact contract, never by example substitution. This increment wires the already-certified square-Jacobian diagonal kernel entry into the emitted Model Exchange derivative getter for the admitted square kernel `der(x) = u .* u`. No production artifact is emitted and no CLI or grammar case is added. |
| FMI 3.0.2, §2.4.7 output variables and §2.4.8 dependencies | The output tensor `J` (value reference 4, declared `J[2,2]` by `TensorMetadata`) is now computed by the emitted adapter in Model Exchange. The tensor adapter preamble declares a second prepared kernel prototype next to `rumoca_rhs` (`TensorStorage.jacobianSignature`/`jacobianPrototype`, always emitted), and the derivative getter is output-aware: when the prepared problem exposes a dense observation (`TensorFMI3Model.hasOutput`), `TensorContinuousStates.derivFunction shape true` emits `rumoca_square_jacobian_diag(&(m->u[0]), &(m->J[0]), nContinuousStates, cells)` after `rumoca_rhs`, with the argument list `TensorContinuousStates.jacobianEntryArgs`. The fused observable-machine execution `TensorContinuousStates.deriv_output_reaches`/`deriv_output_behaviors` composes the derivative entry (`TensorInstanceRhs.derivative_writes_events`) and the Jacobian entry (`TensorInstanceJacobian.jacobian_writes_events`) across the getter, generalizing `deriv_enter` over the saved continuation and adding a `jac_enter` step, and its conclusion adds the conjunct `Reads finalHeap (field pool i outputName) (Diagonal.matrix (SquareDiagonal.doubled u))`. `TensorContinuousStates.DerivContract` is parameterized on the output presence: the output-free case (`hasOutput = false`) is unchanged, and the output case carries the extra Jacobian conjunct. `FMI3.TensorAdapter.Contract` binds the emitted getter (`deriv_contract shape m.hasOutput`) and the second kernel prototype (`jacobianPrototype` fragment plus its arity/parameter-name agreement with `jacobianEntryArgs`). The Co-Simulation `fmi3DoStep` does not yet call the entry, so `fmi3GetFloat64(J)` in a Co-Simulation instance still reads the output region's zero initialization; calling the entry once per accepted step in `TensorDoStep` and extending `TensorDoStep.Contract` with the same conjunct is the remaining wiring item. |
| MISRA C:2025 Dir 4.12 (no dynamic memory) and Rule 21.3 (no `malloc`/`calloc`/`free`) | The emitted getter allocates nothing new: it calls the prepared kernel entry with the instance's array-member pointers and stack-fixed counts, then copies the `der(x)` region into the caller buffer with the existing counted loop bounded by the symbolic element count. No dynamic allocation and no standard-library memory management appear in the emitted C. |
| FMI 3.0.2, importer/boundary evidence (Model Exchange and Co-Simulation) | The development tensor FMU boundary run (`tests/tensor-c.sh`) now reports `fmi3GetFloat64(J) = (2, 0, 0, 4)` in Model Exchange after `fmi3GetContinuousStateDerivatives`, the dense Jacobian `diag(2*u) = diag(2, 4)` in row-major order for `u = (1, 2)`. The native kernel boundary check and the standalone-object compile stay green (the getter now calls the entry; the object-only compile keeps it an undefined extern with an empty `model.c`). Co-Simulation `fmi3GetFloat64(J)` still reads `(0, 0, 0, 0)` because the accepted `fmi3DoStep` does not yet run the entry; the assertion is left at the honest zeros with a comment naming the next-stage step wiring. The `x = (3, 12)` Model Exchange and Co-Simulation trajectories are unchanged. |
| C11 / native boundary | The emitted getter and the second forward prototype are ordinary conforming C; the adapter still compiles cleanly as a standalone object under the strict flags, and `model.c` still compiles cleanly as part of the FMU shared library. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Prepared square-Jacobian kernel entry `rumoca_square_jacobian_diag`: standards impact

| Standard | Impact |
| --- | --- |
| MLS 3.7.2 array-and-record built-ins (`jacobian`) | No admission, grammar, source semantics or provenance change. `jacobian` remains an identified extension, admitted only through complete lowering and an actual-artifact contract, never by example substitution. This increment makes the scratch-free dense-Jacobian materializer a second prepared kernel entry of the certified tensor kernel product for the admitted square kernel `der(x) = u .* u`, alongside the derivative entry `rumoca_rhs`. No production artifact is emitted and no CLI or grammar case is added. |
| FMI 3.0.2, §2.4.7 output variables and §2.4.8 dependencies | The output tensor `J` (value reference 4, declared `J[2,2]` by `TensorMetadata`) is now computed by a certified prepared kernel entry, `rumoca_square_jacobian_diag`, and that entry is part of the emitted kernel product `model.c`. The tensor C emission (`EmitTensor`) renders `Rumoca.CTensor.SquareDiagonal.function` to `build/tensor-c/jacobian-diag.c`; the IVP artifact contract (`TensorCChecks`, `Rumoca.CTensor.ProgramFixture.IVPEntry`) carries the entry's correctness as `JacobianDiagStorageContract`, bundling `SquareDiagonal.helper_call_correct` (the ordinary call writes the dense matrix `diag(2*u)` into the output region), `output_reads` (the region then reads `Diagonal.matrix (doubled u)`) and `output_frame` (every cell outside the region is preserved), universal in the symbolic matrix volume. The development FMU assembly (`tests/tensor-c.sh`) concatenates `jacobian-diag.c` into `model.c` exactly once, after `fill.c`, so the entry is defined once next to `rumoca_rhs`. The observable-machine execution of the entry bound to the static instance record is proved by `FMI3.TensorInstanceJacobian.jacobian_writes_events`, mirroring `TensorInstanceRhs.derivative_writes_events`: `SquareDiagonal.helper_call_correct` (the kernel-call path, which does not consult adapter interface types) embeds into the observable machine through the same transfer lemma `CCalls.Events.loop_call_reaches_events`, its header-type premises supplied by the shared `Library definitions` rather than by an `fmi3Float64 *`/`double *` interface obligation. The entry is not yet emitted or called by the tensor FMI getter or co-simulation step, so `fmi3GetFloat64(J)` still reads the output region's zero initialization; emitting the call and threading the conjunct `Reads finalHeap (field pool i outputName) (Diagonal.matrix (doubled u))` through `TensorContinuousStates.DerivContract`, `TensorDoStep.Contract`, `FMI3.TensorAdapter.Contract` and the tensor lifecycle histories remains the open wiring item. |
| MISRA C:2025 Dir 4.12 (no dynamic memory) and Rule 21.3 (no `malloc`/`calloc`/`free`) | The prepared kernel entry allocates nothing: its body zero-fills the output region with the shared `rumoca_tensor_fill` helper and, in one counted loop bounded by the symbolic element count, stores `u[k] + u[k]` at the diagonal cell using only ordinary size arithmetic (`offset += stride`, `stride = count + 1`). No dynamic allocation and no standard-library memory management appear in the emitted C, consistent with the whole certified kernel product. |
| FMI 3.0.2, importer/boundary evidence | `tests/tensor-c.sh` now compiles and links `rumoca_square_jacobian_diag` in both the native kernel boundary check (asserting `rumoca_square_jacobian_diag((2, 3), out, 2, 4)` writes the dense matrix `(4, 0, 0, 6) = diag(2*u)`) and the development FMU `model.c`. The FMU boundary run still reports `fmi3GetFloat64(J) = (0, 0, 0, 0)` in both interfaces because the adapter does not yet call the entry; the assertion remains the honest documented zeros. The `x = (3, 12)` Model Exchange and Co-Simulation trajectories are unchanged. |
| C11 / native boundary | The entry's C body is ordinary conforming C (a `rumoca_tensor_fill` call and one counted diagonal loop); it compiles and runs under the strict native flags, and `model.c` still compiles cleanly as part of the FMU shared library. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Reusable square-Jacobian output materializer `diag(2*u)`: standards impact

| Standard | Impact |
| --- | --- |
| MLS 3.7.2 array-and-record built-ins (`jacobian`) | No admission, grammar, source semantics or provenance change. `jacobian` remains an identified extension, admitted only through complete lowering and an actual-artifact contract. This increment adds the reusable C helper `rumoca_square_jacobian_diag` (`Rumoca.CTensor.SquareDiagonal`) that materializes the dense Jacobian of the square kernel `der(x) = u .* u`, whose real value is `Matrix.diagonal (fun i => u i + u i)` (`AD.squareJacobian`). The written diagonal is related to the prepared AD program `ArrayProfile.squareJacobianProgram` by `SquareDiagonal.diagonal_nearest`: each stored entry `u[k] + u[k]` is a nearest finite value to `2 * u[k]`, the same nearest property `square_jacobian_coefficients_nearest` proves for the prepared coefficient program; no `2*u` simplification is inserted. No production artifact is emitted and no CLI or grammar case is added. |
| FMI 3.0.2, §2.4.7 output variables and §2.4.8 dependencies | The helper is the scratch-free computing body for the output tensor `J` (value reference 4, declared `J[2,2]` by `TensorMetadata`): it zero-fills the dense output region with the shared `rumoca_tensor_fill` helper and, in one counted loop, stores `u[k] + u[k]` at the diagonal cell `k * (count + 1)` of the row-major matrix. `SquareDiagonal.helper_call_correct` proves the sole terminating behavior writes `Diagonal.resultHeap`, `SquareDiagonal.output_reads` proves the output region then reads the dense diagonal matrix `diag(2*u)` (`Diagonal.matrix`, zero off-diagonal), and `SquareDiagonal.output_frame` proves every cell outside the output region is preserved. These are universal in the symbolic matrix volume; no tensor coordinate is enumerated. The helper is not yet bound to an emitted FMI getter or co-simulation step, so `fmi3GetFloat64(J)` still reads the output region's zero initialization; wiring the helper into `TensorContinuousStates.DerivContract`, `TensorDoStep.Contract` and `FMI3.TensorAdapter.Contract` (emitting the helper, calling it through the existing observable-machine transfer `CCalls.Events.loop_call_reaches_events`, and extending the contract conclusions and lifecycle histories) remains the open item. |
| MISRA C:2025 Dir 4.12 (no dynamic memory) and Rule 21.3 (no `malloc`/`calloc`/`free`) | The materializer allocates nothing: it reads the input tensor `u` and writes the output region in place with a fixed counted loop bounded by the symbolic element count, using only ordinary size arithmetic (`offset += stride`, `stride = count + 1`). No dynamic allocation and no standard-library memory management appear in the emitted C, consistent with the whole tensor adapter. |
| FMI 3.0.2, importer/boundary evidence | Unchanged. `tests/tensor-c.sh` still reports `fmi3GetFloat64(J) = (0, 0, 0, 0)` in both interfaces because the proven helper is not yet emitted or called by the adapter; the boundary assertion remains the honest documented zeros. The `x = (3, 12)` Model Exchange and Co-Simulation trajectories are unchanged. |
| C11 / native boundary | No emitted-adapter change in this increment; the helper's C body (a `rumoca_tensor_fill` call and one counted diagonal loop) is ordinary conforming C, checked in the Lean execution model but not yet part of an emitted artifact. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Kind-aware Co-Simulation exit, tensor instantiation token, and the remaining output item: standards impact

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` (MLS 3.7.2 array-and-record built-ins) remains an identified extension, admitted only through its complete lowering and actual-artifact contract, never by example substitution. No production artifact is emitted and no CLI or grammar case is added. |
| FMI 3.0.2, §2.3 state machine of Co-Simulation | `fmi3ExitInitializationMode` is now kind-aware. `TensorLifecycleModes.Phase.afterKind` writes Event Mode for a Model Exchange instance and Step Mode for a Co-Simulation instance on exiting Initialization Mode, matching the reference `Rumoca.FMI3.nextMode .exitInitialization kind .initialization` and the scalar `InitializationExit` body (the emitted exit body now branches on the record's `kind` cell exactly as the scalar body does). The standalone `TensorLifecycleModes.contract .exitInitialization` and its conjunct in `FMI3.TensorAdapter.Contract` are stated over `writeMode heap p (Phase.afterKind kind)`, so the adapter contract now proves the Co-Simulation Step-Mode exit. `TensorLifecycleHistory.lifecycle_cs_step` threads the Instantiated → Initialization → Step exit into an accepted `fmi3DoStep` (`TensorDoStep.accepted_behaviors`, whose Step-Mode premise `mode = 4` the exit now establishes); the Model Exchange `lifecycle_history` is unchanged. |
| FMI 3.0.2, §2.4.1 instantiation token | The tensor factory validates the tensor model description's declared `instantiationToken`, `lean-rumoca-tensor-v1:TensorSquare` (`TensorMetadata.token`). The shared admission prefix and identity-helper proofs are reused unchanged: `FactoryPrefix.validation`/`body` and the shared `FactoryValidation`/`Identity` admission lemmas are parameterized over the expected token string (defaulting to the scalar `Metadata.token`, so every scalar caller and the scalar production certificate are unaffected), and the tensor factory instantiates them with the tensor token literal. `FMI3.TensorAdapter.Contract` gains a conjunct proving the factory's expected token equals the model description's `instantiationToken` attribute (`TensorMetadata.token_attribute`), mirroring the existing model-identifier agreement, so the emitted adapter accepts precisely the token the model description declares. |
| FMI 3.0.2, §2.4.7 output variables | The output tensor `J` (value reference 4) is still not computed by any emitted adapter body: the prepared diagonal Jacobian kernel `rumoca_square_jacobian` is emitted but wired to no FMI entry, so `fmi3GetFloat64(J)` reads the output region's file-scope zero initialization. Wiring the diagonal kernel into an FMI output (a proved zero-fill of the dense region and a diagonal write from the kernel, universal in the symbolic matrix volume) remains the one open tensor item. The tensor kernel bound to the instance record (`TensorInstanceRhs.kernel`) still carries `diagonal := none`, so completing the output requires undeferring that diagonal observation and adding the computing body with its contract. |
| FMI 3.0.2, importer/boundary evidence (Model Exchange and Co-Simulation) | The development tensor FMU boundary run (`tests/tensor-c.sh`) now instantiates both instance kinds with the model description's token `lean-rumoca-tensor-v1:TensorSquare`. Model Exchange: enter/exit initialization, set `u = (1, 2)`, `fmi3GetContinuousStateDerivatives` returns `der(x) = (1, 4)`, and an importer-driven explicit Euler reaches `x = (3, 12)` at `t = 3`. Co-Simulation: enter/exit initialization reaches Step Mode, and three unit `fmi3DoStep` calls advance `x` by `u .* u` each step to `x = (3, 12)` at `t = 3`. `fmi3GetFloat64(J)` reads `(0, 0, 0, 0)` in both kinds (the open output item). Native compilation, ZIP transport and the FMPy importer are boundaries outside the proof model; the FMU carries no production source-to-archive certificate. |
| C11 / native boundary | The development FMU shared library compiles cleanly under the same strict recipe flags; the emitted exit body's branch on the `kind` cell and the tensor token string literal are ordinary conforming C. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Initialization-entry contract lift and the development tensor FMU boundary run: standards impact

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. No production artifact is emitted, no CLI or grammar case is added, and the scalar adapter, scalar bodies, `Runtime.lean` and every existing contract are unchanged. |
| FMI 3.0.2, Model Exchange interface (`fmi3EnterInitializationMode`) | The standalone `TensorLifecycleModes.contract .enterInitialization` and its conjunct in `FMI3.TensorAdapter.Contract` are now stated over the emitted six-parameter header-signature function `fmi3Status fmi3EnterInitializationMode(fmi3Instance, fmi3Boolean, fmi3Float64, fmi3Float64, fmi3Boolean, fmi3Float64)`. The mode-transition `signature`, `arguments` and `parameters` carry the bound-but-unused tolerance and stop-time parameters (`toleranceDefined`, `tolerance`, `startTime`, `stopTimeDefined`, `stopTime`) that the pinned prototype declares; the body reads only the `instance` handle, so the successful single-mode write, the null-handle rejection and the illegal-mode rejection are quantified over any values of the extra parameters. Every conjunct of the adapter contract for this function is therefore literally about the emitted six-parameter function. The other four mode transitions keep their single-handle prototype. |
| FMI 3.0.2, importer/boundary evidence (Model Exchange and Co-Simulation) | A development tensor FMU for the `TensorSquare` kernel is assembled from the already-checked pieces (the contract-checked adapter as `sources/fmi3.c`, the certified tensor kernel bodies as `sources/model.c`, the checked `TensorMetadata` model description, and a build description mirroring the scalar recipe), compiled to a shared library with the scalar FMU recipe flags, and driven by FMPy in `tests/tensor-c.sh`. Native compilation, ZIP transport and the FMPy importer are boundaries outside the proof model; this is a development artifact and carries no production source-to-archive certificate. Model Exchange: instantiate, enter/exit initialization, set `u = (1, 2)`, and `fmi3GetContinuousStateDerivatives` returns `der(x) = (1, 4)`; an importer-driven explicit Euler over the FMU's derivative reaches `x = (3, 12)` at `t = 3`; `fmi3GetFloat64` of the output `J` reads `(0, 0, 0, 0)`. `fmpy validate` reports no problems. |
| FMI 3.0.2, reported cross-artifact mismatch (identity) | The importer instantiates with the token the adapter validates. The emitted adapter's compiled-in expected instantiation token is the scalar-witness token `lean-rumoca-unit-v1:TensorSquare:x` (the runtime-interface factory bodies of `FMI3.TensorAdapter.Contract` are built over the scalar witness model), while the tensor model description declares `lean-rumoca-tensor-v1:TensorSquare`. The adapter correctly rejects a non-matching token per its proved `FactoryValidation` contract; reconciling the two tokens is an open tensor-adapter identity design item. |
| FMI 3.0.2, reported open item (Co-Simulation Step Mode) | `fmi3DoStep` (Co-Simulation) is currently rejected with `fmi3Error` ("Call is not allowed in the current FMI state"). The tensor `fmi3ExitInitializationMode` writes Event Mode (the proved Model Exchange transition; its own definition states it is "for the Model Exchange profile"), but Co-Simulation `fmi3DoStep` requires Step Mode. The tensor lifecycle table does not yet model the kind-aware Co-Simulation Step-Mode exit transition (unlike the scalar `InitializationExit`, whose body branches on kind). This is a listed open lifecycle-binding item, consistent with the standing "binding these bodies to an emitted FMU wrapper with its lifecycle and numerical policy remain open"; the adapter faithfully emits its proved (Model Exchange) exit behavior, so it is a coverage gap, not a contract violation. The `TensorSquare` output `J` is emitted (`rumoca_square_jacobian`) but wired to no FMI entry, so `J` reads its zero initialization; wiring the diagonal Jacobian into an FMI output is a separate design item. |
| C11 / native boundary | The development FMU shared library compiles cleanly under the scalar recipe flags (`-std=c11 -O2 -Wall -Wextra -Werror -Wno-unused-parameter -pedantic -fno-fast-math -ffp-contract=off -frounding-math -fPIC -shared -DFMI3_OVERRIDE_FUNCTION_PREFIX`); the assembled `model.c` prepends `<stddef.h>` so `size_t` is in scope at the adapter's `#include "model.c"`, and concatenates the certified kernel bodies in dependency order. The FMU and the run/validate logs are retained under `build/tensor-fmi/`. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Header-conforming tensor adapter compiling as a standalone object: standards impact

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. No production artifact is emitted, no CLI or grammar case is added, and the scalar renderer, scalar bodies, `Runtime.lean` and every existing contract are unchanged. |
| FMI 3.0.2, header files and function naming | Every emitted tensor function now carries the pinned FMI prototype for its name. `TensorFunctions.tensorFunction` pairs the dispatched tensor (or scalar) body with the header signature `sig` (`{ tensorDispatch model m sig with signature := sig }`), so the emitted prototype is the one read from the vendored `fmi3Functions.h`/`fmi3FunctionTypes.h` via `FMI3.Header.signatures`. Previously the Model Exchange `fmi3EnterInitializationMode` was emitted under a reduced one-parameter prototype; it is now emitted under the full pinned prototype `fmi3Status fmi3EnterInitializationMode(fmi3Instance, fmi3Boolean, fmi3Float64, fmi3Float64, fmi3Boolean, fmi3Float64)`, with the body reading only the `instance` handle it already read. The vendored header inclusion and the `FMI3_FUNCTION_PREFIX` binary-ABI selection are unchanged. |
| FMI 3.0.2, prototype agreement by section title | `TensorFunctions.functions_signatures` proves the tensor function list's signatures equal the header signature list position by position after the fixed helper prefix, the prototype-level strengthening of `functions_names` (which established only the names). The Model Exchange completed-integrator-step body (`fmi3CompletedIntegratorStep`, §3.2.2) maintains the event-time bookkeeping cells `timeMin`, `eventTime` and `lastCompleted`; these are declared in the tensor instance record (`TensorStorage.bookkeepingMembers`) and reset to `+0` by the reserved-record initializer (`TensorInstanceInit`), mirroring the scalar factory. The body computes over the scalar time cells only, not over any tensor region, and the tensor model exposes no event indicators, so reusing the scalar completed-step, discrete and event bodies is correct. |
| C11 (N1570 §6.7.2 declarations, §6.7.3 qualifiers, §6.9.1 function definitions) | The whole rendered adapter is a well-formed C11 translation unit. Each emitted definition matches the header declaration's type exactly, so no conflicting-type diagnostic arises. Parameters a body ignores are declared but unused, which is conforming (an unused parameter is not a constraint violation). The `fmi3SetContinuousStates` copy local now carries the source qualifier, `const fmi3Float64 * values = continuousStates;`, so no qualifier is discarded across the initialization; the getter and derivative copy locals keep the unqualified `fmi3Float64 *` matching their writable buffers. |
| C11 / native boundary | `tests/tensor-c.sh` (the `tensor-c-test` target) now requires a clean object compile of `build/tensor-fmi/adapter.c` with zero diagnostics under the strict flags (`-std=c11 -O2 -Wall -Wextra -Werror -pedantic -fno-fast-math -ffp-contract=off -Wno-unused-parameter`), failing on any compiler error, any warning promoted by `-Werror`, or any residual compiler output, rather than only on the `incompatible pointer type` pattern. Native compilation, header preprocessing and hardware remain boundaries outside the authored C semantics. |
| MISRA C:2025 Rule 8.x (declarations) | Each emitted adapter function keeps exactly one external definition whose prototype matches the pinned header declaration in the included translation unit, so the visible header prototype and the definition are compatible (Rule 8.2, prototype form; Rule 8.3, one consistent declaration; Rule 8.4, a compatible declaration is visible; Rule 8.6, one definition per external identifier). The added record members `timeMin`, `eventTime` and `lastCompleted` are single struct-member declarations of `double`, used by the completed-step body and initialized by the factory. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The change adds three inline `double` members to the statically allocated instance record and initializes them by direct assignment; it introduces no storage and no allocator (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`; Dir 4.12, no dynamic memory). The continuous-state copy loops and the initializer state-fill loop keep abstract bounds against the symbolic shape volume; no tensor coordinate is enumerated. |
| MISRA C:2025 Rule 11.8 (const qualification) | Qualifying the setter copy local as `const fmi3Float64 *` removes the implicit cast that discarded the `const` from the `const fmi3Float64 continuousStates[]` parameter's pointed-to type (Rule 11.8, a cast shall not remove a `const` qualifier). No other pointer conversions are introduced. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Conforming array-member region pointers in the tensor adapter: standards impact

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. No production artifact is emitted, no CLI or grammar case is added, and the scalar adapter, scalar bodies and every existing contract are unchanged. |
| FMI 3.0.2, header files and function naming | The tensor bodies stage the pointer to an array member's first element, `&(m->name[0])`, in place of the scalar `&(m->name)` idiom, for the array-typed record members (`x`, `u`, `dx`, `J`). The vendored header inclusion, the `FMI3_FUNCTION_PREFIX` binary-ABI selection and the public function names read from the pinned `fmi3Functions.h`/`fmi3FunctionTypes.h` prototypes are unchanged. The kernel prototype `void rumoca_rhs(const double *, const double *, double *, size_t)` and the `fmi3Float64 *` copy locals now receive a `double *` (`&(m->name[0])`) rather than a pointer-to-array, so the tensor derivative call `rumoca_rhs(&(m->x[0]), &(m->u[0]), &(m->dx[0]), n)` and the region copy loops pass arguments of the declared pointer-to-element type. The scalar rank-0 `time` member (`double time;`) keeps the exact `&(m->time)` idiom. |
| C11 array-to-pointer conversion (N1570 §6.3.2.1, §6.5.2.1, §6.5.3.2) | For an array member `double name[N]`, `&(m->name)` has type `double (*)[N]` and is not compatible with `double *`; `&(m->name[0])` applies subscripting (`E1[E2]` = `*(E1 + E2)`) to the array lvalue `m->name`, which undergoes array-to-pointer conversion to `&name[0]`, and takes the address of element `0`, yielding `double *`. Both denote the same storage; only the static type differs. The authored object-memory model in `packages/backend-c` now models this conversion: a subscript takes its base from the operand's address when the operand is an lvalue (a field, subscript or dereference) and otherwise from its stored pointer value, so `m->x[i]` denotes the member's `i`th element cell while a pointer variable `p[i]` still follows the stored pointer. `Runtime.eval_region` proves `&(m->name[0])` denotes `m.member name` (index `0`, `Address.index_zero`), the same address the earlier idiom denoted, so region reads and writes are unchanged. |
| MISRA C:2025 Rule 11.x (pointer conversions) | The change removes an implicit conversion between incompatible pointer types. The earlier initialization/assignment `fmi3Float64 * dst = &(m->x);` converted a `double (*)[N]` to a `double *`, a conversion between pointers to incompatible object types not permitted without an explicit cast (Rule 11.3), and passed such a pointer as a `const double *`/`double *` argument to `rumoca_rhs` (Rule 11.3 at the call). Staging `&(m->name[0])` supplies a `double *` directly, so no cast and no incompatible-pointer conversion occurs; the pointed-to type matches the parameter and local type exactly. No integer/pointer conversions (Rule 11.4/11.6), no removal of `const` (Rule 11.8) and no function-pointer conversions are introduced. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The change alters only the staged pointer expression to an existing statically allocated inline array member; it introduces no storage and no allocator. The region pointers still address the static instance record's inline `double[N]`/`double[N*N]` members; no body allocates (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`; Dir 4.12, no dynamic memory). Loop bounds stay abstract against the symbolic shape volume. |
| C11 / native boundary | `tests/tensor-c.sh` compiles the rendered `build/tensor-fmi/adapter.c` with the verification shell's C11 compiler against the vendored FMI 3 headers (object only) and asserts no `incompatible pointer type` diagnostic: it fails on the array-member idiom before this increment and passes after. Native compilation is a boundary outside the proof model. A full standalone object of this development adapter is not asserted, because its scalar-fallback event/discrete bodies reference scalar-only record members and its reduced lifecycle/query signatures differ from the pinned FMI prototypes, both separate from this array-member pointer-type contract. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Tensor adapter helper set and full-list rendered adapter: standards impact

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. No production artifact is emitted, no CLI or grammar case is added, and the scalar renderer, `Runtime.lean` and every existing contract are unchanged. |
| FMI 3.0.2, header files and function naming | The tensor renderer's declaration preamble and helper set now carry only what the tensor bodies reference. The scalar numerical `Model` record (`typedef struct { double x; } Model;`) is dropped from `TensorStorage.storageRender`, and the scalar wrapper helpers `model_rhs` and `model_advance` are dropped from the helper prefix (`TensorFunctions.helpers` is now `[fail, rumoca_valid_identity, rumoca_reserve_slot]`), because the three scalar bodies that called them (`fmi3GetFloat64`, `fmi3DoStep`, `fmi3GetContinuousStateDerivatives`) are all dispatched to tensor bodies, which call the prepared tensor derivative entry `rumoca_rhs` directly. The official `fmi3Functions.h` inclusion and the `FMI3_FUNCTION_PREFIX` binary-ABI selection are unchanged (`TensorStorage.declarations_header`). The public function names are still those read from the official `fmi3Functions.h`/`fmi3FunctionTypes.h` prototypes: the tensor name list is a sublist of the scalar list (`helper_names_sublist`, `functions_names`, `scalar_names`), so distinctness (`functions_nodup`), the definition table (`function_bound`, `helpers_bound`) and the literal pool follow the scalar development. The native regression executable renders the complete adapter for the full pinned header signature list obtained from the vendored `fmi3FunctionTypes.h` via `FMI3.Header.signatures` (75 signatures), one function per reused helper and per pinned signature, and retains the full bytes for review. |
| FMI 3.0.2, prepared kernel declaration by section title | The preamble now forward-declares the prepared tensor derivative kernel entry the bodies call directly: `TensorStorage.kernelPrototype` renders `void rumoca_rhs(const double * x, const double * u, double * dx, size_t count);`. Its parameter roles come from the tensor plan's derivative function (`const double *` for the read state/input regions, `double *` for the written derivative region, `size_t` for the element count), so the direct calls in the tensor bodies match the definition in the included private kernel `model.c` (§2.2.3, the model-exchange/co-simulation C interface prototypes; the private numerical kernel is compiled together with the adapter). `TensorAdapter.Contract` carries the call-resolution facts: `TensorFunctions.kernel_entry_is_kernel` proves `rumoca_rhs` resolves in the definition table to the prepared RHS kernel (given the header names are disjoint from it, which the pinned list satisfies), `kernel_entry_resolves` proves it is never unresolved, and `kernel_prototype_matches_args` proves the prototype agrees in arity and parameter roles with the arguments the derivative bodies pass (`TensorContinuousStates.derivEntryArgs`). Every function name a tensor body calls by identifier is a defined helper (`fail`, `rumoca_valid_identity`, `rumoca_reserve_slot`, via `helpers_bound`), a defined adapter function (`function_bound`), a C standard header function (`isfinite`, `floor`, `fegetround`, `atomic_exchange`, `atomic_store`, `strlen`, `strspn`, `strcmp`), or this prepared kernel entry. |
| C11 / printer conformance | `TensorStorage.storage_printed` proves the storage section (now without the scalar `Model` record) scans into a concrete token sequence under the shared maximal-munch scanner. `TensorAdapterPrinter.rendered_contract` proves the whole function section following the fixed preamble tokenizes maximally as the tensor function list, universally in the signature list, so it applies to the complete pinned header list; the pure package fixture proves it and the preamble tokenization over a representative dispatched slice, and the native executable renders and retains the full-list adapter bytes. |
| MISRA C:2025 Rule 8.x (declarations) | Dropping the scalar `Model` record removes an unused type definition, and dropping `model_rhs`/`model_advance` removes two `static` functions with no remaining callers in the tensor adapter (Rule 8.4/8.5, no declaration without a corresponding use for the tensor translation unit). The added `rumoca_rhs` prototype is a single file-scope function declaration whose types are the tensor plan's parameter roles, providing a visible prototype before the calls and matching the private-kernel definition (Rule 8.2, function types in prototype form; Rule 8.4, a compatible declaration is visible before the function is called). Each remaining helper and dispatched function keeps exactly one definition and a distinct public name (Rule 8.6). |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The change removes declarations and adds one forward declaration; it introduces no storage and no allocator. The tensor bodies call the prepared kernel by pointer to the statically allocated instance regions; no body allocates (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`; Dir 4.12, no dynamic memory). Loop bounds stay abstract against the symbolic shape volume. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Tensor adapter declaration preamble and the rendered adapter check: standards impact

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. No production artifact is emitted, no CLI or grammar case is added, and the scalar renderer, `Runtime.lean` and every existing contract are unchanged. |
| FMI 3.0.2, header files and function naming | The tensor renderer's declaration preamble now carries the tensor instance record layout the tensor bodies address, in place of the scalar instance record. `TensorStorage.declarations` is the shared header-inclusion block (`Runtime.declarationPrefix`: the official `fmi3Functions.h` include and the C standard headers, reused verbatim) followed by the tensor storage section. `TensorStorage.declarations_header` records that the preamble begins with exactly the scalar header-inclusion block, so the official-header inclusion and the `FMI3_FUNCTION_PREFIX` binary-ABI selection are unchanged. The adapter's function prefix names the same model identifier the tensor model description decodes to: `TensorAdapter.Contract` carries `decodeModelIdentifiers (TensorMetadata.modelDescription m) = some (m.name, modelIdentifier m.name, modelIdentifier m.name)` (`TensorMetadata.modelIdentifiers_decode`) alongside the adapter-prefix witness, so the Model Exchange and Co-Simulation `modelIdentifier` attributes and the source prefix agree. `TensorAdapterPrinter.rendered_contract` proves the whole function section following the fixed preamble tokenizes maximally under the shared C scanner as the tensor function list (`FunctionsTokenization`), the tensor analog of the scalar adapter's function-section grammar, using each dispatched tensor body's printability, the shared helper printability and `factory_printable` for the tensor reserved-record initializer. |
| FMI 3.0.2, platform-dependent definitions by section title | The tensor instance record (§2.4.2, platform-dependent definitions; the record realized behind the `fmi3Instance` handle) declares the FMI-visible tensors of a prepared `TensorFMI3Model`: the independent time base as a single `double`, the state `x`, input `u` and derivative `dx` as contiguous `double[N]` regions of the symbolic state element count `N`, and, when the prepared problem exposes a dense observation, the Jacobian `J` as a `double[N*N]` region, followed by the FMI lifecycle, host and slot bookkeeping fields the tensor bodies read (`kind`, `mode`, `stop`, `stopDefined`, `logging`, `environment`, `logger`, `slot`). `TensorStorage.layout_names` proves the declared region member names are exactly the ones `TensorInstance` addresses (`time`, `x`, `u`, `dx`, `J`); `layout_state_extent` and `layout_output_extent` prove the declared array extents equal the addressed region counts (`shape.volume` for the state-sized regions, `(matrixShape N N).volume = N*N` for the square matrix). The permanent instance pool array, its always-lock-free `atomic_bool` flag array (§2.4.4, thread-safety of the always-lock-free static assertion is retained from the shared `Runtime.declarationPrefix`) and the deployment capacity constant are shared verbatim with the scalar storage; only the record body differs. All extents stay symbolic in the shape; no tensor coordinate is enumerated. |
| C11 / printer conformance | `TensorStorage.storage_printed` proves the complete rendered storage section scans, under the shared maximal-munch scanner (`CTokens.Prefix`), into a concrete token sequence: the shared model record and permanent pool/flag/count declarations reuse the shared record/array/constant render proofs verbatim, and the tensor instance record uses `record_printed`, whose per-member tokenization extends the shared field grammar with the array-declarator tokens `[ number ]` for each region, the symbolic extent rendered as one decimal number token through the shared decimal renderer. The rendered `TensorSquare` adapter is checked concretely: `Tests.TensorAdapterFixture.fixture_function_section` applies the function-section grammar to the actual rendered bytes, `fixture_preamble_tokenizes` applies the storage tokenization, and `fixture_preamble_layout`/`fixture_identifier` the record-layout and identifier agreements. |
| MISRA C:2025 Rule 8.x (declarations) | The tensor storage section is a single translation-unit-scope set of declarations: one `typedef struct { … } Instance;` record type, the permanent `static` pool array of that record type, the `static` always-lock-free flag array and one `static const` capacity constant. Each object has exactly one definition, each member one declarator, and every declared type name is a known primitive or a preceding typedef in the shared vocabulary (Rule 8.2, function-style declarations; Rule 8.4/8.5, single visible declaration; Rule 8.6, single definition). The record members are inline array members of a completed struct type; no member is a pointer to separately allocated storage. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The tensor instance record and its permanent pool form no dynamic storage and run no allocator. Every tensor region is an inline `double[N]`/`double[N*N]` member of the statically allocated instance record; the pool is one `static` array of the deployment capacity; no member is heap-backed and nothing in the preamble allocates (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`; Dir 4.12, no dynamic memory). The region extents stay abstract against the symbolic shape volume. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Tensor FMI 3 adapter function list and the two family contracts: standards impact

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. No production artifact is emitted, no CLI or grammar case is added, and the scalar renderer, the families and every existing contract are unchanged. |
| FMI 3.0.2, header files and function naming | New derived products only. `FMI3.TensorFunctions.functions` maps each pinned-header signature (the names read from the official `fmi3Functions.h`/`fmi3FunctionTypes.h` prototypes) either to its proved tensor behavioral body, dispatched by the exact public function name, or, for the seven model-independent behavioral functions and the 49 unsupported/absent-type functions, to the same body the scalar renderer emits. `tensorFunction_name` proves each dispatched function keeps its header name; `functions_names` proves the name multiset equals the scalar adapter list's, so `functions_nodup` (pairwise-distinct public names), `rendered_member` (each signature rendered once at its header-order slot) and the definition table and literal pool (`function_bound`, `helpers_bound`, `text_bound`) follow the scalar development, universally in the tensor shape and the model name. |
| FMI 3.0.2, unsupported capabilities and absent types by section title | The two model-agnostic families are proved over the tensor list. `TensorAbsentVariables.family_correct` covers the 24 typed getters/setters for the variable types with no declared variables (Float32, Int8/UInt8, Int16/UInt16, Int32/UInt32, Int64/UInt64, Boolean, String, Binary): a request with both cardinalities zero returns `fmi3OK`, any non-empty request returns `fmi3Error` through the shared diagnostic, and a null handle returns `fmi3Error`. `TensorCapabilityRejection.family_correct` covers the 25 unsupported public functions by their §-titled features: Clock activation and interval/shift interfaces (§2.3 clocks), FMU state get/set/free and serialization (§2.4.7 getting and setting state), directional and adjoint derivatives (§2.4.8), variable-dependency queries (§2.4.9), configuration and step modes, and output derivatives; each returns `fmi3Error` (quiet or through the logger callback) writing the terminated mode and forms no state. `fmi3InstantiateScheduledExecution` (§4, Scheduled Execution unsupported) is the companion rejection returning `NULL`. The family execution bodies are identical to the scalar renderer's; only the surrounding function list and its literal pool differ, and the model-agnostic execution core is reused verbatim, so no family execution proof is duplicated. Model-free public-API coverage (`PublicAPI.Covered`) still accounts for every listed signature. |
| C11 / printer conformance | The rendered adapter text is the fixed preamble (model prefix, `model.c` include and the shared declaration block) followed by the concatenated helper and dispatched-function renderings in header order (`TensorFunctions.render`, `rendered_functions`). `TensorAdapter.render_contract` binds that text to the coverage witness, the two family contracts and every proved tensor behavioral function contract with its own printed-text denotation under the shared C printer. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The adapter list, its located positions and the two families form no storage and run no allocator. Every family body is a fixed sequence of guard, comparison and fixed-cell writes with a shared diagnostic call; no body allocates, and the reused helper prefix and declaration preamble are those of the verified scalar adapter (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`; Dir 4.12, no dynamic memory). The tensor behavioral bodies keep every loop bound abstract against the symbolic shape volume. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Tensor Co-Simulation `fmi3DoStep` accepted execution, rejections and contract: standards impact

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| FMI 3.0.2 §4.2.1, `fmi3DoStep` (Co-Simulation) | New derived product completing the accepted-case execution and the bundled contract. `TensorDoStep.front_run` runs the model-independent scalar guard prefix (handle/lifecycle guard, output-pointer check and zero/last writes, invalid communication-point/step rejection) as a `CBody.run 9` over the tensor instance heap; `TensorDoStep.tensorSolve_reaches` runs the model-dependent numerical tail as one observable-machine execution (the function-scope declarations, the outer grid loop `loop "n" steps stepBodyT` through `stepLoopT_reaches`, the `lastSuccessfulTime` publication and the `fmi3OK` return). `TensorDoStep.accepted_reaches`/`accepted_behaviors` compose them with the reused `StepGuards.rounding_path`/`clock_path`/`grid_path` guard sections into one silent prefix from the entry call to the `fmi3OK` return and read off its sole terminating behavior: the state region reaches the `N`-fold finite Euler iterate for the admitted step count (`StepAdmission.duration_count`), the instance time cell and the caller's `lastSuccessfulTime` read the advanced time base, the caller output pointers are written as the scalar body writes them, and every cell of every other instance is preserved. `TensorDoStep.null_behaviors` and `lifecycle_behaviors` reuse the shared `GuardedCalls` rejection lemmas (null handle returns `fmi3Error` unchanged; a disallowed FMI state returns `fmi3Error` writing the terminated mode). `TensorDoStep.signature_printable`/`body_printable`/`function_denotes` give the printed-text denotation of the whole guarded body, and `TensorDoStep.contract` bundles printed text, closedness, denotation, the null rejection and the accepted execution as the tensor-native contract. The accepted-case premises are stated exactly as `StepGuards`/`StepAdmission` expose them for the scalar body. Open: the `fmi3Discard` off-grid/over-bound whole-call behavior (the guard prefix reaches the shared `Runtime.stepDiscard` block, but the discard logging-callback composition `StepDiscard` over the tensor record is not composed); and instantiation of the accepted/discard executions, which carry the reused `stepRounding` guard's C floating-environment premises (`fegetround` external, `FE_TONEAREST` constant). The tensor `cInterface` populates `fmi3OK` but not `FE_TONEAREST`, which the scalar `fmi3DoStep` obtains from the header-aware `RuntimeEnvironment.interface`; re-basing the tensor numerical lemmas on that interface is a separate step. |
| FMI 3.0.2 §4.2.1, communication step policy | Unchanged from the verified scalar `fmi3DoStep`. The accepted execution reuses the model-independent guard prefix verbatim over the tensor instance record's metadata cells (`kind`, `mode`, `stopDefined`, `stop`) and its scalar time base (the `p.member "time"` cell those guards read), deriving the admitted internal step count from the communication step by `StepAdmission.duration_count` and running the tensor grid loop that many times. Only the numerical tail differs from the scalar body. |
| C11 / printer conformance | The whole guarded body denotes its function under the shared C printer: `TensorDoStep.body_printable` proves every statement (the guard prefix, the hoisted declarations, the `size_t`-cast step count, the outer counted loop, the per-step derivative call and elementwise update, the `lastSuccessfulTime` deref-store and the `fmi3OK` return) is `ItemPrintable`, and `function_denotes` yields the printed-text denotation via the shared `CTree.Printer.function_denotes`. The body stays a closed block (`doStepBody_closed`). |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The accepted execution and the rejections form no storage and run no allocator. The guard prefix and the rejections write only fixed instance and caller-output cells; the numerical tail declares a fixed set of pointer and `size_t` locals once at function scope, and each internal step writes only the instance's fixed `der(x)`, `x` and `time` cells through counted `size_t` loops bounded by the symbolic state volume, with the outer loop a counted `size_t` loop over the admitted step count. No dynamic allocation, byte arena or allocator run is introduced (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`; Dir 4.12, no dynamic memory). The `2 ^ 64` size and step bounds stay abstract against the symbolic shape volume. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Tensor Co-Simulation `fmi3DoStep` time advance and guarded body: standards impact

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| FMI 3.0.2 §4.2.1, `fmi3DoStep` (Co-Simulation) | New derived product. The per-internal-step body now advances the instance's independent time base as well as the state: `TensorDoStep.timeStep` performs `m->time = m->time + 1.0` on the scalar time cell, keeping the finite addition explicit as a `Binary64.Adds t 1 (.finite t')` premise (the shared C one renderer `CAlgorithm.literal .one`); `TensorDoStep.stepBodyT` prepends it to the state step and stays declaration-free (`stepBodyT_closed`, `stepBodyT_noDecl`). `TensorDoStep.internalStepPureT_reaches` runs it as one observable-machine execution and `TensorDoStep.stepLoopT_reaches` iterates it `N` times in the outer grid loop `loop "n" steps stepBodyT`: the state region reads the `N`-fold finite Euler step `eulerIterate initial sums N`, the derivative region reads the last result, the input region and every cell of every other instance are preserved, the state and derivative regions stay readable/writable, and the time base reads the `N`-fold finite time sum `times N`. The complete guarded function body `TensorDoStep.doStepBody` is authored: the model-independent scalar guard prefix of `Runtime.doStep` (through `stepGrid`) followed by the hoisted state/derivative pointers, element count, step count and loop counters and the outer grid loop, with `lastSuccessfulTime` set to the advanced time base and an `fmi3OK` return. Open: the accepted-case execution wiring the reused guards, the `fmi3Discard` off-grid/over-bound path and the null/lifecycle rejections ahead of the tensor grid loop, and the bundled function contract in the shape of `StepCalls`/`StepContract.FunctionContract`. |
| FMI 3.0.2 §4.2.1, communication step policy | Unchanged from the verified scalar `fmi3DoStep`. The authored body reuses the model-independent `Runtime` guard prefix verbatim (handle/lifecycle guard, output-pointer check and writes, invalid communication-point/step rejection, `stepRounding`, `stepClock`, `stepGrid`); the tensor instance record carries the scalar metadata cells (`kind`, `mode`, `stopDefined`, `stop`) and its scalar time base coincides with the `p.member "time"` cell those guards read, so the checks apply unchanged. A communication step that is off the unit grid or over the bound reaches `fmi3Discard` without advancing (`Runtime.stepDiscard`). Only the numerical tail is model dependent: it replaces the scalar `model_advance` call with the tensor grid loop above. The accepted-case execution of this prefix over the tensor record remains open. |
| FMI 3.0.2 §4.2.1, time advance | The Co-Simulation communication step advances model time from `currentCommunicationPoint` by `communicationStepSize`. On the unit internal grid the tensor step realizes this incrementally: each internal step advances the time base by one unit, so after the `N` admitted internal steps the time base reads `times N` (the initial time plus `N` under the explicit finite-addition premises `timeAdds`), and `lastSuccessfulTime` publishes that advanced time. The single time cell coincides with the volume-one tensor time member (`Address.index_zero`), consistent with the tensor `fmi3SetTime`. |
| C11 / printer conformance | The guarded body is authored and certified a closed block: `TensorDoStep.doStepBody_closed` proves every statement is a legal closed block (`CBodyEmbedding.closedBlocks`), with the outer counted loop's body declaration-free (`outerLoop_closed`, reusing `stepBodyT_noDecl`), so the pointers, counts and both loop counters declared once at function scope leave no nested declaration. `doStepBody_prefix` records that the guard prefix is exactly `Runtime.doStep.take 16`. No new production emission is added; the emitted `fmi3DoStep` bytes, their tokenization and the accepted-case denotation remain the open items. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The time advance and the guarded body form no storage and run no allocator. The time base is a single fixed `double` cell advanced in place; each internal step writes only the instance's fixed `der(x)`, `x` and `time` cells through counted `size_t` loops (or the single time assignment) bounded by the symbolic state volume; the outer loop is a counted `size_t` loop over the step count; the hoisted staging is a fixed set of pointer and `size_t` locals in the one function block. No dynamic allocation, byte arena or allocator run is introduced (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`; Dir 4.12, no dynamic memory). The `2 ^ 64` size and step bounds stay abstract against the symbolic shape volume. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Tensor Co-Simulation `fmi3DoStep` writable-output contract and N-step grid loop: standards impact

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| FMI 3.0.2 §4.2.1, `fmi3DoStep` (Co-Simulation) | New derived product completing the accepted-case internal-step iteration. The shared prepared tensor-program execution contract `CTensor.Lowering.CallCorrect` is strengthened, additively, to conclude that the emitted program's output region stays writable in the returned heap (`Writable heap (locations (emit p plan layout).result) shape.volume → Writable finalHeap ...`), proved from the dense-store memory lemmas `written_writable` and `written_preserves_writable`; it is threaded through `emit_correct`/`emit_refines`, `program_call_reaches`/`program_call_refines`, `TypedCallCorrect`, `TensorModelRhs.behaviors`/`events_reaches`, `TensorInstanceRhs.derivative_writes`/`derivative_writes_events` and `TensorDoStep.derivative_run`, which now expose that the `der(x)` region is writable after the derivative write. On that fact, `TensorDoStep.stepLoop_reaches` proves the outer grid loop of `N` internal steps (`loop "n" steps stepBody`) by induction on the step count: the state region reads the `N`-fold finite Euler step `eulerIterate initial sums N`, the derivative region reads the last result, the input region and every cell of every other instance are preserved, and the state and derivative regions remain readable and writable. No existing conclusion is weakened and every prior user recompiles. |
| FMI 3.0.2 §4.2.1, communication step policy | Unchanged from the verified scalar `fmi3DoStep`. The reused model-independent `Runtime` guards (`StepCases`, `StepAdmission.AdmittedDuration`, `StepGuards`) still classify the arguments, require round-to-nearest arithmetic, enforce the inclusive stop bound, and discard a communication step that is not a positive integer multiple of the unit step or exceeds the scalar bound. This increment proves only the accepted-case internal-step loop; wiring the guards, the `fmi3Discard` off-grid/over-bound case and the null and lifecycle rejections ahead of the tensor grid loop, and the bundled function contract, remain open, as does the independent per-internal-step time advance folded into the step body. |
| C11 / printer conformance | No new production emission. The loop reuses the declaration-free `TensorDoStep.stepBody` (`stepBody_closed`, `stepBody_noDecl`), so the outer counted loop remains a legal loop body over the one shared function block; the emitted `fmi3DoStep` bytes and their tokenization remain open. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The strengthened contract and the grid loop form no storage and run no allocator. Each internal step writes only the instance's fixed `der(x)` and `x` cells through counted `size_t` loops bounded by the symbolic state volume; the outer loop is a counted `size_t` loop over the step count. No dynamic allocation, byte arena or allocator run is introduced (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`; Dir 4.12, no dynamic memory). The `2 ^ 64` size and step bounds stay abstract against the symbolic shape volume. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Tensor Co-Simulation `fmi3DoStep` declaration-free step body: standards impact

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| FMI 3.0.2 §4.2.1, `fmi3DoStep` (Co-Simulation) | New derived product, declaration-free internal-step body over an arbitrary well-formed instance heap. The prepared tensor derivative transfer is restated over any heap whose state and input regions read the supplied values and whose derivative region is writable (`TensorDoStep.derivative_run`): running `rumoca_rhs` writes the finite tensor derivative into `der(x)` and preserves every cell outside it, including the state, input and time regions and every other instance. `TensorDoStep.stepBody` is the per-internal-step body (evaluate the derivative entry, reset the inner Euler counter, run the elementwise `x[k] = x[k] + dx[k]` update over the symbolic state volume); `TensorDoStep.internalStepPure_reaches` runs it as one observable-machine execution reaching a heap whose state region reads the elementwise finite Euler sum `state + result`. Open for this increment: the full `fmi3DoStep` function body wrapping the handle/lifecycle guards, the communication-step grid policy (§4.2.1: the step must be a positive integer multiple of the unit internal step and at most the scalar bound, else `fmi3Discard` without advancing), the null and lifecycle rejections, the independent time advance, and the accepted step for an arbitrary number of internal steps. The multi-step accepted-case iteration is blocked because chaining internal steps requires the `der(x)` region to remain writable after each derivative write, which the shared tensor-program execution contract (`CTensor.Lowering.CallCorrect`) does not expose; recovering it is a `backend-c` / `RumocaCore` strengthening, not a `backend-fmi3` change. See dev/tensor-ad.md. |
| FMI 3.0.2 §4.2.1, communication step policy | The grid policy itself is unchanged from the verified scalar `fmi3DoStep`: the reused model-independent `Runtime` guards classify the arguments, require round-to-nearest arithmetic, enforce the inclusive stop bound, and discard a communication step that is not a positive integer multiple of the unit step or exceeds the scalar bound (`StepCases`, `StepAdmission.AdmittedDuration`, `StepGuards`). The tensor increment does not alter these guards or the discard condition; it only replaces the scalar unit-Euler solve with the per-internal-step tensor body above. Wiring these guards ahead of the tensor grid loop is deferred with the open items. |
| C11 / printer conformance | `TensorDoStep.stepBody_closed` and `TensorDoStep.stepBody_noDecl` certify the per-internal-step body introduces no declarations, so it is a legal loop body and `CBodyEmbedding.closedBlocks` holds function-wide once the pointers to `x` and `dx`, the element count and both loop counters are declared in the one shared function block. No new production emission is added; the emitted `fmi3DoStep` bytes and their tokenization remain the open items. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The step body forms no storage and runs no allocator. The derivative entry writes only the instance's fixed `der(x)` cells; the Euler update advances the state region in place through a counted `size_t` loop bounded by the symbolic volume; the staging is a fixed set of pointer and `size_t` locals in the function block. No dynamic allocation, byte arena or allocator run is introduced (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`; Dir 4.12, no dynamic memory). The `2 ^ 64` size bound stays abstract against the symbolic shape volume. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

### Tensor behavioral bodies and the Co-Simulation step kernel: standards impact

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| FMI 3.0.2 §5.2.2, header files and naming of functions; common functions | New derived products only. For the seven model-independent behavioral functions (`fmi3GetVersion`, `fmi3SetDebugLogging`, `fmi3InstantiateScheduledExecution`, `fmi3EvaluateDiscreteStates`, `fmi3UpdateDiscreteStates`, `fmi3CompletedIntegratorStep`, `fmi3GetEventIndicators`) the emitted function does not depend on the prepared model: `Runtime.function m signature` is constant in `m` (`Tensor<Name>.independent`, definitionally `rfl`). The tensor slice therefore reuses the scalar bodies and their contracts verbatim over the tensor instance record, whose metadata cells (`kind`, `mode`, `logging`, `environment`, `logger`) supply the scalar execution premises. Each tensor contract carries the emitted text, block closedness, C denotation and the scalar execution behaviors (`Tensor<Name>.contract`). |
| FMI 3.0.2 §2.2.4, getting and setting the version; §2.3.1, logging and debug categories | New derived products only. `fmi3GetVersion` returns a pointer to the pinned `"3.0"` literal, heap unchanged (`TensorVersion.contract.successful`). `fmi3SetDebugLogging` is the model-free constant `DebugLogging.function`; its legal request updates only the instance logging flag, an illegal request is rejected quietly or through the logger callback, and a null handle returns `fmi3Error` (`TensorDebugLogging.contract`, reusing the scalar runtime null/suppressed/logged behaviors). `fmi3InstantiateScheduledExecution` is the fixed rejection returning `NULL`, optionally logging `"Scheduled Execution is unsupported"` (`TensorScheduledCreation.contract`); no Scheduled Execution instance is created. |
| FMI 3.0.2 §3.2.3 and §2.3, Model Exchange event handling | New derived products only. `fmi3EvaluateDiscreteStates` returns `fmi3OK` leaving the heap unchanged for the event-free unit product (`TensorDiscreteEvaluation.contract`). `fmi3UpdateDiscreteStates` writes the fixed `0`/false discrete-update results into the caller's output pointers and returns `fmi3OK` (`TensorDiscreteUpdate.contract`). `fmi3CompletedIntegratorStep` writes the two result flags and the completed-time history and returns `fmi3OK` (`TensorCompletedStep.contract`). `fmi3GetEventIndicators` accepts a valid empty query (the unit product exposes no event indicators) returning `fmi3OK` with the heap unchanged (`TensorEventIndicators.contract`). Each rejects a null handle with `fmi3Error` changing nothing, and each handle/lifecycle premise is a read of the tensor instance record's own `kind`/`mode` cells. |
| FMI 3.0.2 §4.2.1, `fmi3DoStep` (Co-Simulation) | New derived product, internal-step kernel only. The tensor Co-Simulation step mirrors the scalar unit-Euler policy: each internal step evaluates the prepared tensor derivative entry `rumoca_rhs` into the instance `der(x)` region (`TensorInstanceRhs.derivative_writes_events`) and advances the state `x` by `x + dx` elementwise with a counted `size_t` loop over the symbolic state volume (`TensorDoStep.eulerBody`, `euler_reaches`), then delivers the updated state region over the one instance record after the derivative write (`euler_delivers`). Each cell addition keeps its finite-arithmetic outcome explicit as an `Adds` premise, mirroring the derivative getter's explicit `Finite.Executes` premise, and the loop bound is the symbolic state volume, so no tensor coordinate is enumerated. One internal step is proved end to end as one observable-machine execution (`TensorDoStep.internalStep_reaches`): it enters `rumoca_rhs`, applies the transfer lemma to write `der(x) = result` and preserve every other instance, resumes into the staged Euler tail (`euler_delivers`), and advances the state region to the elementwise Euler sum. Open for this increment: the full `fmi3DoStep` function body wrapping the guards, the grid-policy discard for a non-integer or oversized communication step, the null and lifecycle rejections, the independent time advance, and the arbitrary-internal-step iteration; see dev/tensor-ad.md. |
| C11 / printer conformance | Each of the seven behavioral bodies prints its intended C token grammar and denotes its rendered bytes (`Tensor<Name>.contract.denotes`, reusing the scalar tokenization), and its block closedness is checked (`contract.closed`). The Euler loop body's block closedness is checked (`TensorDoStep.eulerBody_closed`). These increments add package-checked semantics, not a new production emission. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | None of these bodies form new storage or run an allocator. The behavioral functions write only into caller-provided output pointers or the instance record's fixed cells; the Euler step advances the state region in place through a counted `size_t` loop bounded by the symbolic volume. No dynamic allocation, byte arena or allocator run is introduced (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`; Dir 4.12, no dynamic memory). The `2 ^ 64` size bound stays abstract against the symbolic shape volume. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |


### Tensor nominal-value getter over the symbolic state volume: standards impact

`FMI3.TensorNominals` delivers the tensor `fmi3GetNominalsOfContinuousStates` body
over the static tensor instance record as a package-checked product. It emits no
production artifact, adds no CLI or grammar case, and leaves the scalar adapter
(`Runtime.lean`, `ErrorCalls`, the scalar nominal contract) and every existing
contract unchanged. The scalar body assumes a single continuous state; the tensor
body writes the fixed nominal `1` into every cell of the caller buffer over the
symbolic state volume, so no tensor coordinate is enumerated during lowering.

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| FMI 3.0.2 §5.2.2, header files and naming of functions | New derived product only. The function reuses the pinned public prototype `ErrorCalls.nominalSignature` for `fmi3GetNominalsOfContinuousStates`; the emitted signature is the header prototype, checked printable and denoting against the runtime typedefs (`TensorNominals.signature_printable`, `function_denotes`). No new header name or type is introduced. |
| FMI 3.0.2 §3.2.2, getting nominal values of continuous states (Model Exchange) | New derived product only. After the shared handle and lifecycle guard (`Runtime.require .getNominals`), the body checks that the requested count equals the symbolic state volume `shape.volume` and that the caller buffer is non-null (`countReject`, `count_pass`), then writes the fixed nominal `1` into every buffer cell with a counted `size_t` loop bounded by the symbolic volume. The sole terminating behavior returns `fmi3OK` with the buffer reading `1` in every cell (`nominal_behaviors`, `reads_nominals`); the write preserves every cell outside the buffer (`preserves_instance`); a null handle returns `fmi3Error` changing nothing (`null_behaviors`). |
| FMI 3.0.2 common functions and ME/CS interfaces | No change beyond the single Model Exchange getter above; the count query, state accessors, derivative getter, time setter, reset, lifecycle transitions, creation and free bodies are unchanged. |
| C11 / printer conformance | The body's block closedness is checked (`TensorNominals.body_closed`); every statement prints its intended C token grammar (`body_printable`) and the whole function denotes its rendered bytes (`function_denotes`). This increment adds a package-checked getter semantics, not a new production emission. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The getter writes into caller-provided storage through a counted `size_t` loop bounded by the symbolic volume; it forms no new storage and runs no allocator. No dynamic allocation, byte arena or allocator run is introduced (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`; Dir 4.12, no dynamic memory). The `2 ^ 64` size bound stays abstract against the symbolic shape volume. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

The theorems hold for arbitrary tensor shape, instance address, caller buffer and
heap. **Open:** the count-negotiation policy for a partial or oversized request,
the whole tensor adapter renderer and its adapter contract binding every emitted
function, and binding this body to an emitted FMU wrapper, remain open, as does
production generation, which this package product does not authorize. **Stage
decision: open; no grammar expansion.**

### Tensor instance creation over the static tensor pool: standards impact

`FMI3.TensorInstanceInit`, `FMI3.TensorFactory` (and the strengthened
`FMI3.TensorLifecycleHistory.lifecycle_from_creation`) deliver the Model Exchange
and Co-Simulation instance-creation bodies over the static tensor instance pool as
package-checked products. They emit no production artifact, add no CLI or grammar
case, and leave the scalar factory (`StaticFactory`, `FactoryPrefix`,
`FactoryValidation`, `InstanceInitialization`, `StaticRelease`), `Runtime.lean` and
every existing contract unchanged. The tensor factory shares the scalar factory's
model-agnostic reservation prefix (`StaticFactory.reserve`, `guard`,
`selectInstance`, `select_step`, `guard_step`, `ReservationBindings`, the
`CAtomicScan` helper) and admission prefix (`FactoryPrefix.body`, the shared
`Identity.function` validator); only the reserved-record initializer differs.

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| FMI 3.0.2 §2.3.2, creation of an FMU instance | New derived product only. `fmi3InstantiateModelExchange` and `fmi3InstantiateCoSimulation` are the `kind`-parameterized `TensorFactory.function model shape kind`. After the shared admission prefix, a bounded serial reservation with the atomic scan helper selects a free slot; the reserved record is initialized inline and its address returned cast to `fmi3Instance`. Successful creation returns a handle to a slot that was free, initializes exactly that record and preserves every other cell, performing only the scan's bounded atomic work (`TensorFactory.successful`), and marks the slot owned in the reservation-flag block (`TensorFactory.successful_owned`, whose postcondition `Created` exposes the created `kind`, mode `Instantiated` and `slot` cells). Exhaustion returns null and changes no record (`TensorFactory.exhausted_silent`). |
| FMI 3.0.2 §2.3.2, instantiation token and instance name rules | New derived product only. The admission prefix reuses the shared `Identity.function` validator through `FactoryPrefix.body`, parameterized over the model only through its `instantiationToken` string (`Metadata.token`). An accepted identity reduces the public call to the tensor reservation body (`TensorFactory.admission_accepts`, reusing `FactoryValidation.admission_equivalence`); a bad instance name or instantiation token is rejected with a null return, the documented `"Invalid name or instantiation token"` logging and no reservation (`TensorFactory.rejected_silent`, reusing `FactoryValidation.rejected_silent`). The Co-Simulation capability guard rejects requested event mode and intermediate updates outside the admitted unit profile, exactly as the scalar prefix (`FactoryPrefix.capabilityGuard`). No identity-validation proof is duplicated. |
| FMI 3.0.2 §2.3.1, initial FMU state | New derived product only. The initializer stores the reserved slot index, writes `kind`, mode `Instantiated`, the captured environment and logger, the logging flag, resets the independent time base to `+0`, and zero-fills the state region `x` with the same counted `size_t` loop the tensor reset uses (`TensorInstanceInit.code`, `return_reaches`). The post-initialization state region reads the fixed-zero fill, which is the evaluation of the prepared IVP's initialization program `fill shape .zero` for the admitted kernel (`TensorInstanceInit.reads_state`, `TensorReset.initialization_is_zero`), so a created instance begins in the initialization program's value. Creation initializes exactly the reserved record's cells and preserves every cell outside it (`TensorInstanceInit.frame`) and every cell of every other pool instance (`other_instance`). |
| FMI 3.0.2, lifecycle ordering from creation | New derived product only. `TensorLifecycleHistory.lifecycle_from_creation` starts from an initial free pool and the proved reservation-body creation call, whose postcondition supplies the created-instance cells the mode transitions and free consume, then proceeds create, enter/exit Initialization Mode, one continuous-state derivative query, and free. It derives the returned handle, the observed statuses, and the final owner map equal to the original free pool (`create` marks the slot owned and `fmi3FreeInstance` restores it to unowned). |
| C11 / printer conformance | The initializer's block closedness is checked (`TensorInstanceInit.code_closed`); the tensor factory reuses the scalar factory's printed reservation prefix and the shared `Identity.function`/`StaticRelease.function`, whose printing and denotation are checked in the scalar review. This increment adds a package-checked reservation and initialization semantics, not a new production emission. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | Creation reserves a permanently existing element of the static instance array with one atomic exchange, forms its address after a capacity check, and initializes its fields in place; the state region is zero-filled by a counted `size_t` loop bounded by the symbolic volume. No dynamic allocation, byte arena or allocator run is introduced (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`; Dir 4.12, no dynamic memory). The `2 ^ 64` size bounds stay abstract against the symbolic shape volume and slot index. |
| MISRA C:2025 concurrency directives for the reservation pool | Slot reservation is one `atomic_exchange` on the pool's reservation-flag block (the shared model-agnostic `CAtomicScan` primitive the scalar factory uses); the ghost lease (`SlotOwners`) is a specification device (`exchange_reserves`, `reserved_owner`), and a concurrent implementation must still discharge atomicity/linearization against its chosen synchronization primitives, as the scalar review records for the pool. The scan's bounded atomic work is the only shared-memory effect of a successful or exhausted creation. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

The theorems hold for arbitrary tensor shape and pool index (and, for the framing
corollaries, the pool root, reservation-flag block, capacity, owner map and slot);
the admission prefix is parameterized over the model only through its
instantiation token. **Open:** the count-negotiation policy for a partial or
oversized request, and binding these bodies to an emitted FMU wrapper with its
lifecycle and numerical policy, remain open, as does production generation, which
this package product does not authorize. **Stage decision: open; no grammar
expansion.**

### Tensor instance lifecycle bodies over the static tensor pool: standards impact

`FMI3.TensorLifecycleModes`, `FMI3.TensorFree` and `FMI3.TensorLifecycleHistory`
define the Model Exchange mode-transition bodies, the instance-free body and a
composed lifecycle history over the static tensor instance pool, as
package-checked products. They emit no production artifact, add no CLI or grammar
case, and leave the scalar adapter (`Runtime.lean`, `Termination`, `EventEntry`,
`InitializationCalls`, `StaticRelease`) and every existing contract unchanged. The
instance-creation body (`fmi3InstantiateModelExchange`/`fmi3InstantiateCoSimulation`)
is the remaining open lifecycle body (see the note below the table).

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| FMI 3.0.2, entering and exiting Initialization Mode | New derived product only. `fmi3EnterInitializationMode` and `fmi3ExitInitializationMode` guard the handle and lifecycle exactly as the scalar bodies (`Runtime.require` with `enterInitialization`/`exitInitialization`), then write the single lifecycle-mode cell (Instantiated → Initialization, Initialization → Event for the Model Exchange profile, matching `nextMode`). Each sole terminating behavior returns `fmi3OK` changing only that cell (`TensorLifecycleModes.call_behaviors`, bundled by `contract`); a null handle returns `fmi3Error` changing nothing (`null_behaviors`); an illegal mode reaches the shared `fail` statement and returns `fmi3Error` with logging suppressed, after entering Terminated as the scalar rejection does (`illegal_behaviors`, FMI 3.0.2 §2.3.1). |
| FMI 3.0.2, event and continuous-time modes | New derived product only. `fmi3EnterEventMode` (Continuous → Event) and `fmi3EnterContinuousTimeMode` (Event → Continuous) share the same guarded single-cell mode write, with the same success, null and illegal-mode behaviors as above (`TensorLifecycleModes.call_behaviors`, `null_behaviors`, `illegal_behaviors`, `contract`). No event indicators or clock activation are modeled in this profile. |
| FMI 3.0.2, terminating an FMU | New derived product only. `fmi3Terminate` (Event or Continuous → Terminated) shares the guarded single-cell mode write with the same success, null and illegal-mode behaviors (`TensorLifecycleModes.call_behaviors`, `null_behaviors`, `illegal_behaviors`, `contract`). A successful transition of instance `i` changes only its `mode` cell and preserves every tensor cell of every other instance in the static pool (`preserves_other_instances`). |
| FMI 3.0.2, freeing an FMU instance | New derived product only, reusing the shared model-agnostic release. `fmi3FreeInstance` reads only the reserved slot index `m->slot` stored at creation and the pool's reservation-flag block, performs one atomic store clearing the slot's flag, and returns void; it never reads or writes a tensor region. For an owned slot it discharges exactly its lease, restores the owner map to `update owners slot none`, preserves every other cell, and returns void (`TensorFree.free_owned`, bundled by `contract`, instantiating `StaticRelease.release_owned` for the tensor pool record `TensorInstance.record pool i = pool.index i`); a null handle changes nothing (`null_behaviors`). |
| FMI 3.0.2, lifecycle ordering | New derived product only. `TensorLifecycleHistory.lifecycle_history` composes the sequence from a created, Instantiated-mode record: `fmi3EnterInitializationMode` and `fmi3ExitInitializationMode` thread into Event Mode by two single-cell mode writes, and from the reached Event-Mode heap the instance answers a continuous-state derivative query (`TensorContinuousStates.deriv_contract`) and is released by `fmi3FreeInstance`. It derives the observed status of each call (`fmi3OK` for the two mode transitions and the derivative query, void for free) and the pool's final owner map (the released slot restored to unowned). The premises are explicit (created-instance record cells, finite kernel execution, direct-resolution, the reached-heap identification, and the reservation-flag representation and release bindings). The derivative query and the free act on disjoint memory, so both issue from the reached Event-Mode heap. |
| C11 / printer conformance | Every mode-transition body prints its intended C token grammar (`TensorLifecycleModes.body_printable`, `signature_printable`) and the rendered functions denote themselves under the shared `CTree.Printer` relation (`function_denotes`), carried by the contracts' `denotes` field. The free body is the shared `StaticRelease.function`, whose printing is checked in the scalar review. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | Each mode transition writes a single `int32` mode cell into permanent static storage; the free performs one atomic store into the reservation-flag block. No dynamic allocation is introduced (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`); both respect Dir 4.12 (no dynamic memory). The instance slots and reservation flags are permanently allocated static arrays. |
| MISRA C:2025 concurrency directives for the reservation pool | The free's slot release is one `atomic_store` on the pool's reservation-flag block, the same shared model-agnostic primitive the scalar factory/release use; the ghost lease (`SlotOwners`) is a specification device, and a concurrent implementation must still discharge atomicity/linearization against its chosen synchronization primitives, as the scalar review records for the pool. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

The theorems hold for arbitrary tensor shape, instance address, and heap (and, for
the framing corollaries, the instance index of the static pool; for the free and
history, the pool root, reservation-flag block, capacity, owner map and slot). The
mode-transition bodies are shape-independent (they never read or write a tensor
region) and the free is exactly the shared release, so both are stated over an
arbitrary instance address and specialized to the tensor pool record only in the
framing corollaries and the history. The instance-creation body
(`fmi3InstantiateModelExchange`/`fmi3InstantiateCoSimulation`) is now delivered as a
package product (see the tensor instance creation subsection above): the tensor
factory reuses the model-agnostic reservation and admission prefixes and a
tensor-specific reserved-record initializer built on the zero-fill loop. The
count-negotiation policy for a partial or oversized request and binding these
bodies to an emitted FMU wrapper with its lifecycle and numerical policy remain
open. **Stage decision: open; no grammar expansion.**

### Tensor count queries, time setter and reset: standards impact

`FMI3.TensorCountQueries`, `FMI3.TensorSetTime` and `FMI3.TensorReset` define the
Model Exchange count-query, time-setter and reset function bodies as
package-checked products. They emit no production artifact, add no CLI or grammar
case, and leave the scalar adapter (`Runtime.lean`, `CountQueries`, `TimeCalls`,
`Reset`) and every existing contract unchanged.

| Standard | Impact |
| --- | --- |
| MLS 3.7, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| MLS 3.7 §8.6 (initialization: solving initialization problems) | The reset body restores the prepared IVP's fixed-zero initialization. `TensorReset.reads_initialization` proves the post-reset state region reads the fixed-zero fill, and `TensorReset.initialization_is_zero` proves that fill is exactly the evaluation of the admitted kernel's initialization program `fill shape .zero` (`TensorInstanceRhs.kernel`), so the interface reset re-establishes the same initial state the initialization program specifies. |
| FMI 3.0.2, Model Exchange interface, getting the number of continuous states and event indicators | New derived product only. `fmi3GetNumberOfContinuousStates` writes the symbolic state volume `shape.volume` as a `size_t` into the caller's pointer; `fmi3GetNumberOfEventIndicators` writes `0`. Each guards the handle and lifecycle exactly as the scalar body (`Runtime.require` with `getCounts`), rejects a null output pointer, and its sole terminating behavior returns `fmi3OK` with the count written (`call_behaviors`, bundled by `contract`); a null handle returns `fmi3Error` changing nothing (`null_behaviors`). The `size_t` conversion is discharged under an explicit `shape.volume < 2 ^ 64` premise through the reusable `CLoops.convert_size_nat` lemma, and the body run is composed from small machine steps, so the `2 ^ 64` bound is never evaluated against the symbolic volume. |
| FMI 3.0.2, Model Exchange interface, setting time | New derived product only. `fmi3SetTime` guards the handle and lifecycle exactly as the scalar body (`Runtime.require` with `setTime`, admitted only in continuous-time mode), rejects a non-finite time value, and writes the finite value into the instance's independent time base (a single `double` cell). Its sole terminating behavior returns `fmi3OK` writing exactly the time cell of instance `i` and preserving every other cell, including every tensor cell of every other instance (`call_behaviors`, `preserves_other_instances`, `contract`); a non-finite value returns `fmi3Error` with logging suppressed (`nonfinite_behaviors`) and a null handle returns `fmi3Error` changing nothing (`null_behaviors`). |
| FMI 3.0.2, Model Exchange interface, reset | New derived product only. `fmi3Reset` guards the handle and lifecycle exactly as the scalar body (`Runtime.require` with `reset`), restores the fixed-zero initialization of the state region `x` with a counted `size_t` loop whose bound is the symbolic state volume, and resets the independent time base to zero. Its sole terminating behavior returns `fmi3OK` writing exactly those cells of instance `i` to `+0` and preserving every other cell of every other instance (`reset_behaviors`, `preserves_other_instances`, `contract`); a null handle returns `fmi3Error` changing nothing (`null_behaviors`). The loop bound is the symbolic volume, with no tensor coordinate enumerated. |
| C11 / printer conformance | Every body prints its intended C token grammar (`body_printable`, `signature_printable`) and the rendered functions denote themselves under the shared `CTree.Printer` relation (`function_denotes`), carried by the contracts' `denotes` field. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The count query writes a single `size_t` cell; the time setter writes a single `double` cell; the reset stages the state region base pointer and element count into ordinary locals and fills with a counted `size_t` loop over the static instance pool. No dynamic allocation is introduced (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`); the reset's fixed-bound counted loop and single-cell writes respect Dir 4.12 (no dynamic memory). |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

The universal theorems hold for arbitrary tensor shape, instance address (and,
for the framing corollaries, the instance index of the static pool) and heap. The
integer-to-`size_t` conversion of `shape.volume` is kept symbolic against the
`2 ^ 64` bound; the count-negotiation policy for a partial or oversized request and
binding these bodies to an emitted adapter wrapper with its lifecycle and numerical
policy remain open. **Stage decision: open; no grammar expansion.**

### Fused tensor derivative getter and typed-to-observable transfer: standards impact

`CCalls.Events.loop_call_reaches_events`/`loop_call_behaviors_events` (in
`packages/backend-c`, the owner of both call machines) transfer a completed void
loop-call execution from the typed tensor call scheduler
(`CLoops.Calls.machine`, the level of `CTensor.Lowering.CallCorrect`) into the
observable call machine (`CCalls.Events`), reaching the identical final heap.
Building on that, `FMI3.TensorContinuousStates.deriv_reaches`/`deriv_behaviors`
prove the fused single-run `fmi3GetContinuousStateDerivatives` body over the
`FMI3.TensorInstance` record as one observable-machine execution, and
`deriv_contract` bundles it as a consumable `FunctionContract`. These are
package-checked products only: they emit no production artifact, add no CLI or
grammar case, and leave the scalar adapter and every existing contract unchanged.

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| FMI 3.0.2, Model Exchange interface, evaluating state derivatives | The fused-run open item of the previous increment is resolved. `fmi3GetContinuousStateDerivatives` now runs in one observable-machine execution: it guards the handle/lifecycle, checks that `nContinuousStates` equals the symbolic state volume and the buffer is non-null, invokes the prepared tensor derivative entry `rumoca_rhs` (resolved directly by name), then copies the written `der(x)` region into the caller buffer. Its sole terminating behavior returns `fmi3OK` with the finite tensor derivative delivered to the caller buffer, the instance's `der(x)` region holding the same values, and every other cell of every other instance preserved (`deriv_reaches`, `deriv_behaviors`, `deriv_contract`). A null handle returns `fmi3Error` changing nothing (`null_deriv_behaviors`). |
| FMI 3.0.2, function-call resolution across the interface | The typed and observable call schedulers share the `CCalls.Typed.nextWith` scheduler and differ only in call-site resolution: the typed scheduler reads a direct callee name from the statement, while the observable scheduler resolves the callee expression through the address dictionary. The transfer lemma (`loop_call_reaches_events`) discharges the difference under `CCalls.Events.Resolves`, the exact premise that each nested direct call the entry visits resolves to its own name (the emitted tensor helper functions are direct calls by identifier, not shadowed by constants). This makes the prepared entry's execution, proved in the typed machine (`TensorModelRhs`, `TensorInstanceRhs.derivative_writes`), available as an observable-machine run (`TensorModelRhs.events_reaches`, `TensorInstanceRhs.derivative_writes_events`) with the identical final heap. |
| C11 / printer conformance | The fused body prints its intended C token grammar (`derivBody_printable`, `derivSignature_printable`) and the rendered function denotes itself under the shared `CTree.Printer` relation (`derivFunction_denotes`), carried by the contract's `denotes` field. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The fused body stages each region base pointer and the element count into ordinary locals, invokes the entry by direct call, and copies with a counted `size_t` loop over the static instance pool; no dynamic allocation is introduced, and the transfer lemma changes neither machine definition. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

The theorems hold for arbitrary tensor shape, instance index, request length and
heap. The fused getter carries an explicit direct-resolution premise
(`resolves`), which a tensor adapter discharges for its own emitted helper
functions. The tensor count queries (`fmi3GetNumberOfContinuousStates`,
`fmi3GetNumberOfEventIndicators`), the count-negotiation policy for a partial or
oversized request, and binding to an emitted adapter wrapper with its lifecycle
and numerical policy remain open. **Stage decision: open; no grammar expansion.**

### Tensor continuous-state interface bodies over the tensor instance record: standards impact

`FMI3.TensorContinuousStates` defines the Model Exchange continuous-state function
bodies `fmi3GetContinuousStates`, `fmi3SetContinuousStates` and
`fmi3GetContinuousStateDerivatives` over the `FMI3.TensorInstance` record as
package-checked products. They emit no production artifact, add no CLI or grammar
case, and leave the scalar adapter (`Runtime.lean`, `StateCalls`,
`DerivativeCalls`) and every existing contract unchanged.

| Standard | Impact |
| --- | --- |
| MLS, admitted subset | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| MLS, Real finiteness | The setter validates that every caller value is finite before any write; a non-finite value would reject before reaching the copy loop (reusing `TensorFloat64.validate_reaches`). This matches the scalar policy: a Real value written through the interface must be a finite binary64 value. |
| FMI 3.0.2, Model Exchange interface, getting and setting continuous states | New derived product only. `fmi3GetContinuousStates` copies the state tensor `x` and `fmi3SetContinuousStates` copies the caller values into `x`, each as a contiguous row-major block whose element count is the symbolic state volume. `nContinuousStates` must equal that volume and the buffer must be non-null; both bodies reject otherwise before touching the buffer. Each is proved end to end through the observable call machine and bound to the instance record (`get_behaviors`, `set_behaviors`, `get_instance_behaviors`, `set_instance_behaviors`); the counted copy loop's bound is the symbolic volume, with no tensor coordinate enumerated. |
| FMI 3.0.2, Model Exchange interface, evaluating state derivatives | `fmi3GetContinuousStateDerivatives` invokes the prepared tensor derivative entry on the instance (whose execution writes `der(x) = f(x,u)` and preserves every other instance is the product `TensorInstanceRhs.derivative_writes`, in the typed tensor call machine), then copies `der(x)` into the caller buffer (`deriv_delivers`, `deriv_instance_delivers`, in the observable call machine). The fused single-run execution of the entry call and the copy in one observable-machine run remains open (see below). |
| FMI 3.0.2, instance handle and calling-sequence state | The handle and lifecycle guard are validated exactly as the scalar bodies (`Runtime.require` with `getStates`/`setStates`/`getDerivatives`): a null handle returns `fmi3Error` changing nothing (`null_get_behaviors`, `null_set_behaviors`, `null_deriv_behaviors`). The successful getter writes only the caller buffer; the successful setter writes only instance `i`'s state region, preserving every other cell including every tensor cell of every other instance (`set_preserves_other_instances`). |
| C11 / printer conformance | Every body prints its intended C token grammar (`getBody_printable`, `setBody_printable`, `derivBody_printable`, `signature_printable`, `derivSignature_printable`) and the rendered functions denote themselves under the shared `CTree.Printer` relation (`getFunction_denotes`, `setFunction_denotes`, `derivFunction_denotes`). |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | Each body stages the region base pointer and element count into ordinary locals and copies with a counted `size_t` loop over the static instance pool; no dynamic allocation is introduced. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

The universal theorems hold for arbitrary tensor shape, instance index, request
length and heap. The bodies are not emitted; the fused single-run derivative
getter (running the typed-machine entry and the observable-machine copy in one
execution), the multi-instance count-negotiation policy, and binding to an
emitted adapter wrapper remain open. **Stage decision: open; no grammar
expansion.**

### Tensor Float64 accessor bodies over the tensor instance record: standards impact

`FMI3.TensorFloat64` defines tensor `fmi3GetFloat64`/`fmi3SetFloat64` function
bodies over the `FMI3.TensorInstance` record as package-checked products. They
emit no production artifact, add no CLI or grammar case, and leave the scalar
adapter (`Runtime.getFloat64`/`setFloat64`, `Float64Calls`, `Float64Set`) and
every existing contract unchanged.

| Standard | Impact |
| --- | --- |
| MLS 3.7 | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| MLS Real finiteness | The setter validates that every caller value is finite before any write; a non-finite value would reject before reaching the copy loop (`validate_reaches`). This matches the scalar policy (`Float64SetProofs`, `FMI3Float64Rejection`): a Real value written through the interface must be a finite binary64 value. `Value.isFinite` classifies the loaded cell. |
| FMI 3.0.2 §2.2.6.5, getting and setting variable values for array variables | New derived product only. One value reference denotes the whole array variable; the accessor reads/writes the referenced instance region as a contiguous row-major block whose element count is the shape volume (`shape.volume` for `u`/`x`/`der(x)`, `1` for `time`, `oshape.volume` for `J`). The caller's `nValues` must equal that count; the accessor rejects otherwise before touching the buffer. The getter dispatches all declared variables (`0→time`, `1→u`, `2→x`, `3→der(x)`, `4→J`, the last present only when the record carries the output); the setter dispatches the writable `u`(1)/`x`(2) and rejects `0`/`3`/`4`/unknown, mirroring the scalar setter's read-only rejection. Each accepted reference is proved end to end through the typed call machine and bound to the instance record; the counted copy loop's bound is the symbolic element count, with no tensor coordinate enumerated. A request must name exactly one value reference (`nValueReferences = 1`); the multi-reference aggregate (with `nValues` the sum of element counts and a running output offset) is rejected, not mishandled, and is the identified extension. |
| FMI 3.0.2 (instance handle / lifecycle) | The handle and lifecycle guard are validated exactly as the scalar bodies (`Runtime.require`): a null handle returns `fmi3Error` changing nothing (`null_get_behaviors`/`null_set_behaviors`), and an unknown/unsupported reference reaches the scalar `fail` error path (returning `fmi3Error` as the scalar bodies do) without reaching the copy loop. The successful getter writes only the caller buffer; the successful setter writes only the selected region of instance `i`, preserving every other cell including every tensor cell of every other instance (`set_preserves_other_instances`). |
| C11 / printer conformance | Both bodies print their intended C token grammar (`getBody_printable`/`setBody_printable`/`signature_printable`) and the rendered functions denote themselves under the shared `CTree.Printer` relation (`getFunction_denotes`/`setFunction_denotes`), carried by the contracts' `denotes` field. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The accessor stages the region base pointer and element count into ordinary locals and copies with a counted `size_t` loop; no dynamic allocation is introduced. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

The universal theorems hold for arbitrary tensor shape, instance index, request
lengths and heap. The memory-machine execution witness for the unknown or
unsupported value-reference `fail` path is now proved end to end
(`get_fail_prefix`/`set_fail_prefix` reach the `fail` statement before the copy
loop with the heap unchanged; `get_fail_behaviors`/`set_fail_behaviors` return
`fmi3Error` through `GuardedCalls.FailurePrefix.silent_behaviors`). The bodies are
not emitted; the multi-reference aggregate copy and binding to an emitted adapter
wrapper remain open. **Stage decision: open; no grammar expansion.**

### Tensor instance storage bound to the model right-hand side: standards impact

`FMI3.TensorInstance` and `FMI3.TensorInstanceRhs` are package-checked products
only. They emit no production artifact, add no CLI or grammar case, and leave the
scalar static adapter (`StaticStorage`, `DerivativeCalls`, `ModelRhs`) and every
existing contract unchanged.

| Standard | Impact |
| --- | --- |
| MLS 3.7 | No admission, grammar, source semantics, initialization or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| FMI 3.0.2 ME/CS (storage/lifetime) | New derived product only. A tensor instance's FMI-visible tensors (`time`, `u`, `x`, `der(x)`, and `J` when present) are modeled as static object regions of `double`, one contiguous array per tensor with extent equal to the shape volume, addressed by an instance index into a bounded static pool. This mirrors the FMI instance-lifetime model: an instance is a distinct, persistent storage record for the duration between `fmi3InstantiateModelExchange`/`CoSimulation` and `fmi3FreeInstance`, with `fmi3GetContinuousStateDerivatives` reading the state and input and writing the derivative buffer. The theorems establish pairwise region separation, cross-instance separation over the pool (mirroring the scalar `deploymentCapacity` pool), and that running the prepared derivative entry writes only `der(x)` and preserves every other instance. No emitted `fmi3*` body, production metadata or mandatory adapter contract changes; the derivative entry stays the derived typed-machine contract `FMI3.TensorModelRhs`, not yet bound to an emitted wrapper. |
| MISRA C:2025 Dir 4.12 and Rule 21.3 (no dynamic allocation) | The instance record is static object storage; there is no dynamic allocation, consistent with the no-heap generated-C rule (Rule 21.3, no `malloc`/`calloc`/`realloc`/`free`). Every tensor member is a fixed static array of `double`; the pool has a fixed bound. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

The universal theorems establish readable state/input regions, a writable
derivative region, distinct-member and distinct-instance separation, and the
derivative-entry write-and-frame result over the typed tensor call machine.
Storage validity is derived from the record, not assumed of the caller. Finite
overflow/error policy, the FMI lifecycle and time base, the dense output
observation binding, and the complete bound tensor FMU/eFMU certificates remain
open. **Stage decision: open; no grammar expansion.**

### Tensor FMI 3 model description: standards impact

`FMI3.TensorMetadata.modelDescription` is a package-checked product only. It is
not emitted by production, adds no CLI or grammar case, and leaves the existing
scalar unit `modelDescription` and every existing contract unchanged.

| Standard | Impact |
| --- | --- |
| MLS 3.7 | No admission, grammar, source semantics or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| FMI 3.0.2 ME/CS | New derived product only. The tensor `fmi3ModelDescription` declares each tensor variable as one `fmi3Float64` with one `Dimension` (constant `start`) per extent, one `valueReference` per variable, `causality`/`variability`/`initial` mirroring the unit document, the derivative's `derivative` attribute referencing the state, and an `fmi3ModelStructure` listing `Output`, `ContinuousStateDerivative` and `InitialUnknown`. Array `start` on `u` and `x` is the space-separated flattened list of one value per element (the `Dimension`-start product) for the uniform fixed-zero initialization. `ModelStructure` entries carry an explicit `dependencies="1"` with `dependenciesKind="dependent"` recording the single input dependency, since an omitted `dependencies` means "depends on all". No emitted `fmi3*` body, production metadata or mandatory adapter contract changes. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

Schema basis: the pinned FMI 3.0.2 XML schema elements `fmi3ModelDescription`,
`fmi3Float64`, the `Dimension` element (`start` versus dynamic `valueReference`),
the array variable `start` list, and `fmi3ModelStructure` (`Output`,
`ContinuousStateDerivative`, `InitialUnknown` with the `dependencies` and
`dependenciesKind` attributes), consistent with the metadata-projection
obligation recorded in `dev/fmi3/contracts.md` and the scalar
ModelStructure/no-Dimension restriction there. The universal theorems establish
well-formedness under the in-tree renderer, distinct value references,
Dimension-start products equal to `Tensor.Shape.volume`, an array `start` list of
that same element count, the derivative-to-state reference, ModelStructure
references to declared variables, every `dependencies` reference declared, and
identical `decodeModelIdentifiers` output. Complete FMI metadata conformance and
the bound tensor FMU/eFMU certificates remain open. **Stage decision: open; no
grammar expansion.**

### Tensor model right-hand-side contract: standards impact

| Standard | Impact |
| --- | --- |
| MLS 3.7 | No admission, grammar, source semantics, initialization or provenance change. The array profiles remain development cases; `jacobian` remains an identified extension. |
| FMI 3.0.2 ME/CS | No emitted function, metadata or mandatory adapter contract changes. `FMI3.TensorModelRhs` is a derived typed-machine contract for a prepared tensor derivative entry, not yet bound to any emitted `fmi3*` body. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code, manifest or archive change. |

The FMI package audit passed with the three new roots on the three permitted
axioms, and the required full gate passed on 2026-09-16 in 10m06s.

### Unsupported public FMI calls: full gate passed

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

The pinned [FMI 3.0.2 §§2.2.1, 2.2.7.2, 2.2.7.4, 2.2.8.4,
2.2.9, 2.2.12, 2.3.6–2.3.7, 2.4.2 and 4.1.2](https://fmi-standard.org/docs/3.0.2/)
review separates capability flags, variable domains, lifecycle restrictions
and defensive calls. Clock and empty output-derivative findings remain open.
Pinned MLS/eFMI findings carry forward. **Stage decision: open.**

### Initialization from checked controls: full gate passed

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

### Private reservation retention and initialization: full gate passed

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

### Resource origins and release histories: full gate passed

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

### Current handle authority and captured release: full gate passed

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

### Computed publication and release completion: full gate passed

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

### Concurrent initialization through host observation: full gate passed

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

### Computed reservation histories through actual claims: full gate passed

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

### Public factory histories through slot claims: full gate passed

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

### Slot claims and suspended callers: full gate passed

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

### Host histories and reservation origins: full gate passed

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

### Release origins and ordinary flag frames: full gate passed

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

### Reservation bounds and actual atomic operations: full gate passed

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

### Concurrent slot histories and atomic-call values: full gate passed

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

### Runtime storage and state-setter permissions: full gate passed

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

### Source-bound runtime and call depth: full gate passed

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

### Generated call policy: full gate passed

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

This is a prerequisite for K02 and MISRA allocation/recursion review, not a
completed guideline-compliance argument. No MLS/GALEC grammar, Solve lowering,
FMI lifecycle/emitter or eFMI artifact behavior changes. The pinned whole-
subset standards findings remain open. Upstream Rumoca `6da1462` retains the
reviewed IR/prepared-product specifications; see `upstream-review-v2.json`
in the call-policy evidence directory.

### SR09 — empty-setter endpoint repair: full gate passed

[FMI 3.0.2 §2.3.8](https://fmi-standard.org/docs/3.0.2/#Terminated) permits
final-value getters after termination; setters are absent from that call list.
The prior empty Float64 and absent-type paths used the getter guard and
returned OK for terminated instances. The separate general setter endpoint
now excludes that mode while retaining empty CS Step Mode calls. Per-variable
nonempty permissions remain a separate obligation.

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

**Nonempty-state setter interpretation (full gate passed for this interpretation):**
The pinned [FMI 3.0.2 Continuous-Time rule](https://fmi-standard.org/docs/3.0.2/#ContinuousTimeMode)
permits generic setters for continuous states; the
[Event rule](https://fmi-standard.org/docs/3.0.2/#EventMode) permits states with
`reinit=false`. Initial-state setting follows the phase's `initial` and
`variability` conditions. Table 17's generic local-variable restriction conflicts
with those state-specific clauses. The compiler retains the state-specific
exception, rather than changing `x`'s metadata to avoid the review.

The standards project's approved [PR #1956](https://github.com/modelica/fmi-standard/pull/1956)
added continuous states to the Continuous-Time generic-setter rule. Its merge
`fd8c034e5b7dd5c8a2ad5689e5df13b84be34ab9` is included in `v3.0.2`;
the retained release comparison is 20 commits ahead and none behind. This
supports the interpretation for identified states, independently of causality;
it does not establish consistency of all prose or license arbitrary locals.
The Table 17 editorial inconsistency remains visible. The policy theorem proves correspondence with this interpretation; the
owning-package and full artifact gates passed as recorded above. Evidence: `build/c-call-depth/fmi-setter-review/` and the nine-root
`state-setter-policy-v3.json` draft result. Complete legal-history correspondence
and the empty Clock/interval/output-derivative findings remain open.

**Legal importer and resource boundary:**
[FMI 3.0.2 §2.2.1](https://fmi-standard.org/docs/3.0.2/#general-mechanisms)
prohibits logger callbacks from calling back into the FMU. The host also owns
race avoidance for calls to one instance. Required native correspondence must
state these obligations; support for forbidden logger reentry is not a required
conformance feature. Shared static-pool ownership and native atomic refinement
remain separate work. A modeled heap invariant does not establish hidden native
allocation, private callback stack use, lock freedom or RTOS timing. See
`build/c-call-depth/runtime-boundary-review-v1.md` and the retained tagged
`2_2_common_mechanisms.adoc`. Prior prose mentioning reentry is scoped by this
legal-importer boundary, without weakening any existing theorem.

### Absent-variable initialization histories: full gate passed

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

The [FMI 3.0.2 §§2.2.1, 2.2.7.2, 2.3, 3.2.1 and 4.2.1](https://fmi-standard.org/docs/3.0.2/) review records the Int64/Enumeration
mapping and separates defensive calls from legal importer histories.
The CS get-after-set restriction still needs complete history evidence.
Pinned MLS/eFMI findings carry forward. **Stage decision: open.**

### Absent-variable accessors: full gate passed

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

The [FMI 3.0.2 §§2.2.1, 2.2.7.2, 2.3, 3.2.1 and 4.2.1](https://fmi-standard.org/docs/3.0.2/) review records the Int64/Enumeration
mapping and separates defensive calls from legal importer histories.
The CS get-after-set restriction still needs complete history evidence.
Pinned MLS/eFMI findings carry forward. **Stage decision: open.**

### Evaluation during initialization histories: full gate passed

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

The existing [FMI 3.0.2 §§2.3.1, 2.3.3 and 2.3.5](https://fmi-standard.org/docs/3.0.2/) review carries forward.
Legal Event calls and defensive rejection during initialization remain
distinct. Prose/schema correspondence is a reviewed interpretation.
Upstream IR specifications were compared at `7d64933d`; the prepared
Solve/interface boundary and separate GALEC refinement chain are retained.
Pinned MLS/eFMI findings carry forward. **Stage decision: open.**

### Discrete evaluation: full gate passed

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

The corrected guard follows [FMI 3.0.2 §§2.3.3–2.3.5 and §2.4.2](https://fmi-standard.org/docs/3.0.2/). The pinned interface schema supplies
the omitted Boolean default. Correspondence with this prose/schema remains
a reviewed interpretation; the theorem binds actual XML omission and C
execution. It does not formalize every schema Boolean spelling.
Pinned MLS/eFMI findings carry forward. **Stage decision: open.**

### Event-indicator histories: full gate passed

The same reviewed lifecycle/count guard now composes through initialization,
mixed ME operation, source-bound creation/release and recurring ME/CS drivers.
Actual calls determine status and memory frames. Original borrowed storage and
universal callback policies remain explicit host conditions; no future heap or
selected logger return replaces them. Null output tolerance is defensive, and
post-Error queries are diagnostic-only.

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

Upstream Rumoca `b0217592` preserves the reviewed SPEC_0007/SPEC_0048 ownership
rules. Its SPEC_0043 affine-elimination/factor-freshness addition concerns later
numerical projection; this increment does not perform that work. The focused
review is retained in `build/c-factory/event-histories/standards-review-v1.json`.
Pinned MLS 3.7 and eFMI 1.0.0 Beta 1 findings carry forward.

The next discrete-evaluation review found an overbroad lifecycle predicate:
`fmi3EvaluateDiscreteStates` was admitted during Initialization, although the
pinned FMI 3.0.2 call table lists it in Event Mode. Its false capability default
requires an ignored operation there, so generic capability rejection is not
the replacement. An Event-only policy correction and complete no-op call,
metadata, source and control-history drafts are in
`build/c-factory/discrete-evaluation/`; combined production and artifact
acceptance remain pending. No new grammar or numerical capability is admitted.
K02–K05 and the recurring whole-subset standards review remain open.

The new evaluation finding is based on [FMI 3.0.2 §§2.3.3–2.3.5 and
§2.4.2](https://fmi-standard.org/docs/3.0.2/) and the
[pinned interface schema](https://raw.githubusercontent.com/modelica/fmi-standard/v3.0.2/schema/fmi3InterfaceType.xsd).
Its isolated drafts do not constitute the corrected emitted-artifact guarantee.
**Stage decision: open; no grammar expansion.**

### Zero-event getter: full gate passed

The source theorem binds the mandatory printed/prepared public function,
actual adapter and XML zero-event count to the same source/Solve product.
The independent lifecycle predicate covers the reviewed ME modes under FMI
3.0.2 §§2.3.3, 2.3.5, 2.3.8 and 3.2.1; §2.4.8 supplies the event-count/order
obligation. The valid empty query preserves the whole heap. Failure preserves
the actual guard priority, Error result and all modeled logger alternatives
under the stated caller and callback memory policies.

FMI §2.2.1's general pointer rule remains separate: the additional tolerance
of a null output pointer is defensive implementation behavior, not a claimed
normative importer permission. Queries following Error remain diagnostic-only.
No event grammar, solver policy, metadata capability or emitter change is added.
Pinned MLS 3.7 and eFMI 1.0.0 Beta 1 findings carry forward unchanged.

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

Initialization/ME history composition, remaining public functions, native/ABI
correspondence, reset policy and MISRA closure remain open. The follow-up
history proofs have isolated development evidence; full conformance is not
established. **Stage decision: open; no grammar expansion.**

### CS simulation logging: full gate passed

Recurring initialization/simulation/reset/release, raw call records, source
observations, interrupted prefixes, access/protocol continuations and unified
restart now have owning-package and actual-artifact acceptance. The pinned
baseline remains MLS 3.7, FMI 3.0.2 and eFMI 1.0.0 Beta 1. Affected FMI
§§2.2.4, 2.3.1 and 2.4.5 retain the reviewed category, suppression, error and
callback obligations. Legal requests remain distinct from defensive handling
of invalid inputs.

Borrowing and universal callback frames are host-profile premises, including
while logging is disabled. Original inputs are retained through actual calls;
expected statuses, source samples and final logging flags are consequences of
the history proof. Reset flag retention describes the authored implementation;
the normative reset-policy finding remains open. No grammar, numerical
lowering, emitter or eFMI product changed. Previous MLS/eFMI findings and
native/ABI/MISRA obligations still apply.

The owning package checks passed at 04:46:54 UTC. The required full
`nix develop .#verification --command lake test` passed at 05:28:57 UTC on
1071 unchanged inputs. All 69 selected roots passed with no unexpected axioms,
changed-module warnings or input drift. Failed package logs are retained;
repairs preserve the five earlier numerical interruption audit roots and the
generalized handoff/restart guarantees. Only the three evidence documents
change after the frozen gate. Evidence is in
`build/c-factory/cs-simulation-logging/package-v4.*`, `full-gate-v1.*`,
`premise-review-v2.json` and `standards-review-v2.json`.

All retained FMU members, including the native library, match the accepted ME
checkpoint byte for byte. The eFMU changes only generation identities and
dependent references/checksums in three manifests. Numerical C, GALEC and
Production C are unchanged; actual-artifact, importer, native and mutation
checks passed. Archives and comparisons are in
`build/c-factory/cs-simulation-logging/artifacts-v1/` and its adjacent JSON.
Upstream Rumoca `c3631581c691ebcc06da5cf14b06e9e477fe7c33` preserves the
reviewed IR/prepared-product ownership. SPEC_0043's additional AD projection
reuse rules concern future optimization; this slice performs none.
**Stage decision: open; no grammar expansion.**

### ME simulation logging: 2026-09-15, full gate passed

The existing ME histories now extend through all initialization
continuations, stopped prefixes, resets and recurring source-bound release.
It retains the reviewed FMI logging-category policy and original borrowing
conditions. The actual initialization bundle now supplies the prepared setter
from the same emitted program; no separate assumed implementation is used.
The source/GALEC grammars, numerical IR semantics, emitters and eFMI product
are unchanged.

The review uses MLS 3.7, FMI 3.0.2 and eFMI 1.0.0 Beta 1. FMI §§2.2.4,
2.3.1 and 2.4.5 govern the affected error/logging and category behavior.
Raw execution retains arbitrary returned values, callbacks and stopped calls;
the prepared contract derives the observed source state and exact flag.
Original category storage and universal callback frames remain explicit host
borrowing conditions, including when logging is disabled. They are not new
FMI restrictions or unrestricted importer coverage. Reset retaining the current
flag is proved for the authored body; the preceding normative reset-policy
finding remains open. Native/ABI correspondence remains a separate boundary.

The owning C/FMI/compiler package gate passed at 03:24:08 UTC. The required
`nix develop .#verification --command lake test` passed at 04:09:01 UTC on
1062 unchanged inputs. All 89 selected roots passed without unexpected axioms,
changed-module warnings or input drift. The stale retained-field audit entry
was replaced by its equivalent relocated theorem; no contract or whitelist
was weakened. Evidence is in `build/c-factory/simulation-logging/package-v4.*`,
`full-gate-v1.*` and `audit-relocation-v1.json`. Only the three evidence
documents change after the frozen gate.

Every retained FMU member, including the native library, is byte-identical to
the initialization checkpoint. The eFMU changes only generation identities and
dependent references/checksums in three manifests. Numerical C, GALEC and
Production C remain unchanged. The existing schema, importer, native,
actual-artifact and mutation checks passed. Archives and comparisons are in
`build/c-factory/simulation-logging/artifacts-v1/` and its adjacent JSON record.
Upstream Rumoca revision `14ea621264819674293d6fc4959f1f2b2b03d99e`
retains the reviewed SPEC_0007, SPEC_0043 and SPEC_0048 ownership rules; the
reviewed hashes are in `build/c-factory/simulation-logging/standards-review-v1.json`.

Mutable CS histories, preceding MLS/eFMI findings and K02–K05 remain open.
**Stage decision: open; no grammar expansion.**

### Mutable logging during initialization: 2026-09-15, full gate passed

The new action uses the previously reviewed FMI 3.0.2 logging-category policy.
Legal selections and defensive C acceptance remain separate: zero-count,
non-null input can have a defensive C result without being a legal FMI request.
The source theorem binds the XML category to the same prepared adapter and
retains initialized source IVPs through logging actions, errors and resets.
No Modelica/GALEC grammar, numerical lowering, C emitter or eFMI product changed.

The current history profile borrows original category arrays and strings.
`ReadBank.Guarded` and `Action.ReadSafe` describe separation from writes and
protected callback storage; they are host-profile conditions, not normative
FMI requirements. Persistent callback binding is now required while logging
is disabled so later enabling is justified. A suppression-only precondition
cannot establish that binding. The premise review is recorded in
`build/c-factory/logging-history/premise-review-v1.json`. These conditional
history theorems do not establish unrestricted FMI compliance.

Creation now derives its input frame from the actual factory frame and the
original readable cells, including string terminators. No new flag-disjointness
premise was added to the source entry theorem. Reset retains the current flag
in this implementation; it is not being declared a new normative FMI rule.
ME/CS continuation contracts use the flag selected by the initialization
history while retaining the original logger/environment.

Both ME and CS simulation now derive exact borrowed-cell preservation through
actual returning calls and universal callback effects. This includes ME count
and nominal writes, numerical and rejection calls, and resets. Recurring
source-bound creation/initialization/simulation/release contracts carry the
same bank and exact accumulated logging update. Suppressed CS certificates
retain exact frames so restart helpers do not assume future input contents.

Write separation remains an explicit borrowing-profile condition, including
ME per-action output regions. These are not new normative FMI requirements.
The original callback binding and universal policy persist while disabled.
The new frame obligations are derived from that policy at actual calls; a
successful callback return remains unnecessary for progress.

The owning package checks passed at 01:38:40 UTC, followed by the required
`nix develop .#verification --command lake test` at 02:22:20 UTC on 1056
unchanged inputs. All 173 selected roots passed, including 68 newly registered
roots, with no unexpected axioms, changed-module warnings or input drift.
Evidence is in `build/c-factory/logging-history/package-v1.*` and
`full-gate-v1.*`. Only the three evidence documents change after the frozen gate.

Retained archives and comparisons are in
`build/c-factory/logging-history/artifacts-v1/`. Every FMU member is unchanged,
including the native library. The eFMU changes only generation identities and
dependent references/checksums in three manifests. Numerical C, GALEC,
Production C, source grammars and numerical lowering are unchanged. The
existing actual-artifact, schema, importer, native and mutation checks passed.

Upstream Rumoca `cb9920bc` retains the reviewed prepared-product and construction
contracts. Its SPEC_0007 update clarifies scalar binding specialization and
preservation of parameter dependencies. That is a future Flat-stage
obligation; this logging slice performs no binding specialization or lowering
in a backend. `build/c-factory/logging-history/standards-review-v3.json` records
the reviewed revision and exact specification hashes.

The subsequent ME checkpoint above now accepts simulation logging through
source-bound recurring creation/initialization/simulation/reset/release, with
the original borrowing and universal callback conditions. Mutable CS histories
still require complete composition and their own package/artifact acceptance.
The preceding MLS/eFMI findings, native ABI/stdlib, MISRA and K02–K05 obligations
remain open.
**Stage decision: open; no grammar expansion.**

### Nominal queries through initialization and ME histories: 2026-09-14

The [pinned FMI 3.0.2 specification](https://fmi-standard.org/docs/3.0.2/)
§§2.2.4, 2.3.1–2.3.4, 2.3.8 and 3.2.1 supply the nominal/error-state review:
ME-only positive nominals, default 1.0 when unspecified, ordered with the
continuous-state vector; Initialization, Initialized and Terminated permit the
query, while Instantiated excludes it. Error transitions enter Terminated;
post-error final-value reads are for debugging, not continued simulation.

The source contract binds the actual XML ordering/default to the same prepared
Solve model and printed C runtime. Universal proofs cover nominal successes,
rejections, original storage, compatible public-buffer aliases and all modeled
returning/blocked logger alternatives through initialization and ME histories.
The mandatory nominal function contract is stronger. The 80-module/56-root
draft passes. The owning-package gate subsequently passed at 22:10:56 UTC on
1022 unchanged inputs in `build/c-factory/nominal-history-package-v2.log`, with
all 56 required roots, no unexpected axioms and no changed-module warnings.
The first package attempt's missing direct import is fixed; its log is retained.
The required full `nix develop .#verification --command lake test` then
passed at 22:56:23 UTC on 1022 unchanged inputs, with all 56 required roots,
no unexpected axioms and no changed-module warnings. Evidence is in
`build/c-factory/nominal-history-full-gate-v1.log` and its JSON record. Only
the three evidence documents change after this frozen full gate.

The retained FMU has identical members, including the native library, to the
ME-count artifact. The eFMU changes only fresh generation identities and their
dependent references/checksums in three manifests. Numerical C, GALEC and eFMI
Production C are unchanged. See `build/c-factory/nominal-history-artifacts-v1/`
and adjacent comparison records. The detailed source review remains in
`build/c-factory/nominal-initialization-source-draft-review-v6.json` and
`build/c-factory/nominal-history-standards-review-v1.json`.
This acceptance does not close the remaining public-call, logging-configuration,
native/ABI, MISRA or K02–K05 obligations.

Upstream Rumoca `23111592` retains the SPEC_0007 and draft SPEC_0048 ownership
boundaries. Its new SPEC_0043 prepared-Jacobian owner rule reinforces the same
prepared-product/source-identity discipline; no optimization is imported here.
MLS 3.7 and eFMI 1.0.0 Beta 1 evidence carries forward with no source grammar,
numerical semantics or eFMI emitter changes. Shared initialization, native/ABI,
MISRA and remaining standards/release findings stay open.
**Stage decision: open; no grammar expansion.**

### Count interleavings in ME simulation: 2026-09-14

This increment uses the existing SR09 count policy: FMI 3.0.2 §§2.3.2 and
2.3.5 permit ME count queries in Instantiated and Event Mode. The mixed ME
history applies the same guard between control/simulation calls and resets;
it retains successful observations and the existing §2.3.1 Error/logging
behavior, including modeled blocked prefixes. Typed count outputs remain
separate from numerical buffers. Original caller storage and the universal
callback policy derive later resources, without a future-heap or callback-return
premise. Recurring source histories retain observations across later resets.

The existing C machine and actual prepared count contracts are reused. Source
and GALEC grammars, numerical semantics, emitters, XML and mandatory artifact
propositions are unchanged; pinned MLS 3.7 and eFMI 1.0.0 Beta 1 evidence and
open shared-initialization/coding-guideline findings carry forward. All 24 draft
modules and 14 selected roots passed standalone Lean checking before package
integration. The owning FMI/compiler package gate passed at 21:15:09 UTC on
1015 unchanged inputs in `build/c-factory/me-count-package-v1.log`, with nine
new and eighteen affected roots and no unexpected axioms or changed-module
warnings. The required full `nix develop .#verification --command lake test`
gate passed at 22:01:57 UTC on 1015 unchanged inputs, with all 27 required
roots and no unexpected axioms or changed-module warnings. Its log and JSON
record are `build/c-factory/me-count-full-gate-v1.*`; only the three evidence
documents change afterward. Retained artifacts and comparisons are in
`build/c-factory/me-count-artifacts-v1/` and adjacent JSON records. Every FMU
member is unchanged, including the native library; the eFMU changes only
generation identities and their dependent references/checksums in three
manifests. Numerical C, GALEC and eFMI Production C are unchanged.
**Stage decision: open; nominal/remaining public calls and K02–K05 block growth.**

### Count observations through initialization/recovery: 2026-09-14

This follow-up reuses the SR09 call-state repair below. FMI 3.0.2 §§2.3.2 and
2.3.5 permit ME count queries in Instantiated and Event Mode, including the
mode reached by initialization exit. Other represented phases and CS reject
them. The history uses the reviewed §2.3.1 Error/termination/reset and logging
policy. A missing output is rejected only after the lifecycle guard permits
the call. Failed outputs contribute no count observation.

The new actions extend the existing raw initialization relation and source
theorems; they do not introduce another C execution model. Count outputs are
caller `size_t` cells, distinct from numerical buffers. Original storage and
the existing protected-region logger policy supply every later storage
precondition. Complete prepared count contracts derive successful outputs,
Error states, returning logger branches and the modeled blocked alternative.
Recurring completed and stopped initialization observations survive later
resets. The same source-bound creation/release and recurring ME/CS theorems
now include the actual XML count contract. Solve remains the owner of counts;
the FMI layer performs no source/DAE lowering or shape inference.

The source/GALEC grammars, numerical semantics, C machine, emitted functions,
metadata and mandatory artifact propositions are unchanged. Pinned MLS 3.7
and eFMI 1.0.0 Beta 1 evidence and open shared-initialization/coding-guideline
findings carry forward. The required full gate passed at 21:05:03 UTC on 1012
unchanged inputs in `build/c-factory/count-history-full-gate-v2.log`, including
eight new and twelve affected audit roots without unexpected axioms or
changed-module warnings. Retained FMU/eFMU archives and comparisons are in
`build/c-factory/count-history-artifacts-v1/` and adjacent JSON records. Every
FMU member is unchanged; eFMU differences are confined to generation identities
and dependent references/checksums in three manifests. Only the three
verification/roadmap documents change after the frozen gate.

Interleaving counts with later ME control/simulation calls has independently
checked drafts, but is not yet accepted by its owning packages and artifact
gate. Native callback behavior, ABI/concurrency correspondence and the remaining
public-call inventory are not established.
**Stage decision: initialization-count extension accepted; K02–K05 and other
open compliance findings continue to block grammar expansion.**

### Count-query call states and shared runtime: 2026-09-14

**Finding SR09 — call-state repair accepted:** the count-query policy
accepted Initialization, Continuous-Time and Terminated as well as Instantiated
and Event Mode. The independently authored `Reference.Allowed` repeated that
extra admission, so `allowed_correct` did not detect it. The earlier
`terminated_me_queries` theorem and native test also treated counts as final
variable values. The pinned [FMI 3.0.2 call tables](https://fmi-standard.org/docs/3.0.2/#common-state-machine)
list both count queries in §§2.3.2 and 2.3.5. They are absent from §2.3.3,
§2.3.8 and §3.2.1's Continuous-Time list, and from the enclosing super-state's
common calls. The policy and reference predicate now admit only ME Instantiated
and Event Mode. The corrected theorem retains final-value accessors and a new
universal lemma rejects counts in the three excluded modes. The existing ABI
check now queries counts in the two permitted modes and checks termination
rejection. The required full artifact gate accepted this repair at 19:55:08 UTC.

The mandatory count-function proposition additionally requires the complete
shared-runtime prepared contract. Existing interface transport and failure-helper
proofs cover success/null, disabled or absent logging, all represented returning
logger outcomes and the modeled blocked alternative. Literal addresses and
contents are supplied by the actual pool, including on later preserving heaps.
The source theorem joins the actual numerical C, count fragments and XML;
successful observations retain the Solve volume or zero event indicators.
Counts are sums of referenced variable sizes (§2.3.2); the admitted metadata
has one scalar state and no events or structural parameters. Array metadata
continues to require a future volume interpretation.

This increment changes the two generated lifecycle guards and strengthens the
actual artifact proposition. It does not change source/GALEC grammars or the
numerical core. Pinned MLS 3.7/eFMI 1.0.0 Beta 1 evidence and open shared
initialization, coding-guideline and MISRA findings carry forward. Callback
termination, native/ABI correspondence and recurring count histories are not
claimed.

`nix develop .#verification --command lake test` passed on 1009 unchanged
inputs in `build/c-factory/count-runtime-full-gate-v1.log`. Nine new and ten
affected roots passed without unexpected axioms or changed-module warnings.
The existing actual-artifact, importer, ABI, native and mutation checks passed.
Only three documentation files change after the frozen gate. Retained archives
and full member comparisons are in `build/c-factory/count-runtime-artifacts-v1/`
and adjacent JSON records. The FMU changes only the two count-query guards and
rebuilt shared library relative to the previous CS artifacts. eFMU changes are
limited to generation identities and dependent references/checksums in three
manifests; numerical C, GALEC and Production C are unchanged.

Local upstream Rumoca at `1464e99c0e95587c20afe190cc0f0b30a632376d` retains
the reviewed `SPEC_0007` and draft `SPEC_0048` contents. The focused comparison
in `build/c-factory/count-runtime-upstream-review-v1.json` confirms that Solve
still owns the executable model and lifecycle composition consumes prepared
products. These remain architecture references, not normative authorities.
**Stage decision: SR09's call-state defect is repaired and artifact-checked;
remaining public-call histories, K02–K05 and other open compliance findings
still block grammar expansion.**

### Recurring ME initialization/simulation/release: 2026-09-14

The admitted Modelica/GALEC grammars, source/Solve/C machine semantics,
generated members and mandatory artifact propositions are unchanged.
`MEProtocol.runtime_create_release` connects actual source-bound creation,
repeated initialization/simulation/reset segments and final release. Original
resources and the universal logger policy supply every later invariant.
Completed and modeled stopped plans retain earlier initialization observations,
source-IVP checkpoints and ME derivative observations. Raw reset values remain
arbitrary; their complete C contracts derive success and exclude blocking.

The [FMI 3.0.2 review](https://fmi-standard.org/docs/3.0.2/) retains §§2.2.4 and
2.3.1's status/logging/reset mapping, §2.2.6's importer-controlled ME time and
§§2.3.3–2.3.4's initialization/termination mapping. Failed outputs are not valid
source observations. A blocked callback in the C/effect model has no FMI return
status; the pending call contributes no invented output, exit checkpoint or
release. The ME proof covers source derivatives and initialized IVPs, not the
correctness of the importer's trial states or integration algorithm. Native
callback termination and concurrent execution are outside this model.

Local upstream Rumoca at `c9e600967aac582fb18ee269272c800e18a56ed3` was checked
against `SPEC_0007` and draft `SPEC_0048`: Solve remains the executable-model
owner, and lifecycle composition consumes prepared products without repeating
lowering. File identities and the focused review are retained in
`build/c-factory/me-cycles-upstream-review-v1.json`. These are architecture
references, not normative compliance authorities. Pinned MLS 3.7 and eFMI
1.0.0 Beta 1 evidence, shared initialization restrictions and MISRA findings
carry forward. No language case or normative policy is added.

The next public-call review has concrete gaps: count-query contracts still use
the earlier typed interface and only disabled-logging errors; nominal-query
contracts need shared-runtime/history integration; debug-logging configuration,
event-indicator/evaluation functions and generic unsupported/type-access paths
need complete metadata-matched coverage. The absence of a capability flag must
be interpreted using the relevant clause before specifying a stub's behavior;
this is not blanket permission to return Error for every optional function.

Twenty new and six affected roots passed the existing FMI/compiler gate on
1007 unchanged inputs in `build/c-factory/me-cycles-package-v1.log` at 18:37:14
UTC, with no unexpected axioms or changed-module warnings. Only three documents
change after that frozen gate. The earlier the previous checkpoint revision passed the full
[GitHub gate 34871354671](https://github.com/CogniPilot/rumoca_lean/actions/runs/34871354671)
at 18:15:01 UTC; this increment still needs its own full-artifact acceptance.
**Stage decision: recurring ME composition is proved for the admitted plans;
K02–K05 stay open and grammar expansion remains blocked.**

### Completed and stopped CS observations: 2026-09-14

The admitted Modelica/GALEC grammars, generated FMI/eFMI members and mandatory
artifact propositions are unchanged. This increment strengthens the recurring
CS creation/initialization/simulation/reset/release theorem with every returned
simulation call's status, events and heap. An erasure/recovery equivalence
proves that the observation view covers exactly the existing completed raw
executions. The same fixed header, prepared table and literal pool supply every
reference transition and actual call contract.

The focused [FMI 3.0.2 review](https://fmi-standard.org/docs/3.0.2/) rechecked
§2.2.4 (defined successful outputs; undefined Error/Discard outputs), §2.2.6
(CS time advancement) and §2.3.1 (reset defaults before a new initialization).
The existing §2.3.3 initialization and §2.3.4 termination mapping is retained.
Each completed step's stored model state has the existing source-IVP sample
and numerical/clock error bound. Only successful steps promise public outputs.
An internal restart retains all three actual returns and the source checkpoint
at initialization exit. Both suppressed and modeled logging paths are covered;
callback totality is not assumed. The pinned MLS 3.7 and eFMI 1.0.0 Beta 1
evidence, shared initialization restrictions and MISRA findings carry forward.
There is no new normative policy or admitted language case.

The stopped-prefix follow-up also rechecked §2.3.1's logging callback interface
alongside §2.2.4's returned-status/output policy. The existing C/effect model's
blocked alternative is not an FMI return status. No return, output or exit
checkpoint is invented for that action. Its recorded heap precedes the pending
action. Prefix splitting reuses completed-history source theorems and retains
an explicit decomposition of the original script; raw stopped/interrupted
relations are equivalent at initialization, CS and recurring-plan levels.
Complete restart/reset call contracts exclude blocking partway through an
internal restart or at a between-cycle reset. This adds no callback-totality
assumption and makes no native callback-termination or native-hang claim.

Completed and modeled stopped CS observations now compose through all admitted
cycles. Recurring ME composition and its stopped observations, the remaining
public-call inventory, native/concurrent execution and translation-unit/ABI
correspondence remain open. The original MLS/eFMI restrictions remain in force.

Nineteen new and eight affected roots passed the existing FMI/compiler package
gate on 998 unchanged inputs in `build/c-factory/stopped-source-package-v1.log`.
The axiom whitelist and existing tests are unchanged. Publication changes only
three documentation files after that frozen gate.
[GitHub run 34868166166](https://github.com/CogniPilot/rumoca_lean/actions/runs/34868166166)
passed the full gate for the previous checkpoint at 17:24:44 UTC, a distinct earlier revision;
its log includes the actual ME/CS and eFMU boundary checks. The current change
still needs its own full-artifact acceptance. K02–K05 remain open.
**Stage decision: no grammar expansion.**

### CS restart return codes and progress: 2026-09-14

The review found a proof-scope restriction: the CS raw restart constructor
already required successful reset/entry/exit codes. It has been broadened to
arbitrary integer codes. The new `ActionContract.restart_returned` derives all
three successful codes from the existing complete C contracts. This corrects
the earlier raw-status claim without changing generated behavior.

Returning and blocked action relations now have equivalence theorems against
their certificates. A finite certified CS history has a completed execution
or a real blocked-call prefix, including the calls within a restart. The
adapter/source theorem exposes progress and derives the observed status list.
The blocked alternative belongs to the existing callback-effect model; it
does not establish native termination, concurrency or callback totality.

The prior FMI 3.0.2 §§2.2.4 and 2.3.1 clause mapping is retained: failed outputs
are not source observations, and reset/initialization precedes a new run.
There is no new normative policy or grammar case. The pinned MLS 3.7 and
eFMI 1.0.0 Beta 1 evidence, initialization restrictions and MISRA findings
carry forward. Source/Solve/C machine semantics and generated artifacts are
unchanged; the raw CS observation relation is deliberately broader.

Six new and seven affected audit roots passed the existing FMI/compiler gate
on 985 unchanged inputs in `build/c-factory/cs-raw-progress-package-v1.log`,
with the axiom whitelist unchanged and no changed-module warnings. No tests
were added. This is package proof evidence, not a new full `lake test` result.
The repeated whole-history theorem, remaining public APIs, native/artifact
correspondence and K02–K05 remain open. **No grammar expansion.**

### Simulation storage and restart protocols: 2026-09-14

This increment changes derived memory/history certificates and source-bound
composition. The frozen unit EBNFs, source admission, generated runtime,
metadata, mandatory artifact propositions and boundary tests are unchanged.
The MLS 3.7 and eFMI 1.0.0 Beta 1 evidence and open findings carry forward.

The focused review rechecked [FMI 3.0.2 §2.2.4 and §§2.3.1–2.3.2](https://fmi-standard.org/docs/3.0.2/):
failed outputs are undefined, Error can recover through reset, reset restores
defaults, and initialization precedes a new simulation run. The new proof
retains those distinctions. Reset starts from the Solve default; later finite
accesses determine the source IVP at actual exit. The existing guards and
non-finite rejection policy are unchanged. An unsuccessful call's buffers are
not source observations merely because their storage survives.

Universal ME/CS logger storage policies preserve the original caller bank's
cell domains, types and permissions while permitting effects outside the
protected region. Existing instance/flag/output value frames remain required.
There is no callback return or determinism premise. Raw reset and later access
statuses, returning alternatives and blocked prefixes reuse the existing C
machine and initialization relations. Simulation supplies the next reset's
storage and ownership; no later valid buffer or selected successful call is a
host premise.

Thirty-three new roots and affected existing roots passed the C/FMI/compiler
package gate on 984 unchanged inputs in
`build/c-factory/simulation-restart-package-v1.log`; the axiom whitelist is
unchanged. No new tests were added. The retained local 869-input full gate and
successful GitHub run `34856771664` for the previous checkpoint remain distinct evidence for
earlier revisions. The latter's complete gate ended at 15:47:48 UTC.

One source-bound repeating simulation/initialization/release theorem, remaining
public calls, native ABI/concurrency, whole artifacts/provenance and existing
MLS/eFMI/MISRA findings remain open. No whole-standard conformance or new
full-artifact pass is claimed. **Stage decision: no grammar expansion.**

### Created initialization protocols through ME/CS simulation: 2026-09-14

This derived-proof increment retains the frozen unit-state EBNFs, source
admission, runtime policy, emitted members and mandatory artifact propositions.
MLS 3.7 Real/default initialization and eFMI 1.0.0 Beta 1 Algorithm/Production
Code evidence are unchanged; all cross-standard findings carry forward.

The focused review rechecked [FMI 3.0.2 §§2.2.4, 2.2.6 and 2.3.1](https://fmi-standard.org/docs/3.0.2/):
Error outputs are undefined, reset restores defaults before reinitialization,
and ME importer time control differs from CS stepping. The new composition
retains those existing distinctions. An actual initialized history supplies
the new simulation seed/clock and original output storage. Rejected-call
outputs are not source observations; later successful reads establish new
observations. Importer trial states are not claimed to solve the initial IVP.

The shared protected-storage invariant now includes scalar ME/CS outputs.
Actual creation and returning logger effects preserve the required cell
types/permissions; the universal external frame remains explicit. Both
simulation continuations reuse the existing mixed histories, source evidence
and release contracts, restoring original ownership. Callback return is not
presumed. Later simulation resets still use the contiguous three-call protocol,
so access interleavings at those restarts remain open.

The 23 new roots and affected existing roots passed the C/FMI/compiler package
gate on 977 unchanged inputs in `build/c-factory/created-protocol-package-v1.log`.
No axiom-policy change or test suite was added. The unchanged runtime/emitter/
mandatory-artifact boundary retains its distinct local 869-input full gate;
GitHub run `34853259941` passed the full gate for the previous checkpoint, a separate revision.
No full-gate pass for this increment or whole-standard conformance is claimed.
Remaining public calls, native ABI/concurrency, complete artifacts/provenance,
K02–K05 and standards/MISRA findings remain open.
**Stage decision: no grammar expansion.**

### Repeated initialization protocols: 2026-09-14

The new reference trace composes accepted/rejected Float64 accesses, entry,
exit and reset without adding source syntax or changing the emitted runtime.
The focused review rechecked [FMI 3.0.2 §§2.2.4, 2.3.1 and 2.3.2](https://fmi-standard.org/docs/3.0.2/):
rejected outputs are undefined, error stops ordinary simulation, reset restores
defaults before reinitialization, and pre-entry queries concern start values.
The protocol follows those distinctions and retains the existing guards.

Each actual exit heap determines a unique source Real IVP; repeated failed
attempts and returning logger effects retain the storage needed to try again.
The logger's universal frame protects instances, reservations and selected
caller storage. The progress theorem also retains an actual blocked-call
prefix when the modeled logger has no return. This is a finite initialization
subprotocol, not the complete FMI state machine or an all-public-call theorem.
The scalar reference state does not admit array source models; buffer counts
describe batched host transfers only.

MLS 3.7 source admission, Real/default initialization and diagnostics are
unchanged. The eFMI Beta 1 GALEC, Production C, mappings and artifact contracts
are unchanged. Cross-standard initialization, complete artifacts/provenance,
native C/ABI correspondence and MISRA findings remain open.

Thirty-five roots passed the FMI/compiler package gate on 970 unchanged inputs
in `build/c-factory/initialization-protocol-package-v1.log`; the accompanying
review records all roots from the existing unquoted ProofAudit output. The
axiom whitelist is unchanged. Earlier full-artifact evidence remains distinct:
the local 869-input gate and successful GitHub run `34853259941` for the previous checkpoint.
The new source-bound factory/protocol/simulation/release composition is still
required. **Stage decision: no grammar expansion.**

### Rejected Float64 calls and recovery initialization: 2026-09-14

This derived-proof increment retains the same EBNF, admitted source profile,
runtime policy, emitted members, metadata and mandatory artifact propositions.
The existing MLS 3.7 initialization interpretation and eFMI Beta 1
Algorithm/Production Code evidence remain unchanged, including open findings.

The focused review rechecked [FMI 3.0.2 §2.2.4 and §2.3.1](https://fmi-standard.org/docs/3.0.2/):
Error outputs are undefined, ordinary simulation cannot continue after Error,
reset is a permitted recovery path, and other instances must remain unaffected.
Reset restores model defaults before a new initialization. The new proofs
follow that policy: rejected accessor outputs are not source observations,
the error-mode write precedes logging, and modeled returning branches preserve
other instances/reservations under the explicit universal callback frame.

Raw typed transfers include every IEEE input encoding. Early lifecycle/array
guards add no input-read premise. The existing validation predicates and
non-finite rejection policy are reused, not inferred from the new host data.
Reset then supplies defaults and recovery storage; subsequent accepted writes
and queries before/during initialization determine a new unique source IVP.
Source-bound accessor function contracts and one table/pool supply execution.
The recovery continuation consumes the invariant proved for each actual
completed rejection, not caller-supplied future buffers or successful results.

Thirty-one new roots and affected existing roots passed the FMI/compiler
package gate on 963 unchanged inputs in
`build/c-factory/float64-rejection-package-v2.log`. The axiom whitelist is
unchanged. The separate 869-input local full gate retains unchanged semantics,
emission, mandatory contracts and boundary-test evidence. GitHub run
`34848939187` passed the full gate for the previous checkpoint, a distinct earlier revision;
no full-gate pass for this increment is claimed.

Created initialization and repeating mixed histories still need these new
operations composed with further recovery failures, simulation and release.
Original valid instance/reset storage, native pointers/ABI, concurrent ownership
and whole-artifact/provenance correspondence remain explicit or open boundaries.
Existing MLS/eFMI/MISRA findings and K02–K05 carry forward.
**Stage decision: no grammar expansion.**

### Initialization access followed by mixed ME execution: 2026-09-14

This derived-proof increment changes no EBNF, admitted source profile, runtime
policy, emitted member, metadata capability or mandatory artifact proposition.
The existing MLS 3.7 initialization interpretation and eFMI Beta 1
Algorithm/Production Code evidence are unchanged, including their open findings.

The existing FMI 3.0.2 variable-access and initialization correspondence
(§2.2.7.2 and §§2.3.2–2.3.3) now composes with the reviewed ME numerical,
event/continuous control, rejected-operation and reset histories. The actual
post-write exit heap supplies the selected state, Event Mode and initial event
iteration, start clock, stop bound, caller buffers and factory logger settings.
The original source and prepared program supply the access and ME contracts.

Every completed raw history retains source derivative observations and the
actual source initialization of each reset checkpoint. Mode-appropriate release
restores original ownership. Suppressed, missing and enabled logging retain the
existing modeled branches and explicit callback frame; no callback return is
assumed. Importer trial-state writes do not establish a solution of the original
IVP. Later resets still use contiguous reset/enter/exit and the Solve default.
The prior status/callback/reset/release review applies to unchanged policy.

Six new roots and affected existing CS roots passed the FMI/compiler package
gate on 955 unchanged inputs in
`build/c-factory/initialization-me-run-package-v2.log`. A missing direct import
found by the first package attempt was corrected before this passing run.
The axiom whitelist is unchanged; no tests were added. Existing semantics,
emitters, mandatory contracts and boundary tests retain the distinct 869-input
local full-gate evidence, not a new full-gate pass for these additions.

Rejected initialization accesses, access interleavings at later restarts,
remaining public calls, concurrent/native correspondence and whole-artifact
composition remain open. Existing MLS/eFMI and MISRA findings carry forward.
K02–K05 are not closed. **Stage decision: no grammar expansion.**

### Initialization access followed by mixed CS execution: 2026-09-14

This derived-proof increment retains the same EBNF, source profile, runtime
policy, metadata, emitted members and mandatory artifact propositions. The
existing MLS 3.7 initialization/Solve semantics and eFMI Beta 1 evidence are
unchanged; their open cross-standard findings remain open.

The FMI 3.0.2 correspondence now connects accepted initialization accesses
(§2.2.7.2 and §§2.3.2–2.3.3) to the existing CS step/reset/error histories.
The selected post-write state becomes the run seed. The prior status, callback
and reset/release review (§§2.2.1, 2.2.4 and 2.3.1) applies to unchanged policy.
Suppressed and callback-enabled histories share the actual source, prepared
table/pool and original storage. Completed scripts derive status equality,
source samples with the existing numerical/clock error bound, and release of
the original ownership. Successful per-call outputs remain in the reused trace
certificates. A callback return is not assumed; the universal external frame
and modeled blocked alternative remain explicit.

Later reset/reinitialization still uses the existing contiguous three-call
protocol and Solve default. Initialization-access rejection/recovery, ME
continuation, accesses during later restarts and other public interactions
remain open. No native callback/ABI, concurrent ownership, whole FMI/eFMI or
MISRA conclusion follows from this composition.

The ten new roots and strengthened creation root passed the FMI/compiler
package gate on 951 unchanged inputs in
`build/c-factory/initialization-cs-run-package-v1.log`. The axiom whitelist is
unchanged. Existing semantics, emission, mandatory artifact propositions and
boundary tests retain the earlier 869-input local full gate. GitHub run
`34842923078` passed the full gate for the previous checkpoint; it is a distinct revision.
No new full-gate pass is claimed for these additions. K02–K05 remain open.
**Stage decision: no grammar expansion.**

### Creation, initialization accesses and release: 2026-09-14

This is a derived-proof continuation of the same unit-stage profile. No EBNF,
runtime policy, generated member, capability flag or mandatory artifact
proposition changes. The existing MLS 3.7 initialization interpretation and
eFMI Beta 1 Algorithm/Production Code evidence remain scoped as before.

The existing FMI 3.0.2 variable-access and initialization correspondence
(§2.2.7.2 and §§2.3.2–2.3.3) now begins at actual source-bound creation.
Original caller memory supplies all later access buffers. Completed scripts
derive the raw observations and source IVP from the post-write exit state.
The same actual runtime supplies termination/release; the proof restores the
original owner map. Atomic preservation follows from the ordinary checked-store
semantics without extra reservation-block separation for caller buffers.
This is a sequential modeled lifetime, not concurrent/native correspondence.

The CS handoff retains the selected state, start time, stop bound and reusable
step-output storage. Later simulation must use this overridden seed; its
composition remains open, as do rejected initialization accesses and their
logging/recovery interactions. No full FMI/eFMI/MISRA conclusion follows.

All 15 added roots and affected existing roots passed the C/FMI/compiler package
gate on 947 unchanged inputs in `build/c-factory/created-access-package-v1.log`.
The axiom whitelist is unchanged. The earlier 869-input full gate continues to
cover the unchanged semantics, emitters, mandatory artifact propositions and
boundary tests; no new full-gate pass is claimed. K02–K05 and the existing MLS,
eFMI and MISRA findings remain open. **Stage decision: no grammar expansion.**

### Accepted initialization access histories: 2026-09-14

This derived-proof increment preserves source admission, runtime policy, emitted
members and mandatory artifact propositions. It composes existing Float64 and
initialization behavior in the same actual compiled adapter/table/pool and binds
the selected source IVP to the actual state at exit for both ME and CS.

| Focused FMI 3.0.2 clauses | Evidence and remaining boundary |
| --- | --- |
| [§2.2.7.2](https://fmi-standard.org/docs/3.0.2/), variable access | Arbitrary represented scalar-reference batches, including empty/mixed/repeated reads and ordered finite state writes, use typed original caller storage. Shapes belong to access batches; no array source profile is admitted. |
| [§§2.3.2–2.3.3](https://fmi-standard.org/docs/3.0.2/), initialization | Before entry, reads select the state start value; time/equation queries are admitted during initialization. Intervening writes determine the finite state used at actual exit. Entry/exit and all intermediate access calls are constructed, with a unique source Real IVP and retained clock storage. |
| [§§2.2.4 and 2.4.7](https://fmi-standard.org/docs/3.0.2/), status and metadata | Actual raw events/statuses/readback are determined by the certificate, rather than assumed in the execution relation. Numeric references and writable-state metadata remain tied to the compiled source. Rejected accesses and their logging/recovery composition remain open. |

The history theorem begins with an original valid instance and disjoint caller
buffers. Creation must establish these premises before the next composed lifetime
claim. The proof frames other cells outside the precise buffer ranges and changed
initialization/state fields, but does not establish native layout, pointer/ABI,
concurrency or whole-standard correspondence. Later simulation and release must
use the newly selected IVP rather than the pre-override seed.

The final certificate also retains exact named-field equality before entry
and at exit. This carries stop-time settings and instance metadata into later
simulation/lifetime proofs without assuming their values in a future heap.

All 41 roots passed the FMI/compiler package gate on 942 unchanged inputs in
`build/c-factory/initialization-access-package-v2.log`; the axiom whitelist and
earlier roots are unchanged. The separate 869-input full gate retains evidence
for unchanged semantics, emission, mandatory contracts and tests. No new full-gate
pass is claimed. MLS 3.7, eFMI Beta 1, MISRA and K02–K05 findings carry forward.
**Stage decision: open; no grammar expansion.**

### Initialization exit and caller-buffer preparation: 2026-09-14

This derived-proof increment changes no source admission, runtime policy,
emitted member or mandatory artifact contract. Independent initialization exit
in the shared runtime and typed caller-buffer writes prepare the composition
required by FMI 3.0.2 §§2.3.2–2.3.3. Original writable storage establishes the
host transfers; successful calls or populated future buffers are not premises
of those transfer proofs. Actual interleaved histories and their selected source
IVP at exit remain open.

The focused lifecycle review rechecked the existing Float64 setter policy
against [FMI 3.0.2 §§2.3.5 and 3.2.1](https://fmi-standard.org/docs/3.0.2/):
Event Mode explicitly permits continuous states with `reinit=false`, and
Continuous-Time Mode permits continuous-state writes. The existing metadata
contract establishes the former property. This supports retaining the guard;
it does not resolve all phase-specific or whole-standard correspondence.

Six added roots passed the C/FMI/compiler package gate on 937 unchanged inputs
in `build/c-factory/initialization-prerequisites-package-v1.log`. The original
axiom whitelist and earlier roots are unchanged. The separate 869-input full
artifact gate remains evidence for unchanged semantics, emission, mandatory
contracts and tests; no new full-gate pass is claimed. MLS 3.7, eFMI Beta 1,
MISRA and K02–K05 findings carry forward. **Stage decision: open; no grammar
expansion.**

### Float64 getter and common accessor runtime: 2026-09-14

This derived follow-up to the previous checkpoint preserves the existing getter behavior in
the shared static runtime. `float64_runtime_source` supplies both accessor
contracts from one source/numerical C/metadata/table/pool. No source grammar,
GALEC lowering, numerical semantics, runtime policy or emitted member changes.

| Focused FMI 3.0.2 clauses | Reviewed consequence and remaining boundary |
| --- | --- |
| [§2.2.7.2](https://fmi-standard.org/docs/3.0.2/), variable access | Existing scalar references justify matching counts. The proof retains arbitrary represented query batches and mixed/repeated time, state and derivative selections in request order. |
| [§§2.3.2–2.3.3](https://fmi-standard.org/docs/3.0.2/), initialization | Instantiated reads concern start values; initialization reads may evaluate equations. This bridge proves the existing access/value policy under represented storage. Full histories must establish phase-specific admissibility and actual initialized-state correspondence. |
| [§2.3.8](https://fmi-standard.org/docs/3.0.2/), termination | Queries after Error have debugging use. Returned derivative/state values do not establish continuation of the original source trajectory. |
| [§§2.2.4 and 2.4.7](https://fmi-standard.org/docs/3.0.2/), status and metadata | The same source-bound reference map, complete existing array/reference rejection paths and actual logging callbacks are retained. An axiom audit of these contracts does not establish whole-standard conformance. |

The helper calls are transported with the actual numerical kernel, type and
symbol bindings unchanged. Failure/empty prefixes omit the helper definitions,
so no new numerical execution/storage premise narrows the prior rejection
contract. Suppressed logging includes a missing logger. Enabled logging retains
every modeled return and the no-return alternative; protected instance/caller
frames and native callback behavior remain separate obligations.

Nine roots passed the FMI/compiler package gate on 935 unchanged inputs in
`build/c-factory/float64-environment-package-v1.log`. All earlier audit roots and
the whitelist are unchanged. The prior 869-input full gate and unchanged archive
hashes retain the earlier semantics/emission/mandatory-contract/test evidence;
no full-gate pass on this follow-up is claimed. MLS 3.7, eFMI Beta 1 and MISRA
findings carry forward. The initialization-history, remaining-API and K02–K05
obligations remain open. **Stage decision: open; no grammar expansion.**

### Float64 setter runtime bridge: 2026-09-14

This derived follow-up to the previous checkpoint reuses the existing batched setter proofs in
the shared static runtime. `float64_set_runtime_source` binds the same numerical
C, actual setter fragment, writable XML state, function-section tokenization and
prepared literal pool. No source/GALEC grammar, emission or admission policy changes.

| Focused FMI 3.0.2 clauses | Reviewed consequence and remaining boundary |
| --- | --- |
| [§2.2.7.2](https://fmi-standard.org/docs/3.0.2/), variable access | Scalar references justify equal reference/value counts for this profile. The existing proof retains batch validation, ordered writes, finite payload bits and rejection paths. No tensor-valued source variable is newly admitted. |
| [§§2.3.2–2.3.3](https://fmi-standard.org/docs/3.0.2/), instantiated/initialization states | Setting the nonconstant `initial="exact"` state is permitted in these modes. The bridge retains the existing lifecycle predicate; host writes must still compose with actual initialization exit. |
| [§2.4.7.5](https://fmi-standard.org/docs/3.0.2/), initialization metadata | The existing XML certificate identifies the same scalar state and exact-start policy used by the setter. This bridge does not close the shared MLS/eFMI initialization finding. |
| [§2.2.4](https://fmi-standard.org/docs/3.0.2/), status/errors | Suppressed logging has the exact Error/Terminated result. Enabled logging retains actual callback arguments, every modeled returning effect and the no-return alternative. Protected-instance callback frames and native execution remain separate. |

`internal_reaches_interface` is generic C proof infrastructure: checked internal
prefixes survive definition-table extension and agreeing interface bindings.
It does not require agreement for unrelated target functions. Setter failures
stop the transported prefix before invoking the real runtime helper and actual
logger; an external return or post-call heap is not assumed.

The ten new roots passed the C/FMI/compiler package gate on 933 unchanged inputs
in `build/c-factory/float64-set-environment-package-v1.log`. The axiom whitelist
and all prior audit roots are retained. Earlier semantics, emission, mandatory
contracts and tests retain the separate 869-input full artifact gate and unchanged
archives, with their input/member hashes rechecked. MLS 3.7, eFMI Beta 1 and
MISRA findings carry forward; this is a focused FMI bridge review. Getter and
initialization-history composition, remaining APIs and K02–K05 remain open.
**Stage decision: open; no grammar expansion or new full-gate claim.**

### Created mixed ME lifetime: 2026-09-14

This derived follow-up to the previous checkpoint connects original static creation storage
and ownership to initialization, the existing mixed ME success/error/reset
history and release. The actual factory chooses the handle, compiler-selected
finite Solve default and lease before the importer chooses its history. Initial caller buffers
come from the pre-creation heap, and logger configuration matches factory arguments.
Every completed branch derives later storage, slot metadata and owners.

The focused FMI 3.0.2 [§2.3.1](https://fmi-standard.org/docs/3.0.2/)
review rechecked reset/reinitialization and instance disposal against the existing
Error-to-Terminated policy. `LifecycleRelease.finish_correct` terminates an active
instance before releasing it, and releases an already Terminated instance directly.
The source-bound theorem restores the original owner map and preserves protected
other-instance/reservation memory. It does not authorize later calls on the freed
handle. No generated lifecycle or allocation policy changed.

The complete branching history retains every modeled callback alternative under
the universal external frame; a return or completed final heap is not presumed.
Arbitrary actual statuses, derivative queries and initialization checkpoints retain
the source consequences. Initial and restarted IVPs are stated at their actual
initialization checkpoints, separately from later importer trial-state writes.
Native callback execution, concurrent callers and complete ABI correspondence
remain external/open obligations.

All seven roots passed the FMI/compiler package gate on 930 unchanged inputs in
`build/c-factory/me-mixed-lifetime-package-v2.log`. The first attempt found a
missing direct import for an existing storage theorem; the corrected dependency
requires no proof-body change. Only the three status documents changed afterward.
Earlier semantics, emission, mandatory contracts and tests retain the separate
869-input full gate and unchanged archive hashes. MLS 3.7, CS/eFMI and MISRA
records carry forward. No new full-gate pass, grammar feature, test suite or full
standards closure is claimed. Float64 initialization interactions, remaining
public APIs and K02–K05 remain open.

### Mixed ME error/recovery histories: 2026-09-14

This derived follow-up to the previous checkpoint composes admitted numerical/control calls,
the represented rejection families and reset/reinitialization in one branching
ME history. Raw importer buffer stores, including non-finite IEEE inputs, are
proved from original writable storage. Rejection selection is independent of
target execution and future heaps. The artifact-bound compiler theorem retains
the same source, Solve product, function table, literals and numerical metadata.

The focused review rechecked FMI 3.0.2
[§2.2.4](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions),
[§2.3.1 and §2.3.8](https://fmi-standard.org/docs/3.0.2/): Error ends simulation
with undefined output arguments and transitions to Terminated; reset permits a
new initialization. Getters after Error are for debugging. The current proof
retains storage for recovery and source initialization at the actual restart
checkpoint, without validating failed outputs or treating later trial-state
writes/debugging queries as a continued source trajectory. No error policy or
generated byte changed. MLS 3.7, CS/eFMI and MISRA records carry forward unchanged.

The certificate retains each actual status, query result and callback invocation.
Every certified returning branch is executable, and every actual returning call
matches a branch. Enabled logging includes every modeled returning effect and
the no-return alternative under a universal external memory frame. Configuration
is fixed during these histories; suppressed and missing logger paths also compose.
The source theorem derives successful derivative equations and initialization/
uniqueness at every actual reset epoch from arbitrary raw target observations.

All 15 roots passed the FMI/compiler package gate on 927 unchanged inputs in
`build/c-factory/me-mixed-run-package-v1.log`. Only the three status documents
changed afterward. Earlier semantics, emission, mandatory contracts and tests
retain the separate 869-input full gate and unchanged archive hashes. No new
full-gate pass, grammar feature, test suite or standards closure is claimed.
Original typed non-null instance/caller storage and represented owners remain
premises. Complete creation/release composition, intervening initialization
accesses, remaining APIs, native callback correspondence and K02–K05 remain open.

### ME rejection and recovery contracts: 2026-09-14

This derived follow-up to the previous checkpoint gives the existing state/derivative, time,
event/continuous entry, completion and discrete-update rejection contracts one
request interface. It retains actual public arguments, guard priorities,
memory-bound time windows and diagnostics from one compiled table/pool. Both
suppressed and enabled-logging contracts retain their complete behavior clauses.
No generated failure policy changed.

The focused review rechecked pinned FMI 3.0.2
[§2.2.4](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions) and
[§2.3.1](https://fmi-standard.org/docs/3.0.2/). An Error leaves output arguments
undefined and ends the current simulation; illegal arguments/state-machine calls
require Error, and other instances remain unaffected. Reset can start recovery.
The existing emitter's transition to Terminated agrees with the specified Error
transition. This proof does not assign numerical validity to failed outputs or
authorize continued simulation before recovery.

`MEFailure.runtime_recovery` retains source compilation, numerical C,
function-section tokenization and derivative/state metadata. Arbitrary completed
target calls determine the Error status and callback invocation. A universal
external frame preserves FMU instance/reservation storage and caller buffers,
while allowing private callback effects. No callback return is presumed. The
existing modeled no-return alternative remains; native callback execution and
its correspondence to that model are separate boundaries.

Every returned branch derives continued writable storage and ownership, and
supplies complete reset/entry/exit calls. `Recovery.executed_source` connects the
three raw observed call results to source initialization and uniqueness at the
actual new checkpoint. Valid original non-null instance/caller storage, reset
permissions, represented owners and the selected rejection predicate remain
premises. Arbitrary mixed histories, their creation/release composition and
intervening initialization accesses are still open.

All 15 roots passed the FMI/compiler package gate on 923 unchanged inputs in
`build/c-factory/me-failure-recovery-package-v1.log`. Only the three status
documents changed afterward. Earlier semantics, emission, mandatory contracts
and tests retain the separate 869-input full gate and unchanged archives;
their source/archive hashes were rechecked. MLS 3.7, CS/eFMI and MISRA records
carry forward unchanged. No grammar feature, test suite, new full-gate pass or
standards closure is claimed. K02–K05 and the grammar gate remain open/blocked.

### Mixed ME numerical/reset lifetime: 2026-09-14

This derived follow-up to the previous checkpoint composes accepted ME operations and repeated
reset/reinitialization from actual creation through release. Writable recovery
storage survives every numerical operation, including inactive stop fields.
Each restart exposes three actual calls and records its actual post-initialization
heap. The raw execution relation supplies no expected status, output value,
source property or reference transition. The derived certificate determines
observations, final memory and all initialization checkpoints.

The focused review rechecked `fmi3Reset` in
[FMI 3.0.2 §2.3.1](https://fmi-standard.org/docs/3.0.2/): reset restores instance
defaults and initialization is required before another run. The proof reuses the
existing reset body and initialization contracts. Each restart selects the Solve
default, resets the clock/event protocol and re-enters Event Mode through both
initialization calls. At every recorded checkpoint, the compiler theorem proves
source Real initialization and uniqueness at the requested start time. Subsequent
trial-state writes do not establish a source IVP trajectory; derivative queries
continue to agree with the source equations.

The restart action describes contiguous reset→entry→exit calls, with each status
visible. Calls inserted between these stages, rejection and enabled-callback
histories, and remaining public interactions are still open. Original storage,
caller-buffer separation, admissible reference protocol and explicit external
bindings remain premises. Slot metadata and atomic ownership survive the complete
history; release restores the original owner map. Native ABI/concurrency and
the complete resource-lifetime obligation remain outside this increment.

All 17 roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-numerical-run-package-v1.log` on 919 unchanged inputs. Only
the three status documents changed afterward. Earlier semantics, emission,
mandatory contracts and tests retain the separate 869-input full gate and
unchanged archives, whose hashes were rechecked. MLS 3.7, CS/eFMI and MISRA
records carry forward unchanged. No grammar feature, new test suite, full-gate
pass or standards closure is claimed. K02–K05 and grammar expansion remain open
and blocked, respectively.

### Created ME numerical lifetime: 2026-09-14

This derived follow-up to the previous checkpoint connects actual creation, initialization,
accepted mixed control/state/derivative histories, termination and release in
one header/object/literal environment. Creation establishes the handle, source
default and lease before the importer chooses its history. Caller storage is
specified before creation; later writable cells, metadata and owners are
derived. Release restores the original owners and preserves unrelated memory.

The focused review rechecked pinned FMI 3.0.2
[§2.3.3](https://fmi-standard.org/docs/3.0.2/#state-initialization-mode),
[§2.3.4](https://fmi-standard.org/docs/3.0.2/#super-state-initialized) and the
[instance lifetime functions](https://fmi-standard.org/docs/3.0.2/#state-machine).
ME initialization exits into Event Mode; the admitted history preserves a mode
from which termination is allowed, then releases its instance. This result
does not close the full resource/native lifetime obligation or arbitrary
reset histories. Existing single-call failure and logging contracts remain.

`runtime_create_me_numerical_release` retains source compilation, numerical C,
function-section tokenization and derivative/state metadata. It derives actual
statuses and raw query values without assuming expected observations. Source
initialization is recorded at the initialized heap, before importer trial-state
updates; derivative queries retain source Real equation agreement. The result
does not certify an importer's integration method or native external code.

All eleven added roots passed the FMI/compiler package gate on 914 unchanged
inputs in `build/c-factory/me-numerical-lifecycle-package-v1.log`. Only the three
status documents changed afterward. Earlier semantics, emission, mandatory
contracts and tests retain the separate 869-input full gate and unchanged
archives; their source and archive hashes were rechecked. MLS 3.7, CS/eFMI and
MISRA clause records carry forward unchanged. No grammar feature, new test suite,
full-gate pass or standards closure is claimed. Mixed ME rejection/reset/callback
histories, remaining public calls, concurrency and complete artifact/native
correspondence keep K02–K05 and grammar expansion open and blocked, respectively.

### Mixed ME control and numerical histories: 2026-09-14

This derived follow-up to the previous checkpoint uses one actual function table/pool for
controls, continuous-state access and derivative queries. The history derives
typed importer buffer writes, subsequent storage, control outputs and read-only
diagnostic preservation. The actual execution relation records arbitrary
statuses, events and raw query values; expected control flags and finite/correct
query results occur only in the derived certificate and its consequences.

The focused review rechecked pinned FMI 3.0.2
[§3.2.1](https://fmi-standard.org/docs/3.0.2/#state-continuous-time-mode) for
time/state updates, ordered state/derivative access and integrator completion,
and retains the [§2.3.5](https://fmi-standard.org/docs/3.0.2/#state-event-mode)
event-iteration and [§2.4.8](https://fmi-standard.org/docs/3.0.2/#model-structure)
metadata records. Setters supply trial states; queries describe the prepared
equations. The proof does not certify the importer's integration algorithm or
identify arbitrary trial states with the source IVP solution. The unit RHS
remains finite and independent of time/state; existing failure policy is unchanged.

`runtime_me_numerical_history` binds source compilation, numerical C, function
tokenization and derivative/state metadata to the history. Observed statuses,
raw query results and final memory are derived for every completed actual script;
every derivative result corresponds to the source Real equation. Complete
single-call failures/logging remain in the prepared contracts. Initial typed
instance storage, a separate reusable float buffer and the control output bank
remain premises. Creation/reset/rejection/release composition, external callback
frames and native ABI/header correspondence remain open.

All 24 roots passed the FMI/compiler package gate on 910 unchanged inputs in
`build/c-factory/me-numerical-history-package-v1.log`. Only the three status
documents changed afterward. Earlier semantics, emission, mandatory contracts
and tests retain the separate 869-input full gate and unchanged archives;
their source hashes and retained archive hashes were rechecked. MLS 3.7 source
and initialization policy, CS/eFMI execution and generated C/GALEC/XML are
unchanged. Their clause records and all MISRA findings carry forward. No new
full-gate pass, grammar feature, test suite or conformance closure is claimed.
K02–K05 and the grammar gate remain open.

### ME control runtime bridge: 2026-09-14

This derived follow-up to the previous checkpoint transports the existing ME control contracts
to the explicit header/object/literal interface. The reviewed policy and actual
function bodies are unchanged. Reuse the clause/evidence records under
"Mandatory ME control histories" and "ME derivative queries and source
equations" below. MLS 3.7, FMI 3.0.2, eFMI Beta 1 and MISRA C:2025 findings
carry forward; no standard or initialization policy is reinterpreted here.

Successful/null event entry, continuous entry, completion and discrete update,
their rejected calls, and time rejection retain the existing contracts.
Suppressed logging includes absent loggers. Enabled callbacks retain every
modeled returning outcome and the no-return alternative, with immutable
diagnostics. Native callback behavior, ABI/header correspondence, caller storage
and ownership remain explicit boundaries. These individual calls do not prove
mixed importer state/control/derivative histories or a source IVP trajectory.

All 21 added roots passed the FMI/compiler package gate on 904 unchanged inputs
in `build/c-factory/me-controls-environment-package-v1.log`. Only the three
status documents changed afterward. Earlier semantics, emitters, mandatory
contracts and tests retain the separate 869-input full gate and archives;
their source hashes and both retained archive hashes were rechecked. No new
full-gate pass, source feature, test suite or compliance closure is claimed.
Prepared-pool and numerical-history composition remain next. K02–K05 and
the grammar gate remain open.

### ME derivative queries and source equations: 2026-09-14

This derived follow-up to the previous checkpoint supplies state-access and derivative-access
contracts from one actual function table and literal pool. The public derivative
getter follows the existing guard, actual `model_rhs`, numerical C kernel,
output write and status return in the header/object/literal runtime used by
creation and CS. The compiler consequence retains actual source compilation,
numerical C and derivative/state metadata, and derives exact finite Solve
agreement and the source Real equation through the existing IR theorems.

Applicable pinned FMI 3.0.2 clauses remain
[§2.3.3](https://fmi-standard.org/docs/3.0.2/#state-initialization-mode),
[§2.3.5](https://fmi-standard.org/docs/3.0.2/#state-event-mode),
[§2.3.8](https://fmi-standard.org/docs/3.0.2/#state-terminated),
[§3.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3GetContinuousStateDerivatives), and
[§2.4.8](https://fmi-standard.org/docs/3.0.2/#model-structure).
The immediately preceding focused review and the earlier derivative/state
clause records are reused for unchanged policy. The getter returns the ordered
continuous-state derivative; it does not advance a solver. The admitted unit
RHS is finite and state independent, so no numerical failure branch is added.
The bracketed Discard advice is not claimed as a generalized failure policy.
Retrieval following Error remains diagnostic, and arbitrary importer trial
states are not identified with a solution of the original IVP.

Null and both independently classified rejection reasons retain their existing
complete calls. Logging suppression covers a disabled flag or missing callback;
enabled logging retains every modeled returning effect and the no-return case.
Diagnostics on later heaps require the established read-only pool frame.
Native callbacks, caller storage/ownership and header/ABI correspondence remain
explicit boundaries. These call proofs do not close mixed ME histories.

The shared helper proof reuses the existing numerical scheduler with explicit
type and symbol bindings. No new source resolution, solver selection, shape
inference, scalarization or DAE work enters the backend. Production grammar,
source/initialization semantics, emitted C/GALEC/XML and archive behavior are
unchanged. The pinned MLS/eFMI/MISRA baselines and open findings carry forward.

The eleven new roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-derivative-environment-package-v1.log` on 903 unchanged inputs.
Only the three status documents changed afterward. Earlier semantics, emission,
mandatory contracts and tests retain the separate 869-input full gate and
archives in `build/c-factory/cs-contract-artifacts-v1/`. No new test suite or
full-gate pass is claimed. **Stage decision: open; no grammar expansion.**

### ME state access in the shared runtime: 2026-09-14

This derived follow-up to the previous checkpoint connects the existing complete state-access
contracts to the same header/object/literal interface used by actual creation
and lifecycle calls. The actual source-bound accessor fragments and pool are
retained. Arbitrary later heaps may be used: valid typed caller/instance storage
is explicit, and failures require the read-only diagnostic pool to survive.
Suppression covers both a disabled flag and a missing callback. Enabled logging
retains every modeled returning effect and its no-return alternative.

The focused review rechecked FMI 3.0.2
[§2.3.3](https://fmi-standard.org/docs/3.0.2/#state-initialization-mode),
[§2.3.5](https://fmi-standard.org/docs/3.0.2/#state-event-mode),
[§2.3.8](https://fmi-standard.org/docs/3.0.2/#state-terminated), and
[§3.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3SetContinuousStates).
The ME getter remains available in Initialization, Event, Continuous-Time and
Terminated modes; the setter supplies new states in Continuous-Time mode.
State ordering retains the existing XML/state metadata contract. A trial-state
setter copies the supplied value; it does not integrate or establish accuracy
of the importer's trajectory. Final retrieval after Error remains diagnostic.
The earlier finite-Real/fail-stop policy and its Error-versus-Discard review are
unchanged; this increment does not attribute that policy to new standard text.

Shared body-interface and complete failure-helper proofs are reused. No source
resolution, shape inference, scalarization, solver selection or DAE work is added
to the backend. Grammar, source/initialization semantics, emitted C, GALEC, XML
and packaging are unchanged. The pinned MLS/eFMI/MISRA baselines and all open
findings carry forward; native callback/ABI and concurrent-host obligations
remain separate. Complete ME state/derivative/control histories are still open.

All six added roots passed `lake build check-fmi3 check-compiler` in
`build/c-factory/me-state-environment-package-v1.log` on 900 unchanged inputs.
Only the three status documents changed afterward. The unchanged earlier
semantics, emission, mandatory contracts and tests retain the separate 869-input
full gate and archives in `build/c-factory/cs-contract-artifacts-v1/`.
No new test suite or full-gate pass is claimed.
**Stage decision: open; no grammar expansion.**

### Created callback-enabled CS lifetime and observed statuses: 2026-09-14

This derived follow-up to the previous checkpoint connects the actual factory and initialization
to callback-enabled mixed step/rejection/reset histories. Original available
storage supplies all created-state and lease premises. The branching contract
retains every modeled outcome; for every completed actual C script, its status
list is proved equal to the reference list and its source/numerical observation
and release ownership are derived. Termination/free follows the final mode and
restores the original owner map. Protected unrelated instance/reservation cells
are retained; private logger storage is allowed to change.

The prior focused FMI 3.0.2 review is reused for unchanged policy:
[§2.2.1, callback protocol](https://fmi-standard.org/docs/3.0.2/#requirements-for-implementations-of-the-c-api),
[§2.2.4, statuses](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions),
and [§2.3.1, creation/reset/release](https://fmi-standard.org/docs/3.0.2/#super-state-fmu-state-settable).
Expected statuses are now conclusions for completed histories rather than
premises. The universal external memory frame and existing returning-effect
model remain explicit; this does not prove native callback behavior or permit
log callback reentry. No callback return or eventual release is presumed for a
blocked history. No logging/category, source initialization or emitted policy
changed. Existing broader single-call contracts remain intact.

The FMI/compiler package gate passed in
`build/c-factory/cs-logged-lifetime-package-v1.log` with all 898 inputs unchanged
and three added roots. Only the three status documents changed afterward.
Earlier semantics, emission, mandatory contracts and tests retain the separate
869-input full gate and archives in `build/c-factory/cs-contract-artifacts-v1/`.
No new full-gate pass or example suite is claimed. The pinned MLS/eFMI/MISRA
baselines and findings remain open where previously open. Remaining public/ME
interactions, concurrency, artifact/native correspondence and the final standards
review are still required. **Stage decision: open; no grammar expansion.**

### Callback-enabled mixed CS histories: 2026-09-14

This derived follow-up to the previous checkpoint proves branching accepted/rejected step and
reset/reinitialization histories using the actual prepared adapter. Complete
call alternatives preserve callback symbols/arguments and all returning effects;
a callback with no modeled return retains the existing `wrong` alternative.
Every returned branch derives later storage, successful outputs and ownership.
An independently defined completed C-call script retains the final source IVP
and numerical/clock error bound. No successful callback is an initial premise.

Applicable FMI 3.0.2 clauses are
[§2.2.1, C-API requirements](https://fmi-standard.org/docs/3.0.2/#requirements-for-implementations-of-the-c-api),
[§2.2.4, status returns](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions),
and [§2.3.1, logging and reset](https://fmi-standard.org/docs/3.0.2/#super-state-fmu-state-settable).
The actual callback invocation retains the environment, status, category and
message arguments. The universal external frame protects the instance pool,
reservation block and caller outputs, while allowing private logger effects.
It is an integration contract, not a consequence of the FMI prose alone.
FMI prohibits log callbacks from calling back into the FMU; supporting such
reentry is not a new admitted requirement. Native protocol conformance,
divergence and floating-environment correspondence remain explicit boundaries.
Disabled/missing-logger histories and the broader single-call contracts remain
unchanged; no logging/category policy or metadata changed.

The FMI/compiler package gate passed in
`build/c-factory/cs-run-logging-package-v1.log` with 896 unchanged inputs and
11 added roots. Only the three status documents changed afterward. Earlier
semantics, emission, mandatory contracts and tests retain their separate
869-input full artifact gate and archives under
`build/c-factory/cs-contract-artifacts-v1/`; no new full-gate pass is claimed.
MLS/eFMI/MISRA findings remain unchanged. Creation/release composition for the
enabled-logging trace, remaining APIs, ME numerical histories and concurrency
still require work. **Stage decision: open; no grammar expansion.**

### Created mixed CS lifetime with logging suppressed: 2026-09-14

This derived follow-up to the previous checkpoint connects actual creation and initialization
to mixed CS steps/rejections/reset histories and final release. It derives the
selected handle and all later storage from available initial storage, preserves
successful outputs and the source/numerical invariant, and restores the original
owner map. The ordinary frame covers the complete lifetime outside the selected
instance, caller outputs and released reservation flag.

The focused review uses FMI 3.0.2
[§2.2.4, status returns](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions),
[§2.3.1, reset and release](https://fmi-standard.org/docs/3.0.2/#super-state-fmu-state-settable),
and [§2.3.8, Terminated](https://fmi-standard.org/docs/3.0.2/#state-terminated).
The final Step path calls Terminate before FreeInstance; a path already
Terminated by an error calls FreeInstance directly. Reset restores defaults and
initialization establishes the new run. Preserved stored values after an error
do not authorize continued simulation; this result adds no getter-call claim.
The existing broader single-call logging contracts remain intact.

All 16 added roots passed the FMI/compiler package gate in
`build/c-factory/cs-run-lifecycle-package-v1.log`, with 893 unchanged inputs.
Only the three status documents changed afterward. Earlier semantics,
emission, mandatory contracts and tests are unchanged, retaining the separate
869-input full gate and archives in `build/c-factory/cs-contract-artifacts-v1/`.
No new full-gate pass or example suite is claimed. This theorem assumes
suppressed logging, the explicit nearest-rounding/library profile and the
existing typed caller-buffer bank; callback effects and concurrent histories
remain open. Existing MLS/eFMI/MISRA findings are carried forward, not closed by
this scoped review. **Stage decision: open; no grammar expansion.**

### Mixed CS steps and recovery with logging suppressed: 2026-09-14

This derived-proof follow-up to the previous checkpoint adds 25 audit roots. An independent
reference relation tracks lifecycle mode, source initial value/time origin,
rounded communication time and cumulative solver duration within each run.
The actual-adapter theorem composes finite accepted/rejected step histories
and repeated reset/reinitialization. It derives later writable state/caller
storage, retains all four successful step outputs and preserves read-only
diagnostics, logger configuration, slot metadata and atomic reservations.
Each stored sample retains the source IVP and numerical/clock error bound.

Applicable FMI 3.0.2 clauses remain
[§2.2.4, status returns](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions),
[§2.3.1, reset](https://fmi-standard.org/docs/3.0.2/#fmi3Reset) and
[§4.2.1, Step Mode](https://fmi-standard.org/docs/3.0.2/#step-mode).
The observation relation specifies successful outputs explicitly. Error and
discard outputs have no standards-level value requirement; reset restores
defaults before reinitialization. Review strengthened the initial history draft
to make successful outputs explicit before accepting this checkpoint.
No emitted behavior, capability or admission policy changed.

The final package gate passed in `build/c-factory/cs-run-package-v2.log` with
all 890 inputs unchanged. Only the three status documents changed afterward.
The earlier 869-input full gate and retained archives under
`build/c-factory/cs-contract-artifacts-v1/` remain evidence for unchanged
semantics, emission, mandatory contracts and existing tests. No new full-gate
pass or test suite is claimed for this derived increment.

This trace uses suppressed logging, an explicit nearest-rounding library
profile and a fixed typed output-buffer bank or omitted pointers. The broader
single-call contracts are retained. Callback-enabled mixed histories,
creation/release composition, ME numerical interactions, concurrency and native
profile/layout remain open. Existing MLS/eFMI/MISRA findings and pinned baselines
are carried forward; this scoped FMI follow-up is not a repeated full review.
**Stage decision: open; no grammar expansion.**

### CS rejection, reset and reinitialization: 2026-09-14

This derived-proof follow-up to the previous checkpoint adds 16 audit roots. The actual
required CS rejection contract now composes with reset and both initialization
calls in one header/object/literal environment. Original writable storage
supplies the later storage; the result retains the Solve default and a new
source IVP at the requested start time. Suppressed logging preserves atomic
reservations, original ownership and slot metadata. Enabled logging retains
all modeled outcomes; each returning callback permits the recovery consequence
only if it preserves the instance record. Global callback lease frames and
reentry are not discharged by that premise.

Applicable clauses are FMI 3.0.2
[§2.2.4, status returns](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions)
and [§2.3.1, reset](https://fmi-standard.org/docs/3.0.2/#fmi3Reset).
Error permits recovery by reset; discard preserves the FMU state. Reset restores
defaults and requires initialization before another run. The new proofs
strengthen correspondence for these existing policies. They change no emitted
transition, logging policy, source admission, capability or initialization
choice, and do not close whole-standard correspondence.

The FMI/compiler package gate passed in
`build/c-factory/cs-recovery-package-v1.log` with all 885 inputs unchanged.
Only the three status documents changed after acceptance. Earlier semantics,
emission, mandatory contracts and existing tests are unchanged; the 869-input
full gate and archives under `build/c-factory/cs-contract-artifacts-v1/` retain
their original scope. No new full-gate pass or test suite is claimed.

The pinned MLS/eFMI/MISRA baselines and findings remain open where previously
open; this is a scoped FMI recovery follow-up, not a repeated full review.
Complete mixed simulation histories, ME numerical interactions, callbacks,
concurrent ownership, native profile/layout, cross-standard initialization and
coding-guideline correspondence still block expansion. **Stage decision: open.**

### Actual creation through accepted CS lifetime: 2026-09-14

This derived-proof follow-up to the previous checkpoint adds nine audit roots. The actual
CS factory, source identity validation, initialization, accepted numerical
history, termination and release now share one prepared program and explicit
header/object/literal interface. Available static storage supplies the handle,
finite Solve default, writable state/caller cells and lease. Release restores
the original owner map. The initialized source solution, numerical/clock error,
bounded reservation trace and memory frames are retained. The former
initialized-lifetime theorem keeps its statement and reuses the shared backend
composition. No created or initialized heap is an input premise.

The FMI/compiler package gate passed in
`build/c-factory/cs-created-lifetime-package-v1.log` with all 881 inputs
unchanged. Only the three status documents changed after acceptance. Earlier
semantic definitions, emitted products, mandatory artifact contracts and
existing tests are unchanged; the preceding 869-input full gate and archives
under `build/c-factory/cs-contract-artifacts-v1/` remain their evidence. No new
full-gate pass or test suite is claimed.

This strengthens the proof correspondence for the already reviewed FMI
instantiation, initialization, Step Mode, termination and release profile.
It changes no admission policy, capability or emitted lifecycle transition.
The pinned baselines and existing MLS/FMI/eFMI/MISRA findings are retained.
Mixed error/discard/logging/reset histories, ME numerical interactions,
callback effects/reentry, concurrent ownership, native header/layout and
cross-standard initialization/coding-guideline correspondence remain open.
Neither this composed theorem nor the earlier artifact checks establish
whole-standard conformance. **Stage decision: open; no grammar expansion.**

### Mandatory CS calls and initialized CS lifetimes: 2026-09-14

This increment follows the previous checkpoint. Eighteen added roots make the complete CS
step-call contract mandatory for actual adapter certification. It covers all
eight raw admission cases and suppressed/supplied logging in the prepared
static interface. The required full artifact gate passed in
`build/c-factory/cs-contract-full-gate-v1.log`, with all 869 inputs unchanged.
The retained FMU/eFMU and comparisons are under
`build/c-factory/cs-contract-artifacts-v1/`. All FMU member contents match the
preceding artifacts; the eFMU differs only in three manifests' fresh generation
identities and dependent references/checksums. The existing archive, importer,
native C and rejection checks passed. No new test suite was introduced.

Twenty-four further derived roots compose actual initialization, any finite
accepted CS request sequence, termination and release from original instance
storage and ownership. The source consequence retains the initialized Real
solution, exact finite Solve state, rounded communication clock and separate
numerical/clock error terms. The FMI/compiler package audit passed in
`build/c-factory/cs-history-package-v1.log`, with all 877 inputs unchanged.
The mandatory contracts, earlier semantics and emission are unchanged by this
follow-up; its package evidence is distinct from the retained 869-input full
artifact gate. Only the three status documents changed after package acceptance.

Applicable pinned clauses are
[FMI 3.0.2 §2.2.6](https://fmi-standard.org/docs/3.0.2/#advancing-time),
[initialization](https://fmi-standard.org/docs/3.0.2/#fmi3EnterInitializationMode),
[§4.2.1, `fmi3DoStep`](https://fmi-standard.org/docs/3.0.2/#fmi3DoStep), and
[§2.2.4, status returns](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions).
The accepted reference starts at the initialization time and requires positive
admitted durations, a progressing reported clock and the optional stop bound.
Keeping solver duration distinct from reported time accommodates the specified
possibility of a reported time differing from the requested endpoint. Error
and Discard output values remain implementation evidence, not importer promises.
The logged single-call contract retains all modeled callback outcomes; the
accepted sequential lifetime has no interspersed logging or rejected calls.

This is a scoped follow-up, not a new complete MLS/eFMI/MISRA review. Source
grammar and emitted products are unchanged. Creation composed with the CS
lifetime, mixed error/reset histories, callback frames/reentry, concurrent
ownership, native headers/layout and existing MLS/eFMI initialization and
coding-guideline findings remain open. The formal call contract establishes
the authored execution model; it does not by itself establish native ABI or
whole-standard correspondence. **Stage decision: open; no grammar expansion.**

### Complete CS discard calls and raw-input partition: 2026-09-14

This derived-proof increment follows the previous checkpoint. Sixteen added roots cover
complete public discard calls and exhaustive, disjoint raw-input admission.
The core/C/FMI/eFMI/compiler package audit passed in
`build/c-factory/cs-cases-package-v1.log` with all 863 inputs unchanged. The
preceding discard-only package audit passed with 861 unchanged inputs. Only
three status documents changed afterward. Earlier declarations, emission,
mandatory artifact contracts and tests are unchanged; the preceding 855-input
full artifact gate remains their evidence. No new full-gate pass is claimed.

[FMI 3.0.2, `fmi3DoStep`](https://fmi-standard.org/docs/3.0.2/#fmi3DoStep)
permits Discard with the FMU's previous state retained and leaves the output
arguments undefined. The checked implementation initializes those arguments
while preserving all instance cells before any logger call. Suppressed logging
therefore returns Discard with the prior instance intact. The logged theorem
represents every foreign callback outcome; deriving the same preservation
after logging requires the external callback's frame. It does not verify native
callback internals or reentry. Both discard paths follow the stop check, and
neither invokes the solver. No numerical-progress or output-value promise is
assigned to an importer after Discard.

Raw admission covers all bit patterns and preserves signed-zero encodings.
This supplies a coverage prerequisite for the mandatory public-CS contract;
it does not independently establish the policy's conformance. That contract,
repeated histories, shared initialization, native header/ABI correspondence and
existing MLS/eFMI/MISRA findings remain open. **Stage decision: open; no grammar
expansion.**

### Complete CS rounding and stop-limit errors: 2026-09-13

This derived-proof increment follows the previous checkpoint. Eleven new roots compose
public output/input admission, ordinary rounding observations and stop-limit
rejection with the actual error helper. Suppressed logging and every represented
callback outcome are retained. The core/C/FMI/eFMI/compiler package audit passed
in `build/c-factory/cs-failures-package-v1.log` with all 860 inputs unchanged;
only three status documents changed afterward. Every earlier declaration,
emitter, mandatory contract and test is retained. The preceding 855-input full
artifact evidence still applies; the full gate was not rerun for this increment.

[FMI 3.0.2, `fmi3EnterInitializationMode`](https://fmi-standard.org/docs/3.0.2/#fmi3EnterInitializationMode)
requires Error when the importer attempts to compute beyond a defined stop
value. The new stop-call theorem includes the rounded binary64 sum and overflow,
and preserves the stop check before discard checks. The rounding-call theorem
uses the explicit header and ordinary-library profile already recorded below;
it does not certify the native floating environment, flags or traps.
[§2.2.4](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions) governs
Error and logging. The proof retains exact implementation output writes while
keeping Error outputs undefined to an importer. Native callback execution,
reentry and instance isolation still need integration evidence. The new public
calls are not yet mandatory in the actual-adapter certificate. Discard and
repeated histories remain open; existing MLS/eFMI initialization, coding-guideline,
MISRA and native-header/ABI findings are unchanged. **Stage decision: open;
no grammar expansion.**

### Complete CS argument-error calls: 2026-09-13

This proof-only increment follows the previous checkpoint. Twelve added roots cover the
complete missing-output and raw-numerical-input rejection calls, including
suppressed logging and every represented callback outcome. Shared direct-prefix
bridges also simplify existing error/lifecycle proofs without changing their
propositions. The FMI/compiler package audit passed in
`build/c-factory/cs-arguments-package-v1.log` with all 859 inputs unchanged;
only three status documents changed afterward. Emission, earlier semantics,
mandatory contracts and tests retain the preceding 855-input full artifact
evidence; the full gate was not rerun for these derived proofs.

[FMI 3.0.2 §2.2.4](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions)
requires Error when illegal arguments are detected and leaves returned output
arguments undefined on Error. The proofs retain the implementation's exact
output writes without turning those values into an importer guarantee. Missing
pointers cause rejection before output access; invalid numerical inputs cause
rejection after output initialization. [§4.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3DoStep)
defines the communication-point and positive-step arguments. All raw encodings
are covered by the existing finite-value admission predicate. Writable caller
storage remains explicit, and enabled callbacks retain their modeled effects;
native validity, reentry and other-instance isolation still need integration
evidence. The mandatory CS artifact contract and rounding/stop/discard/history
proofs remain open. Existing MLS/eFMI initialization, coding-guideline, MISRA
and native-header/ABI findings are unchanged. **Stage decision: open; no grammar
expansion.**

### Explicit error contexts and complete CS lifecycle rejection: 2026-09-13

This proof increment follows the previous checkpoint. Checked local interface requirements
allow the existing error-helper proofs to serve both static objects and an
explicit rounding header. Fourteen existing roots are generalized; sixteen
caller sites retain their public contract statements. Eleven added roots
include complete CS lifecycle rejection with enabled/suppressed logging and
all represented foreign outcomes. The FMI/compiler package audit passed in
`build/c-factory/cs-errors-package-v1.log` with all 858 inputs unchanged; only
three status documents changed afterward. Emitters, earlier semantics,
mandatory artifact contracts and tests remain unchanged, retaining the
preceding 855-input full-gate artifact evidence.

[FMI 3.0.2 §2.2.4](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions)
requires Error for forbidden lifecycle calls and respects logging settings;
[§2.3.1](https://fmi-standard.org/docs/3.0.2/#FMUStateSettable) routes Error to
Terminated. The new call proofs derive the actual mode write and Error return
for the represented forbidden kinds/modes. Output storage is unnecessary:
rejection precedes every output access. Enabled logging retains the represented
callback's effects and traces; it does not certify native callback execution,
reentry or cross-instance ownership. Those assumptions need the remaining
history and integration evidence.

The public CS results are not yet mandatory in the actual-adapter certificate.
Other argument/rounding/stop/discard paths and repeated histories remain open.
Existing MLS/eFMI initialization, coding-guideline, MISRA and native-header/ABI
findings are unchanged. **Stage decision: open; no grammar expansion.**

### Public CS entry and raw-input classification: 2026-09-13

This derived-proof increment follows the previous checkpoint. Sixteen new `StepEntry` roots
cover typed public arguments, every raw point/step input encoding, lifecycle
and output setup, complete successful/null calls, output values and memory
frames. They passed the FMI/compiler package audit in
`build/c-factory/cs-entry-package-v1.log` with all 856 inputs unchanged; only
three status documents changed afterward. Earlier semantics, emitters and
mandatory artifact contracts are unchanged, retaining the preceding full-gate
artifact evidence. No grammar or new test suite is introduced.

[FMI 3.0.2 §4.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3DoStep) defines
positive communication steps and the returned time and event/termination
outputs. The new proof derives the rounded returned time and false output
flags for the current event-free unit profile. The guard compares finite
numerical point/clock values, including both signed zeros. It reaches the
actual rejection statement for invalid raw inputs after the existing output
initialization. The remaining failure/logging and discard-state-restoration
proofs are still required; this increment does not establish them.

The complete success theorem uses an explicit typed-memory and external-library
profile. Native headers/ABI, floating flags/traps, surrounding callback behavior
and repeated clock/source histories remain outside this result. The new public
call theorem is not yet required by the actual-adapter certificate. Existing
MLS/eFMI initialization, coding-guideline and MISRA findings are unchanged.
**Stage decision: open; no grammar expansion.**

### Ordinary CS calls and guarded numerical execution: 2026-09-13

This increment follows the previous checkpoint and changes the emitted CS body. Rounding
and floor calls now initialize explicit function-scope locals. The guard
destination proofs cover all supplied int32 rounding observations and every
finite clock/duration operand, including overflowing sums. The successful
suffix theorem derives its solver count and exact final writes. Eight new
audit roots passed the core/C/FMI/eFMI/compiler package audit in
`build/c-factory/cs-ordinary-package-v1.log`, with all 855 inputs unchanged.
The renewed full artifact gate passed in
`build/c-factory/cs-ordinary-full-gate-v1.log`, with the same 855 inputs
unchanged and all 13 existing native FMI checks passing. Both archives and
exact member comparisons are retained under
`build/c-factory/cs-ordinary-artifacts-v1/`. The FMI adapter source and binary
changed; numerical C, headers, FMI metadata, GALEC and eFMI Production C are
unchanged. The eFMI manifests differ only in fresh generation identities and
dependent checksums. Only the three status documents changed after the gate.
No grammar or Solve policy change is made.

[C11 §6.5.13–14](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)
requires short-circuit evaluation: the normalization keeps floor after the
finite/progress checks and keeps the optional stop rejection before discard.
The earlier header/floor reviews still apply. The theorem describes the new
actual statement sequence; no semantic equivalence to an unsupported nested
ordinary-call expression is assumed. Native control/flags, header/library
correspondence and excess-precision behavior remain separate obligations.

[FMI 3.0.2 §4.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3DoStep) requires a
positive communication step and defines the requested next communication
point. The suffix proof retains the finite rounded communication clock and
separate unit-grid count. It does not yet compose public output initialization,
input/lifecycle rejection, all status/logging outcomes or repeated-step
histories. Existing MLS/eFMI initialization and MISRA findings are unchanged.
**Stage decision: open; no grammar expansion.**

### Explicit rounding header and shared execution environment: 2026-09-13

This derived-proof increment follows the previous checkpoint. Fourteen C/FMI/compiler roots
supply a header-parametric rounding binding, the ordinary observation/branch
prefix, reusable local body-call transfer, and actual-adapter consequences for
ME quiet-time calls, their history/source frame and the numerical helper.
The same definition table and literal pool serve every header value. The
core/C/FMI/eFMI/compiler package audit passed in
`build/c-factory/rounding-environment-package-gate-v1.log`, with all 854 inputs
unchanged. Only the three status documents changed afterward; the full gate
was not rerun for these derived proofs, retaining the preceding 847-input
full artifact evidence. Existing definitions, emitters and mandatory artifact
contracts remain unchanged; no new source case is admitted.

[C11 §7.6 paragraph 8 and §7.6.3.1](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)
require distinct nonnegative supported rounding-direction macro values and
allow a negative `fegetround` failure result. The proof header selects the
existing int32 target profile and supplies a bounded value explicitly; it does
not assume that the macro is zero. Negative observations cannot equal this
nearest-mode value. Reading/validating the native header and relating the
ordinary external binding to the native environment remain separate work.

The value-only guard theorem does not establish mode stability, floating flags,
traps or restoration required by the applicable C/FMI environment contract.
It describes the proposed ordinary-call form; generated `doStep` still uses
nested calls, so actual guarded-body integration remains open. ME errors and
complete histories still need transfer to the extended environment. No MLS,
eFMI or MISRA finding is closed. **Stage decision: open; no grammar expansion.**

### CS duration and ordinary call continuations: 2026-09-13

This derived-proof increment follows the previous checkpoint. Fourteen shared C/FMI roots
connect ordinary floor/rounding calls to fresh local declarations, mathematical
duration admission to the actual comparisons and bounded solver count, and the
actual solver/time/output suffix to its nested execution and memory frame.
The C count conversion is derived from exact duration. An admitted duration
implies finite clock addition, while the separate progress guard remains
necessary. The core/C/FMI/eFMI/compiler package audit passed in
`build/c-factory/cs-duration-package-gate-v2.log` with all 850 inputs unchanged.
Only the three status documents changed afterward; the full gate was not
rerun for these derived proofs.

The existing C11 cast, floor and rounding-observation review applies. Neither
these proofs nor the unchanged prior artifact gate establish target-header
bindings, floating-environment correspondence or a complete public CS call.
Initial output setup, every rejection/logging path and repeated-step histories
remain open. No MLS/eFMI syntax, initialization, solver policy or emitted member
changes; the preceding 847-input full gate supplies unchanged artifact evidence.
No standards or MISRA finding is closed. **Stage decision: open.**

### Finite-operand addition overflow: 2026-09-13

This checkpoint follows the previous checkpoint. Shared C addition now represents overflow
from two finite operands as signed infinity. The independent Real result
relation retains strict finite bounds, nearest/even rounding and signed zero;
its two threshold ties overflow. Encoding/decoding, result correspondence,
infinity classification/comparison and member/register expression proofs add
21 audit roots. Earlier finite theorem statements and mandatory contracts are
retained. The core/C/FMI/eFMI/compiler package audit passed in
`build/c-factory/finite-addition-package-gate-v1.log` with all 847 inputs
unchanged. The renewed full artifact gate passed in
`build/c-factory/finite-addition-full-gate-v1.log`, also with all 847 inputs
unchanged. Both checked archives are retained under
`build/c-factory/finite-addition-artifacts-v1/`; exact comparisons preserve
C/header/GALEC and FMI XML bytes, permitting only fresh eFMI manifest identities
and their dependent checksums. The existing native FMI check passed
overflowing calls with and without a stop bound. Only the three status
documents changed after full acceptance.

The result model follows the current nearest-even binary64 profile and the
[C11 Annex F.3](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf)
mapping of addition to IEC 60559. Annex F.8.6/F.9.1 also requires attention to
floating status flags and control modes; these are outside this numerical
result relation. Native compiler/environment correspondence remains an
explicit review obligation. A result-bit theorem is not a proof of the
complete floating environment or all ISO C implementations.

[FMI 3.0.2 §2.2.1](https://fmi-standard.org/docs/3.0.2/#general-mechanisms)
requires restoration of changed thread settings before return or callbacks.
Retain the environment correspondence/restoration obligation in K03/K05;
distinguish operation status flags from control-setting changes during that
review. No restoration guarantee follows from the new value-only theorem.
Generated `fmi3DoStep` still adds before checking the step cap and keeps its
existing stop-error/discard ordering. The complete public proof must connect
the new overflow result to those actual guards, callbacks and output writes.

No MLS 3.7/eFMI Beta 1 syntax, initialization, lowering, solver policy or
generated member changes. No MISRA, FMI or other standards finding is closed.
**Stage decision: open; no grammar expansion.**

### CS math calls and numerical helper: 2026-09-13

This derived-proof increment follows the previous checkpoint. Five owning core/C/FMI/compiler
modules integrate finite floor, ordinary math-library call contracts, actual
`model_advance` execution and Solve duration/reported-time consequences.
The 27 new audit roots passed the core/C/FMI/eFMI/compiler package audit in
`build/c-factory/cs-prerequisites-package-gate-v1.log`, with all 845 inputs
unchanged. Earlier semantic definitions, emitters, mandatory
artifact contracts and audit roots are unchanged. The preceding 840-input
full gate remains the evidence for those unchanged artifacts; it was not
rerun for these derived proofs. Only these three status documents changed
after package acceptance. No new test suite was added.

The existing C11 §§7.6.3.1/7.12.9.2 mapping now has a computed result for every
finite floor argument and complete ordinary-call behaviors for the authored
library bindings. `fegetround` observes a supplied int32 mode; the native
library, target-header macro and fenv correspondence are still external.
FMI 3.0.2 stepping still needs guarded call integration, every status/output
path and communication-clock refinement. The helper theorem supplies actual
execution and its state frame, without assuming successful execution. The
source error at reported time includes the clock mismatch explicitly.

No MLS 3.7/eFMI Beta 1 syntax, initialization, lowering, solver policy or
generated member changes. No MISRA or other standards finding is closed.
**Stage decision: open; no grammar expansion.**

### Exact integer and Float64 conversions: 2026-09-13

This C-semantic checkpoint follows the previous checkpoint. It replaces integer `0`/`1`
special cases with an exact binary64 encoder for magnitudes below `2^53`, and
adds finite Float64→unsigned-size conversion with truncation and range checks.
The 32 core/C roots connect encoding fields, mathematical values, mathlib
floor/ceiling, nonfinite rejection and actual cast-expression evaluation.
The core/C/FMI/eFMI/compiler audit passed in
`build/c-factory/c-integer-package-gate-v3.log` with all 840 inputs unchanged.
The renewed full artifact gate passed in `build/c-factory/c-integer-full-gate-v1.log`,
also with all 840 inputs unchanged. Both checked archives are retained under
`build/c-factory/c-integer-artifacts-v1/`, with archive/member hashes and exact
comparisons beside them. C/header/GALEC and FMI XML match the ME checkpoint;
only the three eFMI generation identities and dependent references/checksums
changed. Only these three status documents changed after the full gate. All earlier
mandatory contracts and audit roots are retained; emitted C and grammar
are unchanged. Complete CS step execution is still open.

| Applicable obligation | Correspondence and boundary |
| --- | --- |
| [C11 N1570 §6.3.1.4](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), integer/real conversion | Exact integer encodings preserve the mathematical value throughout the stated range. Floating-to-size conversion uses truncation toward zero and representability; it does not use integer modulo for floating inputs. Other integer magnitudes remain outside this exact-conversion fragment. |
| C11 §§7.6.3.1/7.12.9.2, rounding environment and floor | The clauses were rechecked. The bounded-floor proof constructs a representable mathematical result; actual `fegetround`/`floor` calls and native bindings still require their contracts. The current CS body computes a sum before its step-cap rejection, so accepted-case arithmetic alone cannot cover all outcomes. |
| FMI 3.0.2 ME/CS | No interface, capability, initialization or numerical-step policy changes. Every earlier public-call proposition must remain valid under the extended conversion semantics. Repeated CS calls still require a relation between reported binary64 time, cumulative solver duration and source observations. |
| MLS 3.7, eFMI Beta 1 and MISRA C:2025 | No source/GALEC case, IR lowering, solver choice or generated member changes. This does not close initialization, essential-type, variable floating-comparison, ABI or whole-product findings. Proving an individual numeric cast is not a MISRA compliance decision. |

Floating exception flags/traps and later native compilation retain their
existing explicit boundaries. **Stage decision: open; no grammar expansion.**

### Creation through ME release: 2026-09-13

This five-root derived-proof checkpoint follows the previous checkpoint. The actual public
factory now supplies the handle, source default, ownership and caller-buffer
premises for initialization, admitted ME controls, termination and release.
The final lease map equals the original owners, and the combined frame
preserves cells outside the selected instance, outputs and reservation flag.
The FMI/compiler audit passed in `build/c-factory/me-creation-package-gate-v1.log`
with all 838 inputs unchanged. Existing emitters, semantics, mandatory contracts
and prior audit roots are unchanged; the previous full gate remains the
actual-artifact evidence. This derived-proof package snapshot is recorded
separately; no full artifact gate was rerun or new test suite added.

The existing FMI initialization/event/lifetime clause mapping is unchanged.
Creation still requires valid supplied storage, accepted identity buffers,
an available slot and explicit foreign bindings. The derived serial history
does not cover concurrent callers, host state updates/queries, numerical
integration, interspersed failures, reset or use after release. No MLS 3.7 or
eFMI Beta 1 semantics, advertised capabilities or generated bytes change.
No cross-standard or MISRA finding is closed. **Stage decision: open.**

### Initialization, ME controls and release: 2026-09-13

This derived-proof checkpoint follows the previous checkpoint. One actual adapter witness
connects initialization, finite ME control histories, termination and release.
Initialization supplies the control invariant; ordinary typed writes preserve
atomic reservations, so the original lease supplies the later release without
an extra surviving-ownership premise. Exact calls, outputs, source initialization
and the final frame are retained. The 19 roots are integrated into the owning
C, FMI and compiler packages. Their audit passed in
`build/c-factory/me-lifecycle-package-gate-v1.log` with all 835 inputs unchanged.
Earlier emitters, semantics, mandatory contracts and audit roots are unchanged;
the full artifact gate was not rerun for these derived proofs. Their package
snapshot is recorded separately from the preceding actual-artifact evidence.

The preceding FMI 3.0.2 clause mapping remains applicable. This strengthens
the composition of the already checked initialization, event-iteration and
lifetime behavior; it adds no advertised capability or source case. Initial
ownership, native atomic bindings and valid instance storage remain explicit.
Creation, state setters/queries, importer integration, interspersed errors and
concurrent histories remain open. Released handles gain no subsequent-call
validity. MLS 3.7 and eFMI Beta 1 semantics and emitted artifacts are unchanged;
no cross-standard or MISRA finding is closed. The preceding full gate supplies
the unchanged artifact evidence. **Stage decision: open.**

### Mandatory ME control histories: 2026-09-13

This checkpoint follows the previous checkpoint. It retains all earlier mandatory contracts
and adds event/continuous entry, completed integrator steps and discrete-state
updates with exact signatures, independent tokenization and complete represented
success/null/rejection/logging cases. The compiler consequence ties the calls
and their finite control histories to the actual adapter's pool and definition
table. The 92 added roots passed the C/FMI/compiler package audit in
`build/c-factory/me-package-gate-v5.log`, with all 829 inputs unchanged. The
full required gate passed in `build/c-factory/me-full-gate-v1.log` for the
same unchanged snapshot. Both checked archives are retained under
`build/c-factory/me-artifacts-v1/`, with exact member comparisons beside them.
C/header/GALEC and FMI XML match the time checkpoint; the three eFMI manifests
change only generation identities and their dependent references/checksums.
Only these three status documents changed after the full gate.

| Applicable obligation | Proof and remaining boundary |
| --- | --- |
| [FMI 3.0.2 §2.3.5](https://fmi-standard.org/docs/3.0.2/), discrete iteration | The unit profile's discrete update returns all five Boolean flags false and writes positive binary64 zero to the next-time buffer. That numeric value is not a scheduled event when its defined flag is false. `MEHistory` requires a completed iteration before continuous entry and retains the actual returned values at each call. State setters, clocks and general event equations are not added. |
| FMI §§2.2.1/2.2.4, arguments and errors | All six output pointers are required; an undefined next-time result does not make its pointer optional. Complete null/lifecycle/missing-output cases follow the existing guards. Suppressed logging covers absent loggers; supplied logging retains every modeled returning effect and immutable diagnostics. Callback reentry/divergence and native private-memory frames remain open. |
| FMI §3.2.1, continuous mode and completion | Both completion flag inputs and the two false outputs are covered. Time/history updates retain positional completions and the last event, without an added monotonic-completion premise. Importer acceptance of state/input values and numerical integration must still be composed with this control-history result. |
| Memory and actual C | Reusable backend-c assignment/guard lemmas permit uninitialized output storage and compatible aliases. The trace derives writable storage after each call from one initial buffer bank outside the instance block. Public bytes, definitions and literal storage share the actual certificate. Native object layout, whole translation-unit correspondence and transitive no-heap/MISRA policy remain open. |
| MLS 3.7 and eFMI Beta 1 | Source equations, default initialization, DAE→GALEC→Solve and DAE→Solve ownership remain unchanged. No grammar, emitted C/GALEC/XML or numerical solver changes; no MLS/eFMI finding is closed by these proofs. |

The official FMI clauses were rechecked. The earlier draft's time/mode-only
projection was replaced before publication by the composed control history;
it is not evidence for all legal FMI host sequences. The source consequence
preserves initialization, not a claim that a time setter integrates the state.
No example-based proof substitute, new test suite or axiom-policy change was
introduced. K02–K05 and this spiral stage remain open; grammar expansion remains
blocked.

### Mandatory ME trial time: 2026-09-13

This checkpoint follows the previous checkpoint. It adds the exact `fmi3SetTime` signature,
independent tokenization and complete represented call cases to the mandatory
actual-adapter contract. Every prior conjunct and audit root is retained.
The 25 new roots passed the FMI/compiler package gate in
`build/c-factory/time-package-gate-v1.log` with 815 unchanged inputs. The
strengthened actual-artifact contract then passed the full required gate in
`build/c-factory/time-full-gate-v1.log`, again with all 815 inputs unchanged.
Checked FMU/eFMU archives are retained in `build/c-factory/time-artifacts-v1/`.
Their C/header/GALEC and FMI XML bytes match the termination checkpoint; exact
eFMI manifest comparisons permit only fresh identities and dependent
references/checksums. The source reconciliation after this gate changes only
these three status documents. Grammar, emission, numerical semantics, audit
policy and native checks are unchanged.

| Applicable obligation | Added proof and remaining boundary |
| --- | --- |
| [FMI 3.0.2 §3.2.1](https://fmi-standard.org/docs/3.0.2/), ME trial time | `TimeCalls.history_call` and `adapter_time_history` implement the independent history transition. Admission retains start time, second-last completion and last event entry as lower bounds. Retreating trial times remain allowed within that window; no monotonic-time premise is added. Prior history/storage and later event/completion composition remain explicit. |
| FMI §2.3.2, experiment stop | The optional stop remains inclusive. Finite out-of-window arguments take the actual error path. The authored finite-value/nonfinite-rejection policy is explicit; it is not presented as a new quotation from the standard. |
| FMI §§2.3.1/2.3.8, lifecycle and errors | Complete null, invalid-lifecycle, nonfinite and finite-window failures are proved. Suppressed logging includes a missing logger; supplied logging retains every modeled returning outcome and immutable diagnostic bytes. Callback reentry, divergence and private-storage frames remain open. |
| Actual C and source relation | `TimeCalls.FunctionContract` binds the public calls to the prepared pool/table; `adapter_time` locates the actual fragment. Updating time preserves the source initialization relation and model state. It does not prove that the unchanged state is the integrated solution at the new time. Native ABI and whole translation-unit correspondence remain open. |
| MLS 3.7 and eFMI Beta 1 | Source equations, initialization policy, DAE→GALEC→Solve and eFMI artifacts are unchanged. No new source case or MLS/eFMI finding is closed. |

The official FMI 3.0.2 clauses were rechecked for this checkpoint. The stage
remains open under K02–K05; neither the full artifact gate nor this standards review
authorize grammar expansion. No unit-test suite or axiom-policy change was
introduced.

### Mandatory termination and release: 2026-09-13

This increment follows the previous checkpoint. It retains every previous adapter-contract
conjunct and requires the actual termination signature, printed tokenization
and complete represented call cases in the static object interface. No grammar,
emitter, numerical semantics, native check or axiom policy changes. The 15
new roots and strengthened artifact contract passed the full required gate in
`build/c-factory/termination-full-gate-v1.log`, with 809 unchanged inputs.
The actual archives are retained in `build/c-factory/termination-artifacts-v1/`.
C/header/GALEC and FMI XML bytes are unchanged; exact eFMI manifest comparisons
allow only fresh generation UUIDs/timestamps and their dependent references
and checksums. These generation differences do not indicate a new model or
production-code policy.

| Applicable obligation | Added proof and remaining boundary |
| --- | --- |
| [FMI 3.0.2 §2.3.4](https://fmi-standard.org/docs/3.0.2/), termination from Initialized | `Termination.call_behaviors` uses the independent `Reference.Allowed` predicate: ME Event/Continuous or the admitted CS Step mode. `adapter_initialize_terminate` derives acceptance after initialization and retains exact heaps, model and clock. No source termination equations are admitted. |
| FMI §§2.2.4/2.3.8, error and final state | Null returns and invalid lifecycle calls are covered. Suppressed logging includes a missing logger; supplied logging retains every modeled returning outcome, trace, diagnostic bytes and the stuck case. Native callback behavior/private-storage frames and broader public histories remain open. |
| Actual C source and FMI signature | `AdapterContract` and its fixed Lean certificate generator now require `Termination.FunctionContract`; `adapter_termination` locates the exact fragment and obtains the same prepared pool/table. Header/layout/ABI and complete translation-unit correspondence remain open. |
| FMI §2.3.1, freeing a terminated instance; K02 ownership | `adapter_termination_release` obtains both public definitions from the same actual table. Termination preserves metadata and flags, then release discharges the original host lease. The combined frame excludes only the selected mode and atomic reservation flag. Native atomic-store refinement, host ownership and concurrent histories remain separate. |
| MLS 3.7 and eFMI Beta 1 | Source initialization policy and DAE→GALEC→Solve are retained. The new source theorem preserves the IVP selected by existing finite storage; it introduces no initialization/termination syntax. No MLS/eFMI open finding is closed. |

The four derived release roots passed the FMI/compiler package audit in
`build/c-factory/termination-release-package-gate-v1.log` with 811 unchanged
inputs. This follow-up retains every preceding emitter, mandatory contract and
audit root; its unchanged artifacts use the earlier 809-input full-gate evidence.
Released handles are not admitted for subsequent FMI operations. No new test
suite was introduced.

This increment does not close K02–K05 or authorize grammar growth. In
particular, successful termination's frame is not asserted for arbitrary
external logger effects, and its three-call composition is not a theorem
about arbitrary intervening simulation histories.

### Reset in the static runtime: 2026-09-13

On top of the previous checkpoint, fifteen derived proof roots connect the actual adapter's
reset definition to the static object interface and then to both initialization
calls. The FMI/compiler package gate passed with 806 unchanged inputs in
`build/c-factory/static-reset-package-gate-v1.log`. The prior full artifact gate
supplies unchanged emitter/contract evidence; no grammar, emitted member,
mandatory contract or native check changes in this follow-up.

| Applicable obligation | Added evidence and remaining boundary |
| --- | --- |
| [FMI 3.0.2 §2.3.1, reset](https://fmi-standard.org/docs/3.0.2/) | `adapter_static_reset_initialize` restores the Solve default, supplies writable initialization cells, and composes three complete calls through exact heaps to the source IVP. This covers model/lifecycle effects; equivalence of all host configuration to fresh instantiation, including logging policy, remains open. |
| FMI instance isolation and K02 ownership | `StaticReset.record_frame`, `restarted_other_instance` and `restarted_owners` preserve nested cells in other slots of the same array, metadata and reservation flags. Native layout, valid host ownership and concurrent execution remain separate. |
| MLS 3.7 §§4.9/8.6 | The stored finite default and unique completed real trajectory use the unchanged source/Solve initialization policy. No source equation is added; SR08 remains open. |
| eFMI Algorithm/Production Code | DAE→GALEC→Solve and its production/archive contracts are unchanged. No eFMI finding is closed by this FMI proof increment. |

All earlier audited roots remain required. Callback frames, other public calls,
complete host histories, whole-output provenance and MISRA/profile obligations
remain open, so grammar expansion remains blocked by the stage gate.

### MISRA C:2025 and static storage review

The full 223-guideline enforcement ledger (per-row category, applicability,
byte-level evidence, status and closure) lives in [misra-c-2025.md](misra-c-2025.md).
The MC01-MC10 findings below remain the finding-level record; MC02's `calloc`/`free`
observation is superseded there, since the current default emission uses the
static instance pool and no allocator call site remains.

Reviewed 2026-09-13 against the user-supplied **MISRA C:2025, March 2025** PDF,
SHA-256
`42d1f700d83506566964131c6b618f4eba14782ea8fa7b7355924bb7c4b882aa`.
This is the primary MISRA baseline. The earlier supplied MISRA-C:2004 with
Technical Corrigendum 1 (July 2008 reprint), SHA-256
`f5325b58af9355bdab6a2c26495650715171bdcdb76b267d1255ff6c3f590fcd`,
is a historical reference. Neither PDF nor its extracted text is redistributed
or required by a repository build.

The 2025 Appendix A.1 inventory has **223 entries: 22 directives and 201 rules**.
There are 22 Mandatory, 154 Required, 46 Advisory and one Disapplied entry
(Rule 15.5). The IDs and categories were cross-checked against the main text.
Appendix A.2 separately records five withdrawn/renumbered rules. Inventory is
not enforcement: **MISRA compliance remains open and blocks the stage**.

Use the existing **C11** generation profile. Section 1.4 supports it, so the
2004-only C90 mismatch does not apply to this primary baseline. Rule 15.5 is
Disapplied in 2025; multiple returns need no deviation for that rule. Keep
proofs of every error/return path. The earlier floating equality concern
remains applicable under the 2025 essential-type Rule 10.1, with its stated
exceptions; it must not be carried forward under an obsolete rule number.

Section 1.5.2 requires MISRA Compliance:2020; §1.5.3 and Appendix E also apply
to code generators. Record implementation choices, essential-type strategy,
runtime failure handling and the user integration interface. Retain default
categories; no optional automatic-code recategorization or deviations have
been approved. Mandatory rules cannot be deviated (§3.4.1). The optional
[official recategorization plan](https://github.com/The-MISRA-Consortium/GRPs/)
is a separate reviewed decision. Deterministic compiler output and authored
adapter implementation must be scoped correctly; using a generator or having
Lean proofs alone does not establish qualification or an automatic exemption.

The compliance boundary includes generated C, adopted FMI/eFMI headers,
external interfaces and platform assumptions. Standard Library internals and
standard headers have the specific treatment in §1.5.4; FMI headers are not
C Standard Library headers. The project no-allocation requirement still needs
transitive library/callback evidence, even where MISRA does not require a
library's implementation to follow its coding rules.

| Finding | Guideline and observed evidence | Required disposition |
| --- | --- | --- |
| MC01 — C11/profile evidence | Required Rule 1.1 permits the chosen C11 edition. Current [build options](../packages/backend-fmi3/RumocaFMI3/BuildDescription.lean), [FMI types](../packages/backend-fmi3/vendor/fmi3/fmi3PlatformTypes.h) and shared C rely on binary64, integer widths and floating environment features. | Pin actual syntax, constraints, translation limits, types/ABI and compiler options; document implementation choices under Dir 1.1. C11 itself is no longer a mismatch. Compiler acceptance alone does not establish all these obligations. |
| MC02 — allocation | Required Dir 4.12 covers all dynamic allocation packages. Required Rule 21.3 specifically excludes allocator identifiers/macros. [Runtime.makeInstance/body](../packages/backend-fmi3/RumocaFMI3/Runtime.lean) emit `calloc`/`free`. | Remove them; no allocation waiver is proposed. Use a fixed array of fully typed, permanently existing instance objects, with bounded activation/deactivation and explicit field initialization. Prove ownership, exhaustion, isolation and reuse; review Dir 4.12 for the actual implementation. A custom allocator over a static byte arena is not an acceptable workaround. |
| MC03 — return structure, disposition | Rule 15.5 is Disapplied; the runtime uses early guard returns. | No single-exit rewrite or deviation is required by the 2025 baseline. Preserve all-path semantic proofs. Any older eFMI-referenced guideline has a separate disposition under MC08. |
| MC04 — essential types and floating comparison | Required Rule 10.1's operator table restricts floating `==`/`!=`, with exceptions for zero and positive/negative infinity. `Runtime.doStep` compares two variable floating values for the exact communication point and integer time grid. Integer literals are also used in some Boolean and floating expressions. | Review actual expression types under Rules 10.1–10.8. Preserve exact FMI time and solver behavior; an epsilon comparison is not an equivalent repair. Use typed emission for routine fixes and prepare an explicit numerical/deviation argument for any necessary remaining comparison. The exceptions do not cover arbitrary variable-to-variable comparisons. |
| MC05 — initialization and lifetime proof gap | Mandatory Rule 9.1 concerns automatic objects before reads; Rule 9.7 separately concerns atomics. Required Rule 18.6 and Dir 4.1 address escaped automatic storage and runtime failures. Existing typed loads/stores and frames do not yet establish complete creation/lifetime and native layout correspondence. | Bind actual storage declarations and initialization to complete calls. Initialize all reused fields and any synchronization objects correctly, including Rule 22.14 where applicable. Record RTOS startup guarantees. No Mandatory-rule deviation is possible. |
| MC06 — effects, recursion and concurrency | Required Rules 13.2/13.5 concern evaluation order and conditional effects; 17.2 excludes recursive call chains. Required Dir 5.1–5.3 address races, deadlocks and dynamic thread creation; 21.25 requires sequentially consistent synchronization. | Prove order independence where C leaves order open, effect constraints and an acyclic generated call graph. Prove safe shared activation/release, including the chosen atomic semantics and implementation. Keep synchronization outside numerical stepping and avoid hidden library locks. No generated threads are planned; host callbacks/reentry and native RTOS primitives need explicit boundaries. |
| MC07 — identifiers, pointers and provenance | Rules 5.1–5.10, 11.1–11.6/11.8–11.11 and 18.1–18.10 require profile-specific namespace/type/pointer evidence. Required Dir 3.1 also requires documented requirement traceability. Source spans alone do not identify every generated policy requirement. | Connect existing name, conversion, bounds and origin proofs to the exact rules and actual preprocessed interfaces. Preserve generated-rule ancestry. Symbolic pointer cells and a 63-character name check alone cannot close the whole-product obligations. |
| MC09 — implicit pointer guards | Required Rule 11.11 prohibits implicit comparison of pointers with null. The shared `instancePrefix` now emits `m == ((void *)0)` with null-value, printer and branch-preservation proofs. Other instance/name/callback pointer guards remain implicit. | Partial progress only. Complete the remaining explicit comparisons and essential-type review. Preserve short-circuiting, logger behavior and all existing function contracts; a textual replacement without semantic preservation is insufficient. |
| MC08 — eFMI references and generator process | eFMI 1.0.0 Beta 1 §5.2 references MISRA AC AGC for generated code; its GALEC rules also name MISRA C:2012. MISRA C:2025 §1.5.2 and Appendix E impose additional compliance/generator documentation. | Map the separate normative references and review their applicable text. The 2025 book does not silently replace eFMI's references or close SR07. Complete the generator and product compliance documentation and independent review. |
| MC10 — nested aggregate address scope | The former `CMemory.Address` flattened indices across member selection. It now records the containing element's offset at each selection and starts the selected member's local offset at zero. Ten new roots, all affected packages and the required main artifact gate pass. | The modeled address correction is complete; both checked archives retain identical C/header/GALEC bytes. Keep bounds, valid native objects, leaf types and layout separate. Arbitrary-depth descendant and store-frame proofs establish structural isolation for the planned static array; they do not implement its native storage or concurrency. |

The initial enforcement plan is below. Each group must become a separate entry
for every applicable directive/rule before claiming compliance, with its
category, language applicability, analysis scope, independent predicate,
evidence, actual-file coverage, reviewer and any approved deviation. **All
groups retain open work; Rule 15.5's Disapplied disposition is explicit.**
“Formal” describes the intended evidence, not an existing MISRA theorem.

| Guideline inventory | Planned enforcement and boundary |
| --- | --- |
| Dir 1.1–1.2 | Implementation choices and language-extension documentation. |
| Dir 2.1 | Actual build diagnostics and pinned toolchain/options. |
| Dir 3.1 | Source and generated-policy requirement traceability through actual outputs. |
| Dir 4.1–4.15 | Runtime-failure argument, external inputs, library calls, coding policy and whole-call-graph no-allocation evidence. |
| Dir 5.1–5.3 | Race/deadlock freedom and no dynamic thread creation; host integration assumptions. |
| Rule 1.1, 1.3–1.5 | C11 syntax, constraints, behavior and permitted feature profile. |
| Rule 2.1–2.8 | Reachability, statement purpose and unused declarations. |
| Rule 3.1–3.2 | Actual-source comment/line-splicing policy. |
| Rule 4.1–4.2 | Proved literal escapes and preprocessor-sensitive source checks. |
| Rule 5.1–5.10 | Namespace, scope, significance, uniqueness and reserved-name checks. |
| Rule 6.1–6.3 | Bit-field type, width and union restrictions. |
| Rule 7.1–7.6 | Literal spelling, integer suffixes and string literal treatment. |
| Rule 8.1–8.19 | Declarations, prototypes, linkage, qualification, atomic/alignment usage and header evidence. |
| Rule 9.1–9.7 | Definite initialization, initializer shape and atomic initialization. |
| Rule 10.1–10.8 | Independent essential-type/operator/conversion model and emitter preservation. |
| Rule 11.1–11.6, 11.8–11.11 | Pointer/cast permissions and actual typedef/layout correspondence. |
| Rule 12.1–12.6 | Operator grouping, shifts, unsigned arithmetic and permitted object access. |
| Rule 13.1–13.6 | Expression effects, evaluation order and discarded computations. |
| Rule 14.1–14.4 | Loop and Boolean controlling-expression policy. |
| Rule 15.1–15.7 | Branch/jump/block structure; 15.5 is Disapplied. |
| Rule 16.1–16.7 | Switch grammar, labels, termination and discriminant constraints. |
| Rule 17.1–17.5, 17.7–17.13 | Call graph, prototypes, arguments, results and restricted function features. |
| Rule 18.1–18.10 | Pointer/array operations, nesting and object lifetime. |
| Rule 19.1–19.3 | Aggregate assignment overlap and union representation/initialization. |
| Rule 20.1–20.15 | Actual preprocessing, macros, conditional definitions and reserved library names. |
| Rule 21.3–21.26 | Library facilities/arguments, allocation prohibition and synchronization semantics. |
| Rule 22.1–22.20 | Resource lifecycle, error indicators and thread/synchronization objects. |
| Rule 23.1–23.8 | Generic selection/type-generic macro policy. |

Appendix A.2's withdrawn IDs are tracked rather than assigned invented current
requirements: Rule 1.2 → Dir 1.2; 11.7 → 11.4; 17.6 → 17.5;
21.1 → 20.15; 21.2 → 5.10. The grouped inventory covers each of the 223 current
IDs exactly once; this is bookkeeping evidence, not a compliance percentage.

Prefer independent Lean predicates with sound checkers and universal emitter
preservation proofs, made mandatory in the actual-artifact contract. Existing
parser/printer and execution proofs may supply premises after exact mapping.
Analyzer/manual/platform evidence fills boundaries not yet formalized. The
RTOS numerical kernel must use supplied storage, have explicit operation and
storage bounds, and avoid OS services, heap calls, hidden locks and incidental
I/O. Bounded object activation/release and its concurrency proof remain K02 in
[the roadmap].

### Explicit null comparison and storage prerequisites

This increment follows the previous checkpoint. It changes only the shared FMI instance guard
from `!m` to `m == ((void *)0)`. Rule 11.9 permits the explicitly cast zero
constant; a `NULL` macro is not required for this spelling. The independent
C expression grammar and null-value proof bind the printed expression to the
authored C semantics. The shared branch theorem preserves execution for every
represented pointer value; the existing complete-call contracts remain required
for the changed actual adapter. Literal pooling and interface extension preserve
the syntactic constant distinction: a variable containing integer zero is not
accepted as a null pointer constant. C11 6.3.2.3p3–4 and 6.5.9p6 supply the
reviewed null-pointer meaning. Equality between two non-null symbolic pointers
and broader integer constant expressions remain outside this expression slice.

`CStorage` proves that internal modeled execution preserves the supplied cell
domain, types and permissions. This does not prove termination of unsupported
allocation calls or constrain foreign effects; it is not a no-heap certificate.
`StaticSlots` proves bounded serial search, exclusion and release/reuse of fixed
slots. C atomics, concurrent scan behavior, caller ownership and actual instance
storage still need refinement proofs. In particular, serial exhaustion cannot
be inferred from a scan interleaved with other callers releasing slots.

The current address representation's nested-index collision has a universal
Lean review witness in `build/c-static-storage/AddressScope.lean`; this records
MC10 without introducing a new admitted source case. The shared C, FMI and
compiler package checks pass in `build/c-static-storage/package-v3.log`, with
44 added audit roots and all earlier roots and the axiom policy retained.
The required actual-artifact gate passed in
`build/c-static-storage/full-gate.log`, including all 13 existing native FMI
groups and the eFMU checks. All 710 source inputs and the file set remained
unchanged throughout the gate. Both archives are retained under
`build/c-static-storage/artifacts/`. Compared with the previous checkpoint, only the
70 shared instance guards in `sources/fmi3.c` changed; all other C, header
and GALEC bytes are identical (`build/c-static-storage/artifacts.log`).
No MISRA finding other than the named shared guard is
closed, no grammar is added, and no full compliance claim follows.

### Atomic reservation helper: standards impact

This increment follows the previous checkpoint and leaves source grammars, numerical IRs and
production emitters unchanged. C11 7.17.1p5, 7.17.7.1 and 7.17.7.3 supply the
selected non-explicit store/exchange value and ordering contracts; 7.17.3p6/p12
specify their SC ordering and preceding modification. Static atomic Boolean
initialization and the always-lock-free macro value are reviewed against
7.17.2.1p2 and 7.17.5p1. Native declarations and bindings are still required.
See the [WG14 C11 draft](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).

MISRA C:2025 Rule 21.25 requires the selected sequentially consistent order.
The new helper uses two declared unsigned operands for counter addition
(10.4), representable integer constants for size initializers (10.3), and
explicit Boolean casts of zero/one under 10.5's exception. It performs at most
one exchange per slot and contains no recursive C call. This is a scoped
review, not a whole-product essential-type or MISRA compliance certificate.

The helper's actual CTree executes through the shared typed call scheduler,
including fresh parameter binding, local initialization, the bounded loop and
an arbitrary caller continuation. Admitted flag cells yield termination and
an exact sequential trace/result, with frame and storage-preservation proofs.
The shared printer binds the actual function text to its independent token
grammar. The new `_Bool` and `volatile` productions retain all prior cases.
The independent FMI slot reference is refined by the atomic operations and
the complete sequential scan. All C/FMI/eFMI/compiler package checks pass in
`build/c-atomics/package-check.log`; 38 roots are added and none removed.
The required main artifact gate passed in `build/c-atomics/full-gate.log`,
including the existing native FMI and eFMU checks. All 720 source inputs
and the complete file set remained unchanged throughout the run. Both
archives are retained in `build/c-atomics/artifacts/`; every C/header/GALEC
member is byte-identical to the previous checkpoint (`build/c-atomics/artifacts.log`).

MC05/MC06 and K02 remain open: production uses `calloc`/`free`, and this helper
is not yet emitted by its factory. Complete native object declarations,
stdatomic macro/header binding, concurrent ownership, full initialization on
reuse and creation/release must be composed with actual artifacts. A failed
concurrent scan need not observe one globally full snapshot. Requiring
`ATOMIC_BOOL_LOCK_FREE == 2` in the eventual native profile will not by itself
prove operation latency, implementation correctness or whole-program no-heap
behavior. The modeled `size_t` remains 64-bit; native width/ABI interpretation
requires its existing K04 evidence. No MLS/FMI/eFMI expansion is authorized.

### Identity validator and storage foundations: standards impact

This increment follows the previous checkpoint. It retains the existing name/token acceptance
condition and moves its string calls into an explicitly sequenced private
helper. C11 7.24.6.3 specifies length before the terminating null character;
7.24.5.6 specifies the maximal accepted prefix; 7.24.4 and 7.24.4.2 specify
unsigned-character ordering and the sign of a comparison result. The modeled
`strcmp` permits every representable result with that sign, not only -1/0/1.
The selected target remains eight-bit characters, 32-bit `int` and 64-bit
`size_t`; native-library/header correspondence is an explicit boundary.
See the [WG14 C11 draft](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).

The complete helper proof covers parameter/local initialization, explicit
null rejection, all three library calls, unchanged memory and arbitrary caller
observations. The independently defined acceptance predicate requires a byte
outside the supplied whitespace set and equality to the supplied expected
token. The actual factory supplies its prepared token and existing six-byte
whitespace literal. The mandatory adapter certificate binds the helper's
printed fragment, definition table and complete execution contract. Its
library-name check and environment-construction theorem rule out a vacuous
linkage premise. Native buffer validity and the enclosing factory still need
their separate contracts. The helper's explicit null comparisons advance MC09;
remaining logger/instance pointer guards and whole-product essential types are
open. No no-heap guarantee follows from modeled library purity.

The accompanying shared-memory/interleaving proofs preserve private atomic
flags through ordinary C steps and relate an explicit slot-ownership protocol
to those steps. They do not prove that all production histories satisfy that
protocol, or that native C11/RTOS execution refines this scheduler. MC02,
MC05/MC06 and K02 remain open, including actual `calloc`/`free` removal.
All affected package checks pass in `build/c-factory/identity-packages-v1.log`,
with 60 added roots, no removed roots and unchanged axiom auditing. The required
full artifact gate passed in `build/c-factory/identity-full-gate.log`, including
both actual archives, with all 743 source inputs unchanged. The retained
code-member comparison under `build/c-factory/identity-artifacts/` shows only
the identity helper and its two factory call sites changed in FMI C; numerical
C and eFMI C/GALEC are unchanged from the previous checkpoint. No source grammar, numerical behavior or
FMI/eFMI capability is expanded; the recurring standards gate remains closed.

### Public factory admission: standards impact

This increment follows the previous checkpoint and changes proofs/certification without changing
the emitter. ME and CS retain the pinned header signatures. The shared typed-call
semantics performs fresh parameter binding; CS's unsupported-capability guard
precedes identity validation. The name/token predicate, diagnostics and public
capabilities are unchanged. C11 parameter adjustment/conversion, null-pointer,
string-library and readonly-object assumptions remain as previously recorded.

The mandatory actual-adapter contract now binds both public function fragments
to their execution table and installed literal pool. All null/nonnull identity
decisions and the rejected CS capability path have complete logging/silent
proofs. Represented callback memory effects and missing outcomes are retained.
Prepared diagnostic bytes are protected by readonly storage; this does not
establish a frame for private writable instance fields. Native callback
reentrancy/divergence and header/ABI correspondence remain explicit boundaries.

C/FMI/eFMI/compiler package checks pass in
`build/c-factory/factory-contract-packages-v1.log`, with 50 added roots, none
removed and unchanged axiom auditing. The required full artifact gate passed
in `build/c-factory/factory-full-gate-v2.log`, with all 760 inputs unchanged.
The retained FMU and eFMU under `build/c-factory/factory-artifacts/` have identical
C/header/GALEC members to the previous checkpoint. An earlier generated membership-proof error
was rejected by the audit and corrected before this successful gate.

FMI 3.0.2 [§2.3.1](https://fmi-standard.org/docs/3.0.2/#fmi3InstantiateModelExchange)
requires diagnostics on failed instantiation subject to the explicit prohibition
on callbacks when logging is disabled. Null callbacks denote missing support.
The [§2.2.1](https://fmi-standard.org/docs/3.0.2/#requirements-for-implementations-of-the-c-api)
restriction on log-callback reentry is a host obligation. These clauses were
rechecked for the admission contract; native callback correspondence remains
open. The six-byte whitespace predicate is proved as the emitted policy;
its correspondence to the prose name requirement remains part of K05 review.
K02, MC02 and the whole-product MISRA/FMI/eFMI findings remain open: successful
creation/release, typed static storage and `calloc`/`free` removal are unfinished.
There is no MLS grammar, numerical or capability expansion; the recurring
standards gate remains closed.

### Hierarchical subobject correction: standards impact

This increment follows the previous checkpoint. Each `Address.member` preserves its containing
element's index in the member path. The next array offset is local to that
member, so it cannot be confused with an outer instance index.
`member_index_eq_iff` recovers both indices and the member name; `InRecord`
supports arbitrary member depth and local array offsets. `store_other_record`
uses the actual typed store and proves preservation of another enclosing
record's descendants, including nested model fields and tensor cells.
Tensor-region preparation and view separation use the same representation.

The reviewed C rules are array selection (C11 6.5.2.1p2), member selection
(6.5.2.3p3–4), and bounded pointer displacement (6.5.6p8).
See the [WG14 C11 draft](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
The authored model still requires valid objects, bounds, leaf types and
lifetimes from a separate layout interpretation. It does not infer unequal
native pointer values from every pair of distinct symbolic paths: aggregate
and initial-member pointers, non-null pointer comparisons and general nested
C array decay have separate obligations. This change addresses array indices
across named member selection, without adding a new source grammar case.

All ten added roots and existing C/FMI/eFMI/compiler checks pass in
`build/c-static-storage/address-package-v3.log`. The exact five changed
implementation/audit files are recorded in `address-promote.json` in the same
directory. The required main artifact gate passed in
`build/c-subobjects/full-gate.log`, including the existing native FMI and
eFMU checks. All 711 source inputs and the complete file set remained
unchanged throughout the gate. Exact archives are retained in
`build/c-subobjects/artifacts/`; all C/header/GALEC members are byte-identical
to the previous checkpoint (`build/c-subobjects/artifacts.log`). Numerical operations,
IR lowering, emitters and metadata are unchanged. Actual static declarations,
creation/release, concurrency, native layout and whole-stage compliance remain
open; no dynamic-allocation removal is claimed.

### Complete initialization calls: standards impact

This correction follows the previous checkpoint. Source/GALEC grammars, indexed IRs, numerical
Solve programs and eFMI emitters are unchanged. The FMI unit adapter now admits
equal start/stop and ignores unused tolerance. Its full-call and source
contracts become mandatory in the actual-file certificate; this is not a
grammar expansion or a whole-stage conformance claim.

| Obligation | Coverage and remaining boundary |
| --- | --- |
| [FMI 3.0.2 §2.3.2](https://fmi-standard.org/docs/3.0.2/#fmi3EnterInitializationMode), arguments | Finite start, optional finite inclusive stop, and exact raw-bit admission/rejection are proved. CS may ignore tolerance; the ME rationale is the absence of an internal tolerance-controlled algorithm in this unit model. This does not assert universal permission for other solvers or a requirement to accept arbitrary inputs. |
| FMI §§2.3.2–2.3.3, initialization | Complete typed entry/exit establish clock/history and the reference ME/CS mode while preserving the actual model state. Old clock payloads may be uninitialized. Allocation must still establish storage and the default state. |
| [FMI §§2.2.4](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions) and [2.3.1](https://fmi-standard.org/docs/3.0.2/#FMUStateSettable), failures | Illegal arguments/lifecycle calls reach Error and the Terminated write. Disabled logging and all represented returning logger outcomes are characterized. Null handles return Error defensively. Callback ownership/reentry and native ABI remain outside this call model. |
| FMI §3.2.1, time | The initialized heap discharges the existing SetTime guard's reference window, including its inclusive stop. Complete subsequent public-call histories remain separate. |
| MLS 3.7 §§4.4.2.1 and 8.6 | The unmodified declaration leaves its initial state free. The compiler default is zero; a finite host override is preserved. The source contract ties the stored value to its unique Real trajectory at the supplied time origin. No binding/modifier syntax is added; S01/SR08 are not closed. |
| eFMI 1.0.0 Beta 1 | Algorithm/Production Code, initialization program, manifests and archive layout do not change. Their prior actual-artifact contracts remain required by the full gate. |

Architecture was checked against Rust Rumoca `bc71577f`, including
`crates/rumoca-ir-solve/src/model.rs`: the executable model and initialization
plan remain Solve responsibilities. These calls own FMI time/lifecycle state
and do no source resolution, shape inference, scalarization, DAE lowering or
solver selection. The reusable LALR parser remains unchanged.

Composition builds in `build/c-initialization/composition-v2.log`. All 51 added
roots and affected package checks pass in `build/c-initialization/package-v1.log`.
The required full artifact gate passed in `build/c-initialization/full-gate.log`
with all 706 inputs and the complete file set unchanged. Both archives are
retained in `build/c-initialization/artifacts/`; their hashes are recorded in
[the FMI contracts](fmi3/contracts.md#complete-initialization-calls). Compared
with the previous checkpoint, only the FMI initialization-entry body changed; every other
C/header/GALEC member is identical. All 13 native FMI groups pass, including
the extended argument/atomicity group, with no new suite.
The strict `above_iff` policy root is replaced by the inclusive proof; all other
earlier roots and the axiom whitelist are retained. **Stage decision: open;
grammar growth remains blocked.**

### FMI parameter types and typed call entry: standards impact

This increment follows the previous checkpoint. Both EBNFs, LALR admission, IR lowering,
initialization and emitted C/GALEC/XML remain unchanged. The reusable mechanisms
are width-parametric unsigned conversion and parameter-list-parametric typed
call entry. The FMI dictionary adds the missing adjusted pointer spellings and
unsigned 32-bit value references; it does not add general source integer syntax.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| C11 [N1570](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), §6.3.1.3p1–2 | `CUnsigned.Converts` specifies the in-range integer congruent modulo one more than the maximum value. Uniqueness, identity for in-range values, BitVec correspondence and target conversion/store/load proofs cover arbitrary widths and integer inputs. Actual C widths and typedef meanings remain adapter assumptions. Signed overflow, floating-to-integer and pointer-to-integer conversions are outside this increment. |
| N1570 §§6.7.6.3p7 and 6.9.1p10 | The call theorem uses the existing array-parameter adjustment, derives fresh named value/type environments and preserves the caller's heap/continuation at entry. It quantifies over convertible arguments and proves those lists exist. Whole body behavior, pointee types/layouts and external declarations remain separate. |
| FMI 3.0.2 ME/CS, [§§2.2.1–2.2.3](https://fmi-standard.org/docs/3.0.2/#platform-dependent-definitions) | The pinned header specifies `fmi3ValueReference` as `uint32_t`; pointer aliases and callback parameters are opaque symbolic addresses in the authored machine. The actual-file checker now kernel-checks readiness of every collected signature; the contract includes every helper too. It retains all previous grammar/reset fields. Header interpretation, callback execution, allocation, remaining public-call behavior and SR04/SR05/SR07 stay open. |
| MLS 3.7 | No admission, source equations, initialization selection, Real refinement or provenance changes. The existing unit clause map and S01/SR08 findings carry forward. |
| eFMI 1.0.0 Beta 1 | The shared target adds an unsigned conversion constructor; eFMI selects its existing dictionary. No Production/Algorithm Code member, manifest, lowering or archive contract changes. Existing coding-guideline and SR07/SR08 findings carry forward; downstream proofs and artifact checks must pass. |

All 26 new roots and affected packages pass
`build/fmi-types/package-audit-v2.log`. The signature review now reports zero
missing parameter types among the 75 APIs. The strengthened actual-file checker
passes in `build/fmi-types/actual-fmi.log`. The required full gate passed in
`build/fmi-types/full-gate.log`, with all 629 inventoried inputs unchanged and
both actual archives checked. Exact archives and hashes are retained in
`build/fmi-types/artifacts/`; C and GALEC members match the previous checkpoint
(`code-member-comparison.log`). No new example-based suite is added. **Stage decision: open;
grammar growth remains blocked.**

### Float64 setter: standards impact

This increment follows the previous checkpoint and changes proofs and mandatory actual-file
contracts. The source EBNFs, admitted unit profile, IRs, initialization policy,
C/GALEC/XML emitters and archive layout are unchanged. Pinned FMI 3.0.2 clauses
and its schema were reviewed for the state setter.

| Obligation | Coverage and remaining boundary |
| --- | --- |
| FMI §§2.2.7.1–2.2.7.2, type and serialization | Complete validation precedes all state writes. Accepted requests select only reference 1 and retain finite payload bits, including signed zeroes. Request buffers reuse the tensor-memory relation; nValues=nValueReferences remains specific to scalar variables. Repeated requests leave the final value. No duplicate-setting prohibition was found in this section; the separate prohibition for InitialUnknown entries does not apply to API buffers. |
| FMI §§2.3.2–2.3.3, setting start values | XML identifies the selected variable as local, continuous and initial=exact. Instantiated/Initialization writes implement the semantic state update and preserve every other cell. Allocation and the complete initialization history still require composition; this does not close S01/SR08. |
| FMI §§2.3.5 and 3.2.1, ME state writes | Event Mode permits continuous states with reinit=false; Continuous-Time Mode permits setting continuous states. The XML judgment follows ModelStructure to the same declaration selected by numeric reference, without assuming unique names. It checks the exact/local attributes and interprets omitted reinit as false under the pinned [FMI 3.0.2 schema](https://raw.githubusercontent.com/modelica/fmi-standard/v3.0.2/schema/fmi3AttributeGroups.xsd). |
| FMI §§2.2.4 and 2.3.1, errors and logging | Null instances return Error defensively; empty requests permit null arrays. Lifecycle/array/first-entry failures reach the actual helper before state writes. Unknown references do not require a value load. All represented returning logger outcomes/absence and disabled logging are covered. Actual host storage, callback effects/reentry, ownership and native ABI remain explicit boundaries. |
| MLS 3.7 | No source grammar or initialization syntax is added. The setter supplies a finite state to the existing mathematical Real equation; the same Flat/DAE/Solve numerical consequence is retained. Complete source/initialization histories remain open. |
| eFMI 1.0.0 Beta 1 | The reusable memory overwrite lemma and FMI adapter proofs add no eFMI behavior. Prior GALEC/Production C/XML/archive contracts remain required. The full gate passes and actual C/header/GALEC members match the previous checkpoint. |

The setter uses the state-specific permissions despite the broader
local-variable restriction in §2.4.7.1. This cross-clause interpretation remains
part of the prose review; Lean proves the authored contract.

Enabled logging requires a represented callable logger. FMI §2.3.1 permits
null callback pointers for unsupported functionality and leaves use of that
functionality undefined. This contract covers enabled logging with the supplied
callback and disabled logging with either pointer value; it does not claim a
logging guarantee for an enabled but missing callback.

Architecture was checked again against Rust Rumoca `bc71577f`, particularly
`crates/rumoca-ir-solve/src/model.rs`: Solve owns derivative programs,
initialization programs and layouts. The setter consumes prepared state
storage and performs no resolution, shape inference, solver selection or
per-element IR lowering. All 51 new roots and affected packages pass in
`build/c-float64-set/package-v1.log`. The required full artifact gate passed in
`build/c-float64-set/full-gate.log`, with all 694 source inputs unchanged and
both actual archives checked. Retained artifacts are in its `artifacts/`
directory; all C/header/GALEC members match the previous checkpoint.
No new test suite is added.
**Stage decision: open; grammar growth remains blocked.**

### Float64 getter: standards impact

This integration follows the previous checkpoint. The source EBNFs, admitted unit profile,
IRs, initialization policy, C/GALEC/XML emitters and archive layout are unchanged.
The pinned FMI 3.0.2 text was reviewed for the applicable getter obligations.

| Obligation | Coverage and remaining boundary |
| --- | --- |
| FMI §§2.2.7.1–2.2.7.2, retrieval and serialization | The complete public call validates all numeric references before writing concatenated results in request order, preserving duplicates. All three declared variables are scalar; only for this profile does nValues equal nValueReferences. Reusing the tensor-memory buffer judgment does not license tensor-variable serialization. |
| FMI §2.2.7.2, type and identity | Independent XML lookup resolves a unique continuous scalar Float64 declaration by decimal reference, and agrees with C selection of time/state/derivative. Names come from the prepared Solve model, including its time-name collision rule. The decimal judgment covers nonempty ASCII digits including leading zeroes; complete XSD lexical/schema conformance remains separate. |
| FMI §§2.3.2–2.3.3, start values and initialization | The getter returns represented time/state and evaluates the constant RHS. This does not prove those stored values satisfy the lifecycle's start/current-value invariants. Allocation, host setters and complete initialization composition remain open; the getter proof does not close S01/SR08. |
| FMI §§2.2.4 and 2.3.1, errors and logging | Empty arrays may be null. Invalid length/pointer and first invalid reference reach the real failure helper before any output write. All represented enabled logger outcomes/absence and disabled logging are characterized. Actual caller storage, callable bindings, native effects/reentry and ownership remain explicit boundaries. |
| MLS 3.7 | The source remains one Real state with unit derivative. The same Flat/DAE/Solve chain supplies the derivative's exact Real meaning. No declaration, initialization syntax or mathematical/IEEE domain expansion occurs. |
| eFMI 1.0.0 Beta 1 | Generic event-loop composition adds no emitter behavior. Existing GALEC, Production C, manifest and actual archive contracts remain required. The downstream full gate passed; every C/H/ALG member matches the prior checkpoint. This does not close the remaining prose-standard obligations. |

Architecture review against local Rust Rumoca `bc71577f`: `SolveProblem` owns
continuous derivative and initialization programs together with their layouts.
This Lean increment consumes prepared Solve and reuses generic C loops and
tensor-memory frames; it performs no source resolution, shape inference,
per-element IR lowering or solver selection. All 58 added roots and affected
packages pass in `build/c-float64-get/package-v2.log`. The required full gate
passed in `build/c-float64-get/full-gate.log`, with all 686 inputs unchanged.
Both actual archives are retained in its `artifacts/` directory, and all
C/H/ALG members match the previous checkpoint. No new test suite is added. **Stage decision: open;
grammar growth remains blocked.**

### Continuous-state derivative query: standards impact

This proof integration follows the previous checkpoint. The EBNFs, production admission,
IRs, initialization, emitters and archive layout are unchanged. Pinned FMI 3.0.2
§§3.2.1 and 2.4.7 were reviewed directly for the getter and derivative order.

| Obligation | Coverage and remaining boundary |
| --- | --- |
| FMI §3.2.1, first-order derivative query | The actual public call follows `model_rhs` into the verified numerical C statements and writes the prepared Solve derivative. The output frame is explicit; no solver/time update occurs. The admitted constant RHS is provably finite, so this slice has no numerical-failure case. The bracketed Discard advice is not claimed as a generalized failure policy. |
| FMI §2.4.7, ModelStructure order | Independent XML lookup resolves ordered ContinuousStateDerivative entries through unique derivative/state declarations. The derivative list's state projection agrees with the state-access order. Array serialization is outside this scalar judgment. |
| FMI lifecycle, §§2.2.4 and 2.3.1 | The independent ME relation governs legal modes; wrong kinds/modes, wrong counts and null buffers reach the actual Error/log helper. Null handles are covered defensively. Enabled callback execution requires callable binding; disabled execution permits a null logger. Native effects, reentry and ownership remain boundaries. |
| MLS 3.7 | Existing Flat/DAE/Solve theorems relate the exposed derivative's Real value exactly to the source equation. No grammar, Real-domain or initialization change; S01/SR08 remain open. |
| eFMI 1.0.0 Beta 1 | The shared C increment only lifts existing numerical statement executions into the event scheduler. GALEC, Production Code, manifest and archive contracts remain required. Their downstream gate and byte comparison remain separate evidence. |
| Actual artifact and header boundary | Both actual adapter fragments, numerical C contract, XML order and eventful literal preservation are mandatory for the same Solve/table/pool. The fixed checker proves membership and numerical-name freshness for its quoted candidates; this does not verify header parsing, typedef/layout or ABI correspondence. |

Architecture review against Rust Rumoca `bc71577f`: `SolveProblem` owns the
continuous derivative program and initialization data. The Lean backend still
consumes prepared Solve; it adds no DAE resolution, source lookup, shape inference
or per-element lowering. Generic C scheduler and public-call prefix proofs are
reused. All 41 additional roots and affected packages pass in
`build/c-derivatives/package-v1.log`; the required full artifact gate passed in
`build/c-derivatives/full-gate.log`, with all 675 inventoried inputs unchanged.
Both actual archives are retained in `build/c-derivatives/artifacts/`; their C,
header and GALEC members match the previous checkpoint (`artifacts.log`).
No new test suite is added. **Stage decision: open; grammar growth remains blocked.**

### Continuous-state access: standards impact

This proof increment follows the previous checkpoint. Production grammar, source semantics,
IR lowering, C/GALEC emitters, metadata and archive layout are unchanged.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| [MLS 3.7 §4.9.1](https://specification.modelica.org/maint/3.7/class-predefined-types-and-declarations.html#real-type) | Stored Real values must be finite. The setter accepts every finite binary64 value, preserving signed zeros, and rejects non-finite encodings. Ideal continuous trajectories remain a separate reference; source initialization findings S01/SR08 remain open. |
| FMI 3.0.2 [§3.2.1](https://fmi-standard.org/docs/3.0.2/#fmi3SetContinuousStates) and §2.4.7 | State calls obey the independent ME lifecycle relation and the XML derivative/state reference order. Count/pointer and non-finite checks precede state writes. `StateMetadata` resolves that order uniquely for scalar continuous Float64 declarations; array serialization is excluded. |
| FMI §§2.2.4, 2.2.7.3 and 2.4.4 | Illegal calls use Error. Domain failures may use Error or Discard; the bracketed setter guidance recommends Discard for rejected values. Our reviewed policy is fail-stop Error for non-finite Modelica state values, not a claim that FMI mandates that choice. The helper changes mode and respects logging; it does not implement Discard. |
| Actual adapter boundary | Both printed function contracts, same-table literal preparation and all represented error callback outcomes become mandatory. Caller storage, finite internal state, atomic host effects, header meaning and native ABI remain explicit assumptions or open obligations. |
| eFMI 1.0.0 Beta 1 | No GALEC, Production Code or artifact contract changes. Existing clause maps and SR07/SR08 findings carry forward, with the full downstream gate still required. |

Architecture review against `~/git/rumoca` at `bc71577f`: its SolveProblem owns
prepared continuous and initialization data, with no DAE evaluation in Solve
consumers. This increment keeps the Lean backend on prepared Solve and uses
shared public-call proofs; it introduces no solver selection, source resolution,
shape inference or per-element lowering in the backend.

All 39 additional roots and affected package checks pass in
`build/c-state-calls/package-v1.log`; the required full artifact gate passed
in `build/c-state-calls/full-gate.log`, with all 667 inventoried inputs unchanged.
Both actual archives are retained in `build/c-state-calls/artifacts/`; their C,
header and GALEC members match the previous checkpoint. No new test suite is added. **Stage decision: open; grammar growth remains blocked.**

### Nominal queries: standards impact

This proof integration follows the previous checkpoint. Both EBNFs, LALR admission, source
and Solve semantics, initialization policy and emitted members are unchanged.
The generic C partial-body theorem and failure-statement contracts are reused
for public-call composition. The pinned FMI 3.0.2 clauses below were checked
directly against the published specification for this increment.

| Obligation | Coverage and boundary |
| --- | --- |
| FMI 3.0.2 [§2.3.3, nominal query](https://fmi-standard.org/docs/3.0.2/#fmi3GetNominalsOfContinuousStates) | Allowed ME calls return OK and store the positive decoded default 1. The independent lifecycle guard, exact count, null buffer, rejected modes and defensive null-instance cases have complete call proofs. Valid caller storage and declared instance fields remain premises. |
| FMI 3.0.2 [§3.2.1, continuous-state order](https://fmi-standard.org/docs/3.0.2/#fmi3SetContinuousStates) and §2.4.4, nominal defaults | Independent XML interpretation follows the ordered derivative entries to unique scalar continuous Float64 states, excluding dimensions, explicit nominal and declaredType. The actual metadata yields the compiled state and the same binary64 value as the output write. Arrays and inherited types require extensions of this judgment. |
| FMI 3.0.2 [§2.3.1, logging](https://fmi-standard.org/docs/3.0.2/#fmi3LogMessageCallback) | Both error messages and category storage are constructed from the actual table. Enabled execution retains every represented returning host effect or absent outcome; disabled execution is silent. Callback reentry, native divergence and writable host ownership retain the boundaries recorded below. |
| Actual C and header boundary | `AdapterContract` requires the complete nominal function contract; the fixed checker kernel-proves signature membership for the actual collected candidates. This does not prove header parsing, typedef/layout correspondence, ABI or native callback execution. |
| MLS 3.7 and eFMI 1.0.0 Beta 1 | No lexical, grammar, source initialization, GALEC/Solve, numerical or renderer changes. Existing clause maps and S01/SR07/SR08 findings carry forward. No additional production source case is admitted. |

All 33 added audit roots and affected packages pass in
`build/c-nominals/package-v2.log`. The required full `lake test` gate passed in
`build/c-nominals/full-gate.log`, including both actual archives and the existing
native, extraction and mutation checks. All 660 inventoried inputs remained
unchanged. Retained archives and hashes are in `build/c-nominals/artifacts/`
and `artifacts.log`; all C, header and GALEC members match the previous checkpoint.
No test suite is added. **Stage decision: open; grammar growth remains blocked.**

### All failure-helper outcomes: standards impact

This increment follows the previous checkpoint; it changes proofs and mandatory artifact
contracts. The admitted subset, generated code and boundary checks are unchanged.

| Obligation | Coverage and boundary |
| --- | --- |
| FMI 3.0.2 [§2.3.1, logging](https://fmi-standard.org/docs/3.0.2/#fmi3LogMessageCallback) | Every represented returning host choice emits the evaluated environment/Error/category/message invocation, returns Error and preserves immutable strings. Disabled logging has empty events in the same machine. Existence and uniqueness of host outcomes are no longer premises of the mandatory helper contract. |
| FMI 3.0.2 [§2.2.1, callback restrictions](https://fmi-standard.org/docs/3.0.2/) | Log callbacks must not call back into the FMU. The atomic external relation does not model nested native execution; an admissible-host and native correspondence contract remains required. No-outcome stuck behavior is a property of this machine, not a claim about a native callback that never returns. |
| FMI 3.0.2 [§2.4.5, categories](https://fmi-standard.org/docs/3.0.2/#log-categories) | The same successful pool and actual XML category witness remain mandatory. Category selection through SetDebugLogging and all public-entry/lifecycle composition remain open. Writable host effects remain explicit, so private-instance framing still requires a host ownership contract. |
| MLS 3.7 and eFMI 1.0.0 Beta 1 | No changes to grammar, initialization, tensor/IR semantics, numeric policy or renderers. Existing clause maps and S01/SR07/SR08 findings carry forward; this does not expand the eFMI execution contract. |

Compiler composition passes in `build/c-logging-choices/promotion-v2.log`.
The 21 new roots retain every earlier audit root and axiom whitelist; affected
package checks pass in `build/c-logging-choices/package-audit.log`.
The required full artifact gate passed in
`build/c-logging-choices/full-gate.log`, with all 654 inputs unchanged and both
actual archives checked. Archives and hashes are retained in
`build/c-logging-choices/artifacts/`; their C, header and GALEC members match
the previous checkpoint (`artifact-retention.log`). **Stage decision: open;
grammar growth remains blocked.**

### Eventful literal lowering: standards impact

This proof increment follows the previous checkpoint. The admitted grammars, source/IR
semantics, renderers and tests are unchanged.

| Obligation | Coverage and boundary |
| --- | --- |
| FMI 3.0.2 [§2.3.1, callbacks](https://fmi-standard.org/docs/3.0.2/#fmi3LogMessageCallback) | Rechecked environment forwarding, callback parameters and string lifetime. The literal pass preserves all event labels, converted arguments and heaps; `logging_source` now carries this contract for its actual helper table. Native function-pointer correspondence and full public-call composition remain open. |
| Shared C transformation | Interface extension and literal replacement each have forward/reflected labeled simulations. Complete-call preservation derives structural premises from the actual function collection. Foreign effect relations are retained without a successful-outcome premise; execution inside a nonreturning foreign call is outside this machine. |
| MLS 3.7 and eFMI 1.0.0 Beta 1 | No grammar, initialization, numeric policy, DAE/GALEC/Solve or emitted-member change. The existing clause maps and S01/SR07/SR08 findings carry forward. This does not extend the eFMI execution contract. |

The actual checker requires the pass contract and successful pool preparation
alongside every earlier field. All 37 added audit roots and affected package
checks pass in `build/c-events/literal-package-audit-v1.log`. The required full
artifact gate passed in `build/c-literal-events/full-gate.log`, with all 651
inputs unchanged and both target archives checked. Their C, header and GALEC
members match the previous checkpoint; artifacts and comparison evidence are retained in
`build/c-literal-events/`. **Stage decision: open; grammar growth remains blocked.**

### Enabled failure-helper callback: standards impact

This increment follows the previous checkpoint. MLS 3.7 and eFMI 1.0.0 Beta 1 syntax,
initialization, tensor/IR products, numerical policy and emitted C/GALEC/XML
are unchanged. Existing S01/SR07/SR08 findings continue to block grammar growth.

| Obligation | Formal coverage and boundary |
| --- | --- |
| FMI 3.0.2 [§2.3.1, logMessage](https://fmi-standard.org/docs/3.0.2/#fmi3LogMessageCallback) | The actual enabled failure helper evaluates the stored environment and logger, passes Error/category/message, records the callback invocation and returns Error after the supplied host effect. Disabled logging retains the earlier proof. Arbitrary callback termination, reentrant hosts and full public-entry composition are not established. |
| FMI 3.0.2 [§2.4.5, log categories](https://fmi-standard.org/docs/3.0.2/#log-categories) | `logging_source` relates the constructed `logStatus` storage to the category in the actual model XML. Category and supplied immutable message bytes survive the call. Other SetDebugLogging/public lifecycle obligations remain separate. |
| C call and environment boundary | The scheduler, loop bodies, parameter conversion and continuations are shared. Symbolic function addresses and the callback prototype are explicit. Returning host effects must preserve read-only cells; their writable effects are retained. Identifier/field/index callee accesses are supported; function-designator dereference/casts, native ABI, allocation and nested external expressions are outside this increment. |
| Architecture and reuse | Generic labeled execution, finite/infinite histories, quiet embedding and label-preserving bisimulation live in core. backend-c owns callback dispatch and external semantics; backend-fmi3 owns the emitted helper contract. Existing literal-lowering/internal-call proofs are retained; eventful named-literal transformation was still an open bridge at this checkpoint. No new example suite or grammar case is added. |

The actual adapter checker now requires `Logging.FunctionContract` in addition
to every earlier field. All 58 new audit roots and affected packages pass
`build/c-events/package-audit-v1.log`. The required full artifact gate passed
in `build/c-events/full-gate.log`, with all 646 inventoried inputs unchanged
and both actual archives checked. Retained artifacts and hashes are in
`build/c-events/artifacts/`; their C, header and GALEC members match the previous checkpoint
(`code-member-comparison.log`). **Stage decision: open; grammar growth remains
blocked.**

### Version call and XML agreement: standards impact

This increment follows the previous checkpoint. Source syntax, initialization, lowering,
numerical policy, generated C/GALEC and XML renderers are unchanged.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| FMI 3.0.2 [§2.2.5](https://fmi-standard.org/docs/3.0.2/#fmi3GetVersion) | The version getter is permitted without an instance and in every interface state. The actual signature returns `const char *`. The mandatory function contract proves complete typed calls returning immutable, zero-terminated `3.0` storage from the collected pool, with an unchanged heap and no lifecycle/logging premise. The pinned header's `fmi3Version` macro is `3.0`; formal native macro/header and ABI interpretation remain open. |
| FMI 3.0.2 §§2.4.1, 2.4.10.1 | `version_source` relates that string to the version attributes in both actual XML documents. The model document is bound to prepared Solve; independent successful build decoding implies the required root/version fields. This is version agreement, not complete XML/FMI conformance. |
| MLS 3.7 and eFMI 1.0.0 Beta 1 | The admitted Modelica and GALEC grammars, equation semantics, initialization, IRs and emitted products are unchanged. Existing S01/SR07/SR08 findings and the full downstream gate remain applicable. |

No new example suite is added. All 11 new audit roots and affected packages pass
`build/fmi-version/package-audit.log`. The required full gate passed in
`build/fmi-version/full-gate.log`, with all 637
inventoried inputs unchanged and both actual target archives checked. Exact
archives and hashes are retained in `build/fmi-version/artifacts/`; their C and
GALEC members match the previous checkpoint (`code-member-comparison.log`). **Stage decision:
open; grammar growth remains blocked.**

### ME count queries and complete metadata binding: standards impact

This increment follows the previous checkpoint. The source EBNFs, LALR admission, IR lowering,
initialization, numerical policy, runtime C, metadata renderer and archive
layouts are unchanged. Two existing count getters instantiate reusable typed
call, lifecycle, printer, definition lookup and literal-pool proofs. No new
example suite or source case is introduced.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| FMI 3.0.2 [§2.3.2](https://fmi-standard.org/docs/3.0.2/#fmi3GetNumberOfContinuousStates) and §2.4.8 | Both count getters are ME-only; their initial counts sum the sizes of ModelStructure references. `CountMetadata.ScalarCounts` independently resolves each selected reference uniquely to a continuous scalar Float64, excludes dimensions and duplicate references, and counts those scalars. The current counts are one state and zero indicators. Structural parameters/array sizes are outside this admitted profile; extending the relation must interpret tensor volumes. This is a cardinality relation, not full XML/FMI conformance or a derivative/state graph proof. |
| FMI 3.0.2 §§2.3.1–2.3.2 and §2.3.8 | `CountQueries.FunctionContract` requires all terminating-call behaviors for success and null instances, plus lifecycle rejection and missing output with logging disabled. Rejected calls return Error and write Terminated. `counts_source` joins returned counts, Solve volume and actual metadata; `counts_failure_source` constructs the literal pool for the actual function list and preserves immutable bytes and the remaining heap. Enabled logger callbacks, allocation, ABI and other public calls remain open. |
| Actual metadata boundary | The earlier checker rejected a metadata mismatch natively, but its final theorem bound only public identifiers. `SourceBuildContract.metadata` now requires the full independent `XML.Document` relation on the same compiled artifact's prepared model. Candidate tree equality and actual bytes are kernel checked. The adapter contract additionally requires both count signatures/contracts and successful literal-pool construction; these are mandatory evidence, not optional helper theorems. |
| MLS 3.7 | Unit syntax, equations over Real, default initialization selection and source provenance are unchanged. The existing clause map and S01/SR08 findings carry forward. |
| eFMI 1.0.0 Beta 1 | The generic literal-install/load theorem is shared C infrastructure. Algorithm/Production Code, lowering and archive contracts are unchanged. Existing coding-guideline and SR07/SR08 findings carry forward; the downstream artifact gate remains required. |

The authored C dictionary, readable/writable instance cells, fresh symbolic
literal blocks and native preprocessing/header meanings remain explicit
boundaries. Success covers all allowed lifecycle modes; this is not a claim
of full public-API coverage. All 28 new roots and affected packages pass
`build/fmi-counts/package-audit-v2.log`. Elaborated quantifiers and interface
instances were inspected in `scope-review.log`; the constructed-pool theorem
has no supplied literal-address instance. The initial actual-file check stopped
at closed reduction of pool readiness. The candidate builder now composes
checked function-tree equalities and collection equations before kernel-checking
the explicit pool validity conditions (`pool-certificate-v13.log`). The required
proposition and axiom whitelist are unchanged. The strengthened actual-file
checker passes on the retained FMU in `actual-fmi-v2.log`. The required full gate
passed in `build/fmi-counts/full-gate.log`, with all 634
inventoried inputs unchanged and both actual target archives checked. Exact
archives and hashes are retained in `build/fmi-counts/artifacts/`; their C and
GALEC members match the previous checkpoint (`code-member-comparison.log`). **Stage decision:
open; grammar growth remains blocked.**

### Complete FMI function-section grammar: standards impact

This increment follows the previous checkpoint. Both source EBNFs, LALR admission, IR
lowering, initialization, runtime emission, metadata and archive layouts are
unchanged. The shared extension is a list-parametric C printer theorem and a
caller-parametric Lean candidate builder for signature spelling proofs. No new
runtime parser or example-based test suite is introduced.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| C11 [N1570](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), §§6.4–6.9.1 | `function_sequence_tokenization` composes independent function grammars, longest ordinary-code tokens and unchanged ordinary-string concatenation across actual function boundaries. Every existing FMI body and helper instantiates that theorem. Typedef spellings use an explicit name context; actual declarations, scope/type constraints and header/macro interpretation remain separate. The prior lexical/grammar clause review is reused without changes to those rules. |
| MLS 3.7 | All admitted/rejected forms, source equations, initialization selection, Real refinement and source spans are unchanged. The existing unit clause map and S01/SR08 findings carry forward. |
| FMI 3.0.2 ME/CS, [§§2.2.1–2.2.3](https://fmi-standard.org/docs/3.0.2/#header-files-and-naming-of-functions) | The actual `AdapterContract` requires the entire function-section grammar after its exact fixed preamble. The fixed checker kernel-checks spelling proofs for the header collector's 75 signatures. `adapter_reset_source` retains grammar and reset execution for the same definition list. The three official headers still define the API, types and prefix macros; the name-context grammar does not establish those meanings. Other public-call execution, allocation, callbacks and SR04/SR05/SR07 remain open. |
| eFMI 1.0.0 Beta 1 | No Algorithm/Production Code member, manifest, archive contract or method changes. The generic C theorem is reusable, but its composition with the actual eFMI C members is still required. Coding-guideline and SR07/SR08 findings carry forward. |

All nine new roots and affected packages pass
`build/fmi-functions/package-audit-v2.log`. The fixed actual-file checker passes
in `build/fmi-functions/actual-fmi.log`. The required full gate passed in
`build/fmi-functions/full-gate.log`, with all 625 inventoried inputs unchanged
and both actual archives checked. Exact archives and hashes are retained in
`build/fmi-functions/artifacts/`; their C/header/GALEC members match the previous checkpoint.
The type-coverage review found 57 of 75 collected signatures with an adjusted
parameter spelling absent from `FMI3.cTypes` (43 spellings). The universal
count-getter result confirms a concrete entry failure in the authored typed
machine, while native C checks pass. This sharpens the existing F03/SR07
proof-coverage finding; it is not a new native standards failure. See
`build/fmi-functions/signature-types.log` and `unmapped-call-v2.log`.
**Stage decision: open; grammar growth remains blocked.**

### C maximal tokenization and concatenation: standards impact

This increment follows the previous checkpoint and changes proof relations and the required
reset artifact contract. Both source EBNFs, parser/lowering behavior, emitted
C bytes, numeric initialization, metadata and archive layouts are unchanged.
The shared mechanism is a suffix-parametric refinement of token judgments,
followed by grammar induction. It adds no runtime scanning or parsing pass.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| C11 [N1570](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), §6.4p4 and §§6.4.2–6.4.8 | `CTokens.Normal.Candidate` covers the ordinary-code competing token classes, including conservative universal-name/nonbasic extensions and encoded/character literal prefixes. `Consumes.normal` proves longest matching across those classes with the actual continuation. Header names belong to include/implementation-defined pragma contexts, which remain excluded. The enlarged candidate envelopes are not output acceptance rules or a claim that every candidate is valid on a host. |
| N1570 §6.4.9 | Per-class no-comment theorems exclude both comment openers at actual token starts. Literal payload slash/star characters are preserved inside independently decoded strings. This is a comment-free printed subset, not a general comment reader. |
| N1570 §§5.1.1.2 and 6.4.5p5–6 | Shared expression/statement/function grammar proofs separate ordinary literal tokens. `FunctionDenotes.tokenization` uses one witness for maximal lexing, the intended function tree and stability under concatenation. Tokens retain object bytes, anticipating the phase-seven terminator; joining removes the intermediate terminator. Prior macro expansion, source/execution encodings and header interpretation remain separate. |
| MLS 3.7 | No source admission, equation, initialization, Real refinement or diagnostic change. The existing clause map and S01/SR08 findings carry forward. |
| FMI 3.0.2 ME/CS | `Reset.FunctionContract.tokenization` is now required by the actual adapter certificate alongside all earlier fields. `adapter_reset_tokenization` locates its exact fragment. Other functions, headers, allocation, callbacks and SR04/SR05/SR07 remain open. |
| eFMI 1.0.0 Beta 1 | The reusable C theorem is available to Production Code. This increment does not change the eFMI file/archive proposition, GALEC, manifests or methods, and does not close coding-guideline or SR07/SR08 obligations. |

All 67 new roots and affected packages pass
`build/c-lexical/composed-audit.log` (2460 jobs), with the existing axiom
whitelist. The required full `lake test` gate passed in
`build/c-lexical/full-gate.log`, with all 621 inventoried inputs unchanged and
both actual archives checked. Exact artifacts and SHA-256 identities are in
`build/c-lexical/artifacts/`. No new example-based suite was added.
**Stage decision: open; grammar growth remains blocked.**

### Shared C token and function grammar: standards impact

This increment follows the previous checkpoint and keeps the production subset and both EBNF
files unchanged. It adds shared proof rules and strengthens the actual reset
artifact contract; it changes no IR semantics, initialization, generated C,
FMI metadata, GALEC or archive layout.

| Baseline | Correspondence and remaining obligations |
| --- | --- |
| C11 [N1570](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), §§5.2.1 and 6.4.2–6.4.8 | Independent identifier, preprocessing-number, ordinary-string and all-punctuator candidate rules support actual-suffix lexical composition. Word rules include universal-name syntax and conservative nonbasic extensions. Cross-category longest matching, valid implementation extensions and phase-six string concatenation remain open. |
| N1570 §§6.5, 6.7, 6.8 and 6.9.1 | Shared printer theorems preserve the intended expression precedence, initializer/assignment categories, compound control bodies, parameter lists and static/external definitions. Raw type strings require explicit `TypeDenotation`. C type constraints, scope, macros, header declarations and ABI interpretation are separate. |
| MLS 3.7 | Admission, equation and initialization semantics, Real refinement and diagnostics are unchanged. S01/SR08 remain open as recorded in the unit review below. |
| FMI 3.0.2 ME/CS | `Reset.FunctionContract` adds the shared text/tree judgment while retaining all existing call and memory guarantees. `adapter_reset_syntax` binds it to the actual adapter fragment. Other calls, whole-file interpretation and SR04/SR05/SR07 remain open. |
| eFMI 1.0.0 Beta 1 | Shared C proof infrastructure is available to Production Code; no eFMI printer or artifact proposition is changed by this increment. Existing GALEC, Production Code, manifest and coding-guideline findings carry forward. |

All 85 new roots and affected packages pass
`build/c-token/final-package-audit.log`. The required full `lake test` artifact
gate passed in `build/c-token/full-gate.log`, with all 613 inventoried inputs
unchanged. Exact checked FMU/eFMU archives and their SHA-256 identities are
retained in `build/c-token/artifacts/`. No new example-based suite is added.
**Stage decision: open; grammar growth remains blocked.**

### Prior unit-stage baseline

Reviewed implementation: the previous checkpoint.
The normative baselines are [MLS 3.7](https://specification.modelica.org/maint/3.7/MLS.html),
[FMI 3.0.2](https://fmi-standard.org/docs/3.0.2/) and the pinned
[eFMI 1.0.0 Beta 1 archive](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip).
The eFMI archive identity is recorded below; this is not a final eFMI 1.0 claim.

Production accepts a single unmodified `Real` declaration and `der(x) = 1`,
with matching model/end names and a derivative reference to that declaration.
The EBNF also contains frozen development profiles; their recognition does
not imply production acceptance. Reviewed EBNF SHA-256 identities are:

| File | SHA-256 |
| --- | --- |
| `packages/modelica-parser/grammar/Modelica.ebnf` | `90be2d4fe36634a43af1c0c57c394054468b8ebfc1c08c572f6bdfc7cb412b0e` |
| `packages/galec-parser/grammar/GALEC.ebnf` | `0cfa1a87ac98a207d6fd05628414763e0d4b7640641d6c262f246cecae40ab7a` |

This is the initial clause map for S01, not closure of the full source-semantics
review. A restriction of the supported language and a mismatch for accepted
input are different findings.

| Applicable obligation | Implementation/proof correspondence | Review result or remaining obligation |
| --- | --- | --- |
| MLS §§2.1–2.4 and A.1: ordinary identifiers, keywords, whitespace and the integer literal `1`. [Lexical clauses](https://specification.modelica.org/maint/3.7/lexical-structure.html) | [Lexer](../packages/modelica-parser/ModelicaParser/Lexer.lean): `lex_correct` characterizes maximal-munch scanning; `reserved` includes the keywords and four protected predefined type names. | Reviewed for the ASCII restriction. Comments, quoted identifiers and other literal forms remain excluded; the theorem is about the authored lexical rules. |
| MLS A.2.1, A.2.2, A.2.4, A.2.6–A.2.7: one model, declaration and equality equation. [Concrete syntax](https://specification.modelica.org/maint/3.7/modelica-concrete-syntax.html) | [ParserProofs](../packages/modelica-parser/ModelicaParser/ParserProofs.lean): `parsed_in_ebnf`; [Compiler](../packages/compiler/Rumoca/Compiler.lean): `compile_complete` for the resolved unit token shape. | Generated-grammar membership and independent metalanguage correspondence are proved for the admitted dialect (P02). S01 retains correspondence with MLS; there is no full MLS parser-completeness claim. |
| MLS §§8.2–8.3.1: equation lookup and compatible equality operands. [Equation clauses](https://specification.modelica.org/maint/3.7/equations.html) | [AST](../packages/modelica-parser/ModelicaParser/AST.lean): `Resolved`; [LocatedProofs](../packages/modelica-parser/ModelicaParser/LocatedProofs.lean): `resolved_references`, `resolve_error_locations`. | The derivative must name the one declared state; failed resolution has exact occurrence/declaration spans. General scopes are excluded. Record the literal-Integer-to-Real interpretation explicitly in S01. |
| MLS Operator 3.12: `der` is the time derivative of the continuous Real operand. [Operator clause](https://specification.modelica.org/maint/3.7/operators-and-expressions.html) | [Source](../packages/compiler/Rumoca/Source.lean): `Solves`, `trajectory_derivative`; [Behavioral](../packages/compiler/Rumoca/Behavioral.lean): `lowering_chain_behavior_correct`. | The ideal `x₀ + t` trajectory and unit derivative are proved. This does not give finite storage semantics or choose an initial value. |
| MLS §4.9.1: finite stored Real values. [Real type](https://specification.modelica.org/maint/3.7/class-predefined-types-and-declarations.html) | [Encoding](../packages/core/RumocaCore/Real/Encoding.lean): `finiteEncodingEquiv`; [Verified](../packages/compiler/Rumoca/Verified.lean): `compiler_semantic_preservation` and `ArtifactContract.real_solution_refinement`. | Binary64 profile and rounding refinement are proved under the documented C/IEEE assumptions. S01/N01 still require reviewed correspondence; unbounded mathematical trajectories are not stored Real values. |
| MLS §8.6 and §4.9: initialization and fallback selection; FMI initialization metadata; eFMI Startup. | Source takes an external finite initial value; [FMI metadata](../packages/backend-fmi3/RumocaFMI3/Metadata.lean) supplies a zero start; [GALEC](../packages/core/RumocaCore/GALEC/IR.lean) selects zero in Startup. | **Open SR08/S01:** justify and compose these policies, including any required diagnostic. Do not infer an initial equation from the derivative equation. |
| FMI §§2.3–2.5, Chapters 3–4: common lifecycle, ME/CS, metadata and artifacts. [FMI specification](https://fmi-standard.org/docs/3.0.2/) | Existing [FMI contracts](fmi3/contracts.md), source-build certificate and selected public-call theorems. | SR01–SR02 corrections are checked. SR04–SR05 and SR07 remain open; selected calls and numerical-file proofs do not certify the complete adapter/archive. |
| eFMI Chapters 2, 3 and 5: container, Algorithm Code and Production Code. [Beta 1 specification](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip) | [EFMIArchiveProofs](../packages/compiler/Rumoca/EFMIArchiveProofs.lean): `compile_archive_verified`, retaining code, method, mapping and manifest contracts. | SR03's status correction is checked. SR06 is resolved as the documented checker limitation below; SR07 and the SR08 cross-standard initialization review remain open. |

**Evidence checkpoint:** the required full local gate passed at this revision
in `build/diagnostic-locations-full-gate.log`, including both FMI interfaces,
the actual eFMU archive theorem, extracted manifests and mutation controls.
Both gates retain their successful archives; reviewed SHA-256 identities are:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `955258912a6037fe0c37bd243bc4b2e6a872cad9d2b1b618d89e6dea22d252f0` |
| `build/Integrator.efmu` | `6c92cdd9e8beea6e1bef21349a6eb456514960a734d3f1911db664056fa9047f` |

The [hosted run for this revision](https://github.com/CogniPilot/rumoca_lean/actions/runs/34524473640)
also passed. **Stage decision: open; grammar growth is blocked.**

### Independent EBNF reader: standards impact

This candidate follows the previous checkpoint. The Modelica and GALEC EBNF hashes still match
the unit-stage table above. No source production, lexer policy, initialization,
IR lowering, numerical behavior, interface or archive layout changes.

| Baseline | Change and claim boundary |
| --- | --- |
| MLS 3.7 §§2 and A.2 | Independent character/token relations now specify the existing EBNF dialect. The public reader is sound and complete at its normal budgets; generated Modelica source contracts compose this notation with EBNF-to-CFG preservation and LALR acceptance. This closes a reader-proof gap after integration; it does not assert full MLS grammar coverage or settle S01/SR08. |
| FMI 3.0.2 ME/CS | The existing source profile, Solve preparation, emitted C and interface contracts are unchanged. The same complete artifact gate remains required. Open adapter/lifecycle and standards findings carry forward. |
| eFMI 1.0.0 Beta 1 | The same independent notation theorem is emitted for GALEC. The admitted GALEC block, Production C path and archive contract are unchanged. A proof of this documented EBNF dialect is not a full ISO 14977 or eFMI conformance claim. |

Forty generic roots pass the parser package audit in
`build/source-cutover/build/ebnf-reader/parser-package.log`; both grammars were
regenerated. Both language package audits and the existing integration checks
pass in that directory's `language-packages.log` and `integration.log`.
The required main artifact gate passed in `build/ebnf-reader/full-gate.log`,
with all 591 inventoried inputs unchanged and both actual target archives
retained under its `artifacts/` directory. This closes P02 for the documented
notation; it does not complete correspondence with the prose standards.
No new test suite or grammar case is introduced. Stage decision stays open:
the remaining core, adapter and standards obligations still block growth.

Earlier checkpoint entries below describe P02 as open at those checkpoints.
The reader increment above closes it; their other standards findings remain open.

### Generic C character-preservation increment: standards impact

The admitted Modelica/GALEC productions, Solve programs, generated C and
FMI/eFMI artifacts are unchanged. This increment strengthens the actual FMI
adapter contract with a reusable theorem about character rewrites.

| Standard | Coverage and remaining boundary |
| --- | --- |
| [C11 N1570](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf), §§5.1.1.2 and 5.2.1.1 | Generic CTree fragments and the complete FMI adapter are stable under trigraph replacement and physical newline splicing. Raw name/type conditions are explicit and checked. Encoding, preprocessing tokens, macros, headers, typing and execution are separate. |
| MLS 3.7 | Source-name safety follows from the existing lexical theorem. Grammar admission, equations and initialization are unchanged; S01/SR08 remain open. |
| FMI 3.0.2 ME/CS | The actual-file contract includes the new character property while retaining its byte identity and reset behavior. Other public-call, allocation/callback, header/ABI and full artifact obligations remain open. |
| eFMI 1.0.0 Beta 1 | Shared CTree theorems are available to the backend. GALEC/Production Code methods, manifests and packaging are unchanged. No new eFMI conformance claim is made. |

All 35 new roots pass the unchanged axiom policy and affected-package audits
in `build/source-cutover/build/c-printer/composed-package-audit.log`. The fixed
checker passed on the retained FMU files in `actual-fmi.log` in that directory.
The required main artifact gate passed in `build/c-printer/full-gate.log`, with
all 596 inventoried inputs unchanged and both actual archives checked. Exact
archives and hashes are retained in `build/c-printer/artifacts/`.
This is partial assurance progress; the remaining findings still block growth.

### C literal-printer increment: standards impact

The subsequent shared-printer correction is tracked under C01/F03 in
[the roadmap]. It escapes question marks and proves exact literal
bytes after the selected C11 preprocessing rewrites. MLS source admission,
resolution, equation semantics and both EBNFs are unchanged. The FMI impact is
its emitted literals for version/token/category/error handling; correct literal
printing is a prerequisite for complete call proofs, not their replacement.
The current eFMI Production C profile contains no string expressions; its
GALEC method, mapping and initialization obligations remain the same.

The C package audit and disposable native reproduction pass. The complete local
gate for the previous checkpoint passed in
`build/c-string-printer-full-gate.log`, including both artifact paths. The log
now records their SHA-256 identities:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `0d27780b6d2e67f8e68be8157edb0ef52aa564d97e4032e50b63687841ba488a` |
| `build/Integrator.efmu` | `31315a9ec8fc006e9e7c515bec6ae926a8f822fb51a175784ebd218504479886` |

The [hosted run for this revision](https://github.com/CogniPilot/rumoca_lean/actions/runs/34527453846)
also passed. The earlier snapshot's artifact hashes must not be reused for
this run. No SR04–SR08
or whole-adapter obligation is closed by the literal theorem, and this is not
a new completed spiral stage.

### C literal-storage increment: standards impact

The C01/F03 increment adds typed character storage and universal
read-only preservation proofs. It does not change the emitted production C,
source admission, either EBNF, MLS equation/initialization semantics, FMI
metadata/lifecycle policy or eFMI GALEC/Production Code policy. It is a
prerequisite for modeling the FMI adapter's real string-pointer arguments.
The existing clause map and its open findings therefore remain applicable.

The selected C profile uses eight-bit unsigned or two's-complement signed
characters; it does not cover every implementation allowed by
[C11 N1570 §§6.2.5–6.2.6](https://www9.open-std.org/JTC1/SC22/WG14/www/docs/n1570.pdf).
The representation proofs reuse Std, and integer-to-character conversion
accepts only in-range values. Section 6.4.5's literal array bytes are related
to loads from supplied read-only objects, with a fresh-block construction to
establish that the storage premise can be satisfied. No address-distinctness
claim is made for different literal texts; §6.4.5 permits storage sharing.
Actual global storage, static lifetime, array-to-pointer decay and callback
interaction remain unproved. Native character-profile validation is also an
external obligation, not a consequence of the byte round-trip theorem.

The nine new theorem roots pass `build/c-literal-storage-audit.log` with the
unchanged axiom whitelist. The required complete gate passed in
`build/c-literal-storage-full-gate.log`, including the actual archive theorem,
independent extraction, schemas, native execution and mutation controls.
The log records this run's retained artifacts:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `7dc758358ee5f5a253147d4095bef525732b69f4996714fc582e406306620ac3` |
| `build/Integrator.efmu` | `ee10eada0dfb93e153a90375f09da7e5d68bc9c611fb99456ea96ce0a63188e8` |

These identities supersede the preceding snapshot for this run. **Stage decision: open.**
This increment does not close any existing compliance finding or authorize
grammar growth.
The [the hosted run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34533601963)
also passed.

### C literal-pointer and rejected-call increment: standards impact

Reviewed checkpoint: the previous checkpoint.

The next SR04/C01/F03 increment replaces abstract C string values with an
explicit literal-address map, typed pointer conversion and a storage/printing
bridge. `ErrorCalls.nominal_reject_correct` covers the complete generated
nominal-query call from Instantiated through its failure helper and ordinary
return when logging is disabled. It returns Error, sets Terminated and frames
every cell outside the mode field. Counts range over all UInt64 values; output
pointers may be null because the rejection precedes their dereference.
The declaration matches the pinned `fmi3FunctionTypes.h` signature. The added
`fmi3String` alias follows `fmi3PlatformTypes.h`'s const-character pointer.

The applicable FMI status and lifecycle clauses are the same ones reviewed in
SR04 below. The theorem checks the corrected rejection's execution; enabled
callbacks and binding the complete actual adapter bytes remain open. The C
profile selects one address per literal text. Its supplied storage contract
allows compatible sharing, but does not prove every permitted per-occurrence
allocation or the native compiler's global setup. Do not infer those facts
from byte preservation or a function-tree call theorem.

The next callback contract must also retain FMI's logging controls:
[`loggingOn = false` disables callbacks](https://fmi-standard.org/docs/3.0.2/#fmi3InstantiateModelExchange),
and [§2.2.1 forbids the logger from calling back into the FMU](https://fmi-standard.org/docs/3.0.2/#general-mechanisms).
Enabled logging still needs an explicit request/return and memory-effect
contract; assuming that an arbitrary callback simply succeeds would not
establish it.

MLS admission, both EBNFs, initialization/numerical policy and emitted C are
unchanged. The eFMI profile emits no string expressions and keeps its existing
GALEC, Production C and manifest contracts. SR05–SR08 remain open. Twelve new
roots and all affected package audits pass in
`build/c-literal-call-package-audit.log`. The required full local gate passed in
`build/c-literal-call-full-gate.log`, including both FMI interfaces, the complete
actual eFMU archive certificate, independent extraction, schemas, native C and
mutation controls. Both EBNF identities still match the unit-stage table above.
This run retained the following artifacts:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `e1dc2271f9fa22ed5454eb5e30908e26d59bcd41d5231ccdc53bb94f85dc03c7` |
| `build/Integrator.efmu` | `dd22dca1dac2f3af228a3f8bc79e9934ba20860f583daa5a7892654c74d6fb88` |

These hashes identify this increment's local artifacts, not those from its
preceding storage checkpoint. **Stage decision: open; grammar growth remains
blocked.** The new function-tree proof is not a whole-adapter certificate.
The [the hosted run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34536535660)
also passed.

### Named string-storage preparation: standards impact

The next C01/F03 increment prepares a string-expression-to-data-name lowering.
Its memory-body theorem preserves all observations, including failure and
divergence, under explicit binding and freshness conditions. It does not yet
emit static-array declarations or replace the production renderer. Actual
global storage, typed calls, enabled callbacks and complete adapter binding
remain open. The theorem is about the authored C machine; it is not evidence
that the native compiler uses the selected literal-address map.

MLS admission, both EBNFs, initialization and numerical policy, FMI metadata
and lifecycle, and eFMI GALEC/Production Code and manifests are unchanged.
The current clause map and SR04–SR08 findings therefore carry forward. The
core/C package audit passed in `build/c-literal-lowering-package-audit.log`,
including all seven new audit roots under the unchanged whitelist. The required
full local gate passed in `build/c-literal-lowering-full-gate.log`, including
both FMI interfaces, the actual eFMU archive certificate, extracted manifests,
schemas, native C and mutation controls. The retained artifacts are:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `a83b4c29e60867fa69052c5dd3ccf10bd46004fb22e41fadd8b294b027155d3d` |
| `build/Integrator.efmu` | `4c2e2bb0693280dc3dafb66441d444bbb9e023053a6334ed7145c70436eb5657` |

**Stage decision: open.** This preparation does not close actual global storage,
the whole adapter or any existing compliance finding.
The [the hosted run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34539932871)
also passed.

### Typed loop/call string-storage preparation: standards impact

This increment extends the previous lowering proof to typed loops and ordinary
calls, including recursive calls, failed execution and divergence. The public
entry theorem derives the empty continuation invariant. Supplied global-name
bindings and structural freshness remain premises; the proof compares machines
using the same interface and does not yet construct the actual global pool or
certify insertion of declarations into the emitted C translation unit.

| Standard | Review of this increment |
| --- | --- |
| MLS 3.7 | Source admission, both EBNFs, equation/initialization semantics and numeric policy are unchanged. The existing clause map, P02 and SR08/S01 carry forward. No development profile enters production. |
| FMI 3.0.2 ME/CS | Runtime C, metadata, lifecycle, errors/logging and archive contents are unchanged by this proof pass. SR04 still needs enabled callback and complete adapter/global-storage coverage; SR05 and SR07 remain open. |
| eFMI 1.0.0 Beta 1 | GALEC methods, prepared Solve program, Production C, logical mappings, manifests and packaging are unchanged. The layout review below resolves SR06 as a checker limitation. SR07's release obligations and SR08's initialization correspondence remain open. |

The thirteen new roots pass the unchanged axiom whitelist in
`build/c-literal-loop-call-package-audit.log`. The required full gate passed
in `build/c-literal-loop-call-full-gate.log`, including both FMI interfaces,
the exact eFMU archive theorem, official schemas/checksums, native C and mutation
controls. No unit tests or source cases were added. Both EBNF hashes above
were rechecked and are unchanged. The retained artifact identities are:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `4d3121d6cb44cd908ee3dc68e88fd2784f11137accee96d070c2995dbbb1436c` |
| `build/Integrator.efmu` | `7e2a6d7587706337e8d45ebf386ba28582ee9ce0a1dbcfcc13010dd2aa937777` |

**Stage decision: open; grammar expansion remains blocked.** The new theorem
closes the conditional loop/call lowering obligation, not the actual global
setup or complete compiler chain. SR04, SR05, SR07 and SR08 remain open; SR06's
separate disposition resolves only the standalone packaging question.
The [the hosted run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34543106088)
also passed.

### Checked literal pool and interface extension: standards impact

This increment constructs a validated symbolic string pool and proves that
adding its data bindings preserves the original program's identifier lookups.
`CLiteral.Pool.invocation_behaviors` composes this result with the earlier
literal lowering for every typed-call observation, including failure and
divergence. The storage theorem constructs immutable objects; fresh blocks
preserve existing cells. It does not emit declarations or change production C.

| Standard | Review of this increment |
| --- | --- |
| MLS 3.7 | The frontend, both EBNFs, IR lowerings, equation/initialization meaning and numerical profile are unchanged. The existing clause map, P02 and SR08/S01 carry forward. The EBNF hashes above were rechecked; no development case enters production. |
| FMI 3.0.2 ME/CS | Runtime C, headers, metadata, lifecycle and packaging are unchanged. This prepares explicit string storage for the adapter; it does not close logging, public-call, header/linkage or actual-adapter obligations. SR04, SR05 and SR07 remain open. |
| eFMI 1.0.0 Beta 1 | GALEC, prepared Solve, Production C, mappings and manifests are unchanged. The official specification archive still matches the pinned hash. The eFMI resources page still lists Beta 1 as a release candidate; SR06 retains its documented checker limitation. SR07 and SR08 remain open. |

The symbolic construction uses separate block slots; it makes no native C
layout or allocation claim. A future declaration printer must establish the
selected C storage, lifetime and array-decay rules and its complete emitted
bytes. The existing C11 correspondence obligations remain applicable. Source
name collection alone does not validate arbitrary header macros or typedefs.

All 27 new roots pass the unchanged C package axiom audit in
`build/c-literal-pool-package-audit.log`. Review of the elaborated signatures
caught an implicit `reserved` identifier resolving to the imported Modelica
keyword list. Explicit parameters now make the pool results general over
reserved-name lists. The interrupted gate was discarded; the corrected source
passed the required full local gate in `build/c-literal-pool-full-gate.log`,
including the actual eFMU theorem, FMI ME/CS checks, official schemas/checksums,
native C and mutation controls. Reviewed artifact identities are:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `457f8f5b5a59b368054923a4637ff0fd190bda65096541d29da9d0d7009156ca` |
| `build/Integrator.efmu` | `c3fde89246c37fe7448f56bdedb757d9f8a2b6e82692a73bfa814c1106955915` |

No new unit tests or source cases were added.
**Stage decision: open; grammar expansion remains blocked.**

### Literal declarations and FMI function binding: standards impact

This increment supplies an independent declaration-list grammar and proves
exact ordered names and initializer bytes, then connects them to the checked
pool's constructed symbolic storage. It collects literals from every tree
constructor and applies the pass to the actual FMI renderer's function list.
The constructed definition table derives helper bindings and tree coverage;
the authored constant exclusions and structural call conditions are proved.
The complete observation-equivalence theorem includes returns, failure and
divergence. The production C emitter, metadata and package layout are unchanged
by this preparation.

| Standard | Review of this increment |
| --- | --- |
| C11 N1570 §§5.1.1.2, 6.7.9 paragraphs 14/22 | Independent syntax models static character arrays with bounds supplied by their literal initializers, including the terminator. The complete-block proof excludes trigraph/splice changes across physical declaration lines. Macro expansion, the surrounding translation unit and native allocation/layout are separate. |
| C11 N1570 §§5.2.4.1, 7.1.3 | Actual `Pool.make` names start with `rumoca_literal_`, satisfy the checked 63-character bound and exclude supplied names. This does not validate all implementation macros/types or arbitrary `Pool.check` inputs. |
| MLS 3.7 | EBNFs, frontend, IR lowering, source equations and numerical admission are unchanged. P02 and SR08/S01 remain open. |
| FMI 3.0.2 ME/CS | The proof now uses the actual rendered function list, but is not a complete adapter-file or public-call certificate. Unsupported external calls still have stuck observations in the authored machine. Enabled callbacks, header/ABI and allocation remain open; SR04, SR05 and SR07 are not closed. |
| eFMI 1.0.0 Beta 1 | Shared C preparation is available to either backend; GALEC, Production C and packaging are unchanged. SR06's standalone-layout disposition and SR07/SR08 remain as recorded. |

The C clause review uses the [official N1570 draft](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
All 34 new shared C/FMI roots passed with the unchanged axiom whitelist in
`build/c-literal-declarations/package-audit.log`. The full required
`nix develop .#verification --command lake test` gate passed in
`build/c-literal-declarations/full-gate.log`, including both FMI interfaces,
the actual eFMU theorem, extraction, official schemas/checksums, native C and
mutation controls. The checked source snapshot still matches
`build/c-literal-declarations/source.sha256`. Artifact identities are:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `30e39977357de58364f4a2a6d1a3dbf4813b4b1ea950c46cf4197c6b7dc47d29` |
| `build/Integrator.efmu` | `22b0750229afa80eb3986e3076587ba3965cd40d37fbcd4cdc1c04dc4c92004d` |

No new unit tests or language cases are added.
**Stage decision: open; grammar expansion remains blocked.**

### Adapter call and lexical preparation: standards impact

This increment derives the instantiated nominal-query rejection from the
actual collected literal pool and renderer's function table, with disabled
logging. It also proves successful header reads have unique function names.
The production renderer does not yet invoke the literal pass. Its signature
membership, helper/public name separation, callbacks and full-file binding
remain open.

| Standard | Review of this increment |
| --- | --- |
| C11 N1570 §6.4 paragraph 4 and §6.4.6 | The shared scanner prefers a matching configured pair to a single symbol. Exact whole-result refinement, including errors and offsets, holds for all prior disjoint configurations. The new C configuration is a restricted lexical prerequisite, not a complete preprocessing-token grammar. |
| C11 N1570 §6.4.4.1 | The numeric theorem uses a single zero or a nonzero leading digit and independently computes the base-10 value. It excludes leading-zero octal ambiguity. C integer type selection and representability still need their own contract. |
| MLS 3.7 | Source EBNFs, source semantics and production admission are unchanged; P02 and SR08/S01 remain open. |
| FMI 3.0.2 ME/CS | The rejection theorem covers either interface kind and arbitrary nominal output pointers/counts, but only the Instantiated state with logging disabled. It preserves literal bytes and all heap cells except mode. It does not close SR04/SR05/SR07 or establish complete FMI execution. |
| eFMI 1.0.0 Beta 1 | GALEC and Production C scanner configurations have proofs of exact result/error preservation. The source profiles, manifests, methods and packaging are unchanged. SR07/SR08 remain open. |

The C clauses were checked against the [official N1570 draft](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf).
The existing package audits include 17 new roots; no test suite or source case
is added. The required `nix develop .#verification --command lake test` passed
in `build/adapter-preparation/full-gate.log`. The package source snapshot in
`build/adapter-preparation/source.sha256` was checked unchanged after the gate.
The resulting artifact identities are:

| Artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `dbbe7b470a7cfeeb6bf11d522cd95705ad0d10bab8c40d80eeba62dbfa7b8c32` |
| `build/Integrator.efmu` | `b9326e66377399c8228fd01a35107e01b9760f5c0239f8b2945c5caa7b1f597a` |

This checks the preceding production artifacts; initialization work remains
isolated and is not covered by this gate. The partial adapter theorems do not
establish the remaining whole-adapter contract.

**Stage decision: open; grammar expansion remains blocked.**

### Mandatory located source: standards impact

The production artifact now requires its checked located parse. The driver
returns source-indexed diagnostics directly, and the CLI no longer reparses
failures. Generic exact-spelling attachment completeness is derived using
Lean's UTF-8 cursor and iterator proofs. The actual Modelica lexer discharges
the spelling contract, and `compile_complete` retains its original lexical
and resolution assumptions. Invalid-source diagnostics may gain precise
locations; the admitted source syntax and numerical behavior are unchanged.

| Standard | Review of this increment |
| --- | --- |
| MLS 3.7 lexical and concrete-syntax profile | No EBNF production, token class or name-resolution rule changes. The completeness theorem covers the same independent lexer/AST specification, without assuming attachment success. Generic UTF-8 cursor proofs do not enlarge the admitted identifier language. SR08/S01 initialization remains open. |
| FMI 3.0.2 ME/CS | Numerical Solve/C, adapter bodies, metadata and packaging are unchanged. Artifact certificates now construct mandatory source locations using the proved total frontend. This is source provenance, not an emitted-code map or a new FMI lifecycle guarantee. SR04/SR05/SR07 remain open. |
| eFMI 1.0.0 Beta 1 | GALEC/Production C and manifest generation are unchanged. Their actual-file certificate generators use the located compiler theorem. GALEC IR origin propagation and actual emitted-byte source maps remain open with SR07/SR08. |

Fourteen new roots are registered in the existing audits. The package gate
passed in `build/located-provenance/package-gate.log`; the required full gate
passed in `build/located-provenance/full-gate.log`, including actual numerical
C and GALEC certificates, independent FMI ME/CS import, and checked eFMU
publication, schemas, native execution and mutation controls. The unchanged
package source snapshot was checked against
`build/located-provenance/source.sha256` after completion. Artifact identities:

| Artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `169c5964757a1faf7abd08e933b7efc96c700cc98bb03fed459a730fd37e0005` |
| `build/Integrator.efmu` | `472993590dd53d9cb3f1365f746563696ca5d0fee7567786790c7f235e55124b` |

Initialization preparation remains in the isolated checkout and is excluded
from this production gate. These results do not close the remaining provenance
or standards findings.

**Stage decision: open; grammar expansion remains blocked.**

### Shared source origins: standards impact

The generic engine now provides checked source/derived/generated origin tables,
with mandatory parent/rule records and ancestry preservation. The Modelica
frontend supplies exact field and production ranges for its existing AST; the
GALEC lexer supplies the generic attachment-completeness contract. The parallel
frontend reuses the shared immutable input record without changing scheduling
or analysis results.

| Standard | Review of this increment |
| --- | --- |
| MLS 3.7 | The same fixed lexical/AST profile is admitted. Token-indexed production boundaries and literal/name text are proved for the actual parse. No declaration, binding, modifier, initialization, tensor or AD syntax is added. SR08/S01 remains open. |
| FMI 3.0.2 ME/CS | Solve, C, adapter bodies and FMI metadata are unchanged. Source-origin tables are not a lifecycle theorem or a printer map. SR04/SR05/SR07 remain open. |
| eFMI 1.0.0 Beta 1 | Exact source attachment is proved for the current GALEC scanner. Required GALEC IR origins, generated-member maps, and initialization correspondence remain open. Algorithm/Production Code emission is unchanged. |

Twenty-three new roots pass the existing package audits in
`build/origin-tables/package-gate.log`; the required full artifact gate passed
in `build/origin-tables/full-gate.log`. It includes actual numerical C and GALEC
certificates, independent FMI ME/CS import, and checked eFMU publication,
schemas, native execution and mutation controls. The package inventory in
`build/origin-tables/source.sha256` was checked unchanged after completion.

| Artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `4f967951f8e730aa11826d230c906237d96209d56cec0c8214a7bfa8b6c15b05` |
| `build/Integrator.efmu` | `c84a3797dc25ab9a754c631b92488209f09701f9f13b500021952f6df167031e` |

The checked graph prevents absent/dangling parents, but compiler-specific rule
correctness and per-IR occurrence coverage still require their own proofs.

**Stage decision: open; grammar expansion remains blocked.**

### Scoped initialization and required IR origins: standards impact

The unmodified Real/unit-derivative production grammar and both EBNF identities
above are unchanged. The integrated initialization/provenance implementation
was prepared in `build/literal-call-worktree`. Its full gate passed in
`build/scoped-full-gate.log`, and `build/scoped-sources.sha256` remained unchanged
throughout that run. The current mainline audit roots are all retained; older
worktree audit lists were reviewed and restored before integration.

| Normative obligation | Checked correspondence | Open boundary |
| --- | --- | --- |
| MLS 3.7 §§4.4.2.1, 4.9 and 8.6: bindings, start guesses, fallback and selected initial conditions. | `Initialization.Real` proves preparation soundness/completeness, constant-binding inconsistency for `der(x)=1`, and a unique completed trajectory. `Source.initializes_iff` retains the unfixed source equation. Required Flat/DAE/Solve settings select zero with both notices, whose declaration spans agree between compiler and LSP. | No binding/start/fixed syntax is admitted. General initialization systems remain outside this grammar. |
| FMI 3.0.2 §§2.3.1–2.3.3: instantiated defaults, host changes, initialization and reset. | Prepared Solve data supplies an explicit C store after allocation and on reset. `CInitialization.write_behaviors` proves its value and heap frame; existing body/literal-call proofs cover that statement. The full isolated gate passes both ME and CS boundaries. | Allocation, public-call/artifact composition and the SR04/SR05 lifecycle and host-set policy remain open. |
| eFMI 1.0.0 Beta 1 §3.2.3, §3 R-1: Startup determines block-variable initialization. | Existing actual Production C contracts initialize state, period and status from writable uninitialized storage. `GALEC.initialization_matches` identifies the same selected source plan. The added `ArchiveStartupContract` binds the actual C member, all terminating Startup behavior, the value read from the resulting heap, and the completed source solution. Its strengthened actual-file proposition passed the final integrated gate below. | GALEC/Solve operation origins, manifest/source-map correspondence and general coding-guideline obligations remain open. |

Artifact identities for the completed **isolated preceding snapshot**, not the
subsequent strengthened checker or the main workspace's later artifacts:

| Artifact in the isolated checkout | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `c6c4b6dcddcbe0bcef6f53307c24dc3fbe7367798f3b7a09811097c46fd6901a` |
| `build/Integrator.efmu` | `d08885b29e3c9886fc278b19de2cb22e58114888c8864d3f23fb9492c20db3fa` |

The added archive-initialization roots and affected package audits pass in
`build/literal-call-worktree/build/scoped-startup-integration.log`. Main-workspace
package/audit checks passed in `build/initialization-provenance/package-gate.log`
(3282 jobs), retaining all 1108 prior audit entries and adding 50. Its final
full gate passed in `build/initialization-provenance/full-gate.log`, including
the strengthened actual-file proposition. The main-workspace input inventory
`build/initialization-provenance/sources.sha256` was unchanged after completion.
Its final retained artifact identities are:

| Actual artifact | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `df945b602bf305b402cc361f86c41d85fa7afa86eed6e111e5dd9c80ec482a54` |
| `build/Integrator.efmu` | `eb403ed61b99b92d914e4a00e3ff8e98ef938469eb8d51b4ac6f794e5ccc2e2c` |

Fixed source-file certificates now quote the actual checked filename and bytes
together. `Artifact.source_identity` preserves the caller's complete input table
and selected entry. Published checks name their staged snapshot; no certified
map to the original filename or generated archive-member ranges is claimed.

The neighboring Rust checkout was read at `bc71577f85df24957e5c9ab30fdaf4ed48da4311`
with user changes present. Its provenance and initialization ownership informed
the review; no Rust file was modified. Inspected file identities are retained in
`build/literal-call-worktree/build/scoped-rust-reference.sha256`. The normative
authorities remain the pinned standards linked above.

**Stage decision: open.** SR08, PV06–PV09 and the whole-adapter obligations still
block grammar growth. This change introduces no new test suite or axiom policy.

### Required GALEC/Algorithm origins: standards impact

This increment follows the previous checkpoint. It changes
required provenance in the existing DAE → GALEC → Solve Algorithm chain;
source admission, equation/initialization semantics, the unit sampling policy,
both EBNFs, and FMI/eFMI interface or archive layouts are unchanged.
The current normative clause map and its open findings therefore still apply.

The generated initialization value explicitly retains the MLS fallback and
unfixed-start selection parents. eFMI Startup/period and DoStep occurrences
retain separate generation rules; the sampling constant is not presented as a
written source constant. Exact origin-event preservation composes with the
existing GALEC-to-Solve lifecycle semantics. These are provenance guarantees,
not a proof of the still-open FMI lifecycle or eFMI coding-guideline clauses.

Sixteen new roots pass the unchanged axiom audit. The complete package gate
passed in `build/literal-call-worktree/build/galec-origins-package-gate-lean-only.log`
(3296 jobs), including both backend consumers and compiler contracts.
The main-workspace required full artifact gate passed in
`build/algorithm-provenance/full-gate.log`; its recorded source inventory
remained unchanged throughout the run. It retains the complete eFMU Startup
contract, independent extraction, native ME/CS and Production C checks, and
the existing actual-file mutation controls. This run produced:

- FMU SHA-256: `fcf9f72dd77e818f6f84ca1cf5201c9a80586f75fd07c9fcc4363db388e78477`.
- eFMU SHA-256: `5197818bc34e2ae7a401b869e9b1ebeb2dd0c8bd1aef3b8074f1a5f919f71e4b`.

No new test suite was added. **Stage decision: open** pending tensor/FMI
origin integration, actual emitted-byte maps and the earlier
whole-adapter/compliance obligations. No grammar expansion is authorized by
this provenance checkpoint.

### Required unit FMI IVP origins: standards impact

This increment follows the previous checkpoint and strengthens preparation metadata for the
existing unit profile. Canonical source-table preservation is required through
Flat, DAE and Solve. The prepared FMI IVP requires every operation/operand
origin, including explicit rules for the empty input channel, state observation
and solver policy. The actual initial fill remains tied to the selected Solve
initial plan; a generated observation does not assert a source output qualifier.

The MLS 3.7 initialization/equation clause map, FMI 3.0.2 lifecycle/metadata
findings and eFMI Beta 1 Algorithm/Production Code review carry forward.
Neither EBNF, production source admission, numerical policy nor interface or
archive layout changes. These proofs do not close SR04, SR05, SR07 or SR08.

Nineteen added roots pass the unchanged audit, retaining every prior entry.
The final downstream package gate passed in
`build/literal-call-worktree/build/fmi-origins-trace-gate.log` (3305 jobs).
The main-workspace required full gate also passed in
`build/fmi-provenance/full-gate.log`, retaining the actual source-to-archive
Startup contract, native ME/CS and C boundaries, extraction/schema checks and
the existing mutation controls. Its source inventory remained unchanged. This
run produced:

- FMU SHA-256: `b8efa712c1758f1419f7ce83045983f6e3b231071498118db3cdb4152ada838c`.
- eFMU SHA-256: `cf46fbdc479e77328358fefa964a0990c0469d5165c5a54a46fc92424fb03eb8`.

No test suite was added. **Stage decision: open** pending development tensor
provenance, emitted-byte maps and the remaining
whole-adapter/compliance obligations. No grammar expansion follows this checkpoint.

### Shared C initialization origins: standards impact

This increment follows the previous checkpoint. It strengthens independent checking of the
actual GALEC block annotations and requires origins on the shared C initializer
consumed by FMI creation/reset. Its theorem combines exact source ancestry and
the annotation contract with all C-body behaviors under supplied writable
binary64 storage. It does not prove allocation or the complete public API.

The preceding MLS 3.7, FMI 3.0.2 and eFMI Beta 1 clause maps and findings carry
forward. Both EBNFs, source admission, numerical policy, rendered C expressions,
public interfaces and archive layout remain unchanged. No additional normative
conformance claim follows from the origin proofs.

Twenty-five added roots retain every previous audit entry and the unchanged
axiom policy. The downstream package gate passed in
`build/literal-call-worktree/build/c-initial-provenance-package-gate.log`
(3316 jobs). The required main-workspace artifact gate also passed in
`build/c-initial-provenance/full-gate.log`, including both target archives and
the existing boundary/mutation checks. All 510 inventoried inputs remained
unchanged. This run produced:

- FMU SHA-256: `0cc3e17ec9052f3738a61ab108e3699b3dd7d241370bb731fc76cee28edb96ab`.
- eFMU SHA-256: `5c4e3af3b5768c2f06948d979b845efdcb31f3d5ae7544b58b13bb55f720820c`.

No new test suite is added.
**Stage decision: open.** Remaining byte maps, full adapter/artifact composition
and unresolved standards findings continue to block grammar expansion.

### Shared initializer printer map: standards impact

This increment follows the previous checkpoint. It adds exact maps for the shared C
initialization fragment, with unchanged production printers, grammar admission,
numerical policy, public interfaces and archive layout. The existing MLS 3.7,
FMI 3.0.2 and eFMI Beta 1 clause maps and unresolved findings carry forward.

The formal contract combines the actual statement printer's UTF-8 bytes,
complete range collection, exact byte extraction, source ancestry and the
existing all-behavior initialization theorem. It assumes supplied writable
binary64 storage and the explicit `double` binding. Whole-function/file and
archive-member map correspondence remain open; no new normative conformance
claim follows from this fragment result.

All 186 prior C audit roots are retained, with 25 additions under the same
axiom policy. The downstream package gate passed in
`build/literal-call-worktree/build/c-mapped-initialization-package-gate.log`
(3319 jobs). The required main-workspace artifact gate also passed in
`build/c-mapped-initialization/full-gate.log`, including both target archives and
the existing boundary/mutation checks. All 513 inventoried inputs remained
unchanged. This run produced:

- FMU SHA-256: `0ef7c4543ee7481fbcafabebdc1cb8737e80cc5ea173f3b12f3da5874d792dc2`.
- eFMU SHA-256: `caa2b6d1f7359897d77ce5a4f75fc2fa1547011f7c4a7de8c04ca034dc388fc1`.

No test suite was added. **Stage decision: open.** The remaining map, adapter/artifact
and standards obligations continue to block grammar expansion.

### Shared statement/function maps: standards impact

This increment follows the previous checkpoint. It adds required annotations and mapped
printers for existing C syntax and migrates the shared initializer to that
statement path. Exact output bytes and all prior initializer execution/map
contracts are preserved. No source admission, numerical policy, public
interface or archive layout changes. The MLS 3.7, FMI 3.0.2 and eFMI Beta 1
clause maps and unresolved findings carry forward.

The generic map contracts preserve supplied origin predicates and exact UTF-8
segments. They do not prove that every production function has received the
correct source/rule attachments, nor certify arbitrary C syntax or establish
whole-file/archive maps. No new normative conformance claim follows.

All 211 earlier C audit roots are retained, with 24 additions under the same
axiom policy. The downstream package gate passed in
`build/literal-call-worktree/build/c-statement-function-map-package-gate.log`
(3324 jobs). The required main-workspace artifact gate passed in
`build/c-statement-function-map/full-gate.log`, with all 517 inventoried inputs
unchanged and both actual target archives checked. No new test
suite is added. **Stage decision: open** pending the remaining producer/map,
adapter/artifact and standards obligations; grammar expansion remains blocked.

This run produced the retained artifacts:

- FMU SHA-256: `baf7f47847d2219d38b6a5fdd48ca0f1a073c27037537a560cf89527413db2aa`.
- eFMU SHA-256: `619669cd9e8009a04174f26fad2b057fcb6b33b0012c371e2003cce59018106f`.

### eFMI Startup maps: standards impact

This increment follows the previous checkpoint. Production and archive export now use the
Startup map renderer; a theorem proves that the complete C bytes remain
unchanged. Its origins come from the prepared Solve trace, with separate shared
C instruction and eFMI interface rules. The production contract additionally
requires exact complete-file map ranges, independent annotation requirements,
distinct state/period source ancestry and every Startup execution behavior.
Existing source, numerical, metadata, interface and archive-layout contracts
are retained. No source admission or standards-profile change occurs; the
MLS 3.7, FMI 3.0.2 and eFMI Beta 1 clause maps/findings carry forward.

All 105 earlier eFMI production audit roots remain, with 22 additions under the
unchanged axiom policy. All downstream package checks passed in
`build/literal-call-worktree/build/efmi-startup-map-package-gate.log` (3337 jobs).
The required main-workspace artifact gate passed in
`build/efmi-startup-map/full-gate.log`, with all 522 inventoried inputs unchanged.
It checked both actual archives and the existing native, extraction, schema,
checksum, mutation and publication controls. Retained products:

- FMU: `66da9eb46b57b878f89c0b6c89627d50221614a3fc86a66ab2ee7aab3647c2aa`.
- eFMU: `d2fb726a2387bd1608fa743674f49b54899c4232957c871f90dca975918a853a`.

The computed map applies to Startup and the certificate's supplied input. Header/later-method
maps, archive map serialization and original-to-staged input identity remain
open. No additional test suite was created. **Stage decision: open**; existing
adapter/artifact and compliance findings continue to block grammar expansion.

### FMI reset and adapter-byte binding: standards impact

The candidate on top of the previous checkpoint leaves both EBNFs, production admission,
emitted C, metadata and archive contents unchanged. The header reader's
accumulator implementation preserves its earlier behavior by theorem. MLS 3.7
and eFMI Beta 1 clause mappings above remain applicable to this unit profile;
there is no new source or GALEC case.

| Applicable obligation | Added proof correspondence | Remaining obligation |
| --- | --- | --- |
| MLS §§4.9 and 8.6: stored Real values and selected initialization. | The complete reset call's returned heap supplies the finite value used by `ResetSourceResult`, with the same compiled Solve default and unique initialized source trajectory. | Reset does not add an initial source equation. Host-set/initialization composition and SR08 remain open. |
| FMI 3.0.2 §2.3.1: reset restores defaults and Instantiated; initialization precedes a new run. [Normative reset clause](https://fmi-standard.org/docs/3.0.2/) | `Reset.correct` and `Reset.FunctionContract` cover termination, eight writes, default state, clock/stop fields and all other memory cells for both interface kinds and declared modes. | Allocation and equivalence to a freshly instantiated object, logging/callback policy and complete cross-call lifecycle composition remain open. |
| FMI §2.2.4: error recovery and instance isolation. | Reset also covers Terminated; `other_instance` preserves every cell in other blocks. | General error/callback execution and native object layout remain outside this result. |
| FMI C source artifact binding. | `SourceBuildContract.adapter` requires exact complete adapter bytes, unique printed definitions, the reset signature and its independently specified function/call contract. | Whole translation-unit/preprocessor meaning, official-header/ABI correspondence, all other public bodies and complete archive composition remain open. |
| eFMI Algorithm/Production Code. | Existing DAE→GALEC→Solve, Startup and production/archive contracts are retained. | This FMI-only increment closes no eFMI finding. |

The 27 new roots and existing package audits pass under the unchanged axiom
policy. The focused printer certificate and added reset-body mutation pass.
The complete fixed actual-file check passes in `build/fmi-reset/actual-file.log`;
the required main-workspace gate also passed in `build/fmi-reset/full-gate.log`,
with all 529 inventoried inputs unchanged and both target archives checked.
The integrated checker reuses the
existing character-join theorem and kernel-checked segment composition to
reduce proof-checking cost without changing its proposition.
**Stage decision: open**; SR04, SR05, SR07,
SR08 and the remaining provenance/adapter obligations continue to block growth.
See [the precise contract](fmi3/contracts.md#reset-and-complete-adapter-bytes).

## Original FMI/eFMI snapshot and evidence

Reviewed source revision: the previous checkpoint.
The production profile remains one state with `der(x) = 1`. The development
array/Jacobian kernels have separate proofs; the production CLI still rejects
those models. This review does not establish conformance for that future slice.

Normative references are [FMI 3.0.2](https://fmi-standard.org/docs/3.0.2/)
and [eFMI 1.0.0 Beta 1](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip).
The official [eFMI resources page](https://www.efmi-standard.org/resources/)
still identifies Beta 1 as a release candidate. Its downloaded complete
archive has SHA-256
`da5caf207aca412b5601cafaaf72d4e613d1c78964e3f39afc6a5a3d06281a89`.
The prose and schemas in that archive are the authority; the checker is
additional evidence, not the definition of the standard.

Generated artifacts were snapshotted before the ongoing full gate could
replace them. The relevant emitter sources were unchanged at the reviewed
revision. Artifact identities are:

| Snapshot | SHA-256 |
| --- | --- |
| `build/Integrator.fmu` | `c50dbceb8202988df9fe38f159187af8a994eafb9edf8da33ad3edea62342438` |
| `build/Integrator.efmu` | `66104a67886d39f70507220c21586347928d1ab82e541ad3e6de6ed9695c3dbf` |

Local evidence is under `build/standards-review/`: `artifacts.json` records
inventories, `probe.py` and `probe-results.json` record the native/source/XML
experiments, and `checker/` records independent checker runs. These are
disposable review experiments, not an added permanent test suite. The results
and reproduction details below remain useful if `build/` is cleared.

## Findings

P1 means a release or integration blocker to repair before backend expansion.
P2 means a smaller interface defect or a policy question requiring resolution.
An evidence gap is distinguished from a demonstrated runtime failure.

### SR01 — P1: source build metadata omits the math-library dependency

[Metadata.buildDescription](../packages/backend-fmi3/RumocaFMI3/Metadata.lean)
lists `model.c` and `fmi3.c` with C11, but no library dependency. The adapter
calls `fegetround`. [Package.archive](../packages/backend-fmi3/RumocaFMI3/Package.lean)
adds `-lm` outside that metadata, as does
`test_sources_rebuild_without_lean` in [the existing integration check](../tests/fmi3.py).
The packaged HTML tells a human to link libm; an importer using only the build
description does not receive that instruction.

**Reproduced:** compiling the listed sources into a shared object without an
extra library succeeds on the current Linux toolchain, but a standalone
`dlopen(..., RTLD_NOW | RTLD_LOCAL)` executable fails with
`undefined symbol: fegetround`. The same executable loads the shipped binary.
The loader links only libdl, avoiding accidental resolution through Python's
already-loaded math library. All other numerical compiler flags were retained.

FMI §2.4.10 makes the build configuration responsible for the required compile
and link information. The missing library is a concrete source-import defect;
it does not mean the shipped binary fails to load.
See [Build Configurations](https://fmi-standard.org/docs/3.0.2/#BuildConfiguration).

**Close with:** an explicit supported-platform build description that includes
the required library and floating-point compilation profile, correlated with
the packaged build. Reuse the source-rebuild check, deriving dependencies from
the XML rather than hard-coding the producer's missing flags. Bind the declared
configuration to the same artifact contract. Native linking remains a tested
boundary; do not describe compiler flags as a machine-code proof.

**Repaired for the declared source profiles:** shared Linux/GCC recipes now drive both the XML and
native argument list. `Build.ArtifactContract` independently decodes each
platform's declared compiler, options, sources and math dependency and binds
the actual XML characters. `FMI3.SourceBuildContract` retains the complete
numerical C contract as a conjunct. Six new audit roots pass in
`build/fmi-build-package.log`; the required full gate passed in
`build/fmi-build-full-gate.log`. The existing rebuild now consumes the published
XML and resolves symbols in a separate process, avoiding Python's ambient
libm. The actual-file, official-schema, native and mutation checks pass in
`build/fmi-build-artifact-gate.log`. The actual FMI adapter/model-description/archive
capstone remains open.
The checked FMU has SHA-256
`c3019d6e316b65f8de3a279d48b66276433cbec151ac566322b46af37337d70f`.
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34502115582)
also passed.

### SR02 — P1: two source FMUs collide at the numerical C symbols

[C.render](../packages/backend-c/RumocaC/Codegen.lean) exports `rumoca_rhs`,
`rumoca_step` and `rumoca_sample` with external linkage. The
[FMI adapter](../packages/backend-fmi3/RumocaFMI3/Runtime.lean) refers to those
unprefixed names. FMI API prefixing changes none of them. Metadata also uses
the fixed model identifier `RumocaModel` for every source model.

**Reproduced:** compile the two adapter copies with distinct
`FMI3_FUNCTION_PREFIX=A_` and `B_`, compile their numerical members separately,
then combine the four objects with `cc -r`. Linking fails with three multiple
definitions, one for each numerical symbol. Distinct FMI API prefixes therefore
do not suffice to compose these generated source packages in one executable.

FMI §2.4.10 recommends minimizing exported symbols to prevent such collisions.
This is an embedded/source-integration defect, not a claim that every
separately loaded binary FMU is invalid.
See [source-file linkage guidance](https://fmi-standard.org/docs/3.0.2/#BuildConfiguration).

**Close with:** private numerical helpers in a single integration translation
unit, or a consistently namespaced numerical interface. Preserve the shared
backend's Solve-only ownership and certify the chosen declaration/name
transformation. Account for the model identifier and helper namespace together.
Keep one source-link boundary check; do not duplicate numerical test matrices.

**Repair in progress:** the shared C printer, independent declaration grammar,
statement tokens and complete existing compiler contract now support external
and `static inline` internal linkage. FMI compiles one `fmi3.c` translation
unit which includes the certified private `model.c`. The numerical behavior,
termination and rounding obligations remain unchanged. A parsed model name
produces the valid C identifier `Rumoca_` followed by that name; the map is
proved injective for distinct names. This does not promise globally unique
identifiers for unrelated artifacts with the same model name.

Build XML and ME/CS metadata use that identifier; the actual adapter begins
with its `FMI3_FUNCTION_PREFIX` and private-kernel include. The producer uses
the official header's `FMI3_OVERRIDE_FUNCTION_PREFIX` when compiling the
unprefixed binary ABI, as specified by [FMI §2.2.2](https://fmi-standard.org/docs/3.0.2/#header-files-and-naming-of-functions).
`FMI3.SourceBuildContract` adds actual XML identity observations and an exact
source-prefix fragment to the internally linked numerical contract. The
adapter remainder, preprocessing, native linking and complete archive remain
outside that proposition; the fragment is not a proof of the entire adapter.

Thirteen new roots and the generalized existing compiler/C roots pass the
unchanged axiom audit in `build/fmi-linkage-package.log`. The actual-file gate
caught a Lean stack overflow while certifying the 45 KB adapter prefix equality,
before publication. The fixed file reader now quotes all independently read
characters in bounded blocks. `sourcePrefix_of_chars` derives the unchanged
string-decomposition contract from the checked prefix; the trusted input
encoding uses `String.ofList` of those actual characters. No native equality
check authorizes acceptance, no character is omitted, and the theorem uses the
same axiom whitelist. The actual-file certificate passes in
`build/fmi-prefix-certificate.log`. The integrated importer and native checks
pass, including two actual source FMUs rebuilt from their own XML recipes,
only their distinct FMI APIs exported, and fresh-process symbol resolution.
A changed source prefix is rejected before native compilation, and a failed
native build preserves the existing FMU. The complete targeted gate passed in
`build/fmi-linkage-artifact-gate.log`. The required full local gate passed in
`build/fmi-linkage-full-gate.log` at the previous checkpoint.
Its checked FMU has SHA-256
`780186d9d0694b2da60d06e55e55c4a8100d2fafca86b2198026b9adc21902ea`.
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34509004071)
also passed. This closes the checked source-linkage correction;
the broader FMI capstone remains open.

### SR03 — P1: eFMI status returns have no logical error-status mapping

[Manifest.algorithm](../packages/backend-efmi/RumocaEFMI/Manifest.lean)
declares `ErrorSignalStatus id="ERROR_Status"`. Each Production C function
declares an `EfmiStatus` return (`CR_Startup`, `CR_Recalibrate`, `CR_DoStep`).
However, `logicalData` maps only `AV_State` and `AV_Clock` through the instance
parameters. **The actual Production manifest has zero references to
`ERROR_Status`.** A consumer cannot identify the error-status result through
that declared anchor.

Beta 1 §3.1.4 defines this anchor for derived-code status access; §3.2.5 §1.6
defines the 32-bit error encoding. §5.1.5 specifies logical-to-physical mappings.
The omission matters even when the successful unit profile always returns zero.
See the [official Beta 1 specification](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip).

The current [MappedResult](../packages/backend-efmi/RumocaEFMI/ManifestProofs.lean)
proves that execution returns zero and that declared state/clock mappings read
the right values. It **does not prove that the status is discoverable through
the XML anchor**. The [compiler manifest contract](../packages/compiler/Rumoca/EFMIManifestProofs.lean)
inherits this omission. XML schema validation and the official checker's deeper
checks both accept the manifest, illustrating the missing semantic obligation.

**Close with:** a decoded status mapping for every block-interface method,
connected to its actual declared C result and Algorithm Code anchor. First
resolve the Beta 1 representation of a return-value reference against the
schema/prose; do not invent an unsupported XML element. Prove uniqueness,
reference/type validity and observation of the executed status. Strengthen the
existing manifest and complete-archive contracts in the same change, with one
missing/redirected-status mutation. No new GALEC error language is needed for
the zero-status unit profile.

**Repaired for the unit profile:** the [status correction](efmi.md#error-status-mapping-correction)
implements a mapped instance field and proves its agreement with each method
result, including uninitialized Startup storage. The nine new audit roots,
native C observations and three official schemas pass. The required full gate
passed in `build/efmi-status-full-gate.log`, including the actual archive
certificate and redirected-status rejection. The checked eFMU has SHA-256
`712a9819677fad8fef65a672fffbbe8ca038540126a6d56fc2cd2071e63ed646`.
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34499145712)
also passed.
The reviewed snapshots above describe the earlier artifact that exposed the
omission. Broader eFMI compliance and release obligations remain open.

### SR04 — P2: nominal-state access is admitted before initialization

[Lifecycle.permittedModes](../packages/core/RumocaCore/FMI3/Lifecycle.lean)
includes `Instantiated` for `getNominals`. Its `Reference.Allowed` predicate
includes the same extra case. Thus `allowed_correct` cannot expose this
specification mismatch.

**Reproduced:** immediately after ME instantiation,
`fmi3GetNominalsOfContinuousStates(instance, &value, 1)` returns `fmi3OK` and
writes `1.0`. FMI lists this call in Initialization, Initialized and Terminated;
it is absent from Instantiated. The status rules require Error for detected
invalid-state calls. See [common states](https://fmi-standard.org/docs/3.0.2/#common-state-machine)
and [return statuses](https://fmi-standard.org/docs/3.0.2/#status-returned-by-functions).

**Close with:** correct the independently reviewed lifecycle predicate and
generated guard together, retain the generalized guard proof, and cover this
rejection through the existing error/lifecycle contract. A small addition to
the existing ABI lifecycle check is sufficient at the native boundary.
State-count and event-indicator-count queries are explicitly listed in
§2.3.2's Instantiated calls; their separate `getCounts` rule is retained.

**Correction in progress:** the table and independently reviewed predicate
now exclude Instantiated specifically for nominal queries. The core theorem
`nominals_reject_instantiated` feeds the existing general guard proof.
`ErrorBodies.nominals_reject_run` proves that the actual generated body reaches
the failure call before reading or writing output storage, preserving the whole
heap. `nominals_reject_reaches` carries that result into the typed C call machine.
The existing ME lifecycle test now checks both logging settings, unchanged
output on rejection, final observations and reset/reinitialization.

`ErrorBodies` also proves the actual error helper's mode write and logging
dispatch for both logging branches, the exact callback arguments, and complete
body-entry termination/frame when logging is disabled. It does **not** execute
an enabled callback or bind the helper's string parameter. Those obligations
prevent composition into a complete public failed-call theorem. The generated
nominal query bytes are not yet covered by the numerical/prefix file contract.
SR04's full proof closure therefore remains open despite the corrected guard.

The generic `CBodyEmbedding` proof reuses successful memory-body runs in the
typed tensor-call machine. Instantiating its scope check exposed a nested
`Instance *m` declaration in SetFloat64's empty-array branch. `CLoops` explicitly
rejects nested declarations because it lacks C block scopes. The initial FMI bridge
excluded that body; no scope check was relaxed. Public array-parameter
adjustment, string argument conversion and indirect callbacks remain separate
target-semantics gaps. These are proof coverage findings, not evidence that the
emitted C's lexical block is illegal. Resolve them before full FMI composition.

Sixteen added audit roots pass the unchanged axiom policy in
`build/fmi-error-embedding-audit.log`. The existing native lifecycle group
fails on the preceding FMU (`build/fmi-nominals-before.log`, OK instead of
Error), and the corrected FMU passes all thirteen groups and the actual-file,
source-link, mutation and publication-failure gate in
`build/fmi-nominals-artifact-gate.log`. The required full gate passed in
`build/fmi-nominals-full-gate.log` at the previous checkpoint; its checked FMU has SHA-256
`1de662a5191c62573f146fc47781473d81400432b0a5a646ce1681bee4468e0f`.
[the hosted CI run](https://github.com/CogniPilot/rumoca_lean/actions/runs/34512618273)
also passed. This validates the guard correction while its full failed-call
proof obligations remain open.
No additional grammar case is admitted.

**Scope correction:** the instance declaration is now hoisted before the
empty-array branch, and both paths reuse one mode-guard constructor. The
existing validation/write suffix is unchanged. `SetterScope` proves the
hoisting law for arbitrary suffixes and caller continuations, preserving all
behaviors in `CCalls`, including wrong/divergent outcomes. It also proves the
actual emitted empty/null bodies terminate with unchanged memory in the typed
C machine and connects nonempty entry to the existing lifecycle predicate.
`BodyEmbedding.body_closed` now covers every generated signature without an
exclusion. The original `noDeclarations` restriction is retained; general C
block scopes have not been added. Nine new roots pass
`build/fmi-setter-scope-audit.log`. All thirteen existing native groups and the
actual-file/source-link/mutation gate pass in
`build/fmi-setter-scope-artifact-gate.log`. The existing argument/atomicity group
also checks null setter calls and empty-call state preservation. The required
full gate passed in `build/fmi-setter-scope-full-gate.log` at the previous checkpoint, and
[its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34516914151)
passed. The full-run FMU has SHA-256
`765662ef91d429089b4a22fd12dd29ec885f375a39a173c02bd4c8c35343a56f`.

**Public entry correction:** C array parameters previously failed before body
entry even for valid pointer arguments. The authored C machine now implements
the unsized-array adjustment in [C11 N1570 §6.7.6.3 paragraph 7](https://www.open-std.org/jtc1/sc22/wg14/www/docs/n1570.pdf),
retaining explicit type resolution and rejection of unknown types, duplicate
names, arity mismatches and unsupported conversions. Generic proofs derive
coherent local value/type environments; complete ME continuous-state get/set
call theorems include entry, exact state observation/update, whole-heap results
and ordinary returns under arbitrary continuations. The existing body proofs
are reused with the same runtime function constructor as the renderer.
The FMI dictionary adds only the two required Float64 pointer spellings.
All twelve new roots and the full package audit pass in
`build/fmi-array-call-audit.log`. The FMI actual-file/source-build/mutation gate
and all thirteen existing native groups pass in `build/fmi-array-call-full-gate.log`.
The full run also passed its GALEC/eFMU archive, extracted-manifest and mutation
checks at the previous checkpoint; [its CI](https://github.com/CogniPilot/rumoca_lean/actions/runs/34521375057)
passed. These are selected function-tree call theorems with
explicit definition-table and storage premises, not an official-header parser,
actual adapter-byte or native ABI certificate. Remaining public signatures,
string binding, enabled callbacks and nonempty SetFloat64-loop execution remain
open; SR04 is not closed by this increment.

**Rejected public-call follow-up:** [ErrorCalls](../packages/backend-fmi3/RumocaFMI3/ErrorCalls.lean)
now supplies ordinary string-pointer parameter binding and composes the
nominal-query rejection through the failure helper's return with logging
disabled. Its all-behavior theorem includes the exact mode change and memory
frame. The [pointer/call checkpoint](#c-literal-pointer-and-rejected-call-increment-standards-impact)
records the full local gate and actual artifacts. Enabled callbacks, literal
global setup and complete printed adapter binding still prevent SR04 closure.

### SR05 — resolved for the unit initialization policy

At the previous checkpoint, [Runtime.body](../packages/backend-fmi3/RumocaFMI3/Runtime.lean) rejected enabled
`stopTime <= startTime` and `tolerance <= 0` for both interfaces. On the actual
binary, zero-duration and zero-tolerance initialization each return Error;
ordinary initialization returned OK. The theorem at that revision correctly
proved the authored strict policy.

The reviewed initialization clause does not specify those exact strict
inequalities and permits CS to ignore tolerance. This is an unresolved
admission-policy question, **not a demonstrated unconditional requirement to
accept every such argument**. See
[FMI §2.3.2](https://fmi-standard.org/docs/3.0.2/#fmi3EnterInitializationMode).

**Close with:** justify each restriction from the numerical profile and
normative call contract, or relax it and update both reference and execution
proofs. Separate tolerance handling from stop-time validity. Review the entire
rejected-call behavior, including the resulting lifecycle state; do not infer
conformance just from `guard_reference`.

The [initialization correction](#complete-initialization-calls-standards-impact)
implements and proves the inclusive-stop/unused-tolerance policy together with
complete failure, logging and source-IVP contracts. Its actual-file requirement
is integrated and the required full gate passed with 706 unchanged inputs.
This resolves the scoped admission-policy finding. Cross-standard
initialization correspondence (SR08), instance lifetime, other public calls,
native ABI and MISRA findings remain open; no whole-stage closure follows.

### SR06 — resolved packaging question: documented checker limitation

The unmodified [official eFMI Compliance Checker v1.0.1](https://github.com/modelica/efmi-compliancechecker/releases/tag/v1.0.1),
commit `edf33452ed0628bde1d8102c77b1030259ad5f57`, was rerun with its bundled
Lark 0.12.0 and colorama 0.4.6 plus the Nix Python/lxml environment. It returns
1 for the actual `.efmu` suffix, then 1 for a byte-identical `.fmu` alias because
it requires a top-level `eFMU/` directory. This repeats the
[documented discrepancy](efmi.md#official-checker-layout-discrepancy).

**New diagnostic evidence:** a disposable `.fmu` copy with each original member
prefixed by `eFMU/` returns **0**. Logs show checks of representation identities,
checksums, schemas, manifest references, GALEC parsing, variables and methods.
The copied member contents were unchanged. This only exercises deeper checker
paths: the transformed archive is not the certified standalone product, and
its pass does not resolve SR03 or establish production-C execution correctness.

**Review disposition (2026-09-10):** the standalone layout is permitted by
[Beta 1 Chapter 2](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip).
Its second package format places the eFMU contents, including `__content.xml`,
at ZIP root with the `.efmu` extension. Its embedded FMU format instead uses
`extra/org.efmi-standard`. The pinned checker's
[entry checks](https://github.com/modelica/efmi-compliancechecker/blob/edf33452ed0628bde1d8102c77b1030259ad5f57/sources/eFMIComplianceChecker/eFMIComplianceChecker.py#L123-L170)
require `.fmu` and `eFMU/`; they do not implement the selected standalone format.
The specification archive SHA-256 and checker commit above were rechecked.

SR06 is resolved as an explicit tool limitation, with no production-layout or
verification-contract change. The loop/call checkpoint's complete local gate
checks the actual standalone archive and independently extracts its members,
schemas and checksum graph. The wrapped checker's deeper pass remains evidence
for the earlier, identified diagnostic copy only. **There is no official-checker
pass for the current standalone artifact.**

Reopen this disposition if the normative version, checker revision or selected
package format changes. It does not waive failures in member contents, GALEC,
Production C or manifests, nor close SR07, SR08 or the remaining E05/E06 proof
and release obligations.

### SR07 — existing release gaps: proof coverage and coding guidelines

The unit numerical theorem and eFMI source-to-archive theorem prove their
authored contracts. Neither establishes all prose obligations of FMI/eFMI.
For FMI, public CS time/status execution, failed calls/logging, lifetime,
correlated metadata and actual adapter/archive binding remain incomplete.
The typed tensor call result at this revision is not a tensor FMU theorem.
See [the exact contracts](../docs/verification.md) and
[FMI proof obligations](fmi3/contracts.md).

Beta 1 §5.2 also calls for coding-guideline compliance for generated C. The
repository has no complete MISRA AC AGC compliance/deviation argument. This is
missing release evidence, not a claim that a particular MISRA rule was proved
violated in this review. See
[Production Code Language in Beta 1](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip).
Functional preservation cannot replace that separate review. Native C
compilation, ABI/linkage and hardware remain outside the Lean theorem.

### SR08 — open correspondence gap: initialization across all three standards

MLS gives ordinary Real variables `fixed=false`; absent start attributes use
the applicable fallback rules. Zero is the fallback for the unit variable's
unmodified bounds. This does not itself add `x(0)=0` to the derivative equation.
See [MLS §4.9, Definition 4.7 and §4.9.1](https://specification.modelica.org/maint/3.7/class-predefined-types-and-declarations.html).
Treating an unfixed start as fixed requires a diagnostic under
[MLS §8.6](https://specification.modelica.org/maint/3.7/equations.html).

The source theorem permits a supplied finite initial state, while FMI metadata
and GALEC Startup introduce their own initialization choices. Their common MLS
justification and diagnostic policy are not yet part of one reviewed contract.
This is an unresolved correspondence finding, not a demonstrated requirement
that all three interfaces expose the same initialization API.

**Close with:** specify the source initialization relation and allowed tool/host
choices, justify each from the clauses, then connect it to FMI initialization
and eFMI Startup with lowering and actual-artifact proofs. Any required source
diagnostic must point to the relevant declaration. Keep S01 and the stage gate
open until this is checked; no new grammar is needed to resolve the policy.

## Items checked without a new defect

The artifact contains both ME and CS descriptions of the same unit model,
using an internal shared kernel. The API capability flags do not advertise
FMI directional/adjoint derivatives merely because Solve AD proofs exist.
The integer-multiple CS communication profile is documented and rejected steps
preserve the instance in the existing native check. FMI headers are supplied
by the importing environment for source builds. eFMI identities, checksums,
GALEC declarations and the two representation manifests pass the available
independent checks described above. None of this closes the open proof items.

## Repair order and early-error discipline

1. **SR01–SR03:** repair source linkage/build metadata and eFMI status metadata,
   with their printer/semantic/actual-artifact contracts. Reuse existing
   package checks and integration entry points.
2. **SR04–SR05 and SR08/S01:** reconcile lifecycle and initialization against
   cited clauses across MLS, FMI and eFMI, then prove the affected successful
   and rejected behaviors.
3. Resume the existing small tensor/FMI work: typed public wrappers, instance
   storage/metadata, finite failure policy and source-to-archive composition.
   Arrays remain rejected in production until that complete path is checked.
4. Retain SR06's documented disposition and close the SR07 release review
   obligations before claiming standards compliance or assurance comparable
   to an established verified compiler.

For each interface change, record **normative clause → independent predicate →
generated-body proof → actual-artifact observation** before implementing it.
Reviewers must challenge the predicate itself, especially if both the emitter
and reference table were written together. Use one focused external boundary
check where Lean does not model the tool or ABI; retain universal proofs for
the semantics. A passing schema validator or an extra collection of examples
does not close a missing contract.

The unchanged required gate remains
`nix develop .#verification --command lake test`; reuse cached package proofs
during local development. Review probes are not a substitute for that gate.


## Static runtime and public factory composition checkpoint — 2026-09-13

This incremental review records progress within the frozen stage. It is not a
completed recurring stage checklist, a grammar expansion, or a MISRA declaration.

- **FMI 3.0.2 §§2.2.1, 2.3.1:** the emitter uses 32 permanent shared ME/CS
  objects and bounded atomic reservation/release. The derived public-call
  theorems cover supported creation, sequential exhaustion, unsupported CS
  requests, missing/invalid identities, exact diagnostics, optional logging,
  immediate release/reuse and null release. Logging disabled implies no logger
  invocation; enabled logging retains all represented callback outcomes and
  effects. The initial value is tied to the compiled Solve plan. Full host
  histories, other-instance callback frames, native concurrency and subsequent
  initialization/operation composition remain open. Normative reference:
  [FMI 3.0.2](https://fmi-standard.org/docs/3.0.2/).
- **MLS 3.7:** source grammar, parser, lowering and numerical Solve semantics
  are unchanged. The unit derivative does not itself specify an initial value;
  the checked fallback plan selects zero and retains its existing notices.
  The creation theorem proves the stored binary64 value agrees with this plan
  and selects the unique completed source trajectory.
- **eFMI 1.0.0 Beta 1 Algorithm/Production Code:** the full static-runtime gate
  passed actual eFMU archive/source/native/mutation controls. Algorithm Code and
  Production C members are byte-identical to the published checkpoint. Their
  existing normative findings and correlated-product obligations remain open.
- **MISRA C:2025/C11:** generated factory/release code no longer calls dynamic
  allocation. Static declarations and selected atomic calls have authored
  semantics and printer contracts. The existing native checks passed pool
  exhaustion, isolation/reuse and allocator/out-of-line-atomic import checks.
  These do not prove a transitive no-heap policy or native atomic semantics.
  Essential types, remaining pointer guards, floating comparisons, native
  size/alignment/profile and the guideline matrix still block conformance.
- **Architecture:** Rust SPEC_0007 at
  `b102b3f710eb232880728d4e474292cfb07d5ce0` was rechecked. Numerical
  initialization stays in Solve, with DAE → GALEC → Solve for eFMI and
  DAE → Solve for FMI. These changes add no name resolution, shape inference,
  equation lowering or solver selection to a backend.

Evidence: `build/c-factory/static-runtime-full-gate-v1.log/.exit` passed for
793 unchanged inputs and both actual target archives. Thirteen later roots
passed two focused package audits, the last with 798 unchanged draft inputs and
all 760 published inputs unchanged. Earlier semantic/emitter/mandatory-contract
definitions and every audit root were retained. The current seven-root increment
adds three compiler proof modules and audit entries, with no new test suite.
These later package checks are not a new full artifact gate. The detailed
record is `build/c-factory/static-runtime-review-v1.md`.

**Decision:** stage remains open; do not expand the grammar or claim whole
FMI/eFMI, MISRA, native machine-code or aircraft assurance completion.

### Static creation through initialization — 2026-09-13

Seventeen additional audit roots connect creation, EnterInitialization and
ExitInitialization in one actual object-aware program. The generic C body
bisimulation proves local binding changes preserve returned values/heaps,
failure and divergence. The FMI instance proves syntax lookup and type
agreement, complete successful/null calls, and the storage premises derived
from creation. The compiler consequence retains the exact intermediate heaps,
clock, lifecycle mode, reservation flags, slot metadata and the actual finite
value's agreement with the Solve plan and completed source solution.

[FMI 3.0.2 §§2.3.2–2.3.3](https://fmi-standard.org/docs/3.0.2/) were rechecked:
initialization uses the supplied start time; exit activates ME event equations
and, with CS event mode unused in this profile, CS stepping. The theorem uses
the existing admissible finite-time profile and makes no new tolerance,
variable-step or event capability claim. Host setters and invalid subsequent
calls still need composition in this same interface. MLS/GALEC grammars,
numerical semantics and eFMI members are unchanged. Rust SPEC_0007 at
`c89fde703f82afc323d9f38bdf1e8f316452d723` retains the same DAE/GALEC/Solve
ownership boundaries; the backend reuses prepared Solve initialization.

The C/FMI/compiler package audit passed for 801 unchanged inputs in
`build/c-factory/static-initialization-packages-v1.log`; the strengthened
compiler consequence passed `static-initialization-packages-v2.log`. No prior
emitter, semantics, mandatory contract or audit root was removed or weakened.
No test suite was added. The required main-workspace integration gate then
passed with all 801 source inputs unchanged in
`build/c-factory/static-integration-full-gate-v1.log`. Its FMU/eFMU archives
and member comparisons are retained under `build/c-factory/`; only the FMI
adapter C differs from the preceding allocating artifact. Numerical C,
FMI metadata, GALEC and eFMI Production C are unchanged. Subsequent
current-status documentation cleanup changes no code or audit input.
Concurrent histories, callback frames, remaining API behavior, native ABI,
no-heap policy and MISRA obligations keep this stage open.

### Static initialization error coverage — 2026-09-13

The derived source/adapter consequence now covers successful/null calls and
initialization rejection with disabled, missing or enabled supplied logging.
The preceding initialization error contract omitted the missing-logger/enabled
flag case; the emitted guard already suppressed it. The new contracts prove
that behavior and the exhaustive nullable-pointer/Boolean case split. The
actual definitions and immutable diagnostics come from the same prepared
artifact on heaps that can include writes by earlier calls.

[FMI 3.0.2 §§2.2.1 and 2.3.1](https://fmi-standard.org/docs/3.0.2/) permit
null callbacks to identify unavailable functionality and restrict its use;
SetDebugLogging with a missing logger, for example, has undefined standard
behavior. These proofs describe the existing defensive error path; they do
not authorize arbitrary use of missing callback support. Disabled logging
causes no callback. Supplied loggers receive the Error status/category/message,
with all modeled effects retained. Native callback execution, private-storage
frames and non-reentry correspondence remain open.

The 22 new roots passed the focused FMI/compiler package audits in
`build/c-factory/static-error-package-gate-v2.log`, with 804 unchanged draft
inputs and the 801 main gate inputs unchanged. The latter full artifact gate
and its retained FMU/eFMU cover the same emitters and mandatory contracts.
No previous definition or audit root was weakened and no test suite was added.
MLS 3.7 and eFMI 1.0.0 Beta 1 language/output profiles are unchanged. Rust
SPEC_0007 at `5d0f62d147caa94e04befb9532f437b0b16cb9de` retains the reviewed
DAE/GALEC/Solve ownership. This is an incremental review within the frozen
stage; whole host histories, remaining APIs, native ABI, no-heap/MISRA and
the other recurring checklist findings remain open.
