# MISRA C:2025 enforcement ledger (K05)

This is the roadmap **K05** MISRA C:2025 enforcement matrix for the C that
lean_rumoca generates. It records, for every one of the 223 current guidelines
(22 directives, 201 rules), the category, applicability to the generated C, the
current evidence bound to the actual emitted bytes, a status, and a closure
criterion for open rows. It complements, and does not replace, the finding-level
review in
[standards-review.md](standards-review.md#misra-c2025-and-static-storage-review)
and the K05 checklist in the closure checklist.

**Normative text and provenance.** The normative guideline text is the
user-supplied *MISRA C:2025, March 2025* PDF pinned by SHA-256 in the standards
review; it is not vendored here. The guideline **titles in this ledger are
paraphrased** from the identifiers to make the table readable; where a title and
the PDF disagree, the PDF governs. The inventory (223 entries; 22 Mandatory, 154
Required, 46 Advisory, one Disapplied) and the withdrawn-ID mapping are the
figures cross-checked in the standards review.

**No unverified compliance claim.** No row is marked Compliant on inventory
alone. A row carries concrete evidence only where this pass inspected the actual
emitted bytes or cites a specific Lean theorem; those rows are the first formal
targets below and are still Open (strong partial), because native compilation,
the adopted headers, host callbacks and the full essential-type model remain
outside the current proofs. Every other applicable row is Open with a closure
criterion. The **reviewer field is unassigned for all rows**: no independent
reviewer has signed off, so independent sign-off is itself an open K05 item.

**Category caveat.** The per-row category reproduces the guideline's
commonly-published default category. The Mandatory set in particular has not
been reconciled entry-by-entry against the pinned 2025 PDF in this pass; it must
be before any deviation decision, because Mandatory guidelines cannot be
deviated. Default categories are retained; no optional recategorization is
applied.

## Compliance scope

**Generated products under review** (regenerate with the commands noted; the
paths below are from a local regeneration into `build/k05/` and `build/tensor-fmi/`):

- **Unit profile numerical kernel** `model.c` (`packages/compiler/.lake/build/bin/rumoca examples/Integrator.mo -o model.c`): three pure functions `rumoca_rhs`, `rumoca_step`, `rumoca_sample`.
- **Unit profile FMI 3 adapter** `sources/fmi3.c` inside `build/Integrator.fmu` (retained by `tests/fmi3.sh`; or `lake run fmu`). It `#include`s `model.c` and implements the full FMI 3.0 Model Exchange / Co-Simulation entry-point set over a fixed static instance pool.
- **Tensor profile FMI 3 adapter and kernel** `sources/fmi3.c` and `sources/model.c` inside the production `build/TensorSquare.fmu` (`rumoca examples/TensorSquare.mo -o build/TensorSquare.fmu`; `tests/fmi3.sh`). The default CLI publishes this profile through the `tensor-fmi3` actual-artifact certificate. `build/tensor-fmi/adapter.c` and the individual helpers in `build/tensor-c/*.c` remain development inspection products from `tests/tensor-c.sh`; they do not replace review of the complete production translation unit.
- **Constant-rate FMI 3 adapter and kernel** `sources/fmi3.c` and `sources/model.c` inside `build/ConstantRates.fmu` (`rumoca examples/ConstantRates.mo -o build/ConstantRates.fmu`; `tests/fmi3.sh`), published through the `constant-fmi3` actual-artifact certificate. The pinned source has two states and rates `2.5` and `-1`. Rule-by-rule evidence must cover this product too; prior unit/tensor scans do not establish its compliance. Constant eFMI output remains rejected.
- **Unit eFMI Production Code** `ProductionCode/production.c` inside the eFMU (`rumoca Source.mo -o model.efmu`; `tests/efmi-production.sh`): `UnitIntegrator_Startup`, `UnitIntegrator_Recalibrate`, `UnitIntegrator_DoStep` over a plain `Model` record.
- **Tensor eFMI Production Code** in `build/TensorSquare.efmu`, published through the `tensor-efmi-archive` actual-artifact certificate and checked by `tests/efmi-production.sh`. `build/tensor-efmi/ProductionCode.c` is a development inspection product. The tensor translation unit, generated headers and manifests must be included in the remaining product-level review; the unit eFMI evidence is not a substitute.

**Adopted headers (compliance boundary, not authored here).** The FMI 3 headers
`fmi3Functions.h`, `fmi3FunctionTypes.h`, `fmi3PlatformTypes.h`
(`packages/backend-fmi3/vendor/fmi3/`), and the C Standard headers the adapter
includes: `<stdint.h>`, `<float.h>`, `<math.h>`, `<string.h>`, `<fenv.h>`,
`<stdatomic.h>`. Per MISRA C:2025 Section 1.5.4 the Standard Library's own
implementation is out of scope, but the project's transitive no-allocation and
RTOS obligations still require evidence about what the generated code calls.
FMI headers are not Standard Library headers and are inside the boundary.

**Language profile.** C11 (Section 1.4 supports it; the earlier C90-only
concern from the 2004 baseline does not apply). Every translation unit begins
with a binary64 guard: `#if FLT_RADIX != 2 || DBL_MANT_DIG != 53 || DBL_MAX_EXP
!= 1024 || DBL_MIN_EXP != -1021 || FLT_EVAL_METHOD != 0` `#error`. The adapter
additionally asserts `_Static_assert(ATOMIC_BOOL_LOCK_FREE == 2, ...)`.

**Compiler options** (from `packages/backend-fmi3/RumocaFMI3/BuildDescription.lean`
and echoed into each FMU `sources/buildDescription.xml`): `gcc -std=c11 -O2 -Wall
-Wextra -Werror -Wno-unused-parameter -pedantic -fno-fast-math -ffp-contract=off
-frounding-math`; the shared object adds `-fPIC -shared
-DFMI3_OVERRIDE_FUNCTION_PREFIX -I <fmi3 headers> -lm`. The tensor-C and eFMI
boundary checks use the same strict flags (plus `-frounding-math` for the eFMI
driver). Compiler acceptance under these flags is a boundary check, not a MISRA
conformance argument.

## Generator documentation (MISRA Compliance:2020 and Appendix E)

Section 1.5.2 requires a MISRA Compliance:2020 summary and Section 1.5.3 /
Appendix E require automatic-code-generator documentation. The four required
items, recorded here as the current state, all still open for completion:

- **Implementation choices (Dir 1.1).** Modelica `Real` is IEEE 754 binary64;
  the target is checked for it at compile time via the `#error` guard above.
  `size_t` is modeled as 64-bit; integer widths, ABI and the floating
  environment rely on the pinned platform types. The generator is deterministic
  and its output is fixed per source; the Lean proofs certify the modeled C, and
  the generator itself is untrusted (`packages/compiler/Certify.lean` prints and
  checks each artifact's axiom footprint). Native compilation and header
  preprocessing are trusted boundaries, not proven.
- **Essential-type strategy.** Emission is typed through the C memory model's
  `CType`/`convert` gate (`packages/backend-c/RumocaC/Memory.lean`) with
  per-operation conversion lemmas (for example
  `IntegerConversions.integer_float64`). There is **no dedicated MISRA
  essential-type-model theorem yet**; Rules 10.1-10.8 therefore remain open, and
  the concrete mixing sites found in the bytes (below) are the first work items.
- **Runtime failure policy (Dir 4.1, Dir 4.15).** The adapter validates
  identity and pointers, guards every call against the FMI state machine
  (`RumocaCore/FMI3/Lifecycle.lean` `allowed`, compiled to a `modeGuard`),
  checks array lengths, requires round-to-nearest (`fegetround() ==
  FE_TONEAREST`), and returns `fmi3Error`/`fmi3Discard` on the rejected paths;
  it performs no dynamic allocation, so there is no allocation-failure path.
  Floating-point error evaluation (Dir 4.15) beyond the round-mode check and the
  `isfinite` guards is not yet argued.
- **Integration interface.** The user integrates through the FMI 3.0 C API with
  the pinned vendored headers; the host supplies the `fmi3InstanceEnvironment`,
  the `fmi3LogMessageCallback` logger, and (Co-Simulation) the intermediate/clock
  callbacks. Host-callback reentry, native RTOS timing/stack, and the C11 atomic
  implementation are documented as separate assumptions, not proven here.

## First formal targets: concrete observations

All greps below use case-sensitive GNU-`grep` semantics over the regenerated
bytes; the tool wrapper in this environment matches case-insensitively, so
`LOCK_FREE` is the only apparent "free" hit and is not an allocator.

- **Allocation (Dir 4.12, Rule 21.3).** No allocator **call site**
  `(malloc|calloc|realloc|free|aligned_alloc)\s*\(` appears in any generated
  file (unit `model.c`/`fmi3.c`, tensor `adapter.c` and `build/tensor-c/*.c`,
  eFMI `production.c`); `<stdlib.h>` is not included anywhere. Instances live in
  a fixed `static Instance rumoca_instances[32]` pool with a `static atomic_bool
  rumoca_instance_flags[32]` reservation block and a `static const size_t
  rumoca_instance_capacity` (emitted by `StaticStorageCode.render`). This
  supersedes the older MC02 observation that the runtime emitted `calloc`/`free`:
  the current default emission has no allocator. Lean coverage:
  `StaticSlots`/`SlotOwners`/`AtomicSlots` (reservation, exclusion, exhaustion,
  release/reuse) and `HeapFreeExpressions.heap_free`; the `Memory.lean` model has
  no allocation primitive at all. Not covered: a single transitive whole-program
  no-heap theorem, libm/atomics/string.h internals, and native compilation.
- **Recursion (Rule 17.2).** The direct-call graph is acyclic. Lean:
  `Rumoca.FMI3.CallPolicy.source_program_policy`
  (`packages/compiler/Rumoca/FMI3CallPolicy.lean`) proves the emitted adapter's
  prepared function table is ranked by `functionRank` and has no cycle (for every
  `ProgramEdge caller callee`, `callee` cannot reach `caller`), via
  `CallPolicyProofs.program_no_cycle` and `CallPolicy.complete_program_no_cycle`.
  Independently reproduced on the actual bytes: a brace-matched call graph over
  the unit `model.c`+`fmi3.c` (83 defs), the tensor `adapter.c` (78 defs) and the
  tensor kernel (8 defs) has **no self-recursion and no cycle**. Not covered:
  foreign leaves (`floor`, `isfinite`, `fegetround`, `atomic_exchange`, `memcpy`),
  the host logger callback, and native linkage are outside the ranked set.
- **Initialization (Mandatory Rule 9.1; Rule 9.7).** Every automatic object is
  initialized at its declaration (for example `size_t k = 0;`, `_Bool busy =
  ((_Bool)0);`, `double next = ...`, `int rounding = fegetround();` in `fmi3.c`;
  `double v0 = ((double)0);` in `production.c`). The reserved static `Instance`
  is fully field-initialized before it is returned in
  `fmi3InstantiateModelExchange`/`CoSimulation`. No bare uninitialized scalar
  local was found. The atomic flags are `static`-storage (zero-initialized).
  Being Mandatory, Rule 9.1 admits no deviation; it stays Open pending an
  independent definite-initialization predicate and a native storage/lifetime
  correspondence (MC05).
- **Essential types / floating equality (Rules 10.1-10.8).** Exactly two
  floating variable-to-variable inequalities remain, both exact FMI time-grid
  checks not covered by Rule 10.1's zero/infinity exceptions:
  `currentCommunicationPoint != (m->time)` and `floored != communicationStepSize`
  (unit `fmi3.c:1085,1103`; identically in the tensor adapter at `1133,1151`). No
  floating `==` is emitted. Additional mixing sites: unsigned
  `valueReferences[k]` compared with signed integer constants `0`/`1`/`2` and
  `> 2`, and `double` operands combined with signed integer constants
  (`communicationStepSize <= 0`, `> 1000000`). Rule 10.1 is a Deviation
  candidate; an epsilon repair is not an equivalent fix, and the exact FMI time
  semantics must be preserved.
- **Pointer comparisons (Rule 11.11, Rule 11.9).** The earlier scan counted
  75 `(ptr == ((void *)0))` / `!=` comparisons in unit `fmi3.c`, 77 in
  the tensor adapter, and zero direct `if (!ptr)` / `if (ptr)` tests. That scan
  missed the implicit pointer operand in the logger's `&&` expression and does
  not establish that all guards are explicit. The regenerated development tensor
  adapter now uses an explicit logger comparison at all three shared logger
  sites, and its standalone-object boundary check passes. Known implicit tests
  remain: `Runtime.pointerCheck` emits, for example, `!nEventIndicators` and
  `!eventHandlingNeeded` inside disjunctions; tensor Float64 guards also emit
  `!valueReferences` and `!values`. The logger repair passed the required full
  artifact gate in `build/logger-contract-full-gate-v2.log`; the later
  numerical-linkage gate retains it. This does not close the residual violations. The
  null constant is `((void *)0)` in comparisons and `NULL` in `return NULL;`; no
  integer zero is used as a null pointer constant. Lean: the null value and
  comparison semantics are `CNull.literal_contract` and `CNull.comparison_iff`
  (`packages/backend-c/RumocaC/NullPointerPrinter.lean`,
  `NullComparison.lean`), with the emitted idiom produced by `instancePrefix`
  (`Runtime.lean`). Not covered: equality of two non-null pointers, relational
  pointer comparison, and native address assignment.

## Reconciliation with the finding-level review (MC01-MC10)

The finding IDs in
[standards-review.md](standards-review.md#misra-c2025-and-static-storage-review)
map onto this ledger as follows. **MC02 (allocation) is the one place the review
text is now stale**: it states the runtime emits `calloc`/`free`, but the current
default emission uses the static pool and no allocator call site remains (see Dir
4.12 / Rule 21.3 rows). MC03 is Rule 15.5 (Disapplied). MC04 is Rules 10.1-10.8
(Deviation candidate at 10.1). MC05 is Rule 9.1/9.7 and the lifetime rows. MC06
is Rules 13.2/13.5, 17.2 and Dir 5.1-5.3. MC07 is Rules 5.x, 11.x, 18.x, Dir 3.1.
MC09 is Rule 11.11 (the earlier scan missed logical operands: the logger is
repaired locally, while output/accessor pointer negations remain known violations).
MC01 is Rule 1.1 and Dir 1.1; MC08 is the eFMI mapping below; MC10 is the nested
aggregate address correction underlying Rule 18.x. None of these findings is
closed by this ledger; the ledger records where each stands against the actual
bytes.

## eFMI reference mapping (MC08)

eFMI 1.0.0 Beta 1 references its own MISRA baselines, which MISRA C:2025 does
**not** silently discharge (roadmap K05; MC08). They must be mapped and reviewed
separately:

- **MISRA AC AGC** (Autocode / Automatically Generated Code guidelines) is
  referenced by eFMI Beta 1 (Production Code section) for generated code. AC AGC
  recategorizes several MISRA-C:2004 rules for generated code (many
  readability/style rules are relaxed for autocode). It is not a superset of
  MISRA C:2025 and is not enforced by the 2025 matrix; the eFMI Production Code
  (`production.c`) must be reviewed against AC AGC on its own terms.
- **MISRA C:2012** is named by eFMI's GALEC/Production rules. The 2012 to 2025
  renumbering that matters here: Rule 1.2 became Dir 1.2; Rule 11.7 folded into
  11.4; Rule 17.6 became 17.5; Rule 21.1 moved to 20.15; Rule 21.2 moved to 5.10.
  MISRA C:2025 also adds the C11/C18 concurrency and generic-selection families
  (Rules 21.21-21.26, 22.11-22.20, 23.1-23.8, plus 6.3, 9.7, 12.6, 8.15-8.19)
  that MISRA C:2012 predates; a 2012-based eFMI claim does not address these.
- Neither eFMI reference closes SR07/SR08. The eFMI Production Code review is
  tracked under eFMI E05-E06 and MC08, distinct from this C:2025 ledger, though
  `production.c` is inventoried here for the shared no-allocation and
  initialization observations.

## Row counts by status

Across the 223 current guidelines (the five withdrawn IDs are tracked in their
own table and excluded from these counts):

| Status | Count |
| --- | --- |
| Disapplied (Rule 15.5) | 1 |
| Deviation candidate (Rule 10.1) | 1 |
| Open (strong partial): Dir 4.12, Rule 21.3, Rule 17.2, Rule 11.11 | 4 |
| Open (partial; Mandatory): Rule 9.1 | 1 |
| Open (partial): Rule 11.9 | 1 |
| Open | 215 |
| **Total current guidelines** | **223** |

No guideline is Compliant. The Advisory/Required/Mandatory and applicability
work, the independent predicates for the Open rows, the essential-type model, and
independent reviewer sign-off all remain open K05 obligations.

## The matrix

Each row: ID, category (default), applicability to the generated C, current
evidence bound to the actual bytes or a named Lean theorem, status, and the
closure criterion for open rows.
### Directives

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Dir 1.1 | Required | Implementation-defined behaviour the output depends on shall be documented and understood | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 1.2 | Advisory | Use and document language extensions with caution (renumbered from Rule 1.2) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 2.1 | Required | All source files shall compile without errors | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 3.1 | Required | All code shall be traceable to documented requirements | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.1 | Required | Run-time failures shall be minimized | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.2 | Advisory | Use of assembly language should be documented | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.3 | Required | Assembly language shall be encapsulated and isolated | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.4 | Advisory | Commented-out code sections should not be present | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.5 | Advisory | Identifiers in the same name space should be typographically unambiguous | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.6 | Advisory | typedefs of specific-length shall be used instead of the basic numerical types | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.7 | Required | A function returning error information shall have that information tested | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.8 | Advisory | Hide the implementation of a structure/union where a pointer is never dereferenced | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.9 | Advisory | A function should be used in preference to a function-like macro | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.10 | Required | Header files shall be protected against repeated inclusion | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.11 | Required | Validity of values passed to library functions shall be checked | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.12 | Required | Dynamic memory allocation shall not be used | Applicable: grep of the actual bytes: no allocator call site `(malloc\|calloc\|realloc\|free\|aligned_alloc)(` in build/k05/unit-fmu/sources/fmi3.c, build/k05/model.c, build/tensor-fmi/adapter.c, the build/tensor-c/*.c kernel, or build/k05/efmi/.../ProductionCode/production.c; no <stdlib.h> included. Storage is a fixed `static Instance rumoca_instances[32]` pool (StaticStorageCode.render, packages/backend-fmi3/RumocaFMI3/StaticStorageCode.lean). | Open (strong partial) | Bind a transitive whole-call-graph no-dynamic-memory predicate (including libm/atomics/string.h and the host logger callback) to the emitted adapter; document RTOS/native heap assumptions. Native compilation stays a boundary. |
| Dir 4.13 | Advisory | Functions that operate on a resource should be a coherent set | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.14 | Required | Validity of values received from external sources shall be checked | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 4.15 | Required | Floating-point exceptions/error conditions shall be evaluated | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 5.1 | Required | There shall be no data races between threads | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 5.2 | Required | There shall be no deadlocks between threads | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Dir 5.3 | Required | No dynamic thread creation | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 1.x - A standard C environment

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 1.1 | Required | Program shall not violate the C syntax/constraints or exceed translation limits | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 1.3 | Required | No occurrence of undefined or critical unspecified behaviour | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 1.4 | Required | Emergent C11/C18 features shall not be used (with the stated profile) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 1.5 | Required | Obsolescent language features shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 2.x - Unused code

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 2.1 | Required | A project shall not contain unreachable code | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 2.2 | Required | There shall be no dead code | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 2.3 | Advisory | A project should not contain unused type declarations | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 2.4 | Advisory | A project should not contain unused tag declarations | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 2.5 | Advisory | A project should not contain unused macro definitions | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 2.6 | Advisory | A function should not contain unused label declarations | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 2.7 | Advisory | There should be no unused parameters in functions | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 2.8 | Advisory | A project should not contain unused object definitions | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 3.x - Comments

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 3.1 | Required | The character sequences /* and // shall not appear within a comment | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 3.2 | Required | Line-splicing shall not be used in // comments | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 4.x - Character sets and lexical conventions

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 4.1 | Required | Octal and hexadecimal escape sequences shall be terminated | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 4.2 | Advisory | Trigraphs and digraphs should not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 5.x - Identifiers

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 5.1 | Required | External identifiers shall be distinct | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 5.2 | Required | Identifiers in the same scope/name space shall be distinct | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 5.3 | Required | An inner-scope identifier shall not hide an outer one | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 5.4 | Required | Macro identifiers shall be distinct | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 5.5 | Required | Identifiers shall be distinct from macro names | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 5.6 | Required | A typedef name shall be a unique identifier | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 5.7 | Required | A tag name shall be a unique identifier | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 5.8 | Required | Identifiers with external linkage shall be unique | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 5.9 | Advisory | Identifiers with internal linkage should be unique | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 5.10 | Required | Object-like macro names shall not clash with reserved/library names (absorbs Rule 21.2) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 6.x - Types

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 6.1 | Required | Bit-fields shall only be declared with an appropriate type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 6.2 | Required | Single-bit named bit-fields shall not be of a signed type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 6.3 | Required | Bit-fields shall not be declared in a union type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 7.x - Literals and constants

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 7.1 | Required | Octal constants shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 7.2 | Required | A u/U suffix shall be applied to unsigned integer constants | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 7.3 | Required | The lowercase l shall not be used as a literal suffix | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 7.4 | Required | A string literal shall not be assigned to a non-const-qualified pointer | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 7.5 | Required | Integer-constant macro arguments shall have appropriate form | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 7.6 | Required | The small integer variants of integer-constant macros shall be used appropriately | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 8.x - Declarations and definitions

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 8.1 | Required | Types shall be explicitly specified in declarations | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.2 | Required | Function types shall be in prototype form with named parameters | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.3 | Required | All declarations of an object/function shall use the same names and type qualifiers | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.4 | Required | A compatible declaration shall be visible when an object/function with external linkage is defined | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.5 | Required | An external object/function shall be declared once in one and only one file | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.6 | Required | An identifier with external linkage shall have exactly one external definition | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.7 | Advisory | Functions/objects should not be defined with external linkage if internal suffices (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.8 | Required | The static storage-class specifier shall be used on internal-linkage declarations | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.9 | Advisory | An object should be defined at block scope if its identifier only appears in a single function (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.10 | Required | An inline function shall be declared with the static storage class | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.11 | Advisory | The size of an array with external linkage should be explicitly specified (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.12 | Required | Enumeration constant values shall be unique within an enumerator list | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.13 | Advisory | A pointer should point to a const-qualified type where possible (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.14 | Required | The restrict type qualifier shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.15 | Required | Alignment declarations shall be consistent for the same object/type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.16 | Advisory | The alignment specification of zero should not appear (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.17 | Advisory | At most one explicit alignment specifier should appear in a declaration (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.18 | Required | _Atomic shall not be applied to a function/array/incomplete type inappropriately | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 8.19 | Required | A declared object with an atomic type shall have appropriate linkage/storage | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 9.x - Initialization

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 9.1 | Mandatory | An automatic object shall not be read before it is set | Applicable: Manual inspection of the actual bytes: every automatic object is initialized at its declaration (e.g. fmi3.c `size_t k = 0;`, `_Bool busy = ((_Bool)0);`, `double next = ...`, `int rounding = fegetround();`; production.c `double v0 = ((double)0);`). The reserved static Instance is fully field-initialized before return in fmi3InstantiateModelExchange/CoSimulation (build/k05/unit-fmu/sources/fmi3.c:136-150). No bare uninitialized scalar local was found (grep for `^\s+(double\|size_t\|int...) name;` matched only struct members). | Open (partial; Mandatory) | Independent definite-initialization predicate over the emitter and a native storage/lifetime correspondence for the static record; Mandatory, so no deviation. Compose with complete creation/lifetime calls (MC05). |
| Rule 9.2 | Required | The initializer for an aggregate/union shall be enclosed in braces | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 9.3 | Required | Arrays shall not be partially initialized | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 9.4 | Required | An element of an object shall not be initialized more than once | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 9.5 | Required | Where a designated initializer is used, array size shall be specified explicitly | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 9.6 | Required | An initializer using chained designators shall not contain initializers without designators | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 9.7 | Mandatory | Atomic objects shall be appropriately initialized before use | Applicable: Manual inspection: the atomic pool flags are `static atomic_bool rumoca_instance_flags[32]` (static zero-initialized), reserved with atomic_exchange and released with atomic_store; the static_assert requires ATOMIC_BOOL_LOCK_FREE == 2. No _Atomic automatic object is default-initialized then read. | Open | Bind atomic-object initialization and the C11 memory-order contract to a native concurrency proof (K02); Mandatory in C11 profile. |

### Rules 10.x - The essential type model

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 10.1 | Required | Operands shall not be of an inappropriate essential type | Applicable: Manual inspection of the actual bytes: two floating variable-to-variable inequalities remain, both exact FMI time-grid checks not covered by Rule 10.1's zero/infinity exceptions: build/k05/unit-fmu/sources/fmi3.c:1085 `currentCommunicationPoint != (m->time)` and :1103 `floored != communicationStepSize` (identical at adapter.c:1133,1151). Relational double-vs-integer-constant sites also occur (`communicationStepSize <= 0`, `> 1000000`). No floating `==` was found. | Deviation candidate | Provide an explicit numerical/deviation argument preserving exact FMI time semantics (an epsilon repair is not equivalent); build the independent essential-type model (Rules 10.1-10.8) and prove emitter preservation. Required, deviation must be documented and reviewed. |
| Rule 10.2 | Required | Char-type expressions shall be used appropriately in +/- operations | Applicable: Manual inspection: concrete mixing sites exist, e.g. unsigned `valueReferences[k]` compared with signed integer constants 0/1/2 and `> 2` (fmi3.c GetFloat64), and double operands combined with signed integer constants in the step guards. Not yet modeled. | Open | Independent essential-type/operator/conversion model and emitter-preservation proof over the actual expressions; classify each mixing site as conforming or a documented deviation. |
| Rule 10.3 | Required | An expression shall not be assigned to a narrower/different essential-type object | Applicable: Manual inspection: concrete mixing sites exist, e.g. unsigned `valueReferences[k]` compared with signed integer constants 0/1/2 and `> 2` (fmi3.c GetFloat64), and double operands combined with signed integer constants in the step guards. Not yet modeled. | Open | Independent essential-type/operator/conversion model and emitter-preservation proof over the actual expressions; classify each mixing site as conforming or a documented deviation. |
| Rule 10.4 | Required | Both operands of a binary operator shall have the same essential type category | Applicable: Manual inspection: concrete mixing sites exist, e.g. unsigned `valueReferences[k]` compared with signed integer constants 0/1/2 and `> 2` (fmi3.c GetFloat64), and double operands combined with signed integer constants in the step guards. Not yet modeled. | Open | Independent essential-type/operator/conversion model and emitter-preservation proof over the actual expressions; classify each mixing site as conforming or a documented deviation. |
| Rule 10.5 | Advisory | An expression should not be cast to an inappropriate essential type (Advisory) | Applicable: Manual inspection: concrete mixing sites exist, e.g. unsigned `valueReferences[k]` compared with signed integer constants 0/1/2 and `> 2` (fmi3.c GetFloat64), and double operands combined with signed integer constants in the step guards. Not yet modeled. | Open | Independent essential-type/operator/conversion model and emitter-preservation proof over the actual expressions; classify each mixing site as conforming or a documented deviation. |
| Rule 10.6 | Required | A composite expression shall not be assigned to a wider essential type | Applicable: Manual inspection: concrete mixing sites exist, e.g. unsigned `valueReferences[k]` compared with signed integer constants 0/1/2 and `> 2` (fmi3.c GetFloat64), and double operands combined with signed integer constants in the step guards. Not yet modeled. | Open | Independent essential-type/operator/conversion model and emitter-preservation proof over the actual expressions; classify each mixing site as conforming or a documented deviation. |
| Rule 10.7 | Required | A composite expression shall not be an operand with a wider essential type | Applicable: Manual inspection: concrete mixing sites exist, e.g. unsigned `valueReferences[k]` compared with signed integer constants 0/1/2 and `> 2` (fmi3.c GetFloat64), and double operands combined with signed integer constants in the step guards. Not yet modeled. | Open | Independent essential-type/operator/conversion model and emitter-preservation proof over the actual expressions; classify each mixing site as conforming or a documented deviation. |
| Rule 10.8 | Required | A composite expression shall not be cast to a different/wider essential type | Applicable: Manual inspection: concrete mixing sites exist, e.g. unsigned `valueReferences[k]` compared with signed integer constants 0/1/2 and `> 2` (fmi3.c GetFloat64), and double operands combined with signed integer constants in the step guards. Not yet modeled. | Open | Independent essential-type/operator/conversion model and emitter-preservation proof over the actual expressions; classify each mixing site as conforming or a documented deviation. |

### Rules 11.x - Pointer type conversions

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 11.1 | Required | Conversions shall not occur between a function pointer and any other type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 11.2 | Required | Conversions shall not occur between a pointer to incomplete type and any other type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 11.3 | Required | A cast shall not convert between pointers to different object types | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 11.4 | Advisory | A conversion should not be performed between a pointer and an integer (Advisory; absorbs 11.7) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 11.5 | Advisory | A conversion from pointer-to-void to pointer-to-object should not be performed (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 11.6 | Required | A cast shall not be performed between pointer-to-void and an arithmetic type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 11.8 | Required | A cast shall not remove any const or volatile qualification from the pointed-to type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 11.9 | Required | The macro NULL shall be the only permitted form of integer null pointer constant | Applicable: Manual inspection: the null pointer constant is written `((void *)0)` in comparisons and `NULL` in `return NULL;` (fmi3InstantiateModelExchange). Rule 11.9 permits `NULL` or an explicit `(void*)0`; no integer 0 is used as a null pointer constant. | Open (partial) | Fold into the pointer essential-type predicate; verify the NULL/(void*)0 usage is the only null-constant spelling emitted. |
| Rule 11.10 | Required | The _Bool and void types shall not be used inappropriately with pointers | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 11.11 | Required | A pointer shall be compared explicitly, not implicitly, with the null pointer constant | Applicable: MISRA C:2025 p.120 includes logical operands. `Runtime.log` now compares the logger with `Expr.nullPointer`; `CNull.and_unequal_null_eval` proves lazy-evaluation equivalence. Regenerated `build/tensor-fmi/adapter.c` uses `((m->logger) != ((void *)0))` at all three shared logger sites and passes the standalone-object boundary check (`build/logger-contract-full-gate.log`). That initial full gate later failed at header-membership proof elaboration. After the structural proof repair, the required full gate passed on 2026-09-21 (exit 0; `build/logger-contract-full-gate-v2.log`), including all production FMI and eFMI artifact/mutation checks. Known residual violations in that same file include `!nEventIndicators`, `!nContinuousStates`, `!eventHandlingNeeded`, `!lastSuccessfulTime`, `!valueReferences` and `!values`, emitted by pointer-output/accessor guards. | Open (known residual violations) | Replace the residual implicit tests with proved explicit comparisons and preserve short-circuit/guard ordering. Complete an independent pointer/type predicate across all profiles, including logical operands, conditional/loop guards and Boolean conversions. No whole-rule compliance or native correspondence is claimed. |

### Rules 12.x - Expressions

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 12.1 | Advisory | The precedence of operators within expressions should be made explicit (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 12.2 | Required | The right operand of a shift shall lie in range for the essential type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 12.3 | Advisory | The comma operator should not be used (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 12.4 | Advisory | Evaluation of constant expressions should not lead to unsigned integer wrap-around (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 12.5 | Mandatory | The sizeof operator shall not be applied to a variable-length array parameter (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 12.6 | Required | Structure/union members of atomic objects shall not be directly accessed | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 13.x - Side effects

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 13.1 | Required | Initializer lists shall not contain persistent side effects | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 13.2 | Required | The value of an expression and its persistent side effects shall be the same under any evaluation order | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 13.3 | Advisory | An expression with an increment/decrement should have no other potential side effects (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 13.4 | Advisory | The result of an assignment operator should not be used (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 13.5 | Required | The right operand of && or \|\| shall not contain persistent side effects | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 13.6 | Mandatory | The operand of sizeof shall not contain any expression with persistent side effects (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 14.x - Control statement expressions

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 14.1 | Required | A loop counter shall not have essentially floating type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 14.2 | Required | A for loop shall be well-formed | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 14.3 | Required | Controlling expressions shall not be invariant | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 14.4 | Required | The controlling expression of if/while shall have essentially Boolean type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 15.x - Control flow

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 15.1 | Advisory | The goto statement should not be used (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 15.2 | Required | The goto statement shall jump to a label declared later in the same function | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 15.3 | Required | Any label referenced by a goto shall be in a block enclosing the goto | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 15.4 | Advisory | There should be no more than one break/goto to terminate a loop (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 15.5 | Disapplied | A function should have a single point of exit at the end (Disapplied) | Applicable (Disapplied): Disapplied in the MISRA C:2025 primary baseline (standards-review MC03): the runtime uses early guard returns; all-path semantic proofs are preserved. C11 supports the multiple-return style. | Disapplied | None; keep the Disapplied disposition explicit and retain all-path execution proofs. Any eFMI-referenced single-exit obligation is tracked separately under the eFMI mapping. |
| Rule 15.6 | Required | The body of an iteration/selection statement shall be a compound statement | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 15.7 | Required | All if...else if constructs shall be terminated with an else statement | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 16.x - Switch statements

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 16.1 | Required | All switch statements shall be well-formed | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 16.2 | Required | A switch label shall only appear at the top level of the switch body | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 16.3 | Required | An unconditional break shall terminate every switch-clause | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 16.4 | Required | Every switch statement shall have a default label | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 16.5 | Required | A default label shall appear as the first or last switch label | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 16.6 | Required | Every switch shall have at least two switch-clauses | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 16.7 | Required | A switch controlling expression shall not have essentially Boolean type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 17.x - Functions

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 17.1 | Required | The features of <stdarg.h> shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 17.2 | Required | Functions shall not call themselves, directly or indirectly (no recursion) | Applicable: Lean theorem Rumoca.FMI3.CallPolicy.source_program_policy (packages/compiler/Rumoca/FMI3CallPolicy.lean) proves the emitted adapter's prepared function table is ranked by functionRank and its direct-call graph has no cycle (complete_program_no_cycle): for every ProgramEdge caller->callee, callee cannot reach caller. Independently confirmed on the actual bytes: a brace-matched call-graph over build/k05/{model.c,unit-fmu/sources/fmi3.c}, build/tensor-fmi/adapter.c and build/tensor-c/*.c has no self-recursion and no cycle. | Open (strong partial) | The theorem covers the modeled generated functions only; foreign leaves (floor/isfinite/fegetround, atomic_exchange, memcpy) and the host logger/reentry callbacks are outside the ranked set. Bind the acyclicity to the native call graph and document the foreign/callback boundary. |
| Rule 17.3 | Mandatory | A function shall not be declared implicitly (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 17.4 | Mandatory | All exit paths from a value-returning function shall have an explicit return (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 17.5 | Required | A function argument for a parameter of array type shall have an appropriate number of elements (renumbered from 17.6) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 17.7 | Required | The value returned by a non-void function shall be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 17.8 | Advisory | A function parameter should not be modified (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 17.9 | Required | A function declared _Noreturn shall not return | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 17.10 | Required | A function declared _Noreturn shall have void return type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 17.11 | Required | A function without a return statement shall be _Noreturn where appropriate | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 17.12 | Required | A function identifier shall only be used with a preceding & or a parenthesised argument list | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 17.13 | Required | A function type shall not be type-qualified | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 18.x - Pointers and arrays

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 18.1 | Required | A pointer resulting from arithmetic shall address an element of the same array | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 18.2 | Required | Subtraction between pointers shall address elements of the same array | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 18.3 | Required | Relational operators shall not be applied to pointers into different objects | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 18.4 | Advisory | The +, -, += and -= operators should not be applied to pointers (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 18.5 | Advisory | Declarations should contain no more than two levels of pointer nesting (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 18.6 | Required | The address of an automatic object shall not escape its lifetime | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 18.7 | Required | Flexible array members shall not be declared | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 18.8 | Required | Variable-length array types shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 18.9 | Required | An object with temporary lifetime shall not undergo array-to-pointer conversion inappropriately | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 18.10 | Required | Pointers to variably-modified array types shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 19.x - Overlapping storage

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 19.1 | Mandatory | An object shall not be assigned or copied to an overlapping object (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 19.2 | Advisory | The union keyword should not be used (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 19.3 | Required | An initialised atomic object shall not be re-initialised inappropriately | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 20.x - Preprocessing directives

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 20.1 | Advisory | #include directives should only be preceded by preprocessor directives or comments (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.2 | Required | The ', " or \ characters and /* or // shall not occur in a header-name | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.3 | Required | The #include directive shall be followed by a <filename> or "filename" | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.4 | Required | A macro shall not be defined with the same name as a keyword | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.5 | Advisory | #undef should not be used (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.6 | Required | Tokens that look like a preprocessing directive shall not occur within a macro argument | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.7 | Required | Expressions resulting from macro expansion shall be parenthesised | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.8 | Required | The controlling expression of #if/#elif shall evaluate to 0 or 1 | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.9 | Required | All identifiers in #if/#elif shall be #define'd before evaluation | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.10 | Advisory | The # and ## preprocessor operators should not be used (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.11 | Required | A macro parameter immediately following # shall not be followed by ## | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.12 | Required | A macro parameter used as an operand to # or ## shall only be used as such | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.13 | Required | A line whose first token is # shall be a valid preprocessing directive | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.14 | Required | All #else/#elif/#endif shall reside in the same file as the #if they close | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 20.15 | Required | #define and #undef shall not be used on a reserved identifier/macro (absorbs Rule 21.1) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 21.x - Standard libraries

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 21.3 | Required | The memory allocation and deallocation functions of <stdlib.h> shall not be used | Applicable: Same byte-level grep as Dir 4.12: the memory-management identifiers malloc/calloc/realloc/free/aligned_alloc do not appear as calls in any generated C. The older MC02 finding (Runtime emitting calloc/free) is superseded: the current default emission uses the static instance pool. | Open (strong partial) | Independent Lean predicate that no emitted expression names an allocation identifier/macro, universally over the emitter, made mandatory in the artifact contract. |
| Rule 21.4 | Required | The standard header <setjmp.h> shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.5 | Required | The standard header <signal.h> shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.6 | Required | The Standard Library input/output functions shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.7 | Required | The atof/atoi/atol/atoll functions of <stdlib.h> shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.8 | Required | The library functions abort/exit/getenv/system of <stdlib.h> shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.9 | Required | The library functions bsearch and qsort of <stdlib.h> shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.10 | Required | The Standard Library time and date functions shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.11 | Required | The standard header <tgmath.h> shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.12 | Advisory | The exception-handling features of <fenv.h> should not be used (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.13 | Mandatory | Any value passed to a <ctype.h> function shall be representable as unsigned char or EOF (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.14 | Required | The memcmp function shall not be used to compare null-terminated strings | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.15 | Required | The pointer arguments to memcpy/memmove/memcmp shall point to compatible types | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.16 | Required | The pointer arguments to memcmp shall point to either a comparable type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.17 | Mandatory | Use of the string handling functions shall not result in out-of-bounds access (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.18 | Mandatory | The size_t argument passed to any string/memory function shall have an appropriate value (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.19 | Mandatory | The pointers returned by localeconv/getenv/setlocale/strerror shall only be used as const-qualified (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.20 | Mandatory | The pointer returned by localeconv/setlocale/... shall not be used after a subsequent call (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.21 | Required | The Standard Library function system of <stdlib.h> shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.22 | Required | All memory synchronization operations shall be executed in a sequenced manner | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.23 | Required | All atomic operands of an atomic operation shall have the same atomic type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.24 | Required | The random number generator functions of <stdlib.h> shall not be used | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.25 | Required | All memory-order arguments shall be a compile-time constant of memory_order_seq_cst | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 21.26 | Required | The standard header <threads.h> timed-wait functions shall use a valid duration | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 22.x - Resources

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 22.1 | Required | All dynamically obtained resources shall be explicitly released | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.2 | Mandatory | A block of memory shall only be freed if it was allocated by a Standard Library function (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.3 | Required | The same file shall not be open for read and write access at the same time on different streams | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.4 | Mandatory | There shall be no attempt to write to a stream opened read-only (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.5 | Mandatory | A pointer to a FILE object shall not be dereferenced (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.6 | Mandatory | The value of a pointer to a FILE shall not be used after the stream is closed (Mandatory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.7 | Required | The macro EOF shall only be compared with the unmodified return value of a stream function | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.8 | Required | errno shall be set to zero prior to a call to an errno-setting function | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.9 | Required | errno shall be tested against zero after a call to an errno-setting function | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.10 | Required | errno shall only be tested when the last function was errno-setting | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.11 | Required | A thread previously joined/detached shall not be joined or detached again | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.12 | Required | Thread objects, thread-synchronization objects and thread-specific storage shall only be accessed by appropriate APIs | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.13 | Required | Thread/mutex/condition objects shall have appropriate storage duration | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.14 | Required | Thread synchronization objects shall be initialized before use | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.15 | Required | Thread synchronization shall not be prematurely terminated (no destroy while owned) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.16 | Required | All mutex objects locked by a thread shall be explicitly unlocked by the same thread | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.17 | Required | No thread shall unlock a mutex it has not previously locked | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.18 | Required | A non-recursive mutex shall not be locked again by the owning thread | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.19 | Required | A condition variable shall be associated with at most one mutex object | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 22.20 | Required | Thread-specific storage pointers shall be created before use and deleted appropriately | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Rules 23.x - Generic selections

| ID | Category | Applicability | Evidence | Status | Closure criterion |
| --- | --- | --- | --- | --- | --- |
| Rule 23.1 | Advisory | A generic selection should be expanded from a macro (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 23.2 | Required | A generic selection that is not expanded from a macro shall not contain potential side effects in the controlling expression | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 23.3 | Advisory | A generic selection should have a non-default association with an appropriate type (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 23.4 | Required | A generic association shall list an appropriate type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 23.5 | Advisory | A generic selection should not depend on implicit pointer conversions (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 23.6 | Required | The controlling expression of a generic selection shall have an essential type that matches its standard type | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 23.7 | Advisory | A generic selection that is expanded from a macro should have a default association (Advisory) | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |
| Rule 23.8 | Required | A default association shall appear as either the first or last association of a generic selection | Applicable: None (inventory only; no independent predicate yet) | Open | Author an independent Lean predicate or named analyzer/manual check bound to the actual bytes; see the enforcement plan. |

### Withdrawn and renumbered guidelines (Appendix A.2)

These five IDs are not among the 223 current entries; they are tracked, not enforced.

| Former ID | Disposition | Successor |
| --- | --- | --- |
| Rule 1.2 | Withdrawn | Dir 1.2 (documented language extensions) |
| Rule 11.7 | Withdrawn | Rule 11.4 (pointer/integer conversion) |
| Rule 17.6 | Withdrawn (was Mandatory) | Rule 17.5 (array-parameter element count) |
| Rule 21.1 | Withdrawn | Rule 20.15 (reserved macro identifiers) |
| Rule 21.2 | Withdrawn | Rule 5.10 / reserved names |
