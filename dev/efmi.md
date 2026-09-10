# Tiny eFMI target

The current full gate is `nix develop .#verification --command lake test`.
Make commands in dated checkpoints below record historical runs before the
Lake migration; see the [current commands](../docs/development.md).

Status: active, incomplete. The user has now authorized eFMI for the existing
unit-derivative core, including both GALEC Algorithm Code and Production C.
This supersedes the earlier deferral of GALEC. It does not authorize additional
Modelica equations or a general GALEC language implementation.

## Authority and selected profile

The authority is the **eFMI Standard 1.0.0 Beta 1** specification and its
accompanying schemas, obtained from the official
[release page](https://www.efmi-standard.org/resources/). The release archive
is `build/efmi-beta1-standard.zip`, SHA-256
`da5caf207aca412b5601cafaaf72d4e613d1c78964e3f39afc6a5a3d06281a89`.
Its extracted specification matches the independently downloaded official HTML,
SHA-256 `e4b40e7f7a9916af2f2d1351ff7b1cb3ed1a5e5f65e68e63c1b8cbaddd739e56`.
The official release page still lists Beta 1 as the current candidate, with no
stable release. Pin this version rather than implying final 1.0.0 conformance.
The official [standard description](https://www.efmi-standard.org/standard/)
explicitly makes the accompanying software artifacts part of the standard.
The normative download is the [complete release archive](https://www.efmi-standard.org/media/resources/eFMI-Standard-1.0.0-Beta-1.zip).
The local reference copies and review logs stay under `build/`; deleting them
does not change the source authority recorded here.

The Rust checkout is an architecture reference only. At review revision
`ded5b1c1deae47f1c4638c40a764db4d1bd28c34`, SPEC_0007, SPEC_0034 and
`rumoca-phase-solve/src/algorithm.rs` describe and implement the separate
Algorithm Code refinement. Some spec tables still label that implementation
pending; actual code and the eFMI standard must be distinguished from those
historical status notes.

The authorized implementation path is:

```text
Modelica AST → Flat → DAE ─────────────→ numerical Solve IVP → FMI 3
                       └→ checked GALEC → Solve algorithm → Production C
                               └→ Algorithm Code .alg
```

GALEC is a constrained, causal algorithm product of DAE. It is neither the DAE
residual representation nor a mandatory stage on the numerical IVP path.
GALEC-to-Solve is executable refinement, not an inverse that reconstructs DAE.
The eFMU must contain the correlated Algorithm Code and Production Code members.
The backend renders prepared products; it must not redo name resolution, DAE
restriction, solver choice or algorithm lowering.

The first profile restricts the existing equation to one scalar (rank-zero)
state, zero initialization and unit sampling period. Selecting zero is an
explicit deployment choice within the existing host-initialized unit source
profile; it does not add Modelica initialization syntax. `Startup` initializes
the state and period, `Recalibrate` is empty, and `DoStep` performs one addition.
The production arithmetic profile is binary64, nearest-even, with finite states.
This is one eFMI target profile, not a universal eFMI Real representation.

## Standard obligations

| Standard location | Obligation for the tiny target | Current evidence / remaining work |
| --- | --- | --- |
| §3.2.2 and §3.2.4 | Lexical/grammar rules and separate semantic restrictions | Authored restricted EBNF; checked shared LR tables; exact profile actions and scanner proofs. Full lexical support and independent EBNF metalanguage/desugaring proofs remain open. |
| §3.2.3 §2 | Startup, Recalibrate, DoStep, persistent instance state | Explicit state assignments and period initialization in the selected profile; executable method/trace preservation. |
| §3.2.3 §3 | Startup-before-use, serialized calls per instance, independent instances | Checked legal protocol traces, typed entry and C memory isolation; host scheduling and physical ABI remain assumptions. Parser worker parallelism is unrelated to concurrent calls on one block. |
| §3.2.4 expression rules, strict evaluation order | Preserve operation order | Tensor register continuation lowering has a universal interpretation-preservation proof. No reassociation or scalarization. |
| §3.2.5 §2 | IEEE exceptional values and propagation | Existing unit addition cannot overflow for any finite binary64 state. Other arithmetic and exceptional inputs are not admitted. |
| §3.2.5 §3 | Entry/exit limitation for ranged variables | This profile declares no ranges; the specification says limitation of an unranged entity has no effect. No saturation code is inferred. |
| §3.1 | Algorithm Code manifest, methods, variables, fixed clock, start values | Actual manifest correlation is kernel checked; the official schema gate passes for the fixture. Complete standards conformance remains separate. |
| Chapter 5 | Production Code mapping to its Algorithm Code | Solve-to-C execution, actual-file contracts and decoded XML mappings are checked. Native compilation remains an external boundary. |
| Chapter 2 and referenced XSDs | Container graph, identifiers, files, checksums, entry manifest | The passing actual archive certificate composes the complete ZIP with source, code and manifest contracts. UUID layout, case-normalized distinctness and Gregorian UTC validity are checked. Public generation now proposes identities using OS APIs and requires the staged-archive certificate; its publication gate and the checker/layout review are tracked below. |

Specific findings from the text, lifecycle diagram and official XSDs:

- §3.1.2 requires a **fixed** sampling-period constant, in seconds (implicitly
  seconds if no unit is supplied). The period is not a tunable parameter. The
  earlier general overview's potentially varying period does not override
  this concrete Clock requirement in the selected version.
- The §3.2.3 state diagram starts in initialization, then enters idle. Only
  idle admits output reads, recalibration and sampling. Shutdown is terminal.
  The tiny profile has no input/parameter writes; it still needs the admitted
  lifecycle trace and C memory contracts. Repeated Startup is not a normal
  sampling-cycle transition. Outputs cannot be written by the host.
- §3.2.3 L-1 permits an explicitly agreed deployment restriction, such as
  omitting recalibration. We retain all three methods and independent instance
  state. That permission is not a basis for claiming general generator coverage.
- GALEC Real is target-independent; Production Code selects a concrete
  representation. Binary64 is our choice, not a requirement of all eFMI code.
  The unit's lack of external writes and no-overflow proof justify the finite
  arithmetic restriction for reachable initialized states. General GALEC
  comparisons must raise the NAN signal for qNaN operands (§3.2.5 §2); reusing
  C's unordered comparison result alone would miss that semantic requirement.
- `efmiAlgorithmCodeManifest.xsd` requires `Files`, `Clock`, all three
  `BlockMethods`, `ErrorSignalStatus`, `Units`, and `Variables`, in that order.
  The prose calls Units optional; the schema requires the element, which can
  be empty. Emit `<Units/>` for this profile. Use the schema's fixed
  `xsdVersion="0.14.0"`, not the release label `1.0.0`.
- `efmiProductionCodeManifest.xsd` requires the Algorithm Code reference,
  files, target/language/platform/precision information, code files and logical
  data mappings. Its fixed schema version is `0.17.0`. XML validity alone
  does not show that mappings describe the actual C declarations or behavior.
- Chapter 2 requires `__content.xml` and `schemas` at the archive root.
  The content schema version is `0.11.0`. Root entries identify each member
  manifest; Production Code references the Algorithm Code manifest and its
  variables. Checksums are SHA-1 over the unmodified file bytes, including
  line endings. They establish consistency, not semantic preservation or an
  authenticity signature. A separate SHA-256 inventory may record our gate.
- An `.efmu` ZIP can contain the correlated Algorithm and Production Code
  representations. Embedding or exposing an FMI FMU is a separate arrangement
  under §1.2 and Chapter 2; it is not implied by containing Production C.
- §5.1.5 requires explicit logical mappings even when a GALEC variable becomes
  a C structure field or formal parameter. §5.2 requires the actual C/C++
  language and version in the manifest. Do not describe a C11 artifact merely
  as generic C, or infer MISRA compliance from Lean semantic preservation.

**Draft discrepancy to retain in the conformance review:** §3.2.4 G-2's printed
`state-entity-declaration` production omits input/output prefixes, while the
block-interface specification and official GALEC examples explicitly use them.
Our authored profile follows that specified interface and example usage for
`output Real x;`; it does not claim verbatim equality with the incomplete G-2
production. Do not silently present a Rust workaround as a normative correction.
The emitted profile must be reviewed against the official schemas and available
conformance tooling before an eFMU conformance claim.

The reference-to-implementation alignment is an authored standards review.
Lean checks the formal definitions and their connections to actual artifacts;
it does not turn the prose standard or its diagram into a kernel theorem.

The Production Code review also found a concrete discrepancy in §5.1.3.2
“Functions”: the prose says a void function omits its return parameter, while
`ProductionCode/efmiFunctions.xsd` requires `ReturnParameter` with
`minOccurs="1"`. The schema exposes an `efmiVoid` target type, but emitting that
metadata would still conflict with the prose's omission rule. The current C
interface avoids this conflict by returning `EfmiStatus` (`int32_t`), with
proved value zero for every legal method execution. `EfmiReal` (`double`) and
`EfmiStatus` are actual emitted typedefs. This gives both return and field
mappings real declared types; it does not claim that the draft inconsistency
has been corrected. The execution, lifecycle and actual-file contract were
updated for this interface together.

## Required completion gates

- [x] **E01 — Checked DAE restriction and numerical policy.** Prove the unit DAE
  licenses the generated algorithm and distinguish real solutions from finite
  sampled execution. Retain the full source/shape provenance.
- [x] **E02 — GALEC → Solve algorithm.** Preserve every method, assignment,
  reference, operation order and period; include initialization and protocol
  state in the core reference. The target memory/ABI connection remains E04;
  this is not yet the whole deployed block-interface theorem.
- [x] **E03 — Second EBNF and actual .alg binding.** Reuse the same LR engine;
  check source lexing, grammar membership, action/name correctness, and the
  selected input bound. Bind actual grammar and .alg bytes to the source theorem.
  Keep generic LR completeness and standardized EBNF conformance claims separate.
- [x] **E04 — Production C.** Generate exclusively from the checked Solve
  algorithm, with an independent target execution theorem and certificate for
  the actual complete C member. Preserve lifecycle storage and all observable
  outputs; reuse existing arithmetic proofs without bypassing GALEC refinement.
- [ ] **E05 — Correlated Algorithm/Production manifests and eFMU.** Use the
  official release schemas, validate member/reference/checksum graphs, and bind
  actual archive members to the same checked model. Test independent extraction,
  schema validation, C execution and failure-preserving publication.
  Use the official [Compliance Checker](https://github.com/modelica/efmi-compliancechecker/tree/v1.0.1)
  as an additional interoperability check when the complete eFMU exists. Pin
  the tool and its supported dependency versions; run it in a disposable
  directory under `build/` because it extracts into its working directory.
  Its test result cannot replace the actual-artifact Lean contract, and its
  parser is not part of the Lean compiler. Version 1.0.1 currently rejects the
  standalone root layout before inspecting its manifests; see the checker
  discrepancy below. No passing official-checker result is claimed.
- [ ] **E06 — Review and release.** Run the unchanged full gate, audit every new
  proof root, review standard discrepancies, and state the exact trust boundary.
  Do not infer full eFMI compliance from schema validation or a matching trace.

No eFMU release claim is currently established. The original FMI 3 and generic
LALR completeness obligations remain open and are not replaced by this work.

## Algorithm Code checkpoint evidence

The complete `nix develop .#verification --command make test` passed with exit
status zero. The log is `build/efmi-algorithm-gate.log`. It includes all 388
audited roots (36 added for the GALEC/scanner/algorithm/profile path), the
existing source/C artifact and adversarial checks, 13 native FMI 3 test groups,
and the additional Algorithm Code checks. Audit dependencies are limited to
`propext`, `Classical.choice`, and `Quot.sound`.

The new grammar generates 60 canonical LR states and 57 merged states. Three
valid source forms and eleven malformed/out-of-profile forms are tested. The
same generator also emits an independently named recursive grammar, imported
beside GALEC. The regression caught and fixed a namespace dependency in the
emitter; generated modules now explicitly open the shared Rumoca namespace.
Invalid namespace input preserves the previous candidate file.

Actual-file tests reject changed step arithmetic, changed clock initialization,
changed Modelica input and either changed EBNF. Failed source compilation
preserves a published `.alg`. The CLI refuses `.efmu` until its producer exists
instead of placing C text under an archive extension. A separately generated
checked example is `build/Integrator.alg`, with its checking log at
`build/efmi-algorithm-export.log`.

The core corrections made during the standards review include moving clock
initialization into explicit GALEC and Solve programs and preserving it in the
full state theorem. The restricted lifecycle theorem follows the standard's
initialization/idle/method/shutdown diagram. Renderer imports exclude the LR
parser and its proof tables; concrete EBNF processing stays in the parser
package so IR changes do not repeat that expensive kernel computation.

`build/efmi-algorithm-snapshot.sha256` records the repository source/configuration
snapshot for this checkpoint. It is an inventory, not a semantic proof. E04–E06
remain open: neither a generated Production C member nor a complete eFMU has
been certified by this checkpoint.

## Production C work after the Algorithm Code checkpoint

E04's implementation, proofs and required full repository gate have passed.
The gate log is `build/efmi-production-gate.log`, with 415 audited roots and
only the three permitted foundations. `Solve.Algorithm.Model` seals the already lowered algorithm.
The backend renders its instructions directly as fresh C declarations and
field stores, rejecting unsupported tensor storage without scalarization.

`Production.method_correct` covers all method behaviors, complete heap effects,
the clock and isolation. Startup additionally accepts allocated uninitialized
storage. `CProtocol` proves both directions of legal serial interaction traces
against Solve. Typed entry and a separate C token grammar connect the complete
emitted member to these bodies. The compiler's `ProductionContract` composes
these facts with `AlgorithmContract` for one source artifact.

`CheckEFMIProduction.lean` independently reads the Modelica source, both EBNFs,
the GALEC file and the C file; only a kernel-checked, axiom-audited theorem for
that pair can authorize acceptance. Early native mismatches only reject.
The fixture producer writes to `build/efmi-production/`; this is a code pair,
not an archive or public `.efmu` output. `lake run efmi-production-test` checks the
certificate, native execution and actual-member mutation rejection.

The remaining E05 work is the standards-correlated XML graph and actual ZIP
binding: declarations/fields/parameters/methods, manifest origins, raw-byte
SHA-1 checksums, schema membership and all archive members. E06 still requires
the complete artifact gate and a final review. No complete eFMU has been emitted
or certified, and no machine-code theorem is claimed.

The full gate includes the existing actual-source/C, forged-producer and
parser controls, all 13 FMI 3 native groups, Algorithm Code regressions, and
the new Production C certificate/native/5-mutation gate. A failed mutation
fixture initially left GALEC unchanged; the corrected test changes `self.x`
arithmetic, and the harness now rejects ineffective mutations explicitly.

As an additional standards check, the official Compliance Checker v1.0.1's
GALEC parser and function validation accepted the emitted block. The checkout
is pinned to `415c4ad441f4486dab6c728f245cefa2147e8e6b`; the supporting local
environment uses Python 3.13.14, lxml 6.0.2, lark-parser 0.12.0 and colorama
0.4.6. Its log is `build/efmi-official-galec.log`. This is not the complete
official eFMU check: no archive exists yet.

## E05 transport proof work

The transport now has a list-based ZIP byte specification, a tail-recursive
ByteArray writer and a separate cursor reader with a complete-byte acceptance
validator. Generic Lean theorems establish serialization soundness and
completeness for every admissible member sequence, acceptance soundness for
arbitrary archive bytes, and lossless numeric fields at every representable
width. They also establish unique names, bounded members, inclusion of each
actual member record and uniqueness of the complete bytes for a member list.
The proof build passed in `build/efmi-zip-proofs.log`. The required
`nix develop .#verification --command make test` also passed with exit status
zero; its log is `build/efmi-transport-gate.log`. The existing production audit
includes the transport proof roots and permits only `propext`,
`Classical.choice` and `Quot.sound`. This checkpoint reran the actual source/C,
GALEC and Production C certificates and the existing external integration gate.

This work follows the user's preference for general proofs over more example
tests. No ZIP test matrix was added. Remaining E05 work is still the typed XML
mapping, schema and checksum graph, and the actual eFMU certificate/publication
path. Reader completeness is a separate open transport property; parser
acceptance is already guarded by the independently specified byte grammar.

Proof-only binary64 imports were also separated from runtime algorithm
semantics. The compiler executable went from 179 MiB to 4.9 MiB; the affected
proof modules rebuild without changing arithmetic, emitted C or contracts.
The E04 full-gate snapshot remains the historical checkpoint above.
`build/efmi-transport-snapshot.sha256` records the source/configuration inventory
for the new transport checkpoint. This inventory is not a semantic proof and
does not change the open status of the complete eFMU milestone.

## E05 declared interface and logical mappings

The production interface now uses declared `EfmiReal` and `EfmiStatus` aliases
and returns status zero from Startup, Recalibrate and DoStep. The independent
C token grammar, all method executions and both lifecycle trace directions
were updated. `CHeader.Contract` binds the actual complete C source to the
header's typedefs and fields; `Production.return_checked` validates the returned
value against the declared status type.

`Metadata` describes the logical variables, tensor shapes, identifiers,
exported functions and instance-parameter/component references. Its proofs
establish unique identifiers and matching declarations/signatures.
`Metadata.execution_preserves` takes an actual C execution and proves that
both mapped variables yield their exact Solve values, including the clock;
it also proves the returned status is zero. `ProductionContract` now includes
this mapping contract and recovers the actual GALEC AST's canonical names.

The required `nix develop .#verification --command make test` passed with
exit status zero; its log is `build/efmi-interface-gate.log`. The independent
actual-file checker also accepted the newly emitted GALEC/C pair in
`build/efmi-interface/`; its log is `build/efmi-interface-artifact.log`.
The certificate's dependencies are limited to `propext`, `Classical.choice`
and `Quot.sound`. `build/efmi-interface-snapshot.sha256` records the source and
configuration inventory for this checkpoint, not a semantic proof.
The existing native driver now checks the status returned by its existing
calls; no test matrix or new source-language case was added. Serialized XML,
schema/resource membership, manifest-origin/checksum correlation and the
complete `.efmu` certificate/publication path remain open.

GALEC verification remains a prerequisite, not an external-parser test result.
For the admitted unit profile, `AlgorithmContract` binds the actual `.alg`
characters to a parsed, name-checked block, its DAE admission, rounded method
and sample semantics, and full state/lifecycle refinement to Solve. Its parser
has a sufficient bound for this fixed token skeleton. The general LALR
completeness theorem and unsupported GALEC language features remain outside
this claim. Integration tests support the file adapters, external formats and
native toolchain; they do not replace these semantic obligations.

The Rust alignment review at commit
`338b1a6e3e178df230bf6b7a5ee8ac38a7bcaf3a` checked SPEC_0007,
SPEC_0034 and `rumoca-phase-solve/src/algorithm.rs`. The implemented route
likewise refines a checked DAE-derived Algorithm Code product into a sealed
Solve algorithm before Production C emission. Tensor operations, lifecycle
effects and storage decisions belong in those products, with a thin backend.
The Rust spec's float32 target profile is not adopted here: this core retains
its proved binary64 policy. Stale pending labels in those Rust documents are
not treated as evidence that their implementation is absent.

## Incremental development checks (2026-09-09)

Package proofs and axiom audits now have separate Lake check libraries. The
central audit roots have moved to the packages defining their declarations,
including the GALEC/parser and Solve roots previously checked only through the
compiler. Tensor checks live in core. The small `verification` package enforces
the existing three-axiom whitelist during Lean elaboration; Lake can therefore
reuse successful checks with its normal source/import dependency traces.
No artifact byte check or semantic obligation was removed.

Measured warm checks rebuilt zero modules: parser 0.93 s, core 1.12 s, FMI 3
0.97 s, eFMI 1.00 s, compiler 2.03 s, and the combined package audit 1.81 s.
These are local development measurements, not portable performance guarantees;
the logs and timings are under `build/incremental/`. See the
[development workflow](../docs/development.md) for commands.

This is a development workflow checkpoint, not E05 completion. The actual
manifest certificate failed with a stack overflow (`build/efmi-cli-manifest.log`).
An initial diagnosis attributed the failure to the final axiom audit. A later
backtrace showed that Lean was formatting an earlier kernel-check error:
returning from command elaboration does not establish that its declarations
passed. The completed generic XML and manifest theorems do not replace that
missing successful artifact gate.

The required `nix develop .#verification --command make test` was run once for
this reorganization (`build/incremental/full-gate.log`). Package checks, source/C
certificates and mutations, FMI 3 importer/ABI checks, and GALEC checks passed.
The final eFMI manifest checker again exited 134 with a stack overflow; Make
returned 2. The full gate therefore remains failing. This is not a new fully
verified compiler or eFMU checkpoint.

The current SHA-1 certificate work checks individual compression blocks and
composes their execution with `Certificate.block_cons` and
`Certificate.hash_of_blocks`. These generic lemmas build, and a certificate
for `abc` passes the kernel and axiom audit. The actual 5,235-byte production
manifest still has no successful checksum certificate. A reduced diagnostic
exposes `(kernel) deep recursion detected` when checking the conversion from
the actual string to its proposed UTF-8 byte list, even without hashing.
Increasing `maxRecDepth` and using Boolean equality did not solve it. Large
certificate timings previously printed before the process failed must not be
reported as successful verification times. Diagnostics remain under `build/`.
The targeted `make check-efmi` run passed with the new composition lemmas in
the enforced axiom audit (`build/efmi-sha-package-check.log`). This establishes
the package proof checkpoint only; it does not close the manifest failure in
the required full gate.

## Independent SHA-1 and XML packages

The checksum certificate now composes checked character/UTF-8 conversion,
original byte counts, short padding suffixes and individual compression blocks.
It reuses the standard library's UTF-8 lemmas and keeps `String.ofList` opaque
to elaboration while checking the source literal; kernel checking is unchanged.
The actual 5,235-byte production-manifest checksum passed with exit status zero
and only `propext`/`Quot.sound` dependencies in
`build/efmi-sha-manifest-blocks.log`. Its elaboration took 109 seconds locally.
This resolves the isolated checksum failure, not the complete manifest gate.
A separate actual-XML serialization check still overflows the stack
(`build/efmi-manifest-xml-probe.log`), so that proof boundary is the next task.

At the user's request, SHA-1 and XML now have independent Lake packages under
`packages/sha1` and `packages/xml`, with public namespaces `SHA1` and
`XML`. Each owns its implementation, proofs and existing audit roots.
Their implementation/proof imports use only Lean's standard library; check
libraries use the local verification tooling. Neither depends on the compiler,
parser, mathlib, FMI or eFMI. The backends retain model-specific documents and
the manifest/reference contracts. The compiler retains actual-file composition.

`make check-sha1`, `make check-xml` and both packages' standalone `lake test`
commands passed. Warm root-workspace checks rebuilt zero modules and took
0.72 and 0.76 seconds respectively (`build/utility-packages-warm.json`). All
migrated audit roots remain enforced by the required full gate. These timings
are local measurements, not portable performance guarantees. No remote
dependency was added or updated, and no source-language case was introduced.

The first full-gate run during this change was stopped when XML extraction was
requested (`build/sha1-package-full-gate.log`); it is an interrupted run, not a
passed checkpoint. The replacement run is logged in
`build/utility-packages-full-gate.log`: package proofs/audits, parser and source/C
certificates/mutations, FMI 3 archive/importer/ABI/runner checks, and GALEC checks
passed. The final eFMI manifest checker exited 134 with a stack overflow; Make
returned 2. Its actual files and failure log remain in
`build/efmi production test.TkPNYQ/`. Complete manifest and archive verification
remain open until that artifact gate and the remaining E05/E06 obligations pass.

A diagnostic generic character projection of the XML renderer has a checked,
axiom-audited preservation theorem (`build/XMLCharProjection.lean`,
`build/xml-character-projection.log`). Checking a whole production document by
one computation over this projection still fails
(`build/xml-projected-manifest.log`). The next certificate work should compose
small element/attribute results rather than normalize the entire document in
one kernel reduction. These are temporary diagnostics, not shipped XML API or
a successful actual-document certificate.

## Compositional manifests and native Lake checkpoint

The actual three-document certificate now passes. `XML.Certificate` composes
per-element rendering equalities and child lists. The builder checks the
composed list against a flat character literal before relating it to the
original string with standard-library lemmas. This avoids the failing large
string reduction. Separate header and child certificates prove XML validity
using the validator's equation theorem, without reducing its entire recursive
implementation. Runtime rendering and the admitted XML profile are unchanged.

The compiler composes these facts with the existing SHA-1 block certificates,
typed mappings and source/GALEC/Production C contract. The exact
`Rumoca.CheckedEFMIFiles.source_to_manifests` theorem passed kernel checking and
the unchanged three-axiom audit (`build/lake-manifest-contract.log`). The
standalone document/validity check also passed
(`build/xml-element-manifests.log`). The earlier failed integration attempt
is retained in `build/xml-manifest-artifact-gate.log`; it exposed a stale Lean
printing option and an unsuitable whole-tree validity reduction. Neither the
contract nor the axiom audit was weakened to resolve those failures.

The complete `nix develop .#verification --command lake test` passed with exit
status zero (`build/lake-full-gate.log`). This includes all package proofs and
audits, grammar freshness, actual-source/C and forged-producer controls, LALR
and GALEC checks, all thirteen FMI 3 native groups, and the eFMI manifest
certificate, official schemas, independent checksum comparisons, native C
execution and mutations. This closes the actual manifest certificate failure.
E05/E06 remain open for complete identity/schema correspondence, archive
binding, the independent compliance checker and publication. No `.efmu`
producer or new language case was added.

Reusable package/module names are now `sha1`/`SHA1`, `xml`/`XML`, and
`proof_audit`/`ProofAudit`. Compiler-specific packages retain Rumoca names;
the combined parser keeps its name until its generic engine is separated from
language instances. All existing audit statements and pinned remote
dependencies survived the rename; the new XML composition roots are also
audited.

The Makefile and its explicit Nix dependency were removed at the user's
request. Package checks are native Lake build targets and the complete gate is
the root test driver. The redundant public `lean-test` command was removed;
its checks remain in `lake test`. No compatibility aliases are retained. CI,
repository instructions and current documentation use Lake. Historical Make
commands above retain their original evidence. `lake --no-build build
check-sha1 check-xml audit` passed with every target up to date
(`build/lake-native-cache.log`); `lake run demo` also passed. No separate proof
cache or passing stamp was introduced. Actual-file certificates still run
per invocation, and the eFMI CLI first brings their imported checker modules
up to date through Lake.

## Manifest identity obligations

The earlier `ManifestContract` admitted arbitrary strings for UUIDs and the
generation time, provided the document/checksum graph was internally consistent.
It now requires `Identity.Valid`, and its target includes `Documents.Identified`
for the root attributes of all three actual manifests. The file adapter quotes
the fields and constructs a kernel decision for this additional premise. No
producer proof, schema-validator exit code or native reduction authorizes it.

`Identity.UUID` describes the exact brace-delimited 8-4-4-4-12 hex layout from
`efmiIdentifierType.xsd`; uppercase and lowercase hex are admitted, and the
three IDs must differ after case normalization. `Identity.UTC` requires ASCII
digits and the exact UTC-second layout from `efmiManifestAttributes.xsd`.
The producer profile uses years 0001–9999, hours 00–23, and minutes/seconds
00–59. Calendar validity reuses `Std.Time.Year.Offset.Valid` and bounded month
and day types. `utc_fields` constructs a `Std.Time.PlainDate` with exactly
those parsed year/month/day values. It does not normalize an invalid day,
admit leap seconds or claim every alternate XSD date-time spelling.

Package proofs and their original three-axiom audit passed
(`build/efmi-identity-package.log`). The complete
`nix develop .#verification --command lake test` passed with exit status zero
(`build/efmi-identity-full-gate.log`). The strengthened actual-file theorem
`Rumoca.CheckedEFMIFiles.source_to_manifests` passed kernel checking and the
same axiom whitelist (`build/efmi-identity-manifest-contract.log`).
One new boundary rejection changes the shared generation date to the impossible
1900-02-29 while updating all dependent SHA-1 references. This exercises the
identity requirement independently of the existing mismatched-XML controls;
the general proofs cover arbitrary strings without a date/UUID test matrix.
The new rejection passed (`build/efmi-identity-rejection.log`), alongside all
existing grammar, source/C, FMI 3, GALEC and eFMI gates. No language case,
runtime arithmetic, solver policy or machine-compilation guarantee was added.

The Rust alignment review at `6bd616e3e6623a4556dad4730169f16d1435149c`
checked `rumoca-compile/src/codegen_target/checked_plan/target_artifact.rs` and
the eFMU templates. Rust also validates a canonical UTC instant, supplies
artifact identities separately from the compiler IR and rejects repeated IDs
within the artifact session. Lean retains that ownership: no identity work is
added to DAE or Solve lowering. Global identity freshness and accuracy of the
supplied generation time remain external facts. Fresh identity allocation for
the eventual producer, general schema correspondence, pinned schema-resource
membership, actual archive binding and failure-preserving publication remain
E05 work; the independent compliance checker and final review remain required.

The E05 composition sequence must connect the existing contracts, rather than
establish a separate archive-only success condition:

1. Preserve the originating model name in the manifest header and prove its
   source binding. The source-name checkpoint below replaces the former
   hardcoded `UnitIntegrator` with `a.parsed.ast.name`. Chapter 2 defines `name`
   by the originating modeling environment. This is prepared metadata, not
   backend name resolution or new grammar.
2. Specify the exact five code/manifest members plus the 45 pinned schema and
   companion resources. Prove unique paths and actual member lookup, then
   compose `ManifestContract` with `StoredZIP.Format.Conforms` for the same
   complete byte array. Include the official resources themselves, not merely
   a checksum inventory supplied by the producer.
   Resource embedding must use Lake's tracked file dependencies so changes to
   vendored files invalidate their checked module. The pinned Lean 4.29.1
   `include_str` elaborator reads a file into a string literal but does not
   register that file as a build dependency; supply the dependency through
   the owning package's Lake target and keep unrelated proof libraries cached.
3. Construct a practical actual-archive certificate using bounded per-member
   facts and the existing serialization theorems. A standalone ZIP theorem or
   a successful directory check cannot authorize different archived bytes.
4. Add the `.efmu` producer only when it can stage, certify and atomically
   publish this complete product, retaining previous output on failure. Run
   independent extraction, official schemas, native Production C execution and
   the pinned compliance checker on that actual product before closing E05/E06.

## Certified printers and shared C ownership

The two executable C function-body parsers have been replaced by structural printer proofs for
both existing C profiles. `RumocaC.PrinterProofs.module_render` handles every
numerical module, using induction over expressions.
`RumocaEFMI.CPrinterProofs.program_render` handles every syntactically valid straight-line
program, using compositional proofs for identifiers, expressions, statements,
lists, indentation and functions. Both prove membership in independently
defined character/token grammars and retain the execution-tree connection.
An equality to a second renderer alone is not the contract.

`RumocaC.SyntaxProofs.denotes_unique` proves lexical and program grammar
uniqueness. The high-level property-transfer theorem now uses this result to
identify every interpretation of the actual emitted text with the verified
target. The all-behavior, termination, IEEE, memory and protocol obligations
remain. Exact actual-byte binding and exact-root axiom auditing remain.
The source Modelica/GALEC parser is unchanged. Executable C parser-only checks
were removed with their implementation; actual-file attack controls remain.

The former unit round-trip theorem was cached and actual checking compared
exact emitted bytes; it did not reparse each artifact. The new proof strategy
removes that reader dependency and generalizes the printer proof within the
existing syntax profiles. It does not certify the complete FMI 3 adapter,
preprocessing, host ABI or native C compilation. XML already uses direct
printer certification.

Validation passed with exit status zero:

- `lake build check-fmi3 check-efmi check-compiler`:
  `build/c-printer-package.log`.
- `nix develop .#verification --command lake test`:
  `build/c-printer-full-gate.log`, including actual byte binding, forged producers,
  FMI 3 archives/native interfaces, GALEC, eFMI schemas/checksums and mutations.
- The actual source/C and eFMI contract roots are preserved in
  `build/c-printer-artifact-contract.log` and
  `build/c-printer-efmi-artifact-contract.log`. Their audits use only
  `propext`, `Quot.sound` and `Classical.choice`.

The printer migration is complete for these existing function profiles.
## Shared C extraction checkpoint

`packages/backend-c` now owns `RumocaC.*`: numerical emission/proofs,
`Tree`, `Memory`, `Body`, `Calls`, `Arithmetic`, `Interface`, and the thin
`Algorithm.emitProgram` renderer. The old FMI-owned implementations and module
paths have been removed, without compatibility aliases. The shared audit roots
moved into `RumocaCChecks`; `lake build check-c` builds that cached package.
The root Lake targets coordinate it alongside both adapter check libraries.
Only local package dependency records changed; external git revisions remain
pinned. eFMI no longer depends on the FMI 3 backend.

The C execution definitions take a `CInterface` dictionary. The adapter-owned
constant and C typedef bindings are selected by private local instances;
importing a backend does not install a global default. Shared execution and
call-lifting theorems are universal over the dictionary. FMI helper proofs
discharge their uint64 conversion premise using the actual FMI binding.
eFMI aliases are derived from header declaration nodes, and its actual header
contract now includes `interface_alias` and `interface_return` for every scalar
and value. Existing state, method, trace and compiler preservation proofs
have been rebuilt against these bindings.

The two logical routes are intentional:

```text
DAE → checked GALEC IR ──→ GALEC text
                     └─→ Solve IR → C → eFMI artifacts
DAE ───────────────────→ Solve IR → C → FMI 3 artifacts
```

C consumes prepared Solve programs on both paths. GALEC restrictions and its
method/initialization semantics belong before C emission. The FMI path must
not inherit those restrictions. Interfaces mean external C names, bindings,
method signatures, lifecycle wrappers and metadata/packaging; they do not
perform solver selection or Modelica/GALEC lowering.

Solve is the executable-program boundary, not a synonym for time integration.
Keep initialization and derivative evaluation available to the FMI 3 Model
Exchange interface; Co-Simulation composes these with a separately verified
solver policy. On the eFMI route, preserve the sampled algorithm already
specified by the checked GALEC methods. This distinction follows the
[FMI 3 ME/CS execution split](https://fmi-standard.org/docs/3.0.2/)
and the [eFMI Algorithm/Production Code relationship](https://www.efmi-standard.org/media/home/eFMI-Standard-1.0.0-Beta-1.html).
The C backend implements the prepared operations in either case; it must not
introduce a discretization or change the prescribed evaluation order.

The current tiny numerical `Solve.Model` and tensor
`Solve.Algorithm.Program` representations remain distinct. Their eventual
convergence should be within the shared tensor Solve program language, with
separate verified interface profiles. Do not erase a method's initialization,
clock, state or arithmetic obligations to force the types together. No source
language expansion is part of this extraction.

The Rust alignment review used checkout
`b9cdfcd373a1f5ab5767cd5ba71bb77039414215`:
`rumoca-ir-solve/src/lib.rs` keeps Solve free of DAE evaluation/phase logic;
`rumoca-phase-codegen/src/lib.rs` describes rendering checked phase-specific
projections and executable Solve blocks with typed layout. This extraction
keeps that separation while retaining Lean target grammar and execution proofs.

`lake build check-c check-fmi3 check-efmi check-compiler` passed with exit zero
in `build/shared-c-adapters.log`. The required
`nix develop .#verification --command lake test` also passed with exit zero,
recorded in `build/shared-c-full-gate.log`. This includes actual source/C and
GALEC certificates, all thirteen FMI 3 native interface groups, the FMU
archive/importer/runner checks, and the eFMI C/manifest certificate, official
schemas/checksums, native execution and existing mutation controls.
`build/shared-c-efmi-artifact.log` records the exact source-to-algorithm,
source-to-production and source-to-manifests roots, each using only `propext`,
`Quot.sound` and `Classical.choice`. The numerical actual-file root is retained
in `build/shared-c-source-artifact.log`.

`build/shared-c-audit-coverage.log` confirms that every previously audited root
is retained after namespace relocation (268 previous roots, 271 current).
`build/shared-c-ownership.log` records the source import checks and the absence
of an FMI 3 backend dependency in eFMI's manifest. No language cases or new
example tests were added for the extraction.

Next, resume E05's source-model-name binding and archive composition.
FMI 3 whole-adapter certification, the driven profile, parser completeness and
complete eFMU certification remain open.

## Source model name checkpoint

`Manifest.baseAttributes`, the three manifest builders and `prepare`/`checked`
now take the originating model name explicitly. The compiler supplies
`a.parsed.ast.name`; the backend does not inspect or resolve source syntax.
For `examples/Integrator.mo`, the three manifest roots now name `Integrator`.
The GALEC/C interface identifiers remain canonical to the admitted unit profile.

`Documents.Named` specifies all three decoded root names. `prepare_named`
proves this property universally, and `checked_correct` preserves it alongside
the existing identity and XML contracts. The composed `ManifestContract` binds
that property to the source AST; `ManifestContract.source_name` exposes the
connection through `XML.Document` for the three actual XML strings. Both new
theorem roots are included in the owning packages' axiom audits.

The fixed actual-file checker now shares one kernel-checked source AST and
`Parsed` witness between Algorithm Code checking and the name certificate.
Parser determinism identifies the parsed name with the artifact's AST name;
the final manifest graph theorem uses that equality. Native candidate fields
and byte comparisons still supply no proof authority.

One artifact boundary rejection renames both Modelica class delimiters while
retaining the original complete code/XML/checksum graph. This mutation leaves
the unit's GALEC and C bytes unchanged but must fail the source-name contract.
No additional language case or numerical example matrix was added.

The authority review used Chapter 2's common `name` definition and the pinned
`efmiManifestAttributes.xsd`, which identifies the originating block name.
The Rust checkout remains `b9cdfcd373a1f5ab5767cd5ba71bb77039414215`;
`solve_algorithm_production/presentation.rs` likewise carries a manifest name
from semantic model identity separately from code identifiers.

Package proof/audit checks passed in `build/efmi-source-name-packages.log`.
The required `nix develop .#verification --command lake test` passed with exit
zero in `build/efmi-source-name-full-gate.log`, including the actual GALEC and
combined code/manifest certificates, official schemas/checksums, native C,
all thirteen FMI 3 interface groups, archive/importer checks and the existing
mutation controls. `build/efmi-source-name-artifact.log` retains the exact
source-to-algorithm, source-to-production and source-to-manifests audits; each
uses only `propext`, `Quot.sound` and `Classical.choice`.
`build/efmi-source-name-rejection.log` records rejection of the renamed source
with its unchanged old code/manifests.

The source-model-name gap is closed for the admitted profile. Next is binding
the five code/XML members and the 45 pinned schema resources to the actual
archive. E05 archive composition/publication, E06 and the other core coverage
gaps remain open.

## Official checker layout discrepancy

The pinned official Compliance Checker v1.0.1, commit
`edf33452ed0628bde1d8102c77b1030259ad5f57`, was run in a disposable directory
under `build/`. Its bundled Lark 0.12.0 and colorama 0.4.6 were loaded directly
from the pinned release ZIPs, with the Nix environment's Python 3.13.14 and
lxml 6.0.2. No checker source or compiler dependency was changed.

The unmodified checker rejects `.efmu` filenames before inspecting the archive
(`build/efmi-official-checker.log`). A byte-identical `.fmu` alias passes that
guard but is rejected because the checker requires a top-level `eFMU/` folder
(`build/efmi-official-checker-alias.log`, `read_model_container` lines 133–170).
The pinned standard's Chapter 2 packaging definition admits a standalone
`.efmu` ZIP with `__content.xml` at ZIP root. Its separate definition for
embedding in a regular FMU uses `extra/org.efmi-standard`. A later example
uses `.fmu` naming. The checker's hard-coded `eFMU/` requirement does not match
the selected standalone definition.

Our selected profile remains the standalone root layout, consistent with the
Rust reference's `templates/galec/target.toml` packaging description. Changing
the certified member roster merely to satisfy this tool would depart from
that selected definition. The existing independent ZIP, exact-resource and XSD
checks are separate evidence; they do not count as a passing official checker.
Resolving or explicitly accommodating this upstream tool limitation remains
part of E05/E06 review before a release claim.

## Archive certificate construction checkpoint

`ArchiveContract` now composes the same source/code/manifest contract with
`StoredZIP.Format.Conforms` for five code/XML members and all 45 pinned schema
resources. General member, roster and lookup theorems are in the backend and
compiler audits. This is the authored stored-ZIP and manifest profile; it
does not extend the C endpoint, prove general XSD semantics or authorize a
release claim.

The pinned resources are embedded in `RumocaEFMIResources`, with a binary
Lake input-directory trace. `RumocaEFMISchemaCertificates` checks their UTF-8,
length and CRC-32 facts in bounded pieces and binds the resulting text roster
to the embedded resources. The complete library passed in
`build/efmi-schema-certificates.log`; both audit roots use only `propext` and
`Quot.sound`. `build/efmi-schema-cache.log` confirms native Lake reuse with
`--no-build`. The library's 64 MB Lean thread stack changes resource limits,
not kernel checking or axiom policy.

The new fixed archive checker reads one complete byte array, quotes consecutive
segments including the entire remainder, and composes header, payload, CRC,
offset, length and end-record facts. The code/manifest checker accepts the
same in-memory snapshot for directory and archive inputs. `verify-efmi`
selects that path from the filesystem type. The completed fixed root is
`Rumoca.CheckedEFMIFiles.source_to_archive`.

Package proofs and audits passed in `build/efmi-archive-packages.log`. The first
full gate reached the new archive check after passing the prior compiler,
parser, FMI 3 and GALEC checks. The source-to-manifests root passed, but local
record composition for the 5231-byte Production Code manifest exceeded the
elaborator recursion limit (`build/efmi-archive-gate-attempt1.log`). Keeping
record and encoding functions symbolic during unification fixes the isolated
8353-byte largest-resource case (`build/efmi-zip-large-member.log`), with the
normal axiom whitelist and unchanged recursion limit. The checker rebuilt in
`build/efmi-archive-checker-package.log` without rebuilding schema proofs.

Profiling isolated a separate path-validation cost: `cbv` spent about 11 seconds
constructing a safety proof for one 33-character member name. Simplifying with
the standard library's `String.splitOnAux` equations checks the same predicate
in under a second, including its kernel check, and uses the same axiom whitelist
(`build/efmi-zip-name-profile.log`, `build/efmi-zip-name-simp.log`). The checker
now uses that proof construction. The original slow diagnostic was explicitly
interrupted after this measured improvement, with exit 130; its log is retained
in `build/efmi-full-zip-slow-probe.log`. No timeout was treated as completion.

The revised complete 50-member check passed in `build/efmi-full-zip-probe.log`,
including the exact `FullZIPProbe.conforms` root audit with only `propext`,
`Quot.sound` and `Classical.choice`. It checks the complete candidate archive,
including every schema payload and all local, central and final record bytes.
The combined source-to-archive root and repeated full gate passed with exit
status zero in `build/efmi-archive-full-gate.log`. The root uses only `propext`,
`Quot.sound` and `Classical.choice`. The updated integration gate independently
extracts the certified archive, checks its pinned resources and official XSDs,
and executes its C; it adds only trailing-byte and changed-schema boundary
rejections to the existing controls.

Independent extraction, CRCs, all pinned resources and the three XSDs passed
for the unverified candidate under `build/efmi-archive-candidate`. A direct
kernel probe also rejects an appended byte at the final-record equality
(`build/efmi-zip-assembly-reject.log`). Neither observation substitutes for
the completed source-to-archive certificate. The checked deterministic fixture,
source, grammars and exact-root audit were retained in `build/checked-efmu/`;
its independent SHA-256 inventory passed. The grammar and IR semantics are
unchanged. Publication was still open at this checkpoint; its implementation
is described below. E06, full FMI 3 adapter certification and the other core
coverage gaps remain open.

## Pure archive generator theorem

`Artifact.archiveCode` now prepares the code and three manifests once from the
compiler artifact and supplied identity. `Artifact.efmuArchive` encodes that
prepared product with the fixed resource roster. Neither function writes files
or selects a solver, and the actual-file checker remains independent.

`archive_code_correct` proves the full source/Production C/manifest contract
for every successful preparation. `efmu_archive_correct` composes this with
the ZIP writer theorem. `compile_archive_verified` exposes the resulting
source-compilation-to-archive contract for every successful pair of compiler
and archive-generator results. All three roots passed their package audits in
`build/efmi-archive-generation-proofs.log`, using only the usual three axioms.
The existing integration fixture now obtains its prepared strings from this
function instead of duplicating manifest construction. The grammar, IR
semantics, required actual-byte checks and publication boundary are unchanged.

## Public eFMU publication

The CLI's `.efmu` output now calls the proved `Artifact.efmuArchive` function.
It writes the source snapshot and complete candidate into a private staging
directory beside the destination, invokes the fixed actual-archive checker,
audits its exact output, and renames the checked archive into place. Exceptions
clean up staging. Process execution, file I/O and rename remain trusted/tested
infrastructure; no filesystem or host-scheduler theorem is claimed.

Candidate identities use `IO.getRandomBytes` and the UUIDv4 bit layout in
[RFC 9562 §5.4](https://www.rfc-editor.org/rfc/rfc9562.html#section-5.4).
The UTC timestamp uses `Std.Time.Timestamp.now` and its formatter. Existing
identity predicates and the actual-file certificate check validity and local
distinctness. They do not assume global uniqueness, entropy quality or an
accurate system clock. There are no new dependencies, identity environment
variables or separate UUID/date executables.

The integration gate now uses this public command instead of the deleted
fixture-only producer. It retains independent extraction, official schemas,
checksum graphs, native Production C and existing artifact mutations. The
new publication boundary check fails the checker process after staging and
requires an existing destination to remain byte-identical, a new destination
to remain absent, and staging to be removed. The same extracted manifests
also exercise the OS identity adapter with an independent UUID/date reader.
The first public invocation passed the complete `source_to_archive` certificate
and all four exact-root axiom audits. Its full integration run then exposed
`compgen` being absent from the Nix shell's Bash build. Replacing that assertion
while the shell was reading the script also disturbed its input position and
caused an EOF error. That attempt is retained in
`build/efmi-publication-gate-attempt1.log`; it is not a passing full gate.
The assertion now uses ordinary pathname expansion, and both integration
scripts pass `bash -n`. After the script edit finished, the unchanged required
`nix develop .#verification --command lake test` passed with exit status zero
in `build/efmi-publication-full-gate.log`. It retained `build/Integrator.efmu`
and all four exact-root audits in `build/efmi-publication-artifact.log`.
Independent extraction, all pinned resources, official schemas/checksums,
native Production C, actual-file mutations and failure-preserving publication
passed. The separate FMI3 initialization-exit proof increment added during
the artifact run also passed its package and aggregate proof audits in
`build/fmi-initialization-exit-package.log` and
`build/fmi-initialization-exit-audit.log`; it changed no emitted code or grammar.

The pinned upstream checker was then run on this exact published archive
(SHA-256 `ea84dc8ff8ddb6c2d3c7c8e42ea47a49470399f929e276480319f858b0b9c99b`).
`build/efmi-publication-official.log` records its revision, dependency versions
and results. It returns 1 for the `.efmu` suffix, and returns 1 for missing
`eFMU/` after copying identical bytes to a `.fmu` alias. This reproduces the
documented layout discrepancy before manifest inspection. Neither the checker
nor the certified archive was modified to obtain a pass. The probe's own zero
exit status confirms the diagnosis, not eFMI conformance.

The current Rust reference is `d4d80fbb5d6c86a4859f96ed85bd814a4f4a9eff`.
Its `rumoca-ir-galec` facade describes checked array-native export data, and
`rumoca-ir-solve` owns solver-facing data without DAE phase logic. Its CLI
`packaging.rs` supplies artifact UUIDs; the `galec-production/target.toml`
keeps code/manifests and schema assets in one package graph. This increment
retains that separation: identity and publication belong to the compiler
driver, prepared code/XML and ZIP transport to the backend, and no packaging
work enters DAE or Solve. Grammar and IR cases are unchanged.

Public-artifact evidence is complete for this implementation checkpoint.
E05/E06 remain open for the documented standards/checker-layout review and
release claim. Full FMI 3 adapter certification, the driven
profile's target/artifact contract and generic parser completeness remain
required before grammar expansion.
