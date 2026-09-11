# In-tree verified LALR parser

The current full gate is `nix develop .#verification --command lake test`.
Make commands in dated checkpoints below record historical runs before the
Lake migration; see the [current commands](../docs/development.md).

Status: **2026-09-09, active and incomplete**. This work follows the user's
request for our own LALR(1) parser in Lean, with no assumed-correct parser
generator. It changes parser infrastructure, not the admitted Modelica language.
The existing DFA/action parser remains the production path until the replacement
has its complete contract. The FMI wrapper obligations remain open as well.

The later [GALEC Algorithm Code checkpoint](efmi.md#algorithm-code-checkpoint-evidence)
now passes the full gate using a second EBNF and this same LR engine. Its
profile-specific acceptance and actual-file contract do not close LR04–LR07.
This authorization supersedes the GALEC deferrals recorded in historical round
evidence below.

## Required contract

The intended public interface is a grammar-indexed, proof-carrying result:

```lean
generate : (g : Grammar) → Except GeneratorError (CertifiedParser g)
```

The certified result must establish the following independently of candidate
table construction:

- Every returned AST belongs to the grammar's token/semantic-action relation.
- Every grammar-valid input is accepted with its specified AST, within a proved
  resource domain. Checking a returned tree alone does not establish this.
- The parser cannot underflow its stack, use an invalid reduction, miss a
  required goto, or report another internal table error.
- Finite-input termination and the supported fuel bound are justified. Resource
  exhaustion is distinct from syntax rejection, including on malformed input.
- The lexer, EBNF reader and EBNF desugaring compose with those results, binding
  the actual grammar file and source characters to the result.

Candidate construction is entirely Lean and in this repository. A bug in it
must prevent certification rather than invalidate an accepted parser's theorem.
A further generator theorem should establish success for the supported class
of conflict-free LALR grammars under explicit preprocessing limits. That is a
separate obligation from correctness of successfully certified output.

Reusability is a requirement on this core, not another language milestone.
The runtime, table validator and their theorems must quantify over the supplied
grammar and remain independent of Modelica ASTs and compiler IRs. Lexical
categories, token payloads and typed AST actions belong at the language boundary;
their contracts should compose with the generic engine. The present EBNF reader
still has a small dialect and a reserved `IDENT` category, so loading an arbitrary
standard's EBNF verbatim is not yet supported.

The engine is now the independent `parser` package (`Parser.*`). Modelica and
GALEC live in sibling `modelica-parser` and `galec-parser` packages, including
their EBNFs, generated tables, lexical policies, AST actions and concrete
certificates. Both depend on the engine; the engine imports neither language.
All prior audit roots remain checked across the three packages, with no
compatibility modules or duplicated proofs. This adds no grammar cases.

GALEC is now the user's authorized tiny reuse case. Its
[published specification](https://www.efmi-standard.org/media/home/eFMI-Standard-1.0.0-Beta-1.html)
uses ISO/IEC 14977 EBNF together with separate lexical and semantic rules. We
have added a restricted unit-block EBNF, a configurable scanner with its own
lexical contract, and a named action profile using the same LR runtime and
generic proofs. A profile-specific acceptance theorem covers its fixed token
skeleton; it does not close generic LR completeness or ISO EBNF preservation.
The [eFMI roadmap](efmi.md) records the standard authority, DAE-to-GALEC-to-Solve
pipeline and unfinished Production Code/archive gates. Parser reuse alone does
not prove another language's typing, execution or lowering semantics.

The design reference is
[*Validating LR(1) Parsers*](https://gallium.inria.fr/~fpottier/publis/jourdan-leroy-pottier-validating-parsers.pdf),
especially its separation of soundness, safety and completeness. Its proofs
are not imported or assumed. The implementation and new proofs are Lean;
mathlib supplies the context-free grammar rewriting semantics.

## AST ownership and action boundary

Use user-defined Lean AST types and explicit, pure, typed construction actions.
The generic parser owns grammar derivations; the language owns the AST. A
grammar-shaped syntax tree is a useful default representation, but users should
not have to expose EBNF helper productions in their compiler AST.

For LR06, give each source production an action whose arguments are the typed
values of that production's children and whose result has the nonterminal's
declared value type. The EBNF-to-CFG proof must account for helper actions for
sequences, alternatives, options and repetition. Helpers should not require
handwritten actions tied to generated integer production IDs. Initially keep
the existing tiny AST and small explicit constructors; generated AST datatypes,
field annotations and reflective record population are not required now.

Typing actions is necessary but insufficient: two fields of the same type can
still be swapped. State an independent source/tree-to-AST relation, prove that
the language actions preserve it, and compose that with the generic parser
theorem. Pure total actions avoid introducing hidden effects or new termination
assumptions. Language validity checks belong to a separately specified checked
phase; action failure must not silently weaken syntax completeness.

Keep original tokens and eventual source locations separate from the chosen AST
representation. Multiple syntactic forms may intentionally map to one AST, so
the generic action contract should use a relation rather than require the AST
to reconstruct one exact token sequence. The existing `ParserActions.Actions`
contract suffices for the frozen profiles but is tied to their DFA and exact
token encoding; it is not yet the intended grammar-generic LR action interface.

## Implementation and proof sequence

- [x] **LR01: independent grammar semantics.** `LALR.Grammar` uses mathlib's
  `Symbol`, `ContextFreeRule`, `ContextFreeGrammar` and `Derives`, with array
  storage and separate terminal/nonterminal IDs. EOF has a dedicated table
  column and cannot occur as an input token.
- [x] **LR02: candidate LALR construction.** `LALR.Generator` implements nullable
  and FIRST fixed points, canonical LR(1) item closure/goto, kernel merging and
  conflict detection. Merge keys contain LR(0) kernel items; lookaheads are
  unioned. No precedence or conflict-resolution policy is silently selected.
  Preprocessing bounds and internal consistency failures are explicit errors.
- [x] **LR03: checked runtime soundness.** `LALR.Runtime` implements shift,
  reduce, goto, EOF acceptance and a stack of trees. `LALR.Soundness.parse_sound`
  proves every successful checked result derives exactly the complete input
  in mathlib's grammar semantics, for arbitrary tables and fuel. An accumulator
  yield traversal is proved equivalent to the declarative tree yield. Increasing
  fuel preserves successful raw execution. `RuntimeProofs` now also proves that
  every raw shift/reduce execution preserves tree validity and the complete
  input word, so the final tree check cannot fail. This is not the full parser
  contract.
- [ ] **LR04: full table validation.** Prove the finite validator's safety and
  completeness implications, including stack invariants, item propagation,
  nullable/FIRST facts, EOF and absence of invalid reductions/gotos. Add a
  progress/termination certificate; do not turn fuel exhaustion into rejection.
  The planned `CertifiedParser` API must remain unavailable until these proofs
  have an actual instance, not just assumed certificate fields.
  **Proved increment:** `Safety.validated_parse_safe` composes the finite
  structural validator with the actual runtime: any input/fuel can only
  succeed, reject or exhaust fuel, never fail an internal table/tree check.
  Checked annotations cover all shifts/gotos; backwards state summaries
  establish valid reduction symbols, enough stack, available return gotos and
  a singleton start tree at EOF, for every concrete stack path. The emitted
  Modelica and recursive tables carry kernel instances of this theorem.
  The emitter now certifies each production's reduction summary separately,
  combines them with array extensionality, and substitutes the checked arrays
  into the same `Safety.validate` obligation. These private certificate arrays
  are noncomputable definitions, so they add no runtime parser storage. On the
  138-state array grammar, the local check with two Lean threads passed in
  226 seconds with a measured process peak of 8,740,704 KiB
  (`build/tensor-lalr-shards.log`); the monolithic check was observed above
  18 GiB. This fits the public repository's
  [16 GB GitHub runner](https://docs.github.com/en/actions/reference/runners/github-hosted-runners).
  This changes certificate evaluation, not the validation conditions or the
  runtime parser, and does not establish a bound for arbitrary grammars.
  Both parser packages passed their audits in
  `build/tensor-sharded-parser-gate.log`. Generated-file freshness and the
  complete LALR certificate/mutation gate passed in
  `build/tensor-sharded-lalr-gate.log`. Mutation checks identify failure of the
  public safety root after rewriting, rather than matching its earlier goal text.
  **Next:** checked LR-item propagation facts that imply completeness, then a
  justified parsing bound. A reject-all table can satisfy
  structural safety; its counterexample is included in the kernel regressions.
  **Nullable/FIRST increment:** `FirstCheck.validate` checks grammar-equation
  closure independently of the search. `FirstProofs.derives_below` proves
  prediction coverage backwards through any mathlib CFG derivation;
  `nullable_complete`, `first_complete` and `lookahead_complete` give the empty
  suffix and leading-token facts needed by LR closure. Actual emitted fact
  arrays carry kernel certificates. These facts may be conservative; they are
  not a proof of exact FIRST sets or a substitute for LR-item validation.
- [ ] **LR05: verified EBNF frontend.** `LALR.EBNF` currently prepares candidates
  using the existing reader. References stay nonterminals; sequences remain
  sequences; alternatives, optional forms and repetition use fresh helper
  nonterminals. Recursive references are supported. Prove the reader against
  an independent metalanguage relation (P02), and prove language preservation
  of desugaring in both directions, including helper freshness and empty forms.
- [ ] **LR06: typed AST actions and production replacement.** Connect actions
  and original token payloads to the grammar relation; instantiate the complete
  contract for both current profiles; preserve character/source binding,
  freshness and artifact checks. Only then replace the current production
  parser and retire redundant runtime recognition. Keep the production compiler
  restricted to the unit profile until the driven FMI path is fully verified.
  Use the [AST ownership boundary](#ast-ownership-and-action-boundary) above;
  a configurable AST derivation framework is not a prerequisite for this slice.
- [ ] **LR07: preprocessing success and cost.** Prove fixed-point convergence,
  LR construction/merging invariants and success under documented limits. Review
  canonical-state growth before larger grammars: canonical LR(1)-then-merge is
  an understandable first implementation, not a claimed optimal LALR algorithm.
  Improve construction only with unchanged certificates and measured evidence.

The next LR04 increment must connect checked item annotations to the actual
table entries. Check the initial augmented item, closure using the certified
`lookaheads` function, dot advancement through shifts/gotos, completed-rule
reductions and augmented-rule acceptance. Our whole-input runtime uses only
the dedicated EOF lookahead at the start and accepts only after consuming all
input; do not silently adopt a prefix-parser contract from the design reference.

Then prove that execution follows any valid derivation tree, with explicit fuel
for its shifts/reductions, and connect existence of such a tree back to mathlib
CFG derivability. The concrete tree is a proof device, not an oracle supplied
by the user. Combine with structural safety to remove internal-error alternatives.
A separate progress argument is still needed for malformed inputs and for a
practical bound expressed in terms of input size. Keep all these obligations
under LR04; the new FIRST certificate alone closes none of them.

## Regression evidence required

`Tests/LALRChecks.lean` exercises recursive/nullable and left-recursive grammars,
the non-SLR assignment grammar, canonical-LR-only merge conflicts, ambiguity,
malformed input, EOF, exhaustion and forged trees/tables. It separately checks
missing table rows/columns, invalid shift/goto targets, shifting EOF, unknown
reductions, stack underflow and missing gotos, distinguishing them from syntax
rejection. Its theorem roots are
included in the unchanged strict axiom audit. These concrete examples do not
close LR04–LR07.

`Tests/LALRSafetyChecks.lean` additionally checks the validator itself against
missing edges, wrong symbols, invalid targets/reductions, missing return gotos,
premature acceptance and EOF shifts. A second path to a reduction state exposes
an unsafe return even if the producer omits its annotation. The public parser
safety theorem is instantiated for arbitrary inputs/fuel, and a reject-all
counterexample explicitly distinguishes safety from completeness.

`Tests/LALRFirstChecks.lean` checks nullable propagation, direct and transitive
FIRST dependencies, inherited EOF lookahead, malformed grammar/fact dimensions
and omission of facts. A conservative-summary example distinguishes coverage
from exactness against the independent CFG language. The actual-file integration
check also strips the emitted fact array and requires kernel rejection.

Some checks use Lean's proof-producing `cbv` normalizer to rewrite defining
equations: the standard library's merge operation has an opaque accessibility
proof that blocks direct kernel reduction. The resulting terms are still
kernel checked and axiom audited; no native-reduction axiom is used. The
experimental-tactic advisory is disabled only for concrete regression and
generated certificate computations so the axiom reports remain machine readable.
The universal soundness, safety and FIRST coverage proofs use ordinary induction
and rewriting.

`lalrgen` is an experimental Lean emitter of candidate Lean tables and their
structural safety and nullable/FIRST certificates. It does not produce
`CertifiedParser`, and its
generated header states that limitation. `tests/lalr.sh` checks deterministic
output, kernel checking and axiom auditing of the actual emitted certificates,
kernel execution of emitted recursive tables, corruption of emitted shift/edge
constants, conflict/undefined-reference rejection and preservation of output on
those failures. The separate native
test executable parses both current Modelica profiles and nested inputs through
depth 500. The required overall gate remains
`nix develop .#verification --command lake test`.

## Algorithm and cost boundary

The generator constructs canonical LR(1) states and merges equal LR(0) kernels.
It rejects conflicts instead of silently choosing an action. This is standard
LALR construction, not a proof that every grammar is LALR(1). The current safety
certificate does not classify a grammar as LALR(1) or prove completeness; those
need the remaining LR04/LR07 obligations.

The present choice is provisional for the full language. Modelica 3.7 explicitly
notes that its equation/procedure productions need left-factoring and extra
semantic checks for recursive-descent parsing; see
[Appendix A.2.6](https://specification.modelica.org/maint/3.7/modelica-concrete-syntax.html).
This motivates an LR runtime, but does not establish that the entire published
grammar is LALR(1). Keep the validator contract independent of LALR merging so
another LR construction could reuse it if needed. This is a design boundary,
not a commitment to implement multiple generators now.

At runtime, dense action/goto arrays provide direct lookup without backtracking.
Reduction work is proportional to the selected rule length, with a final tree
validation and accumulator-based yield traversal. For a fixed grammar with a
linear bound on reductions, this supports linear parsing work. That bound is
not yet proved for our accepted candidate domain. Proof terms are erased;
the finite table validator runs during preprocessing, not on each input.

Generation currently uses repeated closure scans, list sorting/deduplication and
linear state lookup. Canonical LR(1) construction can produce many more states
than the merged LALR table. Dense tables also use space for absent entries.
These are scaling limits to measure before a larger grammar; no performance
parity with parol is claimed. LR07 tracks construction improvements under the
same certificate contract. Lexer modes, generated typed actions, error recovery
and grammar editor tooling are separate features, outside this tiny core.

Parol currently offers both LL(k) and LALR(1), plus generated AST/action types,
scanner states, error recovery, analysis/visualization and editor tooling; see
its [official documentation](https://github.com/jsinger67/parol). Its
[LALR construction adapter](https://github.com/jsinger67/parol/blob/main/crates/parol/src/analysis/lalr1_parse_table.rs)
uses `lalry` and configures conflict resolution with shift preference and
production-order priority. Our current generator rejects conflicts. Adding
resolution would require specifying which parses it selects and adjusting the
semantic contract, not merely suppressing diagnostics. The Rust Rumoca checkout
reviewed below actually uses parol's `LLKParser` with `MAX_K = 3`, as recorded in
its generated `modelica_parser.rs`; it does not instantiate parol's LALR mode.

At this round's reference review, `~/git/rumoca` was at
`6ea5ea44d9c4ad70dca67f957e5721d1bb31fa90`; its parser is now
`crates/rumoca-phase-parse`, with the grammar in `src/modelica.par` and parol as
a build dependency. The existing selected grammar is unchanged. None of these
parser-only fixtures introduces a Modelica expression, IR lowering, tensor
scalarization or backend responsibility.

## Modelica and GALEC design priorities

The user selected Modelica and future GALEC as the workloads that should drive
parser choices. Reusability means sharing a small verified engine, with a grammar,
lexical contract and typed actions for each language. It does not require a
framework for every parsing algorithm or arbitrary action effects.

LALR(1) remains the starting construction. Modelica 3.7's
[equation/procedure grammar note](https://specification.modelica.org/maint/3.7/modelica-concrete-syntax.html#equations1)
identifies difficulties for recursive descent; the Rust reference similarly
factors equation/function-call syntax and then checks the result in its actions.
This favors evaluating LR tables against the standard productions. It does not
prove either complete language's grammar is LALR(1), or establish a speed ranking.
Keep the runtime certificate independent of state merging. If a future admitted
fragment has conflicts, distinguish grammar ambiguity from conflicts introduced
by merging LR(1) states before choosing a remedy. Preserve distinguishable states
where necessary rather than silently resolve conflicts or change the language.
Any grammar rewrite needs a preservation argument against the selected standard
fragment. No second construction algorithm is being added now.

Concrete constraints for subsequent verified increments:

- Keep expression precedence and associativity in the grammar/action contract.
  AST construction must preserve operator grouping, component references,
  array dimensions and subscripts. Name resolution, dimensional analysis and
  tensor lowering remain subsequent compiler work.
- Use a shared scanner interface with language-specific lexeme rules. GALEC's
  [lexical specification](https://www.efmi-standard.org/media/home/eFMI-Standard-1.0.0-Beta-1.html#_lexemes)
  includes nested block comments, structured quoted identifiers and signed
  numeric forms. Its identifier and keyword rules also differ from Modelica's.
  A regular-token DFA alone cannot recognize arbitrary nested comments; a
  future implementation needs a proved nesting-aware scanner component.
  Reusing infrastructure must not equate the two token languages.
- Preserve raw source spans independently of decoded identifier/literal values.
  Plan efficient scans over source buffers, with exact character/UTF-8 and
  maximal-munch correspondence proofs; do not assume every source character is
  ASCII or change lexical behavior to reduce allocations.
- Bind each admitted EBNF fragment to its standard rule and revision. GALEC's
  ISO/IEC 14977 notation includes exceptions and special sequences beyond our
  current dialect. Specify and verify needed translations or lexical contracts
  when admitting a fragment; parsing the notation alone does not establish its
  lexical and prose semantic restrictions.
- Build typed ASTs directly through pure reductions, with no mandatory temporary
  grammar tree in the eventual fast API. Keep grammar/keyword tables immutable
  and file state local so batches can run concurrently.
- Evaluate Modelica package batches and, when admitted, generated GALEC code
  separately. File-count scaling, long names, comments and large expression or
  array syntax can stress different parts of the parser. Start measurements
  with the already admitted inputs; broader corpora must wait for their proofs.

These choices refine the performance plan below. They do not add GALEC syntax,
broaden the current Modelica profile or close its unfinished parser contract.

## Performance and parallel batch design

The user requires competitive speed with parol and ANTLR on projects containing
thousands of files. This is an acceptance requirement to measure, not an
established result. Pin comparison versions, name the ANTLR runtime target and
use equivalent admitted syntax, AST construction and error behavior. Report
cold and warm results separately: ANTLR's adaptive prediction caches analysis
results at runtime, as described in the authors'
[ALL(*) paper](https://www.antlr.org/papers/allstar-techreport.pdf).

The following decisions constrain the existing core; they do not add languages:

- Generate and kernel-certify the grammar once when building the parser. Share
  immutable tables across files. Parsing each source must not invoke Lean
  elaboration, grammar construction or table certificate checking.
- Support many files in one native process, with parallelism across files.
  Each worker owns its input buffer, tokens, stack, AST construction and
  diagnostics. Shared grammar data is immutable; AST actions are pure. Keep
  cross-file name resolution in its later compiler phase. Avoid a global mutable
  symbol interner or diagnostic accumulator in the parsing loop.
- Bound worker count and outstanding input bytes so temporary parsing memory
  follows the active workload; account separately for retained source buffers
  and completed ASTs. Associate every result with a stable input index/source
  identity and return diagnostics in input order, independent of worker completion order.
  Cancellation and I/O failures must be explicit and distinct from syntax errors.
  Splitting a single file across workers and incremental parsing are not needed
  for this core.
- Keep integer token/state/production IDs and direct action/goto lookup. Dense
  arrays already provide this. Measure table size and cache behavior before
  adding compression. Bounded machine-index representations require a proved
  correspondence to mathematical indices and explicit size limits.
- Intern repeated identifier spellings using the design below. Token kinds and
  resolved variable slots already having integer IDs does not establish this
  separate memory property.
- Permit contiguous token/stack storage with local updates and source-buffer
  spans. The current list stack and character-list lexer favor simple proofs;
  they are not a final performance commitment. Any replacement must preserve
  maximal munch, source positions, accepted results and error behavior. Avoid
  repeated copying or string lookup for token kinds.
- Make typed actions suitable for building the desired AST during reductions.
  Constructing a full derivation tree and traversing it again to build the AST
  must not be mandatory in the final API. A grammar-shaped tree can be one action
  instance. Proofs belong in erased propositions; retain concrete token/tree
  data only when the requested result or diagnostics require it.
- Eliminate redundant runtime checks only through proved refinements. The new
  word/tree and structural safety theorems provide the necessary starting facts.
  The current final tree validation and reduction-symbol checks still execute;
  Lean does not erase executable Boolean checks merely because they are proved
  redundant.
- Measure preprocessing, lexing, token parsing and AST construction separately.
  Start with batches of the existing admitted models, long valid identifiers
  and whitespace, and existing recursive parser fixtures. Track files/s,
  bytes/s, peak memory, allocations where available, increasing-size behavior
  and one-worker versus multiple-worker scaling. Separate filesystem I/O from
  in-memory parsing; equivalent-output baselines must not compare a recognizer
  with a parser that also constructs an AST.

The semantic batch reference is the ordered map of the pure per-file parser
over the supplied source snapshots. A completed parallel implementation must
refine that reference, including result-to-file association. Pure parsing makes
the language result independent of scheduling; it does not by itself prove an
arbitrary task orchestrator correct. The Lean task runtime, native compilation
and host execution must remain explicit at the execution trust boundary; do not
introduce concurrency axioms or claim the scheduler has been verified.

The worker adapter and performance comparisons were not implemented in this
original design round. The subsequent deterministic batch implementation is
recorded in [provenance.md](provenance.md#parallel-frontend); performance parity
and bounded outstanding input bytes remain open. Subsequent parser refinements
must preserve completeness, progress and the frontend/action contract and pass
the required artifact gate. No separate concurrency framework or
additional grammar is needed to establish this design.

### Identifier interning

**Current status: planned, not implemented.** `Parser.Token.ident` and the
Modelica AST name fields contain `String`. The lexer constructs a spelling for
each occurrence; no compiler-owned interner canonicalizes these strings.
Resolved core references use bounded slots, while declaration/presentation data
still retains strings. The checked `CLiteral.Pool` deduplicates C literal text
for a proposed backend transformation; it is not a frontend identifier table
and is not yet connected to production emission.

The intended representation is a compact `StringId` plus a compilation-owned
table of unique spellings. Keep this utility independent of Modelica and GALEC.
Spelling identity must remain distinct from declaration identity: two names
with the same spelling can resolve to different declarations. Every occurrence
keeps its own source span; interning must not merge diagnostic locations.

Each parser worker owns a file-local pool. Merge the completed pools in stable
input/first-occurrence order and remap every retained ID before cross-file
resolution. This permits parallel lexing without a shared mutable interner in
the parsing loop. A compilation or immutable LSP snapshot owns its table;
avoid a process-global pool retaining names from discarded edits indefinitely.
Keep stable IDs within a table's lifetime and make table identity explicit at
API boundaries so IDs from unrelated files cannot be accidentally compared.
For incremental sessions, preserve the existing workspace table and append new
spellings from changed files in a defined merge order. Re-sorting all spellings
after each edit would renumber unchanged IDs and defeat incremental reuse.
Own tables by reclaimable workspace epochs; any later compaction needs an
explicit remapping proof. See the [performance audit](performance-audit.md#interning-sharing-and-incremental-sessions).

Reuse Lean's standard collection implementations and their available proofs
when implementing the table; do not write a separate hash algorithm. Hashes
may accelerate lookup, but exact spelling equality must decide identity, even
under collisions. Any fixed-width ID requires a proved bound and explicit
exhaustion behavior. The required Lean refinements establish:

- Interning then resolving recovers the exact spelling; duplicate spelling
  receives the same ID in the same table, and distinct spellings never alias.
- Table extension preserves all existing IDs and their meanings.
- Decoding interned tokens/ASTs recovers the current reference representation,
  including rejection behavior, name resolution and source spans.
- Merging and remapping preserve decoded results and diagnostics independently
  of worker completion order; the composed artifact guarantee still holds.

These are semantic properties, not a measured memory bound. Record peak and
retained memory, allocations and merge overhead on batches of the current
subset before claiming a saving. Interning does not eliminate source buffers,
character-list lexing or retained predecessor IRs. Track implementation under
[E03](roadmap.md#maintainability-and-efficiency); it adds no language cases and
does not substitute for the open FMI/eFMI core obligations.

## Previous checked working snapshot

The complete `nix develop .#verification --command make test` gate passed on
2026-09-09. `build/lalr-gate.log` records 231 main roots, 8 scalar, 4 tensor,
6 memory, 9 call, 14 time, 16 history and 13 LALR regression roots: **301 audited
roots**, all within the unchanged standard-axiom policy. The new generator
produced 76 LALR states from 81 canonical LR(1) states for the current EBNF.
Both current syntax profiles, recursive inputs through depth 500, emitted
Lean-table execution and generator failure checks passed.

The existing actual-source/C certificate, all adversarial artifact controls,
thirteen native FMI groups and FMU publication failure tests also passed.
`build/Integrator.fmu` and both runner CSVs were rebuilt; ME and CS agree on
`0.5, 1.5, 2.5, 3.5` at times `0, 1, 2, 3`. The working source inventory is
`build/lalr-snapshot.sha256`. These checks preserve the production baseline and
establish the stated LR01–LR03 increment; they do not close LR04–LR07 or certify
the whole FMU.

## Structural safety gate and working snapshot

The complete `nix develop .#verification --command make test` gate passed on
2026-09-09 in `build/lalr-safety-gate.log`. It audited 246 main roots, 8 scalar,
4 tensor, 6 memory, 9 call, 14 time, 16 history, 13 LALR runtime and 12 LALR
safety regression roots: **328 audited roots**, within the unchanged standard
axiom policy. The emitted Modelica and recursive safety/execution theorems were
also kernel checked and axiom audited. Corrupted emitted shifts and missing
edge annotations failed certification as required.

Both current Modelica syntax profiles and recursive native inputs through
depth 500 passed. All existing actual-source/C and forged-artifact controls,
thirteen native FMI groups, ME/CS runner traces and publication failure checks
passed. The combined `build/Integrator.fmu` was rebuilt. The working source
inventory is `build/lalr-safety-snapshot.sha256`; logs and inventories stay under
`build/`. This closes the structural safety increment, not the remaining LR04
completeness/progress work, LR05–LR07 or whole-FMU verification. GALEC support
and automatic AST generation were not added.

## Nullable/FIRST coverage gate and working snapshot

The complete `nix develop .#verification --command make test` gate passed on
2026-09-09 in `build/lalr-first-gate.log`. It audited 260 main roots, 8 scalar,
4 tensor, 6 memory, 9 call, 14 time, 16 history, 13 LALR runtime, 12 structural
safety and 10 FIRST regression roots: **352 audited roots**, under the unchanged
standard-axiom policy. Emitted Modelica and recursive table safety/FIRST
certificates and their universal consequences were also kernel checked and axiom
audited. Removing the actual emitted fact array failed certification as required.

The two existing syntax profiles, recursive native parsing through depth 500,
all actual-source/C and forged-artifact controls, thirteen native FMI groups,
ME/CS runner parity and archive publication controls passed. The rebuilt
`build/Integrator.fmu` produces `0.5, 1.5, 2.5, 3.5` at times `0, 1, 2, 3`
through both interfaces. Working source inventory:
`build/lalr-first-snapshot.sha256`. Reference review:
`0cfc506d9fd8ad8cc7433b173ec20b51ef603a57` in `~/git/rumoca`.

This closes the nullable/FIRST coverage increment. It does not close LR-item
propagation, parser completeness/progress, frontend/action preservation or the
whole-FMU proof. The Modelica/GALEC workload and parallel batch decisions above
are design constraints; no additional syntax, worker implementation or
performance comparison was introduced in this increment.
