# Account-switch handoff — 2026-09-22

User requested wrap-up for an account switch. No further work should start
until resumed. All subagents are closed; the last tensor-proof assignment
failed on account authentication before producing a tensor draft.

## Checkpoint being committed

Base: `f0d6410`. This checkpoint adds the generic structural EBNF bridge,
computable certified runtime annotations for both frontends, audits and the
existing LALR native/mutation integration. It changes no grammar, production
frontend action, source admission, lowering or emitted C.

`packages/parser/Parser/LALR/EBNFStructure.lean` converts the actual payload CST
using `Fragment`/`AnnotatedRule` metadata. Universal proofs establish structural
fidelity, exact payload recovery, independent EBNF derivations, totality after
checked parsing and preservation of the complete parser language. Source
semantics use decoded encoded symbols; actual frontend classifier compatibility
and structural AST cutover remain separate obligations. No encoder injectivity
or helper-freshness assumption is introduced.

Focused terminal successes, with retained logs:

- `build/ebnf-structure-module-14.log`: 741 owner jobs.
- `build/ebnf-structure-parser-checks-2.log`: 791 jobs, 279 audited reports,
  including 19 new generic roots.
- `build/ebnf-runtime-frontend-audits-v1.log`: 839 jobs, 130 audited reports,
  including four actual frontend annotation roots.
- `build/ebnf-structure-native-lalr-v1.log`: existing `tests/lalr.sh` passed,
  1529 jobs and 24 audited reports; native recursive structural conversion,
  annotation-name mutation preserving CFG productions, and existing controls.

Bounded independent Astra reviews found no remaining bridge/projection issue.
These results do not establish frontend cutover or standards conformance.

## Required full gate is STILL RUNNING — not pass evidence yet

Command: `nix develop .#verification --command lake test`.
Shell session **54471**, launcher PID **2631750**, Lake PID **2631751**.
Log: `build/ebnf-structure-full-gate-v1.log`.
Frozen snapshot: `build/ebnf-structure-full-gate-v1-inputs.sha256` (2484 files).
All snapshot hashes were unchanged at handoff. This new handoff document and
the checkpoint commit were created after the run started; compiler inputs were
not edited. Do not restart merely because polling times out or is unavailable
after the account switch: inspect the same session/process first.

Observed passed stages include Lean regressions, LALR native/mutations,
LSP, source/C certificates and rejection controls, tensor/constant helpers,
tensor eFMI manifests and complete archive, and the production-shaped tensor
FMI source-build/boundary run. Latest output is for `SecondIntegrator`, the
second public source-FMU identity. The run has not returned a terminal result.

On terminal exit 0, recheck frozen hashes; join wrapped axiom reports and run
the unchanged `scripts/audit-lean.sh`; verify all 23 roots listed in
`build/ebnf-structure-new-roots.txt`, the recursive fixture's two runtimeRules
roots, and four retained FMU roots. Verify all artifact/mutation checks and
FMI matrices (75 functions, expected 526/650/526 cells). Then update
`docs/verification.md`, `dev/standards-review.md`, and `dev/lalr-parser.md`.
Do not describe the gate as passed without its terminal evidence.

## Confirmed open standards finding GJ01

`packages/backend-efmi/RumocaEFMI/TensorAlgorithmCode.lean` emits an undeclared
`jacobian(self.u .* self.u, self.u)` call. Independent Astra review inspected
the retained Algorithm Code and `build/TensorSquare.efmu`: no GALEC function,
external wrapper or corresponding manifest interface supplies that name.

Pinned eFMI Beta 1 §1.3.2 / §3.2.6 do not define this built-in. §1.3.3 and
§3.2.4 S-3.TODO (function lookup / Name-analysis) require valid resolution.
Normative local extract: `build/standards-review/efmi.txt`, especially lines
199–206 and 2738. The historical “resolved jacobian built-in” statement in
`dev/standards-review.md` near line 826 needs correction after the frozen gate.
Internal derivative/parse/artifact proofs do not establish this requirement.

Closure needs conforming lowered GALEC or a valid definition/wrapper/interface,
with mathematical refinement and actual-artifact binding. No repair is made
here. The user has NOT yet answered whether repair-only GALEC syntax changes
are allowed under the grammar freeze. No grammar change is authorized by that
unanswered question. N01, K02–K05, histories, native correspondence and MISRA
findings still block grammar expansion. No safety-critical readiness is claimed.

## Next repair that does not require grammar changes

An Astra review identified whole-interval read-only Euler preflight before
instance writes as the tensor/constant CS overflow repair. Next-step-only
checking cannot preserve the whole call on a later overflow. Preserve time,
x/dx/J, lifecycle/history, guard precedence and output initialization; logging
must retain explicit foreign callback effects, not invent a heap frame.
Scalar unit-rate addition already has a universal no-overflow proof.

Checked scratch prerequisite: `build/cs-euler-draft/FiniteEuler.lean` (266 lines).
Standalone `lake env lean` check passed in `check-03.log`; main reviewed the
whole file and audited all 16 reports in `check-03.axioms`. Hashes and exact
command are in `build/cs-euler-draft/README.md`. Earlier failed logs are retained,
not pass evidence. Scratch files are ignored/local, not part of this commit.

It proves fixed finite initial/rate and arbitrary Nat-count success iff
independent Adds-prefix execution, failure at a reachable real overflow,
absorbing rejection and signed-zero preservation. This is proof-only semantics,
not production code. Tensor lifting was requested but NOT implemented due to
the authentication failure. Tensor composition, prepared RHS correspondence,
actual count/clock progress, C preflight, public Discard and actual-artifact
contracts remain open. Do not infer public clock totality from Nat iteration.

## Process constraints

Use Astra for delegated work; avoid duplicate builds. Preserve the Lean-only
compiler and unchanged axiom/artifact contracts. Commit with author/committer
James Goppert <james.goppert@gmail.com> and `-s`; no AI coauthor. The overall
compiler goal remains incomplete; this is a checkpoint, not goal completion.
