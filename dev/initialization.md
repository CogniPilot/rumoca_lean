# Initialization of the verified unit core

Initialization is the next required compiler slice, ahead of further C-printer
work or array/AD admission. The user explicitly requested binding equations,
start values and default initialization on 2026-09-11. This work closes the
existing SR08/S01 gap; it is not permission to grow unrelated grammar.

The governing reference is the published **MLS 3.7 (May 19, 2026)**, not the
neighboring Rust grammar's earlier 3.7-dev label or the specification's master
branch. The current source has one unmodified continuous Real and `der(x)=1`.

| Source distinction | Required interpretation | MLS clause |
| --- | --- | --- |
| `Real x = c` | A constant binding constrains the state throughout simulation. Together with `der(x)=1` it is inconsistent; it must not be used as an initial value. | [§4.4.2.1](https://specification.modelica.org/maint/3.7/class-predefined-types-and-declarations.html#declaration-equations), [§8.1](https://specification.modelica.org/maint/3.7/equations.html#equation-categories) |
| `start=c, fixed=true` | Add the state equality at initialization. | [§8.6](https://specification.modelica.org/maint/3.7/equations.html#initialization-initial-equation-and-initial-algorithm) |
| `start=c` with `fixed=false` | A guess does not itself constrain the initial state. A tool that selects it as fixed must diagnose that choice. | [§8.6](https://specification.modelica.org/maint/3.7/equations.html#initialization-initial-equation-and-initial-algorithm) |
| No start attribute | Use the predefined-type fallback where a start value is needed. For the current unbounded Real, that is zero. This does not add an initial equation by itself. | [Definition 4.7 / §4.9.1](https://specification.modelica.org/maint/3.7/class-predefined-types-and-declarations.html#predefined-types-and-classes) |

The top-level-input discussion in §4.4.2.2 is not the clause for this ordinary
state. Parameter bindings also differ from continuous-state bindings; they
must not be introduced merely to hide an underdetermined state initialization.

The first implementation keeps the admitted source unchanged. Flat retains
the absence of binding/start/fixed modifiers, DAE carries the initialization
settings, and Solve stores a checked completion with its notices. The default
experiment starts at zero. A supplied FMI initial value
must be described as an explicit experiment choice and checked against source
constraints; the host cannot silently override a required source condition.

The source relation must continue to admit all solutions of the unfixed ODE.
The completed IVP adds the selected initial equation, has a unique trajectory
for arbitrary initial time, and refines the source relation. Compiler
preservation is then stated for that completed problem, with the completion
and diagnostics visible. No theorem should silently assume `x(0)=0` from the
derivative equation alone.

Required implementation and release evidence:

- [x] Computable initialization preparation and mathematical soundness,
  completeness, constant-binding rejection and unique completed solution.
- [x] Actual initialization data and per-pass correspondence through
  AST/Flat/DAE/Solve; require declaration/modifier origins at each stage,
  following the [mandatory provenance policy](provenance.md#mandatory-provenance-policy).
- [ ] Complete C initialization/artifact correspondence. The shared prepared
  initialization store has exact write, frame and printer proofs; FMI now emits
  it after allocation and on reset. Full allocator/adapter composition remains.
- [ ] FMI instantiate/reset/initialization, metadata and host-set policy
  correspond to the selected source initialization. Check ME and CS together.
- [ ] DAE→GALEC→Solve Startup and production C implement the same selected
  initialization, with actual GALEC/C/archive certificates.
- [x] CLI and structured LSP notices expose fallback and inferred fixing at
  the declaration span; successful warnings must not become fatal errors.
- [ ] Add only the required EBNF modification/binding productions from
  `crates/rumoca-phase-parse/src/modelica.par`, with independent source semantics
  and the full target/artifact chain for every newly admitted form.
- [ ] Re-run the MLS/FMI/eFMI stage review and required full artifact gate;
  close SR08 only when all applicable parts above are evidenced.

This implementation has been integrated from `build/literal-call-worktree`.
Its package/audit gate and required full gate passed there, in
`build/scoped-package-gate-fixed.log` and `build/scoped-full-gate.log`.
The latter covers the actual FMI and eFMI artifacts and retains an unchanged
source inventory. Complete current mainline audit lists are preserved.

The additional compiler-owned `EFMIInitializationProofs` module now derives
source initialization and uniqueness from the finite value loaded from the
actual Production C Startup result. `ArchiveStartupContract` additionally
identifies that code member inside the exact ZIP bytes and characterizes every
Startup behavior, including guaranteed termination for admitted entry storage.
The actual archive checker now requires this consequence alongside its existing
contract. These added roots and affected package checks passed in
`build/literal-call-worktree/build/scoped-startup-integration.log`.
The main-workspace package/audit gate passed in
`build/initialization-provenance/package-gate.log` (3282 jobs). All 1108 earlier
audit entries are retained, with 50 additions. The final integrated full gate
passed in `build/initialization-provenance/full-gate.log`; its source inventory
remained unchanged throughout the run. Final artifact identities are recorded
in the [standards review](standards-review.md#scoped-initialization-and-required-ir-origins-standards-impact).

Required scalar origins and declaration-based notices are implemented. The
subsequent required GALEC/Algorithm origin changes passed their full artifact
gate. Unit FMI IVP operation origins and their relation to the actual initial
plan also passed the full artifact gate in `build/fmi-provenance/full-gate.log`.
Development tensor origins, emitted-byte maps, FMI allocation and
host-set/lifecycle composition remain open. No binding/start/fixed grammar
case is admitted by these changes. SR08 is not closed.

The following C increment makes the shared initializer's operation origins
mandatory. FMI creation/reset consume its checked emission;
`CInitialization.Emission.preserves` joins exact annotation/source ancestry
with the existing all-behavior storage contract. The complete downstream
package gate passed in
`build/literal-call-worktree/build/c-initial-provenance-package-gate.log`.
Its required main-workspace artifact gate also passed in
`build/c-initial-provenance/full-gate.log`, with unchanged inputs and both actual
target archives checked. Allocator, host-set and whole-lifecycle/artifact
composition remain separate SR08 obligations.

The next shared-fragment contract, `Emission.printed_preserves`, connects the
same initialization write to its exact printed UTF-8 ranges and every map
entry's source ancestry. It retains the complete C-body behavior theorem.
Its package/audit gate and required main-workspace artifact gate passed; the
latter is recorded in `build/c-mapped-initialization/full-gate.log`, with
unchanged inputs and both actual target archives checked. It does not yet
connect these fragment ranges to enclosing file or
archive-member offsets, nor close the remaining initialization obligations.
