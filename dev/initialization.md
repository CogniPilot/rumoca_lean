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

The first implementation step keeps the admitted source unchanged. Flat must
retain the absence of binding/start/fixed modifiers, DAE must carry the
initialization problem, and Solve must store a checked completion with its
notices. The default experiment starts at zero. A supplied FMI initial value
must be described as an explicit experiment choice and checked against source
constraints; the host cannot silently override a required source condition.

The source relation must continue to admit all solutions of the unfixed ODE.
The completed IVP adds the selected initial equation, has a unique trajectory
for arbitrary initial time, and refines the source relation. Compiler
preservation is then stated for that completed problem, with the completion
and diagnostics visible. No theorem should silently assume `x(0)=0` from the
derivative equation alone.

Required implementation and release evidence:

- [ ] Computable initialization preparation and mathematical soundness,
  completeness, constant-binding rejection and unique completed solution.
- [ ] Actual initialization data and per-pass correspondence through
  AST/Flat/DAE/Solve; require declaration/modifier origins at each stage,
  following the [mandatory provenance policy](provenance.md#mandatory-provenance-policy).
- [ ] Explicit C initialization from prepared Solve data, with actual write,
  frame and printer/artifact contracts. FMI currently obtains its first zero
  through allocation; this must be replaced by the prepared initialization.
- [ ] FMI instantiate/reset/initialization, metadata and host-set policy
  correspond to the selected source initialization. Check ME and CS together.
- [ ] DAE→GALEC→Solve Startup and production C implement the same selected
  initialization, with actual GALEC/C/archive certificates.
- [ ] CLI and structured LSP notices expose fallback and inferred fixing at
  the declaration span; successful warnings must not become fatal errors.
- [ ] Add only the required EBNF modification/binding productions from
  `crates/rumoca-phase-parse/src/modelica.par`, with independent source semantics
  and the full target/artifact chain for every newly admitted form.
- [ ] Re-run the MLS/FMI/eFMI stage review and required full artifact gate;
  close SR08 only when all applicable parts above are evidenced.

Preparation is in the isolated checkout under `build/literal-call-worktree`.
Its initialization preparation, mathematical source/uniqueness proofs,
Flat/DAE/Solve data correspondence, and shared C write/frame/behavior proofs
have built. They are not production support yet; actual adapter/artifact
composition and per-IR provenance propagation remain open. The compiler now
stores a required located parse and retains its completeness theorem; the
isolated initialization notices use those locations directly. They cannot
replace a missing declaration origin with a whole-file range.

The completed root gate in `build/located-provenance/full-gate.log` checks the
mandatory located frontend and unchanged production artifacts. It does not
cover these isolated initialization changes.
