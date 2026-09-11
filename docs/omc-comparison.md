# Side-by-side comparison with OpenModelica

Run from the repository root:

```sh
nix develop .#comparison --command lake run compare-omc
```

This compiles the existing `examples/Integrator.mo` through Rumoca Lean's normal
FMU publication path, including its actual-file kernel check. It compiles the
**same source bytes** with OpenModelica, then compares OMC's native simulation
with both Model Exchange and Co-Simulation from the generated FMI 3 archive.
The harness also checks that the FMU embeds those exact source bytes. Model and
state names come from the compiler's metadata; the harness contains no Modelica
parser or lowering logic.

The optional Nix `comparison` shell adds the same pinned OpenModelica revision as
Rust Rumoca: `a96aa1a682c463b0fd2d285b486c09a8b7fe496d`. The ordinary development
and verification shells do not depend on the OMC package. Lake builds only the
compiler/runner prerequisites and reuses their normal caches. OMC comparison
is opt-in and separate from the required `lake test` proof/artifact gate.
No Rust compiler build or MSL download is required. An existing OMC installation
can also be selected with `--omc /path/to/omc` inside the verification shell.

The output prints a fresh directory under `build/omc-comparison/run-*/` containing:

- `report.md`: side-by-side values, maximum error, RMSE and phase timings.
- `report.json`: settings, commands, tool versions/paths, source/artifact/tool
  hashes, grammar/toolchain identity, per-model status and structured metrics.
- Per-model `Source.mo`, `model.fmu`, `omc/build.mos`, OMC build products and
  stdout/stderr logs for every build/simulation phase.
- Original OMC and ME/CS CSV traces, plus `comparison.csv` with aligned values
  and signed differences. Nothing is interpolated or silently dropped.

Run several **already admitted** test models, or change the host-selected
initial value and number of unit steps:

```sh
lake run compare-omc examples/Integrator.mo path/to/AnotherUnitModel.mo
lake run compare-omc --initial 0 --steps 10
lake run compare-omc --help
```

Production currently admits one unmodified `Real` with `der(state)=1`. This
command does not enable the driven/array/AD development profiles. Unsupported
models fail comparison when the real compiler rejects them; they are not
silently skipped. All requested models get a status and either interface failing
makes the command exit unsuccessfully. Each invocation uses fresh artifact
paths, so old traces cannot hide a failed build. A per-phase timeout terminates
the process group, including native build/simulation descendants.

## Numerical and initialization policy

Default settings are initial state `0.5`, start time `0`, three unit steps and
samples at exactly `0, 1, 2, 3`. OMC uses Euler; ME uses the existing Lean runner
around FMPy's Euler solver; CS uses the FMU's embedded unit-step solver. The
comparison requires every expected sample, a finite value and an exact initial
state match. Missing columns, malformed rows, duplicate/out-of-order times,
truncated traces and non-finite samples fail; there is no event deduplication,
interpolation, overlap-only comparison or extrapolation in this tiny profile.

OMC receives `buildModel` settings with `method="euler"`, the explicit interval
count and tolerance `1e-12`, then a runtime `-override=state=value` and
`-noEventEmit`. These are documented in the official
[scripting API](https://openmodelica.org/doc/OpenModelicaUsersGuide/latest/scripting_api.html#buildmodel)
and [simulation flags](https://openmodelica.org/doc/OpenModelicaUsersGuide/latest/simulationflags.html).
OMC's initialization equations remain enabled. FMI receives the same start
value through the runner. For the current source, OMC warns that initialization
is unspecified; this warning is retained in the report and raw build log. The
comparison fixes a host experiment and verifies its first sample. It does not
resolve the source/FMI/eFMI initialization-policy finding SR08/S01.

For each remaining value, require
`abs(Lean - OMC) <= 1e-12 + 1e-12 * abs(OMC)`.
The report gives the maximum absolute error, maximum error divided by that bound
and RMSE. These acceptance tolerances are separate from a solver's error-control
settings. For the default integrator, all four samples agree exactly:

| Time | OMC | Lean ME | Lean CS |
| ---: | ---: | ---: | ---: |
| 0 | 0.5 | 0.5 | 0.5 |
| 1 | 1.5 | 1.5 | 1.5 |
| 2 | 2.5 | 2.5 | 2.5 |
| 3 | 3.5 | 3.5 | 3.5 |

This was exercised with the pinned OMC build reporting `a96aa1a-cmake`, the
freshly generated unit FMU and both native FMPy interfaces. It is independent integration
evidence at the external tool boundary, **not a semantic proof, full standards
conformance, MSL support or a replacement for formal verification**.

## Relationship to Rust Rumoca and the performance audit

The reference is the inspected Rust Rumoca `rumoca-test-msl` working tree
(HEAD `ab26a3984fd5bc5cd838b9b7e5619045f391f49f`, with local changes), specifically
`msl_tools/omc_simulation_reference.rs`, its session/reference workers and
`msl_tools/plot_compare.rs`. We reuse the workflow ideas: explicit reference
identity, preserved raw traces, per-model failure reporting, numerical deviation
metrics and separate build/run timings. The current Lean subset needs a small
batch script, not its persistent MSL session pool, retry cache or general trace
resampling policy. Those should grow only with the verified language profiles.

Lean's build timing includes kernel checking of the actual staged sources,
native C compilation and FMU packaging; OMC's includes Modelica translation and
native compilation. Simulation process time includes host startup and CSV I/O.
These values are useful phase observations, **not an apples-to-apples compiler
speed ratio**. Native frontend allocation/throughput evidence and outstanding
scaling work are in the [performance audit](../dev/performance-audit.md).

Validation for this addition: the default comparison passed with zero error
in both interfaces; a batch containing an unsupported driven model and a
renamed unit model correctly returned failure while reporting the unit model's
exact agreement. Malformed/mismatched CSV and failed/timed-out child controls
also passed. The required `nix develop .#verification --command lake test`
completed successfully in `build/omc-comparison-full-gate.log`. These boundary
checks introduce no new semantic claims or language cases.
