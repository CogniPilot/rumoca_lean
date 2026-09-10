# FMU runner

A separate Lean CLI around [FMPy](https://github.com/CATIA-Systems/FMPy).
It has no compiler, parser, or mathlib dependency. FMPy supplies the importer,
schema validation, native library loading and the Model Exchange Euler solver.
These are tested host tools, outside the compiler's formal proof.

From the workspace root, inside `nix develop`:

```sh
lake build rumoca_fmu_runner
lake exe fmu-runner info build/Integrator.fmu
lake exe fmu-runner validate build/Integrator.fmu
lake exe fmu-runner simulate build/Integrator.fmu --mode cs \
  --variable x --start x 0.5 --stop 3 --step 1 --csv build/Integrator-cs.csv
lake exe fmu-runner simulate build/Integrator.fmu --mode me \
  --variable x --start x 0.5 --stop 3 --step 1 --csv build/Integrator-me.csv
```

The executable is `packages/fmu-runner/.lake/build/bin/fmu-runner`.
Defaults are CS, start time 0, stop time 3 and step 1. Repeat `--variable`
and `--start NAME VALUE` as needed. Without `--variable`, FMPy records FMI
outputs; the current unit model's `x` is local, so select it explicitly.
`--start-time` controls simulation time; `--start` sets a variable's start.
Use `--timeout SECONDS` to bound FMPy's simulation loop. This is not a process
sandbox or a hard timeout for a hung native FMI call.

All simulation calls validate metadata. Importer errors and discarded steps
produce a nonzero exit status. Paths and options are passed as process
arguments, without shell evaluation. Numerical argument checks are delegated
to FMPy and the FMU. The ME solver's arbitrary-step arithmetic is not covered
by Rumoca's unit-step numerical theorem.

The pinned Nix shell includes FMPy on x86_64 Linux. On other hosts install
FMPy with a compatible platform runtime and put `fmpy` on PATH. The runner
can import other supported FMUs; each FMU's interfaces, platform binaries and
capabilities constrain the simulation options. Current automated interoperability
tests exercise Rumoca's unit FMU in both modes.
