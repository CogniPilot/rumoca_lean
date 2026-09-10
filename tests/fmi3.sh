#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build
compiler=packages/compiler/.lake/build/bin/rumoca
runner=packages/fmu-runner/.lake/build/bin/fmu-runner
"$compiler" examples/Integrator.mo -o build/Integrator.fmu
"$runner" validate build/Integrator.fmu
"$runner" info build/Integrator.fmu
for mode in me cs; do
  "$runner" simulate build/Integrator.fmu --mode "$mode" --start x 0.5 \
    --variable x --stop 3 --step 1 --csv "build/Integrator-$mode.csv"
done
python3 tests/fmi3.py build/Integrator.fmu
python3 - <<'PY'
import csv
for mode in ['me', 'cs']:
    with open(f'build/Integrator-{mode}.csv') as stream:
        rows = list(csv.DictReader(stream))
    assert [(float(r['time']), float(r['x'])) for r in rows] == [(0, .5), (1, 1.5), (2, 2.5), (3, 3.5)]
PY
if "$runner" simulate build/Integrator.fmu --mode invalid > build/fmi-bad-mode.log 2>&1; then
  echo "runner accepted invalid mode" >&2; exit 1
fi
if "$runner" validate build/missing.fmu > build/fmi-missing.log 2>&1; then
  echo "runner accepted missing FMU" >&2; exit 1
fi
if "$runner" simulate build/Integrator.fmu --mode cs --step 0.5 --variable x > build/fmi-bad-step.log 2>&1; then
  echo "runner accepted discarded simulation" >&2; exit 1
fi
# An unsupported model must neither publish nor replace a previously valid FMU.
cp build/Integrator.fmu build/preserved.fmu
if "$compiler" examples/DrivenIntegrator.mo -o build/preserved.fmu > build/fmi-unsupported.log 2>&1; then
  echo "compiler admitted the unverified driven profile" >&2; exit 1
fi
cmp build/Integrator.fmu build/preserved.fmu
# A native build failure after the kernel check must preserve the old archive.
task_tmp=$(mktemp -d "$PWD/build/fmi-tools.XXXXXX")
trap 'rm -rf "$task_tmp"' EXIT
cat > "$task_tmp/gcc" <<'SH'
#!/usr/bin/env bash
echo 'deliberate native compiler failure' >&2
exit 91
SH
chmod +x "$task_tmp/gcc"
if PATH="$task_tmp:$PATH" "$compiler" examples/Integrator.mo -o build/preserved.fmu > build/fmi-build-failure.log 2>&1; then
  echo "FMU publication accepted a failed native build" >&2; exit 1
fi
rg -q 'deliberate native compiler failure' build/fmi-build-failure.log
cmp build/Integrator.fmu build/preserved.fmu
cp build/Integrator.fmu "$task_tmp/model with spaces.fmu"
"$runner" simulate "$task_tmp/model with spaces.fmu" --variable x --csv "$task_tmp/results with spaces.csv"
echo "FMU archive, independent ME/CS importer, ABI, runner and failure checks passed"
