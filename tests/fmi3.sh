#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build
compiler=packages/compiler/.lake/build/bin/rumoca
runner=packages/fmu-runner/.lake/build/bin/fmu-runner
task_tmp=$(mktemp -d "$PWD/build/fmi-tools.XXXXXX")
trap 'rm -rf "$task_tmp"' EXIT
"$compiler" examples/Integrator.mo -o build/Integrator.fmu
"$runner" validate build/Integrator.fmu
"$runner" info build/Integrator.fmu
for mode in me cs; do
  "$runner" simulate build/Integrator.fmu --mode "$mode" --start x 0.5 \
    --variable x --stop 3 --step 1 --csv "build/Integrator-$mode.csv"
done
# Reuse the unit profile under a distinct source name to exercise source linking.
sed 's/Integrator/SecondIntegrator/g' examples/Integrator.mo > build/SecondIntegrator.mo
"$compiler" build/SecondIntegrator.mo -o "$task_tmp/SecondIntegrator.fmu" > build/fmi-second-model.log
python3 tests/fmi3.py build/Integrator.fmu "$task_tmp/SecondIntegrator.fmu"
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
# A new extraction directory must reuse the proof of identical bytes, retaining
# the original Modelica identity. No-build fails if certification would run.
python - build/Integrator.fmu "$task_tmp/changed build" <<'PY'
from zipfile import ZipFile
import sys
with ZipFile(sys.argv[1]) as archive:
    archive.extractall(sys.argv[2])
PY
lake run verify-artifact --check-only fmi3 "$task_tmp/changed build" examples/Integrator.mo \
  > "$task_tmp/cached-fmi3.log"
bash scripts/audit-lean.sh "$task_tmp/cached-fmi3.log"
# A missing declared dependency must fail the actual-file contract before the
# native build. Keep this as one mutation of the existing packaged unit model.
python - build/Integrator.fmu "$task_tmp/changed build" <<'PY'
from pathlib import Path
from zipfile import ZipFile
import sys
root = Path(sys.argv[2])
with ZipFile(sys.argv[1]) as archive:
    archive.extractall(root)
path = root / 'sources/buildDescription.xml'
text = path.read_text()
changed = text.replace('<Library name="m" external="true"/>', '')
assert changed != text
path.write_text(changed)
PY
if lake run verify-artifact fmi3 "$task_tmp/changed build" examples/Integrator.mo > build/fmi-build-metadata-rejection.log 2>&1; then
  echo 'FMI source-build certificate accepted a missing dependency' >&2; exit 1
fi
rg -q 'actual FMI build description differs from the required source-build profile' \
  build/fmi-build-metadata-rejection.log
# The advertised identifier must also agree with the actual source API prefix.
python - build/Integrator.fmu "$task_tmp/changed build" <<'PY'
from pathlib import Path
from zipfile import ZipFile
import sys
root = Path(sys.argv[2])
with ZipFile(sys.argv[1]) as archive:
    archive.extractall(root)
path = root / 'sources/fmi3.c'
text = path.read_text()
changed = text.replace('#define FMI3_FUNCTION_PREFIX Rumoca_Integrator_',
                       '#define FMI3_FUNCTION_PREFIX Wrong_Integrator_', 1)
assert changed != text
path.write_text(changed)
PY
if lake run verify-artifact fmi3 "$task_tmp/changed build" examples/Integrator.mo > build/fmi-source-prefix-rejection.log 2>&1; then
  echo 'FMI source-build certificate accepted a mismatched API prefix' >&2; exit 1
fi
rg -q 'actual FMI source prefix or private-kernel inclusion differs from its model identifier' \
  build/fmi-source-prefix-rejection.log
# Preserve the numerical kernel and API prefix while changing the reset body.
# The complete adapter contract must reject the independently read file.
python - build/Integrator.fmu "$task_tmp/changed build" <<'PY'
from pathlib import Path
from zipfile import ZipFile
import sys
root = Path(sys.argv[2])
with ZipFile(sys.argv[1]) as archive:
    archive.extractall(root)
path = root / 'sources/fmi3.c'
text = path.read_text()
start = text.index('fmi3Status fmi3Reset(')
stop = text.index('\n}\n\n', start) + 4
body = text[start:stop]
changed = body.replace('((double)0)', '((double)2)', 1)
assert changed != body
path.write_text(text[:start] + changed + text[stop:])
PY
if lake run verify-artifact fmi3 "$task_tmp/changed build" examples/Integrator.mo > build/fmi-reset-body-rejection.log 2>&1; then
  echo 'FMI adapter certificate accepted an altered reset value' >&2; exit 1
fi
rg -q 'actual FMI adapter differs from the complete prepared function list' \
  build/fmi-reset-body-rejection.log
# A native build failure after the kernel check must preserve the old archive.
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
sha256sum build/Integrator.fmu
echo "FMU archive, independent ME/CS importer, ABI, runner and failure checks passed"
