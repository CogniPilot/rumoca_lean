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
# Native all-behavior matrix over every one of the 75 public functions: null
# handle, lifecycle rejection, argument rejection, discard, suppressed versus
# enabled logging, capability rejection and absent-typed empty/non-empty. This
# instantiates natively each behavior class the trust ledger otherwise records as
# proof-only (finding F6). The run fails on any status or callback that regresses
# from the proved behavior; recorded findings are printed but tolerated.
python3 tests/fmi3.py --matrix build/Integrator.fmu Integrator.fmu
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

# --- Production array/tensor profile via the default CLI ---
# The default `rumoca` CLI now admits the TensorSquare array profile to FMI 3 FMU
# output: unit sources follow the existing path unchanged, and an array-profile
# source is compiled with compileTensor and published through the tensor
# writeSources/archive path whose publication gate is the fixed `tensor-fmi3`
# source-build certificate. Complete tensor eFMU output is admitted separately
# (tests/efmi-production.sh); only tensor C emission on stdout stays rejected.
# Native compilation, ZIP transport and the FMPy importer remain boundaries outside
# the proof model, exactly as in the development tensor run (tests/tensor-c.sh).
prod_fmu=build/TensorSquare.fmu
"$compiler" examples/TensorSquare.mo -o "$prod_fmu"
"$runner" validate "$prod_fmu"
"$runner" info "$prod_fmu"
# Same native all-behavior matrix on the production tensor FMU (finding F2). It
# also surfaces finding F8: the tensor adapter's fmi3Reset does not restore the
# Instantiated state once initialization has run, so re-initialization is refused.
python3 tests/fmi3.py --matrix "$prod_fmu" TensorSquare.fmu
# Tensor eFMI export stays rejected with a clear diagnostic (the tensor eFMI path is
# not built) and must neither publish nor replace an FMU.
cp "$prod_fmu" "$task_tmp/tensor-preserved.fmu"
if "$compiler" examples/TensorSquare.mo -o "$task_tmp/tensor-preserved.efmu" > build/fmi-tensor-efmi.log 2>&1; then
  echo "compiler admitted tensor eFMI export" >&2; exit 1
fi
rg -q 'tensor eFMU archive export is not built' build/fmi-tensor-efmi.log
# Re-verify the extracted sources through the cached `tensor-fmi3` certificate with
# no build, requiring certificate reuse and the approved axiom audit lines.
tensor_root="$task_tmp/tensor-extracted"
rm -rf "$tensor_root"; mkdir -p "$tensor_root"
python - "$prod_fmu" "$tensor_root" <<'PY'
from zipfile import ZipFile
import sys
with ZipFile(sys.argv[1]) as archive:
    archive.extractall(sys.argv[2])
PY
lake run verify-artifact --check-only tensor-fmi3 "$tensor_root" examples/TensorSquare.mo \
  > "$task_tmp/cached-tensor-fmi3.log"
bash scripts/audit-lean.sh "$task_tmp/cached-tensor-fmi3.log"
rg -q 'Rumoca.CheckedTensorFMI3Files.source_to_build depends on axioms' \
  "$task_tmp/cached-tensor-fmi3.log"
# Mutation-rejection control on the tensor adapter (mirrors the scalar reset-body
# control): preserve the certified numerical kernel and API prefix while altering one
# byte of the reset body. The complete tensor adapter contract must reject the read
# file, and must not replace the previously valid FMU.
python - "$prod_fmu" "$task_tmp/tensor-changed" <<'PY'
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
changed = body.replace('dst[k] = 0;', 'dst[k] = 2;', 1)
assert changed != body
path.write_text(text[:start] + changed + text[stop:])
PY
if lake run verify-artifact tensor-fmi3 "$task_tmp/tensor-changed" examples/TensorSquare.mo > build/fmi-tensor-adapter-rejection.log 2>&1; then
  echo 'tensor adapter certificate accepted an altered reset value' >&2; exit 1
fi
rg -q 'actual tensor FMI adapter differs from the complete prepared function list' \
  build/fmi-tensor-adapter-rejection.log
# Drive the production FMU through FMPy in ME and CS with the tensor-c.sh assertions.
python3 - "$prod_fmu" > build/fmi-tensor-run.log 2>&1 <<'PY'
import sys, ctypes
from fmpy import read_model_description, extract
from fmpy.fmi3 import FMU3Model, FMU3Slave
path = sys.argv[1]
md = read_model_description(path)
vr = {v.name: v.valueReference for v in md.modelVariables}
udir = extract(path)
TOKEN = "lean-rumoca-tensor-v1:TensorSquare"
def arr(vals): return (ctypes.c_double * len(vals))(*vals)
def approx(a, b): return all(abs(x - y) < 1e-12 for x, y in zip(a, b))
me = FMU3Model(guid=TOKEN, modelIdentifier=md.modelExchange.modelIdentifier,
               unzipDirectory=udir, instanceName="me")
me.instantiate(loggingOn=False)
me.enterInitializationMode(startTime=0.0)
me.setFloat64([vr["u"]], [1.0, 2.0])
me.exitInitializationMode()
me.enterContinuousTimeMode()
x = [0.0, 0.0]
for _ in range(3):
    me.setContinuousStates(arr(x), 2)
    d = (ctypes.c_double * 2)()
    me.getContinuousStateDerivatives(d, 2)
    x = [x[i] + 1.0 * d[i] for i in range(2)]
assert approx(x, [3.0, 12.0]), "ME-driven Euler x@t=3 != (3, 12)"
me_J = list(me.getFloat64([vr["J"]], 4))
assert approx(me_J, [2.0, 0.0, 0.0, 4.0]), "ME J != (2, 0, 0, 4)"
me.terminate(); me.freeInstance()
cs = FMU3Slave(guid=TOKEN, modelIdentifier=md.coSimulation.modelIdentifier,
               unzipDirectory=udir, instanceName="cs")
cs.instantiate(loggingOn=False)
cs.enterInitializationMode(startTime=0.0)
cs.setFloat64([vr["u"]], [1.0, 2.0])
cs.exitInitializationMode()
t = 0.0
for _ in range(3):
    cs.doStep(t, 1.0); t += 1.0
assert approx(list(cs.getFloat64([vr["x"]], 2)), [3.0, 12.0]), "CS x@t=3 != (3, 12)"
assert approx(list(cs.getFloat64([vr["J"]], 4)), [2.0, 0.0, 0.0, 4.0]), "CS J != (2, 0, 0, 4)"
cs.terminate(); cs.freeInstance()
print("PROD TENSOR FMU BOUNDARY RUN OK")
PY
if ! grep -q 'PROD TENSOR FMU BOUNDARY RUN OK' build/fmi-tensor-run.log; then
  echo 'production tensor FMU boundary run failed' >&2
  cat build/fmi-tensor-run.log >&2
  exit 1
fi
echo "Production array/tensor FMU (default CLI admission, tensor-fmi3 certificate, ME/CS x@t=3=(3,12), J=(2,0,0,4)) checks passed"
