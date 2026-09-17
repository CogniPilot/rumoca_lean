#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build/tensor-c

lake env lean --run packages/backend-c/Tests/EmitTensor.lean build/tensor-c
for operation in add mul fill diagonal; do
  cat > "build/tensor-c/Check-$operation.lean" <<EOF
import RumocaC.TensorArtifactCheck
verify_tensor_helper "build/tensor-c/$operation.c" as $operation
EOF
  if ! lake env lean "build/tensor-c/Check-$operation.lean" > "build/tensor-c/$operation-contract.log" 2>&1; then
    cat "build/tensor-c/$operation-contract.log" >&2
    exit 1
  fi
done

cat > build/tensor-c/Check-ivp.lean <<'LEAN'
import TensorCChecks.ArtifactCheck
verify_tensor_ivp "build/tensor-c"
LEAN
if ! lake env lean build/tensor-c/Check-ivp.lean > build/tensor-c/ivp-contract.log 2>&1; then
  cat build/tensor-c/ivp-contract.log >&2
  exit 1
fi

# The checker reads the complete actual file, including the loop bound.
sed 's/k < count/k <= count/' build/tensor-c/mul.c > build/tensor-c/corrupt.c
cat > build/tensor-c/Reject.lean <<'LEAN'
import RumocaC.TensorArtifactCheck
verify_tensor_helper "build/tensor-c/corrupt.c" as mul
LEAN
if lake env lean build/tensor-c/Reject.lean > build/tensor-c/rejection.log 2>&1; then
  echo 'corrupted tensor loop passed its actual-file contract' >&2
  exit 1
fi
rg -q 'actual tensor C file differs' build/tensor-c/rejection.log

# Change one operation in the complete IVP; other members remain valid.
mkdir -p build/tensor-c/corrupt-ivp
cp build/tensor-c/initial.c build/tensor-c/derivative.c build/tensor-c/jacobian-diag.c build/tensor-c/corrupt-ivp/
sed 's/rumoca_tensor_add(left, right/rumoca_tensor_mul(left, right/' \
  build/tensor-c/jacobian.c > build/tensor-c/corrupt-ivp/jacobian.c
cat > build/tensor-c/Reject-ivp.lean <<'LEAN'
import TensorCChecks.ArtifactCheck
verify_tensor_ivp "build/tensor-c/corrupt-ivp"
LEAN
if lake env lean build/tensor-c/Reject-ivp.lean > build/tensor-c/ivp-rejection.log 2>&1; then
  echo 'corrupted tensor IVP passed its actual-file contract' >&2
  exit 1
fi
rg -q 'actual tensor IVP differs' build/tensor-c/ivp-rejection.log

# Header preprocessing, native C compilation and hardware remain boundaries.
"${CC:-cc}" -std=c11 -O2 -Wall -Wextra -Werror -pedantic -fno-fast-math -ffp-contract=off \
  -Wno-unused-parameter -include packages/backend-c/Tests/tensor-native.h \
  build/tensor-c/add.c build/tensor-c/mul.c build/tensor-c/fill.c build/tensor-c/diagonal.c \
  build/tensor-c/initial.c build/tensor-c/derivative.c build/tensor-c/jacobian.c \
  build/tensor-c/jacobian-diag.c \
  packages/backend-c/Tests/tensor-native.c -lm -o build/tensor-c/native
build/tensor-c/native
echo 'Tensor C actual-file contracts, mutation rejection and native boundary check passed'

# --- Tensor FMI 3 adapter standalone-object boundary check ---
# The compiler regression executable renders the development tensor adapter to
# build/tensor-fmi/adapter.c. This step confirms that a C11 compiler, using the
# vendored FMI 3 headers, compiles the whole adapter to a standalone object with
# zero diagnostics under the strict flags below: every emitted function carries
# the pinned FMI prototype for its name (parameters a body ignores are unused, so
# -Wno-unused-parameter is kept), each array member `double name[N]` stages its
# element pointer `&(m->name[0])` (type `double *`) to match the copy locals and
# the `rumoca_rhs` kernel prototype
# `void rumoca_rhs(const double *, const double *, double *, size_t)`, the setter
# copy local carries the source qualifier (`const double *`), and the reused
# Model Exchange event/discrete bodies address record members the tensor instance
# record declares. Header preprocessing, native compilation and hardware remain
# boundaries outside the authored C semantics; this step asserts only that the
# rendered adapter is a well-formed C11 translation unit.
adapter=build/tensor-fmi/adapter.c
if [ ! -f "$adapter" ]; then
  packages/compiler/.lake/build/bin/tests
fi
# The adapter includes "model.c" (empty here) and declares the tensor kernel
# prototype itself, so an object-only compile needs no kernel definition;
# rumoca_rhs stays an undefined extern.
: > build/tensor-fmi/model.c
"${CC:-cc}" -std=c11 -O2 -Wall -Wextra -Werror -pedantic -fno-fast-math -ffp-contract=off \
  -Wno-unused-parameter -I packages/backend-fmi3/vendor/fmi3 -I build/tensor-fmi \
  -c "$adapter" -o build/tensor-fmi/adapter.o \
  > build/tensor-fmi/adapter-cc.log 2>&1
status=$?
# Fail on any compiler error or warning, not only a specific diagnostic pattern:
# a non-zero exit (errors, or warnings promoted by -Werror) or any residual
# compiler output both reject the adapter.
if [ "$status" -ne 0 ] || [ -s build/tensor-fmi/adapter-cc.log ]; then
  echo 'tensor adapter did not compile cleanly as a standalone object' >&2
  cat build/tensor-fmi/adapter-cc.log >&2
  exit 1
fi
echo 'Tensor FMI 3 adapter standalone-object boundary check passed'

# --- Development tensor FMU boundary run (NOT a production FMU) ---
# Assemble a development FMU for the TensorSquare kernel from the already-produced
# certified pieces and drive it through FMPy in Model Exchange and Co-Simulation.
# This is a development artifact only: unlike the scalar production path (tests/fmi3.sh),
# the tensor FMU carries no source-to-archive production certificate. Native
# compilation, ZIP transport and the FMPy importer are boundaries outside the proof
# model. The pieces:
#   sources/fmi3.c            = the retained, contract-checked tensor adapter (adapter.c)
#   sources/model.c           = the certified tensor kernel C bodies (build/tensor-c/*.c),
#                               in dependency order, with <stddef.h> prepended so size_t is
#                               in scope at the adapter's `#include "model.c"`
#   modelDescription.xml      = the checked TensorMetadata fixture bytes (from the tests exe)
#   sources/buildDescription.xml = the build recipe mirroring the scalar one (from the tests exe)
# The shared library is compiled with the same recipe flags the scalar FMU build uses
# (RumocaFMI3.Build.recipe) plus -fPIC -shared -DFMI3_OVERRIDE_FUNCTION_PREFIX.
md=build/tensor-fmi/modelDescription.xml
if [ ! -f "$adapter" ] || [ ! -f "$md" ] || [ ! -f build/tensor-fmi/buildDescription.xml ]; then
  packages/compiler/.lake/build/bin/tests
fi
fmu_root=build/tensor-fmi/fmu
rm -rf "$fmu_root"
case "$(uname -m)" in
  x86_64) platform=x86_64-linux ;;
  aarch64|arm64) platform=aarch64-linux ;;
  *) echo "unsupported host arch for the development tensor FMU: $(uname -m)" >&2; exit 1 ;;
esac
mkdir -p "$fmu_root/sources" "$fmu_root/binaries/$platform" "$fmu_root/documentation"
{ echo '#include <stddef.h>'
  cat build/tensor-c/fill.c build/tensor-c/add.c build/tensor-c/mul.c build/tensor-c/diagonal.c \
      build/tensor-c/initial.c build/tensor-c/derivative.c build/tensor-c/jacobian.c \
      build/tensor-c/jacobian-diag.c
} > "$fmu_root/sources/model.c"
cp "$adapter" "$fmu_root/sources/fmi3.c"
cp "$md" "$fmu_root/modelDescription.xml"
cp build/tensor-fmi/buildDescription.xml "$fmu_root/sources/buildDescription.xml"
"${CC:-gcc}" -std=c11 -O2 -Wall -Wextra -Werror -Wno-unused-parameter -pedantic \
  -fno-fast-math -ffp-contract=off -frounding-math -fPIC -shared -DFMI3_OVERRIDE_FUNCTION_PREFIX \
  -I packages/backend-fmi3/vendor/fmi3 "$fmu_root/sources/fmi3.c" -lm \
  -o "$fmu_root/binaries/$platform/Rumoca_TensorSquare.so" \
  > build/tensor-fmi/fmu-cc.log 2>&1
if [ -s build/tensor-fmi/fmu-cc.log ]; then
  echo 'development tensor FMU shared library did not compile cleanly' >&2
  cat build/tensor-fmi/fmu-cc.log >&2
  exit 1
fi
dev_fmu=build/tensor-fmi/TensorSquare-dev.fmu
dev_fmu_abs="$PWD/$dev_fmu"
rm -f "$dev_fmu"
( cd "$fmu_root" && zip -q -X -0 -r "$dev_fmu_abs" modelDescription.xml sources binaries documentation )
fmpy validate "$dev_fmu" > build/tensor-fmi/fmu-validate.log 2>&1
# Drive the actual adapter in ME and CS. The importer instantiates with the token the
# model description declares: the tensor factory now validates the tensor model
# description's instantiationToken "lean-rumoca-tensor-v1:TensorSquare"
# (TensorMetadata.token), and TensorAdapter.Contract proves the factory's expected
# token equals that attribute (TensorMetadata.token_attribute).
python3 - "$dev_fmu" > build/tensor-fmi/fmu-run.log 2>&1 <<'PY'
import sys, ctypes
from fmpy import read_model_description, extract
from fmpy.fmi3 import FMU3Model, FMU3Slave
from fmpy.fmi1 import FMICallException
path = sys.argv[1]
md = read_model_description(path)
vr = {v.name: v.valueReference for v in md.modelVariables}
udir = extract(path)
TOKEN = "lean-rumoca-tensor-v1:TensorSquare"
def arr(vals): return (ctypes.c_double * len(vals))(*vals)
def approx(a, b): return all(abs(x - y) < 1e-12 for x, y in zip(a, b))

# Model Exchange: der(x) = u .* u and an ME-driven explicit Euler trajectory.
me = FMU3Model(guid=TOKEN, modelIdentifier=md.modelExchange.modelIdentifier,
               unzipDirectory=udir, instanceName="me")
me.instantiate(loggingOn=False)
me.enterInitializationMode(startTime=0.0)
me.setFloat64([vr["u"]], [1.0, 2.0])
me.exitInitializationMode()
me.enterContinuousTimeMode()
me.setContinuousStates(arr([0.0, 0.0]), 2)
der = (ctypes.c_double * 2)()
me.getContinuousStateDerivatives(der, 2)
me_der = list(der)
print("ME der(x) with u=(1,2) =", me_der)
assert approx(me_der, [1.0, 4.0]), "ME der(x) != (1, 4)"
x = [0.0, 0.0]
for _ in range(3):
    me.setContinuousStates(arr(x), 2)
    d = (ctypes.c_double * 2)()
    me.getContinuousStateDerivatives(d, 2)
    x = [x[i] + 1.0 * d[i] for i in range(2)]
print("ME-driven Euler x@t=3 =", x)
assert approx(x, [3.0, 12.0]), "ME-driven Euler x@t=3 != (3, 12)"
me_J = list(me.getFloat64([vr["J"]], 4))
print("ME J =", me_J)
# J reads the zero-initialized output region: no adapter lifecycle body computes the
# Jacobian (the diagonal kernel rumoca_square_jacobian is emitted but wired to no FMI
# entry), so the output tensor stays at its file-scope zero initialization.
assert approx(me_J, [0.0, 0.0, 0.0, 0.0]), "ME J != (0, 0, 0, 0)"
me.terminate(); me.freeInstance()

# Co-Simulation: the tensor exitInitializationMode is now kind-aware and enters Step
# mode for a Co-Simulation instance (TensorLifecycleModes.Phase.afterKind, matching the
# scalar InitializationExit body), so fmi3DoStep is accepted. Three unit steps with the
# constant input u = (1, 2) advance x by u .* u = (1, 4) each step, reaching x = (3, 12)
# at t = 3 (TensorLifecycleHistory.lifecycle_cs_step threads the Step-mode exit into an
# accepted step).
cs = FMU3Slave(guid=TOKEN, modelIdentifier=md.coSimulation.modelIdentifier,
               unzipDirectory=udir, instanceName="cs")
cs.instantiate(loggingOn=False)
cs.enterInitializationMode(startTime=0.0)
cs.setFloat64([vr["u"]], [1.0, 2.0])
cs.exitInitializationMode()
t = 0.0
for _ in range(3):
    cs.doStep(t, 1.0)
    t += 1.0
cs_x = list(cs.getFloat64([vr["x"]], 2))
print("CS x@t=3 =", cs_x)
assert approx(cs_x, [3.0, 12.0]), "CS x@t=3 != (3, 12)"
cs_J = list(cs.getFloat64([vr["J"]], 4))
print("CS J =", cs_J)
# J still reads the zero-initialized output region: wiring the emitted diagonal kernel
# rumoca_square_jacobian into an FMI output is the remaining open tensor item.
assert approx(cs_J, [0.0, 0.0, 0.0, 0.0]), "CS J != (0, 0, 0, 0)"
cs.terminate(); cs.freeInstance()
print("DEV TENSOR FMU BOUNDARY RUN OK")
PY
if ! grep -q 'DEV TENSOR FMU BOUNDARY RUN OK' build/tensor-fmi/fmu-run.log; then
  echo 'development tensor FMU boundary run failed' >&2
  cat build/tensor-fmi/fmu-run.log >&2
  exit 1
fi
cat build/tensor-fmi/fmu-run.log
echo 'Development tensor FMU boundary run passed (ME and CS x@t=3 = (3, 12); J = zeros is the remaining open item)'
