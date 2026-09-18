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

# --- Development tensor eFMI Production Code and manifest boundary check ---
# The compiler regression executable renders the development tensor eFMI
# Production Code (build/tensor-efmi/ProductionCode.c) and the Algorithm/
# Production/container manifests (build/tensor-efmi/*.xml) for the prepared square
# kernel. This is a development product only: the default CLI still rejects the
# array profile (asserted in the Lean regression executable and tests/fmi3.sh).
# This step validates the manifests against the vendored eFMI XSDs with the same
# lxml check tests/efmi-production.sh uses, confirms the code-file checksums and
# the origin reference correlate with the emitted bytes, that every array variable
# carries its declared dimensions, and that the Production C is a well-formed C11
# translation unit. XSD validation and native compilation are boundaries outside
# the proof model.
efmi_root=build/tensor-efmi
if [ ! -f "$efmi_root/ProductionCode.xml" ] || [ ! -f "$efmi_root/ProductionCode.c" ]; then
  packages/compiler/.lake/build/bin/tests
fi
(cd packages/backend-efmi/vendor/efmi && sha256sum --quiet -c SHA256SUMS)
python3 - "$efmi_root" <<'PY'
from pathlib import Path
from hashlib import sha1
from lxml import etree
import sys
root = Path(sys.argv[1])
vendor = Path('packages/backend-efmi/vendor/efmi/schemas')
for name, schema in [
    ('AlgorithmCode.xml', 'AlgorithmCode/efmiAlgorithmCodeManifest.xsd'),
    ('ProductionCode.xml', 'ProductionCode/efmiProductionCodeManifest.xsd'),
    ('content.xml', 'efmiContainerManifest.xsd'),
]:
    etree.XMLSchema(etree.parse(str(vendor / schema))).assertValid(etree.parse(str(root / name)))
algorithm = etree.parse(str(root / 'AlgorithmCode.xml'))
production = etree.parse(str(root / 'ProductionCode.xml'))
assert algorithm.find("Files/File[@role='Code']").get('checksum') == \
    sha1((root / 'AlgorithmCode.alg').read_bytes()).hexdigest()
assert production.find("Files/File[@role='Code']").get('checksum') == \
    sha1((root / 'ProductionCode.c').read_bytes()).hexdigest()
assert production.find('ManifestReferences/ManifestReference').get('checksum') == \
    sha1((root / 'AlgorithmCode.xml').read_bytes()).hexdigest()
dims = {v.get('name'): [d.get('size') for d in v.findall('Dimensions/Dimension')]
        for v in algorithm.findall('Variables/RealVariable')}
assert dims['u'] == ['2'] and dims['x'] == ['2'] and dims['J'] == ['2', '2'], dims
components = {c.get('name'): [d.get('size') for d in c.findall('Dimensions/Dimension')]
             for c in production.findall("CodeContainer/CodeFiles/CodeFile/Typedefs/Typedef[@id='TD_Model']/Components/Component")}
assert components['u'] == ['2'] and components['x'] == ['2'] and components['J'] == ['2', '2'], components
print('tensor eFMI manifests: XSD-valid, checksum-correlated, array dimensions declared')
PY
"${CC:-cc}" -std=c11 -O2 -Wall -Wextra -Werror -pedantic -fno-fast-math -ffp-contract=off \
  -Wno-unused-parameter -c "$efmi_root/ProductionCode.c" -o "$efmi_root/ProductionCode.o"
echo 'Development tensor eFMI Production Code and manifest boundary check passed'

# --- Tensor eFMI manifest actual-byte certificate ---
# The tensor Algorithm/Production/container manifests certify against actual bytes
# through the fixed `tensor-efmi-directory` checker: the XML serialization and
# validity of all three documents and the SHA-1 checksum graph binding each code
# file and each hashed manifest to the correlated tensor code products, composed
# into the frozen tensor manifest contract (`source_to_manifests`). The tensor
# Production Code manifest is 7.4 KB; the structural, masked-word SHA-1 schedule
# keeps its checksum certificate within the kernel's budget. This is a directory
# certificate; complete `.efmu` archive admission is a separate, still-open layer.
manifest_root="$efmi_root/directory"
rm -rf "$manifest_root"
mkdir -p "$manifest_root/AlgorithmCode" "$manifest_root/ProductionCode"
cp "$efmi_root/AlgorithmCode.alg" "$manifest_root/AlgorithmCode/model.alg"
cp "$efmi_root/AlgorithmCode.xml" "$manifest_root/AlgorithmCode/manifest.xml"
cp "$efmi_root/ProductionCode.c" "$manifest_root/ProductionCode/production.c"
cp "$efmi_root/ProductionCode.xml" "$manifest_root/ProductionCode/manifest.xml"
cp "$efmi_root/content.xml" "$manifest_root/__content.xml"
lake run verify-artifact tensor-efmi-directory examples/development/TensorSquare.mo "$manifest_root" \
  packages/modelica-parser/grammar/Modelica.ebnf packages/galec-parser/grammar/GALEC.ebnf \
  > build/tensor-efmi-manifest.log
bash scripts/audit-lean.sh build/tensor-efmi-manifest.log
rg 'Rumoca.CheckedTensorEFMIFiles.source_to_manifests depends on axioms:' build/tensor-efmi-manifest.log
rm -rf "$manifest_root"
echo 'Tensor eFMI manifest actual-byte certificate passed'

# --- Tensor eFMU archive actual-byte certificate ---
# Publish the complete tensor eFMU through the default CLI under the fixed
# SOURCE_DATE_EPOCH. The publication gate is the fixed tensor-efmi-archive checker
# (lake run verify-artifact tensor-efmi-archive), which composes the three manifest
# documents' XML serialization and validity and the SHA-1 checksum graph with the
# stored-ZIP transport over all archive members into the axiom-audited
# Rumoca.CheckedTensorEFMIFiles.source_to_archive contract. This certificate peaks
# at parity with the scalar eFMU archive certificate (tests/efmi-production.sh),
# dominated by the composed manifest and stored-ZIP payload over all members, not
# by any single whole-document step. ZIP transport and file I/O are boundaries
# outside the proof model. The fixed epoch and source identity keep the certificate
# reusable across this script and tests/efmi-production.sh.
tensor_efmu=build/tensor-efmi/model.efmu
rm -f "$tensor_efmu"
SOURCE_DATE_EPOCH=1700000000 packages/compiler/.lake/build/bin/rumoca \
  examples/development/TensorSquare.mo -o "$tensor_efmu" > build/tensor-efmi-archive.log
bash scripts/audit-lean.sh build/tensor-efmi-archive.log
rg 'Rumoca.CheckedTensorEFMIFiles.source_to_archive depends on axioms:' build/tensor-efmi-archive.log
echo 'Tensor eFMU archive actual-byte certificate passed'

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
# The derivative getter now runs the prepared square-Jacobian diagonal entry
# rumoca_square_jacobian_diag after rumoca_rhs, so J holds the dense Jacobian
# diag(2*u) = diag(2, 4), row-major (2, 0, 0, 4), for u = (1, 2).
assert approx(me_J, [2.0, 0.0, 0.0, 4.0]), "ME J != (2, 0, 0, 4)"
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
# The accepted fmi3DoStep now runs the prepared square-Jacobian diagonal entry
# rumoca_square_jacobian_diag once per accepted step, so J holds the dense Jacobian
# diag(2*u) = diag(2, 4), row-major (2, 0, 0, 4), for the constant input u = (1, 2).
assert approx(cs_J, [2.0, 0.0, 0.0, 4.0]), "CS J != (2, 0, 0, 4)"
cs.terminate(); cs.freeInstance()
print("DEV TENSOR FMU BOUNDARY RUN OK")
PY
if ! grep -q 'DEV TENSOR FMU BOUNDARY RUN OK' build/tensor-fmi/fmu-run.log; then
  echo 'development tensor FMU boundary run failed' >&2
  cat build/tensor-fmi/fmu-run.log >&2
  exit 1
fi
cat build/tensor-fmi/fmu-run.log
echo 'Development tensor FMU boundary run passed (ME and CS x@t=3 = (3, 12); ME and CS J = (2, 0, 0, 4))'

# --- Production-shaped development tensor FMU via compileTensor + writeSources ---
# Assemble the tensor FMU through the development command `tensor-fmu`, which runs
# compileTensor, the tensor writeSources, the fixed tensor source-build checker and
# the native archive step. This is a development command, not the default CLI path:
# the default compiler still rejects the array profile (asserted in tests/fmi3.sh and
# the Lean regression executable). Native compilation, ZIP transport and the FMPy
# importer remain boundaries outside the proof model.
tensor_compiler=packages/compiler/.lake/build/bin/tensor-fmu
prod_fmu=build/tensor-fmi/TensorSquare.fmu
"$tensor_compiler" examples/development/TensorSquare.mo "$prod_fmu"
# Re-verify the extracted sources through the cached `tensor-fmi3` certificate and
# require the certificate's axiom audit lines.
prod_root=build/tensor-fmi/prod-extracted
rm -rf "$prod_root"; mkdir -p "$prod_root"
python - "$prod_fmu" "$prod_root" <<'PY'
from zipfile import ZipFile
import sys
with ZipFile(sys.argv[1]) as archive:
    archive.extractall(sys.argv[2])
PY
lake run verify-artifact tensor-fmi3 "$prod_root" examples/development/TensorSquare.mo \
  > build/tensor-fmi/prod-cert.log
bash scripts/audit-lean.sh build/tensor-fmi/prod-cert.log
rg -q 'Rumoca.CheckedTensorFMI3Files.source_to_build depends on axioms' build/tensor-fmi/prod-cert.log
# Drive the production-shaped FMU in ME and CS exactly as the development boundary run does.
python3 - "$prod_fmu" > build/tensor-fmi/prod-run.log 2>&1 <<'PY'
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
if ! grep -q 'PROD TENSOR FMU BOUNDARY RUN OK' build/tensor-fmi/prod-run.log; then
  echo 'production-shaped tensor FMU boundary run failed' >&2
  cat build/tensor-fmi/prod-run.log >&2
  exit 1
fi
echo 'Production-shaped tensor FMU (compileTensor + writeSources + tensor-fmi3 certificate) boundary run passed'
