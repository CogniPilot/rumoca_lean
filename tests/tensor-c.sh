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
cp build/tensor-c/initial.c build/tensor-c/derivative.c build/tensor-c/corrupt-ivp/
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
