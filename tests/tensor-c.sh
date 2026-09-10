#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build/tensor-c

lake env lean --run packages/backend-c/Tests/EmitTensor.lean build/tensor-c
for operation in add mul; do
  cat > "build/tensor-c/Check-$operation.lean" <<EOF
import RumocaC.TensorArtifactCheck
verify_tensor_helper "build/tensor-c/$operation.c" as $operation
EOF
  if ! lake env lean "build/tensor-c/Check-$operation.lean" > "build/tensor-c/$operation-contract.log" 2>&1; then
    cat "build/tensor-c/$operation-contract.log" >&2
    exit 1
  fi
done

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

# Header preprocessing, native C compilation and hardware remain boundaries.
"${CC:-cc}" -std=c11 -O2 -Wall -Wextra -Werror -pedantic -fno-fast-math -ffp-contract=off \
  -include stddef.h build/tensor-c/add.c build/tensor-c/mul.c \
  packages/backend-c/Tests/tensor-native.c -lm -o build/tensor-c/native
build/tensor-c/native
echo 'Tensor C actual-file contracts, mutation rejection and native boundary check passed'
