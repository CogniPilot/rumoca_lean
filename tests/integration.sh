#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build
task_tmp=$(mktemp -d "$PWD/build/integration.XXXXXX")
trap 'task_status=$?; if [ "$task_status" -eq 0 ]; then rm -rf "$task_tmp"; else printf "Integration logs retained: %s\n" "$task_tmp" >&2; fi' EXIT
c_flags=(-std=c11 -O2 -Wall -Wextra -Werror -pedantic -fno-fast-math -ffp-contract=off)
packages/compiler/.lake/build/bin/rumoca examples/Integrator.mo -o "$task_tmp/model.c"
"${CC:-cc}" "${c_flags[@]}" "$task_tmp/model.c" examples/driver.c -lm -o "$task_tmp/simulate"
cat > "$task_tmp/expected.csv" <<'CSV'
t,x
0,0.5
1,1.5
2,2.5
3,3.5
CSV
"$task_tmp/simulate" 3 0.5 > "$task_tmp/actual.csv"
diff -u "$task_tmp/expected.csv" "$task_tmp/actual.csv"
test "$("$task_tmp/simulate" 3 -1.5 | tail -n 1)" = '3,1.5'
test "$("$task_tmp/simulate" 1 2.5e-1 | tail -n 1)" = '1,1.25'
test "$("$task_tmp/simulate" 1 9007199254740992 | tail -n 1)" = '1,9007199254740992'
"$task_tmp/simulate" 0 4.9406564584124654e-324 > /dev/null

# Exercise the emitted functions directly, separately from the CSV host.
cat > "$task_tmp/sample-check.c" <<'C'
#include <assert.h>
#include <float.h>
#include <fenv.h>
#include <math.h>
#include <stdint.h>
double rumoca_rhs(void);
double rumoca_step(double x);
double rumoca_sample(double x, uint64_t n);
int main(void) {
  assert(fesetround(FE_TONEAREST) == 0);
  assert(rumoca_rhs() == 1.0);
  assert(rumoca_step(0.5) == 1.5);
  assert(rumoca_sample(-1.5, 3) == 1.5);
  assert(rumoca_sample(0.25, 1000) == 1000.25);
  assert(rumoca_sample(DBL_MAX, 1) == DBL_MAX);
  assert(rumoca_sample(-DBL_MAX, 1) == -DBL_MAX);
  assert(rumoca_step(DBL_TRUE_MIN) == 1.0);
  assert(rumoca_step(-DBL_TRUE_MIN) == 1.0);
  assert(signbit(rumoca_sample(-0.0, 0)));
  assert(!signbit(rumoca_step(-1.0)));
  assert(rumoca_step(0x1p53) == 0x1p53);
  assert(rumoca_step(0x1.0000000000001p53) == 0x1.0000000000002p53);
  return 0;
}
C
"${CC:-cc}" "${c_flags[@]}" "$task_tmp/model.c" "$task_tmp/sample-check.c" -lm -o "$task_tmp/sample-check"
"$task_tmp/sample-check"
for args in '-1' '18446744073709551616' '0x10' '1 garbage' '1 nan' '1 inf' \
    '1 1e309' '1 1e-4000' '1 0x1p0' '1 1e' '1 .' '1 2 3'; do
  # Intentional splitting of fixed test vectors.
  if "$task_tmp/simulate" $args > /dev/null 2>&1; then
    printf 'unexpected host acceptance: %s\n' "$args" >&2; exit 1
  fi
done
printf '%s\n' 'model M Real x; equation der(y)=1; end M;' > "$task_tmp/bad.mo"
if packages/compiler/.lake/build/bin/rumoca "$task_tmp/bad.mo" -o "$task_tmp/bad.c" > /dev/null 2>&1; then
  echo 'invalid model reached C emission' >&2; exit 1
fi
test ! -e "$task_tmp/bad.c"

# Generic EBNF generation and table/source mutation controls run once in
# tests/lalr.sh, against the same engine used by production Modelica and GALEC.
echo 'Binary64 C execution and source rejection tests passed'
