#include <assert.h>
#include <float.h>
#include <fenv.h>
#include <math.h>
#include <stddef.h>
#include <stdint.h>

_Static_assert(FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024 &&
               DBL_MIN_EXP == -1021 && FLT_EVAL_METHOD == 0, "binary64 target required");

/* External linkage declarations for the emitted constant-rate kernel, used only
   by this native boundary check. The definitions come from the certified,
   separately compiled constant.c translation unit. */
void rumoca_constant_rhs(double *der);
void rumoca_constant_step(double *x);
void rumoca_constant_sample(double *x, size_t n);

/* One native boundary check complements the universal Lean proofs: the emitted
   constant-rate kernel writes the exactly rounded rates (2.5, -1) and advances
   the two states from zero to (7.5, -3) after three explicit Euler unit steps. */
int main(void) {
  assert(fesetround(FE_TONEAREST) == 0);

  double der[2] = {-1.0, -1.0};
  rumoca_constant_rhs(der);
  assert(der[0] == 2.5 && der[1] == -1.0);

  double x[2] = {0.0, 0.0};
  rumoca_constant_step(x);
  assert(x[0] == 2.5 && x[1] == -1.0);

  double y[2] = {0.0, 0.0};
  rumoca_constant_sample(y, 3);
  assert(y[0] == 7.5 && y[1] == -3.0);

  /* A zero-count sample leaves the state untouched. */
  double z[2] = {7.5, -3.0};
  rumoca_constant_sample(z, 0);
  assert(z[0] == 7.5 && z[1] == -3.0);

  return 0;
}
