#include <assert.h>
#include <float.h>
#include <fenv.h>
#include <math.h>
#include <stddef.h>
#include <stdint.h>

_Static_assert(sizeof(size_t) == 8, "authored tensor target uses 64-bit size_t");
_Static_assert(FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024 &&
               DBL_MIN_EXP == -1021 && FLT_EVAL_METHOD == 0, "binary64 target required");

void rumoca_tensor_add(const double *left, const double *right, double *out, size_t count);
void rumoca_tensor_mul(const double *left, const double *right, double *out, size_t count);

/* One native boundary check complements the universal Lean proofs. */
int main(void) {
  assert(fesetround(FE_TONEAREST) == 0);
  const double input[2] = {2.0, 3.0};
  double output[4] = {17.0, 0.0, 0.0, 19.0};
  rumoca_tensor_mul(input, input, output + 1, 2);
  assert(output[0] == 17.0 && output[1] == 4.0 && output[2] == 9.0 && output[3] == 19.0);
  rumoca_tensor_add(input, input, output + 1, 2);
  assert(output[0] == 17.0 && output[1] == 4.0 && output[2] == 6.0 && output[3] == 19.0);
  assert(input[0] == 2.0 && input[1] == 3.0);
  const double tiny = -DBL_TRUE_MIN, half = 0.5;
  rumoca_tensor_mul(&tiny, &half, output + 1, 1);
  assert(output[1] == 0.0 && signbit(output[1]));
  rumoca_tensor_add(NULL, NULL, NULL, 0);
  rumoca_tensor_mul(NULL, NULL, NULL, 0);
  return 0;
}
