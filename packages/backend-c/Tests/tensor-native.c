#include <assert.h>
#include <float.h>
#include <fenv.h>
#include <math.h>
#include <stddef.h>
#include <stdint.h>
#include "tensor-native.h"

_Static_assert(sizeof(size_t) == 8, "authored tensor target uses 64-bit size_t");
_Static_assert(FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024 &&
               DBL_MIN_EXP == -1021 && FLT_EVAL_METHOD == 0, "binary64 target required");

/* One native boundary check complements the universal Lean proofs. */
int main(void) {
  assert(fesetround(FE_TONEAREST) == 0);
  const double input[2] = {2.0, 3.0};
  double output[4] = {17.0, 0.0, 0.0, 19.0};
  rumoca_tensor_fill(-0.0, output + 1, 2);
  assert(output[0] == 17.0 && output[1] == 0.0 && signbit(output[1]) &&
         output[2] == 0.0 && signbit(output[2]) && output[3] == 19.0);
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
  /* Initialize and evaluate the same prepared IVP before its observation. */
  double state[4] = {17.0, -1.0, -1.0, 19.0};
  rumoca_initialize(state + 1, 2);
  assert(state[0] == 17.0 && state[1] == 0.0 && !signbit(state[1]) &&
         state[2] == 0.0 && !signbit(state[2]) && state[3] == 19.0);
  rumoca_rhs(state + 1, input, output + 1, 2);
  assert(output[0] == 17.0 && output[1] == 4.0 && output[2] == 9.0 && output[3] == 19.0);
  /* The actual forward-AD program and its explicit diagonal output. */
  double scratch[5][2];
  double jacobian[6] = {17.0, -1.0, -1.0, -1.0, -1.0, 19.0};
  rumoca_square_jacobian(state + 1, input, scratch[0], scratch[1],
      scratch[2], scratch[3], scratch[4], output + 1, 2, jacobian + 1, 4);
  assert(output[0] == 17.0 && output[1] == 4.0 && output[2] == 6.0 && output[3] == 19.0);
  assert(scratch[2][0] == 4.0 && scratch[2][1] == 9.0);
  assert(jacobian[0] == 17.0 && jacobian[1] == 4.0 && jacobian[2] == 0.0 &&
         !signbit(jacobian[2]) && jacobian[3] == 0.0 && !signbit(jacobian[3]) &&
         jacobian[4] == 6.0 && jacobian[5] == 19.0);
  /* The scratch-free dense Jacobian materializer diag(2*u). */
  double jdiag[6] = {17.0, -1.0, -1.0, -1.0, -1.0, 19.0};
  rumoca_square_jacobian_diag(input, jdiag + 1, 2, 4);
  assert(jdiag[0] == 17.0 && jdiag[1] == 4.0 && jdiag[2] == 0.0 &&
         !signbit(jdiag[2]) && jdiag[3] == 0.0 && !signbit(jdiag[3]) &&
         jdiag[4] == 6.0 && jdiag[5] == 19.0);
  assert(input[0] == 2.0 && input[1] == 3.0);
  return 0;
}
