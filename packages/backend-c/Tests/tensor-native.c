#include <assert.h>
#include <float.h>
#include <fenv.h>
#include <math.h>
#include <string.h>
#include <stddef.h>
#include <stdint.h>
#include "tensor-native.h"

_Static_assert(sizeof(size_t) == 8, "authored tensor target uses 64-bit size_t");
_Static_assert(sizeof(double) == sizeof(uint64_t), "binary64 object storage required");
_Static_assert(FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024 &&
               DBL_MIN_EXP == -1021 && FLT_EVAL_METHOD == 0, "binary64 target required");

/* One native boundary check complements the universal Lean proofs. */
int main(void) {
  assert(fesetround(FE_TONEAREST) == 0);
  /* Empty tensors have no dereference, including a null data pointer. */
  assert(rumoca_tensor_all_finite(NULL, 0) == 1);
  const double finite_values[] = {0.0, -0.0, DBL_TRUE_MIN, -DBL_TRUE_MIN, DBL_MAX, -DBL_MAX};
  uint64_t finite_bits[6];
  memcpy(finite_bits, finite_values, sizeof finite_bits);
  assert(rumoca_tensor_all_finite(finite_values, 6) == 1);
  uint64_t after_bits[6];
  memcpy(after_bits, finite_values, sizeof after_bits);
  assert(memcmp(finite_bits, after_bits, sizeof finite_bits) == 0);
  /* Quiet NaNs include a nonzero payload; the scanner must not alter input. */
  uint64_t nan_bits = UINT64_C(0x7ff8000000000042);
  double quiet_nan;
  memcpy(&quiet_nan, &nan_bits, sizeof quiet_nan);
  const double first_failure[] = {quiet_nan, 1.0, 2.0};
  const double middle_failure[] = {1.0, quiet_nan, 2.0};
  const double last_failure[] = {1.0, 2.0, quiet_nan};
  assert(rumoca_tensor_all_finite(first_failure, 3) == 0);
  assert(rumoca_tensor_all_finite(middle_failure, 3) == 0);
  assert(rumoca_tensor_all_finite(last_failure, 3) == 0);
  assert(rumoca_tensor_all_finite((const double[]){INFINITY}, 1) == 0);
  assert(rumoca_tensor_all_finite((const double[]){-INFINITY}, 1) == 0);
  uint64_t negative_nan_bits = UINT64_C(0xfff8000000000081);
  double negative_nan;
  memcpy(&negative_nan, &negative_nan_bits, sizeof negative_nan);
  assert(rumoca_tensor_all_finite(&negative_nan, 1) == 0);
  assert(memcmp(&negative_nan_bits, &negative_nan, sizeof negative_nan_bits) == 0);
  double guarded[6] = {17.0, 1.0, 2.0, 3.0, 4.0, 19.0};
  uint64_t guarded_before[6];
  memcpy(guarded_before, guarded, sizeof guarded_before);
  assert(rumoca_tensor_all_finite(guarded + 1, 4) == 1);
  assert(memcmp(guarded_before, guarded, sizeof guarded_before) == 0);
  assert(guarded[0] == 17.0 && guarded[5] == 19.0);
  guarded[3] = quiet_nan;
  memcpy(guarded_before, guarded, sizeof guarded_before);
  assert(rumoca_tensor_all_finite(guarded + 1, 4) == 0);
  assert(memcmp(guarded_before, guarded, sizeof guarded_before) == 0);
  /* Read-only operation preflight: inputs can alias, including at overflow.
     Exception flags/traps are outside the heap-preservation theorem. */
  assert(rumoca_tensor_mul_finite(NULL, NULL, 0) == 1);
  const double product_left[6] = {17.0, 0.0, -0.0, DBL_TRUE_MIN, DBL_MAX, 19.0};
  const double product_right[6] = {23.0, -DBL_MAX, DBL_MAX, 0.5, 0.5, 29.0};
  uint64_t left_before[6], right_before[6];
  memcpy(left_before, product_left, sizeof left_before);
  memcpy(right_before, product_right, sizeof right_before);
  assert(rumoca_tensor_mul_finite(product_left + 1, product_right + 1, 4) == 1);
  assert(memcmp(left_before, product_left, sizeof left_before) == 0);
  assert(memcmp(right_before, product_right, sizeof right_before) == 0);
  assert(rumoca_tensor_mul_finite(product_left + 1, product_left + 1, 4) == 0);
  assert(memcmp(left_before, product_left, sizeof left_before) == 0);
  const double overflow_left[4] = {DBL_MAX, 1.0, 2.0, -DBL_MAX};
  const double overflow_right[4] = {-2.0, 1.0, 1.0, -2.0};
  assert(rumoca_tensor_mul_finite(overflow_left, overflow_right, 1) == 0);
  assert(rumoca_tensor_mul_finite(overflow_left + 1, overflow_right + 1, 3) == 0);
  assert(rumoca_tensor_mul_finite(overflow_left + 1, overflow_right + 1, 2) == 1);
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
  /* Subtraction and division on the two-wide operands. */
  const double lhs[2] = {3.0, 1.0}, rhs[2] = {2.0, 4.0};
  rumoca_tensor_sub(lhs, rhs, output + 1, 2);
  assert(output[0] == 17.0 && output[1] == 1.0 && output[2] == -3.0 && output[3] == 19.0);
  rumoca_tensor_div(lhs, rhs, output + 1, 2);
  assert(output[0] == 17.0 && output[1] == 1.5 && output[2] == 0.25 && output[3] == 19.0);
  assert(lhs[0] == 3.0 && lhs[1] == 1.0 && rhs[0] == 2.0 && rhs[1] == 4.0);
  rumoca_tensor_sub(NULL, NULL, NULL, 0);
  rumoca_tensor_div(NULL, NULL, NULL, 0);
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
  /* Execute the actual prepared RHS wrapper, not only its arithmetic helper. */
  const double extreme_input[2] = {DBL_MAX, -DBL_MAX};
  double extreme_output[4] = {17.0, 0.0, 0.0, 19.0};
  rumoca_rhs(extreme_input, extreme_input, extreme_output + 1, 2);
  assert(extreme_output[0] == 17.0 && extreme_output[3] == 19.0);
  assert(isinf(extreme_output[1]) && !signbit(extreme_output[1]) &&
         isinf(extreme_output[2]) && !signbit(extreme_output[2]));
  assert(extreme_input[0] == DBL_MAX && extreme_input[1] == -DBL_MAX);
  assert(rumoca_tensor_all_finite(extreme_output + 1, 2) == 0);
  const double tiny_input[2] = {-0.0, -DBL_TRUE_MIN};
  rumoca_rhs(tiny_input, tiny_input, extreme_output + 1, 2);
  assert(extreme_output[0] == 17.0 && extreme_output[3] == 19.0);
  assert(extreme_output[1] == 0.0 && !signbit(extreme_output[1]) &&
         extreme_output[2] == 0.0 && !signbit(extreme_output[2]));
  assert(rumoca_tensor_all_finite(extreme_output + 1, 2) == 1);
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
