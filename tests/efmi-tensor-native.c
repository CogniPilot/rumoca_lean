/* Native boundary check for the existing tensor eFMI profile, not a proof of
 * the host compiler, C ABI, exception flags/traps, or MISRA conformance. The code
 * under test is the Production C member extracted from the checked archive. */
#include <assert.h>
#include <fenv.h>
#include <float.h>
#include <math.h>
#include <stdint.h>
#include <string.h>
#include "production.c"

#ifdef NDEBUG
#error "Native boundary checks require assertions"
#endif
_Static_assert(sizeof(double) == sizeof(uint64_t), "binary64 storage required");
_Static_assert(FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024 &&
               DBL_MIN_EXP == -1021 && FLT_EVAL_METHOD == 0,
               "binary64 evaluation required");

static uint64_t bits(double value) {
  uint64_t result;
  memcpy(&result, &value, sizeof result);
  return result;
}

static void same_values(const double *actual, const double *expected, size_t count) {
  for (size_t i = 0; i < count; ++i) {
    assert(bits(actual[i]) == bits(expected[i]));
  }
}

static void one_case(double first, double second, double square_first,
                     double square_second, double diagonal_first, double diagonal_second) {
  struct {
    uint64_t before;
    Model model;
    uint64_t after;
  } guarded = {UINT64_C(0x123456789abcdef0),
               {{first, second}, {17.0, 19.0}, {23.0, 29.0, 31.0, 37.0}, 41.0, -7},
               UINT64_C(0xfedcba9876543210)};
  Model *model = &guarded.model;
  const double input[2] = {first, second};
  const double initial_jacobian[4] = {23.0, 29.0, 31.0, 37.0};
  const double zero_state[2] = {0.0, 0.0};
  const double square[2] = {square_first, square_second};
  const double jacobian[4] = {diagonal_first, 0.0, 0.0, diagonal_second};

  assert(TensorSquare_Startup(model) == 0);
  assert(model->errorSignalStatus == 0);
  assert(bits(model->samplePeriod) == bits(1.0));
  same_values(model->u, input, 2);
  same_values(model->x, zero_state, 2);
  same_values(model->J, initial_jacobian, 4);

  model->samplePeriod = 0.25;
  model->errorSignalStatus = 11;
  assert(TensorSquare_Recalibrate(model) == 0);
  assert(model->errorSignalStatus == 0);
  assert(bits(model->samplePeriod) == bits(0.25));
  same_values(model->u, input, 2);
  same_values(model->x, zero_state, 2);
  same_values(model->J, initial_jacobian, 4);

  model->errorSignalStatus = -13;
  assert(TensorSquare_DoStep(model) == 0);
  assert(model->errorSignalStatus == 0);
  assert(bits(model->samplePeriod) == bits(0.25));
  same_values(model->u, input, 2);
  same_values(model->x, square, 2);
  same_values(model->J, jacobian, 4);

  model->errorSignalStatus = 17;
  assert(TensorSquare_Recalibrate(model) == 0);
  assert(model->errorSignalStatus == 0);
  assert(bits(model->samplePeriod) == bits(0.25));
  same_values(model->u, input, 2);
  same_values(model->x, square, 2);
  same_values(model->J, jacobian, 4);
  assert(guarded.before == UINT64_C(0x123456789abcdef0));
  assert(guarded.after == UINT64_C(0xfedcba9876543210));
}

/* Exercise the actual helper separately: overflowing squares are not admitted
 * by the finite RHS/public-method theorem. This checks helper result encodings
 * only, and must not be read as source-level DoStep overflow coverage. */
static void jacobian_case(double first, double second, uint64_t first_bits,
                          uint64_t second_bits) {
  const double input[2] = {first, second};
  struct {
    uint64_t before;
    double output[4];
    uint64_t after;
  } guarded = {UINT64_C(0x123456789abcdef0), {17.0, 19.0, 23.0, 29.0},
               UINT64_C(0xfedcba9876543210)};
  rumoca_square_jacobian_diag(input, guarded.output, 2, 4);
  assert(bits(guarded.output[0]) == first_bits);
  assert(bits(guarded.output[1]) == UINT64_C(0));
  assert(bits(guarded.output[2]) == UINT64_C(0));
  assert(bits(guarded.output[3]) == second_bits);
  assert(bits(input[0]) == bits(first));
  assert(bits(input[1]) == bits(second));
  assert(guarded.before == UINT64_C(0x123456789abcdef0));
  assert(guarded.after == UINT64_C(0xfedcba9876543210));
}

/* Total multiplication of finite operands: overflow, gradual underflow and
 * zero signs. These helper checks do not assert complete trajectory behavior. */
static void multiplication_case(double a0, double a1, double b0, double b1,
                                 uint64_t expected0, uint64_t expected1) {
  const double left[2] = {a0, a1};
  const double right[2] = {b0, b1};
  struct {
    uint64_t before;
    double output[2];
    uint64_t after;
  } guarded = {UINT64_C(0x123456789abcdef0), {17.0, 19.0},
               UINT64_C(0xfedcba9876543210)};
  rumoca_tensor_mul(left, right, guarded.output, 2);
  assert(bits(guarded.output[0]) == expected0);
  assert(bits(guarded.output[1]) == expected1);
  assert(bits(left[0]) == bits(a0) && bits(left[1]) == bits(a1));
  assert(bits(right[0]) == bits(b0) && bits(right[1]) == bits(b1));
  assert(guarded.before == UINT64_C(0x123456789abcdef0));
  assert(guarded.after == UINT64_C(0xfedcba9876543210));
}

int main(void) {
  assert(fesetround(FE_TONEAREST) == 0);
  one_case(2.0, -3.0, 4.0, 9.0, 4.0, -6.0);
  one_case(1.5, -0.5, 2.25, 0.25, 3.0, -1.0);
  /* Exact bits distinguish negative diagonal zero from off-diagonal +0. */
  one_case(-0.0, 0.0, 0.0, 0.0, -0.0, 0.0);
  jacobian_case(DBL_MAX, -DBL_MAX, UINT64_C(0x7ff0000000000000),
                UINT64_C(0xfff0000000000000));
  jacobian_case(DBL_MAX / 2.0, -DBL_MAX / 2.0, bits(DBL_MAX), bits(-DBL_MAX));
  double above_half = nextafter(DBL_MAX / 2.0, DBL_MAX);
  jacobian_case(above_half, -above_half, UINT64_C(0x7ff0000000000000),
                UINT64_C(0xfff0000000000000));
  multiplication_case(DBL_MAX, -DBL_MAX, 2.0, 2.0,
                      UINT64_C(0x7ff0000000000000), UINT64_C(0xfff0000000000000));
  multiplication_case(DBL_MAX, -DBL_MAX, 0.5, 0.5,
                      bits(DBL_MAX / 2.0), bits(-DBL_MAX / 2.0));
  multiplication_case(DBL_MIN, -DBL_MIN, DBL_MIN, DBL_MIN,
                      UINT64_C(0), UINT64_C(0x8000000000000000));
  multiplication_case(DBL_TRUE_MIN, -DBL_TRUE_MIN, 1.0, 1.0,
                      UINT64_C(1), UINT64_C(0x8000000000000001));
  multiplication_case(-0.0, -0.0, 3.0, -3.0,
                      UINT64_C(0x8000000000000000), UINT64_C(0));
  return 0;
}
