#include <assert.h>
#include <fenv.h>
#include <stdint.h>
#include <string.h>
#include "production.c"

static uint64_t bits(double x) {
  uint64_t result;
  memcpy(&result, &x, sizeof result);
  return result;
}

static double value(uint64_t x) {
  double result;
  memcpy(&result, &x, sizeof result);
  return result;
}

int main(void) {
  assert(fesetround(FE_TONEAREST) == 0);
  struct {
    uint64_t before;
    Model first;
    uint64_t between;
    Model second;
    uint64_t after;
  } instances;
  instances.before = UINT64_C(0x123456789abcdef0);
  instances.between = UINT64_C(0xfedcba9876543210);
  instances.after = UINT64_C(0x8877665544332211);
  /* Startup must initialize allocated storage without reading old doubles. */
  assert(UnitIntegrator_Startup(&instances.first) == 0);
  assert(UnitIntegrator_Startup(&instances.second) == 0);
  assert(instances.first.errorSignalStatus == 0);
  assert(instances.second.errorSignalStatus == 0);
  instances.second.errorSignalStatus = 7;
  assert(bits(instances.first.x) == 0);
  assert(instances.first.samplePeriod == 1.0);
  for (unsigned i = 1; i <= 100; ++i) {
    instances.first.errorSignalStatus = INT32_MAX;
    assert(UnitIntegrator_DoStep(&instances.first) == 0);
    assert(instances.first.errorSignalStatus == 0);
    assert(instances.second.errorSignalStatus == 7);
    assert(instances.first.x == (double)i);
    assert(instances.second.x == 0.0);
    assert(instances.first.samplePeriod == 1.0);
    instances.first.errorSignalStatus = -1;
    assert(UnitIntegrator_Recalibrate(&instances.first) == 0);
    assert(instances.first.errorSignalStatus == 0);
    assert(instances.first.x == (double)i);
  }
  assert(instances.before == UINT64_C(0x123456789abcdef0));
  assert(instances.between == UINT64_C(0xfedcba9876543210));
  assert(instances.after == UINT64_C(0x8877665544332211));

  /* These test internal finite-state preconditions, not host output setters. */
  static const uint64_t cases[][2] = {
    {UINT64_C(0x8000000000000000), UINT64_C(0x3ff0000000000000)},
    {UINT64_C(0x0000000000000001), UINT64_C(0x3ff0000000000000)},
    {UINT64_C(0x8000000000000001), UINT64_C(0x3ff0000000000000)},
    {UINT64_C(0x4340000000000000), UINT64_C(0x4340000000000000)},
    {UINT64_C(0x4340000000000001), UINT64_C(0x4340000000000002)},
    {UINT64_C(0x7fefffffffffffff), UINT64_C(0x7fefffffffffffff)},
    {UINT64_C(0xffefffffffffffff), UINT64_C(0xffefffffffffffff)},
    {UINT64_C(0x3ff8000000000000), UINT64_C(0x4004000000000000)}
  };
  for (unsigned i = 0; i < sizeof cases / sizeof cases[0]; ++i) {
    instances.first.x = value(cases[i][0]);
    assert(UnitIntegrator_Recalibrate(&instances.first) == 0);
    assert(bits(instances.first.x) == cases[i][0]);
    assert(UnitIntegrator_DoStep(&instances.first) == 0);
    assert(bits(instances.first.x) == cases[i][1]);
    assert(instances.first.samplePeriod == 1.0);
    assert(instances.second.x == 0.0);
  }
  return 0;
}
