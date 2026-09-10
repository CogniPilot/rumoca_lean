#ifndef RUMOCA_TENSOR_NATIVE_H
#define RUMOCA_TENSOR_NATIVE_H
#include <stddef.h>

/* External linkage declarations used only by the native boundary check. */
void rumoca_tensor_add(const double *left, const double *right, double *out, size_t count);
void rumoca_tensor_mul(const double *left, const double *right, double *out, size_t count);
void rumoca_tensor_fill(double value, double *out, size_t count);
void rumoca_square_jacobian_coefficients(const double *x, const double *u,
    double *zero, double *one, double *primal, double *left, double *right, double *result, size_t count);
#endif
