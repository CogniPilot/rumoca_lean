/* External CSV host: Modelica Real state in binary64; unit-time samples.
 * Parsing, decimal conversion and printing are tested host code. The generated
 * numerical functions and their rounding contract are verified separately. */
#include <errno.h>
#include <fenv.h>
#include <inttypes.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

double rumoca_step(double x);

static int parse_u64(const char *text, uint64_t *out) {
    if (*text == '\0') return 0;
    for (const char *p = text; *p; ++p) {
        if (*p < '0' || *p > '9') return 0;
    }
    errno = 0;
    char *end = NULL;
    uintmax_t value = strtoumax(text, &end, 10);
    if (errno || *end || value > UINT64_MAX) return 0;
    *out = (uint64_t)value;
    return 1;
}

static int parse_real(const char *text, double *out) {
    /* A decimal host input, including sign and exponent. No NaN/Inf/hex. */
    const char *p = text;
    if (*p == '+' || *p == '-') ++p;
    int digits = 0;
    while (*p >= '0' && *p <= '9') { ++p; ++digits; }
    if (*p == '.') {
        ++p;
        while (*p >= '0' && *p <= '9') { ++p; ++digits; }
    }
    if (!digits) return 0;
    if (*p == 'e' || *p == 'E') {
        ++p;
        if (*p == '+' || *p == '-') ++p;
        const char *exponent = p;
        while (*p >= '0' && *p <= '9') ++p;
        if (p == exponent) return 0;
    }
    if (*p) return 0;
    errno = 0;
    char *end = NULL;
    double value = strtod(text, &end);
    if (*end || !isfinite(value)) return 0;
    /* Accept representable subnormals; reject underflow of a nonzero literal
     * to zero. errno=ERANGE alone would incorrectly reject subnormals. */
    if (errno == ERANGE && value == 0.0) return 0;
    *out = value;
    return 1;
}

int main(int argc, char **argv) {
    uint64_t steps = 10;
    double x = 0.0;
    if (fesetround(FE_TONEAREST) != 0) {
        fputs("round-to-nearest is unavailable\n", stderr);
        return 2;
    }
    if (argc > 3 || (argc > 1 && !parse_u64(argv[1], &steps)) ||
        (argc > 2 && !parse_real(argv[2], &x))) {
        fputs("usage: simulate [steps=10] [initial_real=0]\n", stderr);
        return 2;
    }
    puts("t,x");
    for (uint64_t t = 0;; ++t) {
        printf("%" PRIu64 ",%.17g\n", t, x);
        if (t == steps) break;
        x = rumoca_step(x);
    }
    return ferror(stdout) ? 1 : 0;
}
