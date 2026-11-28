#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <gmp.h>
#include <mpfr.h>
#include <omp.h>
#include <vector>
namespace {
int P, N, D, L;
mpz_t *V, *G, C[2], DEN, HALF;
int failures;
bool scale_step = false;
mpz_t scaled_step;
void store(mpz_srcptr v, double *out) {
  uint32_t words[256];
  size_t nw = 0;
  if (L > 256 || mpz_sizeinbase(v, 2) > 26u * L) {
    __atomic_add_fetch(&failures, 1, __ATOMIC_RELAXED);
    return;
  }
  mpz_export(words, &nw, -1, sizeof(uint32_t), 0, 6, v);
  int s = mpz_sgn(v);
  for (int j = 0; j < L; j++)
    out[j] = (j < (int)nw) ? s * double(words[j]) : 0.;
}
void restore(const double *dat, mpz_ptr z) {
  mpz_set_ui(z, 0);
  for (int j = L - 1; j >= 0; j--) {
    mpz_mul_2exp(z, z, 26);
    double v = dat[j];
    if (v < 0)
      mpz_sub_ui(z, z, (unsigned long)(-v));
    else
      mpz_add_ui(z, z, (unsigned long)v);
  }
}
void inc(mpz_ptr x, mpz_ptr a) {
  if (scale_step)
    mpz_mul(a, a, scaled_step);
  if (mpz_sgn(a) < 0)
    mpz_sub(a, a, HALF);
  else
    mpz_add(a, a, HALF);
  mpz_tdiv_q(a, a, DEN);
  mpz_add(x, x, a);
}
} // namespace
extern "C" int initialize_hp(int prec, int n, int d, const double *v0,
                             const double *c0) {
  P = prec;
  N = n;
  D = d;
  L = (P + 16 + 25) / 26;
  V = new mpz_t[D];
  G = new mpz_t[D];
  mpfr_t t;
  mpfr_init2(t, P + 80);
  for (int j = 0; j < D + 2; j++) {
    mpz_ptr p;
    if (j < D) {
      mpz_init(V[j]);
      mpz_init(G[j]);
      p = V[j];
    } else {
      p = C[j - D];
      mpz_init(p);
    }
    mpfr_set_d(t, j < D ? v0[j] : c0[j - D], MPFR_RNDN);
    mpfr_mul_2ui(t, t, P, MPFR_RNDN);
    mpfr_get_z(p, t, MPFR_RNDN);
  }
  mpz_inits(DEN, HALF, nullptr);
  mpz_set_ui(DEN, 8 * N * 255);
  mpz_mul_2exp(DEN, DEN, P);
  mpz_tdiv_q_2exp(HALF, DEN, 1);
  mpfr_clear(t);
  return L;
}
extern "C" int state_hp(double *digits, double *v, double *c) {
#pragma omp parallel
  {
    mpfr_t t;
    mpfr_init2(t, P + 80);
#pragma omp for
    for (int j = 0; j < D + 2; j++) {
      mpz_srcptr p = j < D ? V[j] : C[j - D];
      if (j < D)
        store(p, digits + j * L);
      mpfr_set_z(t, p, MPFR_RNDN);
      mpfr_div_2ui(t, t, P, MPFR_RNDN);
      if (j < D)
        v[j] = mpfr_get_d(t, MPFR_RNDN);
      else
        c[j - D] = mpfr_get_d(t, MPFR_RNDN);
    }
    mpfr_clear(t);
  }
  return failures;
}
extern "C" int posterior_hp(const double *dot, double *qd, double *qout,
                            double *sout, double *mout) {
#pragma omp parallel
  {
    mpz_t a, b, z, tmp;
    mpz_inits(a, b, z, tmp, nullptr);
    mpfr_t t;
    mpfr_init2(t, P + 80);
#pragma omp for
    for (int i = 0; i < N; i++) {
      const double *row = dot + 2 * L * i;
      restore(row, a);
      restore(row + L, b);
      mpz_mul(z, a, C[0]);
      mpz_addmul(z, b, C[1]);
      mpfr_set_z(t, z, MPFR_RNDN);
      mpfr_div_2ui(t, t, 2 * P, MPFR_RNDN);
      mpfr_div_ui(t, t, 255, MPFR_RNDN);
      mout[i] = mpfr_get_d(t, MPFR_RNDN);
      mpfr_exp(t, t, MPFR_RNDN);
      mpfr_add_ui(t, t, 1, MPFR_RNDN);
      mpfr_ui_div(t, 1, t, MPFR_RNDN);
      qout[i] = mpfr_get_d(t, MPFR_RNDN);
      mpfr_mul_2ui(t, t, P, MPFR_RNDN);
      mpfr_get_z(tmp, t, MPFR_RNDN);
      store(tmp, qd + i * L);
      for (int j = 0; j < 2; j++) {
        mpfr_set_z(t, j ? b : a, MPFR_RNDN);
        mpfr_div_2ui(t, t, P, MPFR_RNDN);
        mpfr_div_ui(t, t, 255, MPFR_RNDN);
        sout[2 * i + j] = mpfr_get_d(t, MPFR_RNDN);
      }
    }
    mpfr_clear(t);
    mpz_clears(a, b, z, tmp, nullptr);
  }
  return failures;
}
extern "C" int update_hp(const double *gradient, double *gout) {
  mpz_t d0, d1;
  mpz_inits(d0, d1, nullptr);
#pragma omp parallel
  {
    mpfr_t t;
    mpfr_init2(t, P + 80);
    mpz_t x, y;
    mpz_inits(x, y, nullptr);
#pragma omp for
    for (int j = 0; j < D; j++) {
      restore(gradient + j * L, G[j]);
      mpfr_set_z(t, G[j], MPFR_RNDN);
      mpfr_div_2ui(t, t, P, MPFR_RNDN);
      mpfr_div_ui(t, t, 255 * N, MPFR_RNDN);
      gout[j] = mpfr_get_d(t, MPFR_RNDN);
    }
#pragma omp for
    for (int j = 0; j < D; j++) {
      int jprev = (j + D - 1) % D;
      mpz_addmul(x, V[j], G[j]);
      mpz_addmul(y, V[j], G[jprev]);
    }
#pragma omp critical
    {
      mpz_add(d0, d0, x);
      mpz_add(d1, d1, y);
    }
#pragma omp barrier
#pragma omp for
    for (int j = 0; j < D; j++) {
      int jprev = (j + D - 1) % D;
      mpz_mul(x, C[0], G[j]);
      mpz_addmul(x, C[1], G[jprev]);
      inc(V[j], x);
    }
    mpfr_clear(t);
    mpz_clears(x, y, nullptr);
  }
  inc(C[0], d0);
  inc(C[1], d1);
  mpz_clears(d0, d1, nullptr);
  return failures;
}
extern "C" void increase_step_sqrt_two() {
  scale_step = true;
  mpz_init_set_ui(scaled_step, 2);
  mpz_mul_2exp(scaled_step, scaled_step, 2 * P);
  mpz_sqrt(scaled_step, scaled_step);
  mpz_mul_2exp(DEN, DEN, P);
  mpz_tdiv_q_2exp(HALF, DEN, 1);
}
extern "C" int threads_hp(int k) {
  omp_set_dynamic(0);
  omp_set_num_threads(k);
  return omp_get_max_threads();
}
