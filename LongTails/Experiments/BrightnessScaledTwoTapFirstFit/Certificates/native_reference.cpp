#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <gmp.h>
#include <mpfr.h>
#include <omp.h>
#include <vector>
extern "C" {
void *_arb_vec_init(long);
void _arb_vec_clear(void *, long);
void arb_set_interval_mpfr(void *, mpfr_srcptr, mpfr_srcptr, long);
void arb_get_interval_mpfr(mpfr_ptr, mpfr_ptr, const void *);
void arb_exp(void *, const void *, long);
void arb_add_ui(void *, const void *, unsigned long, long);
void arb_inv(void *, const void *, long);
}
namespace {
int P, N, D, L, rate, threads, failures;
bool irrational_rate = false;
mpz_t scaled_rate;
mpz_t *V;
mpz_t DEN, HALF, ONE;
void store(mpz_srcptr v, double *out, std::vector<uint32_t> &words) {
  if (mpz_sizeinbase(v, 2) > 26u * L) {
    __atomic_add_fetch(&failures, 1, __ATOMIC_RELAXED);
    return;
  }
  size_t nw = 0;
  mpz_export(words.data(), &nw, -1, 4, 0, 6, v);
  int s = mpz_sgn(v);
  for (int j = 0; j < L; j++)
    out[j] = j < (int)nw ? s * double(words[j]) : 0.;
}
void restore(const double *digits, mpz_ptr z, std::vector<uint32_t> &w,
             mpz_ptr top) {
  int64_t carry = 0;
  for (int j = 0; j < L; j++) {
    int64_t val = (int64_t)digits[j] + carry;
    w[j] = uint32_t(val) & 0x3ffffff;
    carry = (val - int64_t(w[j])) / 67108864;
  }
  mpz_import(z, L, -1, 4, 0, 6, w.data());
  if (carry) {
    mpz_set_si(top, carry);
    mpz_mul_2exp(top, top, 26 * L);
    mpz_add(z, z, top);
  }
}
} // namespace
extern "C" int init(int p, int n, int d, int eta, int th, const double *v0) {
  P = p;
  N = n;
  D = d;
  rate = eta;
  threads = th;
  L = (p + 32 + 25) / 26;
  omp_set_dynamic(0);
  omp_set_num_threads(threads);
  V = new mpz_t[D];
  mpfr_t t;
  mpfr_init2(t, 128);
  for (int j = 0; j < D; j++) {
    mpz_init(V[j]);
    mpfr_set_d(t, v0[j], MPFR_RNDN);
    mpfr_mul_2ui(t, t, P, MPFR_RNDN);
    mpfr_get_z(V[j], t, MPFR_RNDN);
  }
  mpz_inits(DEN, HALF, ONE, nullptr);
  mpz_set_ui(DEN, n * 255);
  mpz_fdiv_q_2exp(HALF, DEN, 1);
  mpz_set_ui(ONE, 1);
  mpz_mul_2exp(ONE, ONE, P);
  mpfr_clear(t);
  return L;
}
extern "C" int state(double *out) {
#pragma omp parallel
  {
    std::vector<uint32_t> w(L);
#pragma omp for
    for (int j = 0; j < D; j++)
      store(V[j], out + j * L, w);
  }
  return failures;
}
extern "C" int posterior(const double *dots, double *qd, double *q64,
                         double *m64) {
#pragma omp parallel
  {
    std::vector<uint32_t> w(L);
    mpz_t z, k;
    mpz_inits(z, k, nullptr);
    mpfr_t m, s, lo;
    mpfr_init2(m, P + 80);
    mpfr_init2(s, P + 80);
    mpfr_init2(lo, P + 80);
    void *ball = _arb_vec_init(1);
#pragma omp for schedule(dynamic, 20)
    for (int i = 0; i < N; i++) {
      restore(dots + i * L, z, w, k);
      mpfr_set_z(m, z, MPFR_RNDN);
      mpfr_div_2ui(m, m, P, MPFR_RNDN);
      mpfr_div_ui(m, m, 255, MPFR_RNDN);
      m64[i] = mpfr_get_d(m, MPFR_RNDN);
      mpfr_abs(m, m, MPFR_RNDN);
      const double M = std::abs(m64[i]);
      if (M > 1e6) {
        __atomic_add_fetch(&failures, 1, __ATOMIC_RELAXED);
      }
      int e = (int)std::max(0., std::floor(M * 1.442695040888962) - 2.);
      if (e > P + 70) {
        mpz_set_ui(k, 0);
        q64[i] = 0.;
      } else {
        int acc = std::max(96, P + 80 - e);
        arb_set_interval_mpfr(ball, m, m, acc);
        arb_exp(ball, ball, acc);
        arb_add_ui(ball, ball, 1, acc);
        arb_inv(ball, ball, acc);
        arb_get_interval_mpfr(lo, s, ball);
        mpfr_sub(lo, s, lo, MPFR_RNDU);
        if (mpfr_cmp_ui_2exp(lo, 1, -P - 30) > 0) {
          __atomic_add_fetch(&failures, 1, __ATOMIC_RELAXED);
        }
        q64[i] = mpfr_get_d(s, MPFR_RNDN);
        mpfr_mul_2ui(s, s, P, MPFR_RNDN);
        mpfr_get_z(k, s, MPFR_RNDN);
      }
      if (mpz_sgn(z) < 0) {
        q64[i] = 1. - q64[i];
        mpz_sub(k, ONE, k);
      }
      store(k, qd + i * L, w);
    }
    _arb_vec_clear(ball, 1);
    mpfr_clears(m, s, lo, (mpfr_ptr)0);
    mpz_clears(z, k, nullptr);
  }
  return failures;
}
namespace {
std::vector<long> vin;
long a, b;
mpz_t *grad;
} // namespace
extern "C" void setup_metric(const long *v, long ca, long cb) {
  vin.assign(v, v + D);
  a = ca;
  b = cb;
  grad = new mpz_t[D];
  for (int j = 0; j < D; ++j)
    mpz_init(grad[j]);
  mpz_mul_2exp(DEN, DEN, 60);
  mpz_fdiv_q_2exp(HALF, DEN, 1);
}
extern "C" void use_sqrt_rate(int power) {
  irrational_rate = true;
  mpz_init_set_ui(scaled_rate, 1);
  mpz_mul_2exp(scaled_rate, scaled_rate, 2 * P + power);
  mpz_sqrt(scaled_rate, scaled_rate);
  mpz_mul_2exp(DEN, DEN, P);
  mpz_fdiv_q_2exp(HALF, DEN, 1);
}
extern "C" int update(const double *g) {
#pragma omp parallel
  {
    std::vector<uint32_t> w(L);
    mpz_t t;
    mpz_init(t);
#pragma omp for
    for (int j = 0; j < D; j++)
      restore(g + j * L, grad[j], w, t);
    mpz_clear(t);
  }
  mpz_t x, y;
  mpz_inits(x, y, nullptr);
  for (int j = 0; j < D; j++) {
    mpz_addmul_ui(x, grad[j], std::abs(vin[j]) * (vin[j] >= 0));
    mpz_submul_ui(x, grad[j], std::abs(vin[j]) * (vin[j] < 0));
    long h = vin[(j + 1) % D];
    if (h >= 0)
      mpz_addmul_ui(y, grad[j], h);
    else
      mpz_submul_ui(y, grad[j], -h);
  }
#pragma omp parallel
  {
    mpz_t z, k;
    mpz_inits(z, k, nullptr);
#pragma omp for
    for (int j = 0; j < D; j++) {
      int jp = (j + 1) % D, jm = (j + D - 1) % D;
      mpz_add(z, grad[jp], grad[jm]);
      mpz_mul_si(z, z, a * b);
      mpz_addmul_ui(z, grad[j], a * a + b * b);
      mpz_mul_2exp(z, z, 12);
      long v = vin[j];
      if (v >= 0)
        mpz_addmul_ui(z, x, v);
      else
        mpz_submul_ui(z, x, -v);
      v = vin[jp];
      if (v >= 0)
        mpz_addmul_ui(z, y, v);
      else
        mpz_submul_ui(z, y, -v);
      if (irrational_rate)
        mpz_mul(z, z, scaled_rate);
      else
        mpz_mul_ui(z, z, rate);
      if (mpz_sgn(z) < 0)
        mpz_sub(z, z, HALF);
      else
        mpz_add(z, z, HALF);
      mpz_tdiv_q(z, z, DEN);
      mpz_add(V[j], V[j], z);
    }
    mpz_clears(z, k, nullptr);
  }
  mpz_clears(x, y, nullptr);
  return failures;
}
extern "C" int save(const char *fn, int load) {
  FILE *f = fopen(fn, load ? "rb" : "wb");
  if (!f)
    return 1;
  for (int j = 0; j < D; j++) {
    size_t ok = load ? mpz_inp_raw(V[j], f) : mpz_out_raw(f, V[j]);
    if (!ok)
      return 2;
  }
  return fclose(f);
}

extern "C" int precision_change(int next) {
  if (next > P || next < 128)
    return -1;
  if (next == P)
    return L;
  int drop = P - next;
  mpz_t half;
  mpz_init_set_ui(half, 1);
  mpz_mul_2exp(half, half, drop - 1);
#pragma omp parallel for
  for (int j = 0; j < D; j++) {
    if (mpz_sgn(V[j]) < 0)
      mpz_sub(V[j], V[j], half);
    else
      mpz_add(V[j], V[j], half);
    mpz_tdiv_q_2exp(V[j], V[j], drop);
  }
  mpz_clear(half);
  P = next;
  L = (P + 32 + 25) / 26;
  mpz_set_ui(ONE, 1);
  mpz_mul_2exp(ONE, ONE, P);
  return L;
}
extern "C" void set_threads(int th) {
  threads = th;
  omp_set_dynamic(0);
  omp_set_num_threads(th);
}
