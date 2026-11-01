import LongTails.Proofs.RadiusFreeSherpaRun
import LongTails.Proofs.BacktrackingAcceleratedBudget

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.RadiusFreeSherpa

open LongTails.Setups.RadiusOnlyGeneralizedSmoothConvex

lemma execute_algorithm (p : Public) (g : p.E → p.E) (N : ℕ) :
    execute { answer := fun _ (_, x) _ => g x } (algorithm p) (fun _ => N) =
      stateOutput ((T p.L0 p.L1 g)^[N] (initState p.x0)) := by
  erw [execute_iterate]
  rfl

lemma log_two_lower : (0.69 : ℝ) ≤ Real.log 2 := by
  have := Real.log_two_gt_d9
  linarith

lemma one_le_log2q {q : ℝ} (hq : 0 ≤ q) : 1 ≤ 1.45 * Real.log (2 + q) := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 2 + q)
  have := log_two_lower
  linarith

lemma log2q_pos {q : ℝ} (hq : 0 ≤ q) : 0 < Real.log (2 + q) := by
  have := one_le_log2q hq; linarith

lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hs
  have : Real.log x = 2 * Real.log (Real.sqrt x) := by
    have e : Real.log x = Real.log (Real.sqrt x ^ 2) := by rw [Real.sq_sqrt hx.le]
    rw [e, Real.log_pow]; push_cast; ring
  rw [this]; linarith

lemma log_pow_bound {q c : ℝ} (hq : 0 ≤ q) (hc : 0 < c) {a k : ℕ} (hca : c ≤ 2 ^ a) :
    Real.log (c * (1 + q) ^ k) ≤ (a + k) * Real.log (2 + q) := by
  have h2 : (2 : ℝ) ≤ 2 + q := by linarith
  have h1 : (1 + q) ≤ 2 + q := by linarith
  have hb : c * (1 + q) ^ k ≤ (2 + q) ^ (a + k) := by
    rw [pow_add]
    apply mul_le_mul _ (pow_le_pow_left₀ (by linarith) h1 k) (by positivity) (by positivity)
    exact hca.trans (pow_le_pow_left₀ (by norm_num) h2 a)
  calc Real.log (c * (1 + q) ^ k) ≤ Real.log ((2 + q) ^ (a + k)) :=
        Real.log_le_log (by positivity) hb
    _ = (a + k) * Real.log (2 + q) := by rw [Real.log_pow]; push_cast; ring

lemma logb_le {x : ℝ} (hlog : 0 ≤ Real.log x) :
    Real.logb 2 x ≤ 1.45 * Real.log x := by
  unfold Real.logb
  have := log_two_lower
  rw [div_le_iff₀ (by linarith)]
  nlinarith

lemma theta_le {q : ℝ} (hq : 0 ≤ q) : theta q ≤ 1 + q := by
  unfold theta
  rw [Real.sqrt_le_left (by linarith)]
  nlinarith

lemma bigB_le {q : ℝ} (hq : 0 ≤ q) : bigB q ≤ 628 * (1 + q) := by
  unfold bigB
  have hθ := theta_pos hq
  have hθ1 := theta_le hq
  have hθsq := theta_sq hq
  have hs : 2 * Real.sqrt 14 * Real.sqrt 48 ≤ 52 := by
    have h1 : Real.sqrt 14 * Real.sqrt 48 ≤ 26 := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 14)]
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have hlog : Real.log (336 * (1 + q) ^ 2) ≤ 2 * Real.sqrt 336 + 2 * Real.log (1 + q) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have := log_le_two_sqrt (show (0:ℝ) < 336 by norm_num)
    push_cast; linarith
  have h336 : Real.sqrt 336 ≤ 19 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hlogq : Real.log (1 + q) ≤ 2 * theta q := by
    have := log_le_two_sqrt (show (0:ℝ) < 1 + q by linarith)
    unfold theta; linarith
  have hθlog : theta q * Real.log (336 * (1 + q) ^ 2) ≤ 38 * theta q + 4 * theta q ^ 2 := by
    have h1 : theta q * Real.log (336 * (1 + q) ^ 2) ≤
        theta q * (2 * Real.sqrt 336 + 2 * Real.log (1 + q)) :=
      mul_le_mul_of_nonneg_left hlog hθ.le
    have h2 : theta q * (2 * Real.log (1 + q)) ≤ theta q * (4 * theta q) :=
      mul_le_mul_of_nonneg_left (by linarith) hθ.le
    nlinarith
  have hsq : 0 ≤ q := hq
  nlinarith [mul_nonneg hsq hsq]

lemma probeCap_le {q : ℝ} (hq : 0 ≤ q) : (probeCap q : ℝ) ≤ 22 * Real.log (2 + q) := by
  unfold probeCap
  have hlog : 0 ≤ Real.log (3200 * (1 + q) ^ 2) := Real.log_nonneg (by nlinarith)
  have hceil : (⌈Real.logb 2 (3200 * (1 + q) ^ 2)⌉₊ : ℝ) < Real.logb 2 (3200 * (1 + q) ^ 2) + 1 :=
    Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
      (by nlinarith : (1:ℝ) ≤ 3200 * (1 + q) ^ 2))
  have hlb := logb_le hlog
  have hp := log_pow_bound (c := 3200) hq (by norm_num) (a := 12) (k := 2) (by norm_num)
  have h1 := one_le_log2q hq
  have := log2q_pos hq
  push_cast at hp
  linarith

lemma phaseSteps_le {q : ℝ} (hq : 0 ≤ q) : phaseSteps q ≤ 15700 * (1 + q) * Real.log (2 + q) := by
  unfold phaseSteps
  have hB := bigB_le hq
  have hM := probeCap_le hq
  have hM0 : (0 : ℝ) ≤ probeCap q := by positivity
  have h1 := one_le_log2q hq
  have hl := log2q_pos hq
  have hB0 : 0 ≤ bigB q := by
    unfold bigB
    have := theta_pos hq
    have hlog : 0 ≤ Real.log (336 * (1 + q) ^ 2) := Real.log_nonneg (by nlinarith)
    positivity
  nlinarith [mul_nonneg hq hl.le, mul_nonneg hB0 hM0]

lemma phase2_bound_le {q A : ℝ} (hq : 0 ≤ q) :
    4 + 2 * (3 + 13 * q) * Real.log (1 + (2 + 13 * q) ^ 2 * (1 / 64 + 1 / 4 + 5 * q / 16)) +
        4 * Real.sqrt (32 * A) + Real.logb 2 ((2 + 13 * q) ^ 2 * (17 + 20 * q)) ≤
      23 * Real.sqrt A + 262 * (1 + q) * Real.log (2 + q) := by
  have hl := log2q_pos hq
  have h1 := one_le_log2q hq
  have hinner : 1 + (2 + 13 * q) ^ 2 * (1 / 64 + 1 / 4 + 5 * q / 16) ≤ 54 * (1 + q) ^ 3 := by
    nlinarith [mul_nonneg hq hq, mul_nonneg (mul_nonneg hq hq) hq]
  have hlog1 : Real.log (1 + (2 + 13 * q) ^ 2 * (1 / 64 + 1 / 4 + 5 * q / 16)) ≤ 9 * Real.log (2 + q) := by
    have := log_pow_bound (c := 54) hq (by norm_num) (a := 6) (k := 3) (by norm_num)
    push_cast at this
    exact (Real.log_le_log (by positivity) hinner).trans (by linarith)
  have hcoef : 0 ≤ 2 * (3 + 13 * q) := by linarith
  have hterm1 := mul_le_mul_of_nonneg_left hlog1 hcoef
  have hsqrt : 4 * Real.sqrt (32 * A) ≤ 23 * Real.sqrt A := by
    rw [Real.sqrt_mul (by norm_num)]
    have : Real.sqrt 32 ≤ 5.75 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg A]
  have hinner2 : (2 + 13 * q) ^ 2 * (17 + 20 * q) ≤ 3380 * (1 + q) ^ 3 := by
    nlinarith [mul_nonneg hq hq, mul_nonneg (mul_nonneg hq hq) hq]
  have hpos2 : (0 : ℝ) < (2 + 13 * q) ^ 2 * (17 + 20 * q) := by positivity
  have hlog2 : Real.log ((2 + 13 * q) ^ 2 * (17 + 20 * q)) ≤ 15 * Real.log (2 + q) := by
    have := log_pow_bound (c := 3380) hq (by norm_num) (a := 12) (k := 3) (by norm_num)
    push_cast at this
    exact (Real.log_le_log hpos2 hinner2).trans (by linarith)
  have hlog2nn : 0 ≤ Real.log ((2 + 13 * q) ^ 2 * (17 + 20 * q)) :=
    Real.log_nonneg (by nlinarith)
  have hlb := logb_le hlog2nn
  nlinarith [mul_nonneg hq hl.le]

end OracleTemplate.RadiusFreeSherpa
