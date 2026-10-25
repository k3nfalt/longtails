import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedSpectralGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma norm_unit_add_rpow_le {u e : E} (hu : ‖u‖ = 1) {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ‖u + e‖ ^ p ≤ 1 + p * ⟪u, e⟫ + 6 * ‖e‖ ^ p := by
  have hp0 : 0 ≤ p := by linarith
  have he0 := norm_nonneg e
  have hep := Real.rpow_nonneg he0 p
  have hi : -‖e‖ ≤ ⟪u, e⟫ := by
    have h := neg_le_of_abs_le (abs_real_inner_le_norm u e)
    simpa [hu] using h
  by_cases he : ‖e‖ ≤ 1
  · have he2 : ‖e‖ ^ 2 ≤ ‖e‖ ^ p := by
      simpa only [Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_ge' he0 he hp0 hp2
    have hn : ‖u + e‖ ^ 2 = 1 + 2 * ⟪u, e⟫ + ‖e‖ ^ 2 := by
      rw [norm_add_sq_real, hu]
      ring
    have hs : -1 ≤ 2 * ⟪u, e⟫ + ‖e‖ ^ 2 := by
      nlinarith [sq_nonneg ‖u + e‖]
    have hr := rpow_one_add_le_one_add_mul_self hs
      (show 0 ≤ p / 2 by positivity) (show p / 2 ≤ 1 by linarith)
    have heq : (‖u + e‖ ^ 2) ^ (p / 2) = ‖u + e‖ ^ p := by
      rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
      congr 1
      ring
    rw [← add_assoc, ← hn, heq] at hr
    have hm := mul_le_mul_of_nonneg_right hp2 (sq_nonneg ‖e‖)
    nlinarith
  · have he1 : 1 ≤ ‖e‖ := le_of_lt (lt_of_not_ge he)
    have hepow : ‖e‖ ≤ ‖e‖ ^ p := by
      simpa using Real.rpow_le_rpow_of_exponent_le he1 hp
    have hn : ‖u + e‖ ≤ 2 * ‖e‖ := by
      have h := norm_add_le u e
      rw [hu] at h
      linarith
    have ht : (2 : ℝ) ^ p ≤ 4 := by
      have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hp2
      norm_num at h ⊢
      exact h
    have hb : ‖u + e‖ ^ p ≤ 4 * ‖e‖ ^ p := by
      calc
        _ ≤ (2 * ‖e‖) ^ p := Real.rpow_le_rpow (norm_nonneg _) hn hp0
        _ = (2 : ℝ) ^ p * ‖e‖ ^ p := Real.mul_rpow (by norm_num) he0
        _ ≤ _ := mul_le_mul_of_nonneg_right ht hep
    have hi' := mul_le_mul_of_nonneg_left hi hp0
    have hm := mul_le_mul_of_nonneg_right hp2 he0
    nlinarith

lemma log_norm_unit_add_le {u e : E} (hu : ‖u‖ = 1) (hne : u + e ≠ 0)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    Real.log ‖u + e‖ ≤ ⟪u, e⟫ + 2 * ‖e‖ ^ p := by
  have hn0 : 0 < ‖u + e‖ := norm_pos_iff.mpr hne
  have he0 := norm_nonneg e
  have hp0 : 0 ≤ p := by linarith
  have hep := Real.rpow_nonneg he0 p
  have hi : -‖e‖ ≤ ⟪u, e⟫ := by
    have h := neg_le_of_abs_le (abs_real_inner_le_norm u e)
    simpa [hu] using h
  by_cases he : ‖e‖ ≤ 1
  · have he2 : ‖e‖ ^ 2 ≤ ‖e‖ ^ p := by
      simpa only [Real.rpow_two] using
        Real.rpow_le_rpow_of_exponent_ge' he0 he hp0 hp2
    have hl := Real.log_le_sub_one_of_pos (sq_pos_of_pos hn0)
    rw [Real.log_pow] at hl
    have hn : ‖u + e‖ ^ 2 = 1 + 2 * ⟪u, e⟫ + ‖e‖ ^ 2 := by
      rw [norm_add_sq_real, hu]
      ring
    norm_num at hl
    nlinarith
  · have he1 : 1 ≤ ‖e‖ := le_of_lt (lt_of_not_ge he)
    have hepow : ‖e‖ ≤ ‖e‖ ^ p := by
      simpa using Real.rpow_le_rpow_of_exponent_le he1 hp
    have hn : ‖u + e‖ ≤ 1 + ‖e‖ := by simpa [hu] using norm_add_le u e
    have hl := Real.log_le_sub_one_of_pos hn0
    linarith

lemma norm_scaled_unit_add_rpow_le {u e : E} (hu : ‖u‖ = 1) {a p : ℝ}
    (ha : 0 < a) (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ‖a • u + e‖ ^ p ≤ a ^ p + p * a ^ (p - 1) * ⟪u, e⟫ + 6 * ‖e‖ ^ p := by
  have h := norm_unit_add_rpow_le (e := a⁻¹ • e) hu hp hp2
  have heq : a • (u + a⁻¹ • e) = a • u + e := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have hn : ‖a • u + e‖ ^ p = a ^ p * ‖u + a⁻¹ • e‖ ^ p := by
    rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos ha, Real.mul_rpow ha.le (norm_nonneg _)]
  have hn' : ‖a⁻¹ • e‖ ^ p = (a ^ p)⁻¹ * ‖e‖ ^ p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha),
      Real.mul_rpow (inv_nonneg.mpr ha.le) (norm_nonneg _), Real.inv_rpow ha.le]
  have hap : a ^ p ≠ 0 := (Real.rpow_pos_of_pos ha p).ne'
  have h' := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg ha.le p)
  rw [hn', real_inner_smul_right] at h'
  rw [hn, Real.rpow_sub_one ha.ne']
  convert h' using 1
  field_simp

lemma log_norm_scaled_unit_add_le {u e : E} (hu : ‖u‖ = 1) {a p : ℝ}
    (ha : 0 < a) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hne : a • u + e ≠ 0) :
    Real.log ‖a • u + e‖ - Real.log a ≤
      ⟪u, e⟫ / a + 2 * (‖e‖ / a) ^ p := by
  have heq : a • (u + a⁻¹ • e) = a • u + e := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  have hne' : u + a⁻¹ • e ≠ 0 := by
    intro h
    rw [h, smul_zero] at heq
    exact hne heq.symm
  have h := log_norm_unit_add_le hu hne' hp hp2
  have hn : ‖a • u + e‖ = a * ‖u + a⁻¹ • e‖ := by
    rw [← heq, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have hn' : ‖a⁻¹ • e‖ = ‖e‖ / a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    ring
  rw [hn, Real.log_mul ha.ne' (norm_ne_zero_iff.mpr hne'), add_sub_cancel_left]
  simpa only [real_inner_smul_right, hn', div_eq_mul_inv, mul_comm] using h

lemma norm_add_rpow_le {w e : E} {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    ‖w + e‖ ^ p ≤ ‖w‖ ^ p +
      p * ‖w‖ ^ (p - 1) * ⟪‖w‖⁻¹ • w, e⟫ + 6 * ‖e‖ ^ p := by
  by_cases hw : w = 0
  · simp only [hw, zero_add, norm_zero, inv_zero, zero_smul, inner_zero_left, mul_zero,
      add_zero]
    have h := Real.rpow_nonneg (norm_nonneg e) p
    have h0 := Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by rfl) p
    linarith
  · have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hu : ‖‖w‖⁻¹ • w‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw0), inv_mul_cancel₀ hw0.ne']
    have h := norm_scaled_unit_add_rpow_le (e := e) hu hw0 hp hp2
    simpa only [smul_smul, mul_inv_cancel₀ hw0.ne', one_smul] using h

lemma log_norm_add_le {w e : E} (hw : w ≠ 0) (hne : w + e ≠ 0)
    {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    Real.log ‖w + e‖ - Real.log ‖w‖ ≤
      ⟪w, e⟫ / ‖w‖ ^ 2 + 2 * (‖e‖ / ‖w‖) ^ p := by
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hu : ‖‖w‖⁻¹ • w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw0), inv_mul_cancel₀ hw0.ne']
  have heq : ‖w‖ • (‖w‖⁻¹ • w) = w := by
    rw [smul_smul, mul_inv_cancel₀ hw0.ne', one_smul]
  have h := log_norm_scaled_unit_add_le (e := e) hu hw0 hp hp2 (by simpa [heq] using hne)
  rw [heq, real_inner_smul_left] at h
  convert h using 1
  ring

lemma log_gap_of_sq_gap {a b η δ : ℝ} (ha : 0 < a) (ha2 : a ≤ 2)
    (hb : 0 < b) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hgap : b ^ 2 ≤ a ^ 2 - 2 * η * δ) :
    Real.log b - Real.log a ≤ -(η * δ) / 4 := by
  have ha_sq : 0 < a ^ 2 := sq_pos_of_pos ha
  have hb_sq : 0 < b ^ 2 := sq_pos_of_pos hb
  have hr := Real.log_le_sub_one_of_pos (div_pos hb_sq ha_sq)
  rw [Real.log_div hb_sq.ne' ha_sq.ne', Real.log_pow, Real.log_pow] at hr
  have hr' : 2 * (Real.log b - Real.log a) ≤ (b ^ 2 - a ^ 2) / a ^ 2 := by
    convert hr using 1
    · ring
    · field_simp
  have hm := (le_div_iff₀ ha_sq).mp hr'
  have hba : b ≤ a := by nlinarith [mul_nonneg hη hδ]
  have hl : Real.log b - Real.log a ≤ 0 := by
    exact sub_nonpos.mpr (Real.log_le_log hb hba)
  have ha4 : a ^ 2 ≤ 4 := by nlinarith
  have hprod := mul_le_mul_of_nonpos_right ha4 hl
  nlinarith

lemma shifted_rayleigh_log_gap {v Av : E} {η ell : ℝ}
    (hv : ‖v‖ = 1) (hη : 0 ≤ η) (hell : 0 ≤ ell) (hηell : η * ell ≤ 1)
    (hpos : 0 ≤ ⟪v, Av⟫) (hAv : ‖Av‖ ≤ ell) :
    Real.log ‖v + η • Av‖ - Real.log (1 + η * ell) ≤
      -(η * (ell - ⟪v, Av⟫)) / 4 := by
  have hi : ⟪v, Av⟫ ≤ ell := by
    have h := real_inner_le_norm v Av
    rw [hv, one_mul] at h
    exact h.trans hAv
  have hn : ‖v + η • Av‖ ^ 2 =
      1 + 2 * η * ⟪v, Av⟫ + η ^ 2 * ‖Av‖ ^ 2 := by
    rw [norm_add_sq_real, hv, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hη]
    ring
  have hn1 : 1 ≤ ‖v + η • Av‖ ^ 2 := by
    nlinarith [mul_nonneg hη hpos, mul_nonneg (sq_nonneg η) (sq_nonneg ‖Av‖)]
  have hn0 : 0 < ‖v + η • Av‖ := by
    nlinarith [norm_nonneg (v + η • Av)]
  have ha : 0 < 1 + η * ell := by nlinarith [mul_nonneg hη hell]
  apply log_gap_of_sq_gap ha (by linarith) hn0 hη (sub_nonneg.mpr hi)
  have hsq : ‖Av‖ ^ 2 ≤ ell ^ 2 := by nlinarith [norm_nonneg Av]
  have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg η)
  nlinarith

lemma shifted_rayleigh_log_noise {v Av e : E} {η ell p : ℝ}
    (hv : ‖v‖ = 1) (hη : 0 ≤ η) (hell : 0 ≤ ell) (hηell : η * ell ≤ 1)
    (hpos : 0 ≤ ⟪v, Av⟫) (hAv : ‖Av‖ ≤ ell)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (hne : v + η • Av + η • e ≠ 0) :
    Real.log ‖v + η • Av + η • e‖ - Real.log (1 + η * ell) ≤
      -(η * (ell - ⟪v, Av⟫)) / 4 +
      η * ⟪v + η • Av, e⟫ / ‖v + η • Av‖ ^ 2 + 2 * η ^ p * ‖e‖ ^ p := by
  have hn : 1 ≤ ‖v + η • Av‖ := by
    have hnorm := norm_add_sq_real v (η • Av)
    rw [hv, real_inner_smul_right] at hnorm
    nlinarith [sq_nonneg ‖η • Av‖, mul_nonneg hη hpos,
      norm_nonneg (v + η • Av)]
  have hn0 : 0 < ‖v + η • Av‖ := by linarith
  have hlog := log_norm_add_le (norm_ne_zero_iff.mp hn0.ne') hne hp hp2
  have hgap := shifted_rayleigh_log_gap hv hη hell hηell hpos hAv
  rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at hlog
  have hdiv : η * ‖e‖ / ‖v + η • Av‖ ≤ η * ‖e‖ := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith [mul_nonneg hη (norm_nonneg e)]
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ η * ‖e‖ / ‖v + η • Av‖)
    hdiv (by linarith : 0 ≤ p)
  rw [Real.mul_rpow hη (norm_nonneg e)] at hr
  linarith

lemma mixed_power_le {x y p : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hp : 1 ≤ p) :
    x ^ (p - 1) * y ≤ x ^ p + y ^ p := by
  have hp0 : p ≠ 0 := by linarith
  have heq (z : ℝ) (hz : 0 ≤ z) : z ^ (p - 1) * z = z ^ p := by
    have hh := Real.rpow_add_one' hz (show p - 1 + 1 ≠ 0 by simpa using hp0)
    simpa using hh.symm
  by_cases hxy : y ≤ x
  · have hh := mul_le_mul_of_nonneg_left hxy (Real.rpow_nonneg hx (p - 1))
    rw [heq x hx] at hh
    linarith [Real.rpow_nonneg hy p]
  · have hh := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hx (le_of_not_ge hxy) (by linarith : 0 ≤ p - 1)) hy
    rw [heq y hy] at hh
    linarith [Real.rpow_nonneg hx p]

lemma moment_linear_term_bound (w e : E) {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) :
    |p * ‖w‖ ^ (p - 1) * ⟪‖w‖⁻¹ • w, e⟫| ≤ 2 * (‖w‖ ^ p + ‖e‖ ^ p) := by
  by_cases hw : w = 0
  · simp only [hw, inv_zero, norm_zero, zero_smul, inner_zero_left, mul_zero, abs_zero]
    positivity
  · have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hn : ‖‖w‖⁻¹ • w‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw0), inv_mul_cancel₀ hw0.ne']
    have hi : |⟪‖w‖⁻¹ • w, e⟫| ≤ ‖e‖ := by
      simpa only [hn, one_mul] using abs_real_inner_le_norm (‖w‖⁻¹ • w) e
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ p * ‖w‖ ^ (p - 1))]
    have hh := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ p * ‖w‖ ^ (p - 1))
    have hm := mixed_power_le (norm_nonneg w) (norm_nonneg e) hp
    have hmp := mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ p)
    have hp' := mul_le_mul_of_nonneg_right hp2
      (by positivity : 0 ≤ ‖w‖ ^ p + ‖e‖ ^ p)
    nlinarith

lemma logarithm_of_squared_growth {a r d : ℝ} (ha : 0 < a) (hr : 0 ≤ r)
    (hd : 0 < d) (n : ℕ) (hg : (a ^ n / 2) ^ 2 / (2 * d) ≤ r ^ 2) :
    n * Real.log a - Real.log (2 * Real.sqrt (2 * d)) ≤ Real.log r := by
  have hs : 0 < Real.sqrt (2 * d) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ 2 * d by positivity)
  have hsq := (div_le_iff₀ (show 0 < 2 * d by positivity)).mp hg
  have hab : a ^ n / 2 ≤ r * Real.sqrt (2 * d) := by
    have hh : (r * Real.sqrt (2 * d)) ^ 2 = r ^ 2 * (2 * d) := by
      rw [mul_pow, hs2]
    nlinarith [mul_nonneg hr hs.le, pow_pos ha n]
  have hdiv : a ^ n / (2 * Real.sqrt (2 * d)) ≤ r := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hlog := Real.log_le_log (div_pos (pow_pos ha n) (by positivity)) hdiv
  rwa [Real.log_div (pow_ne_zero n ha.ne') (by positivity), Real.log_pow] at hlog

end LongTails.Proofs.HeavyTailedSpectralGeometry
