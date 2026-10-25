import LongTails.Proofs.HeavyTailedMomentBounds

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedSpectralMoments

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma action_moment_control (A : E →L[ℝ] E) (B : Ω → E →L[ℝ] E) (v : E)
    {p η ell σ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hη : 0 ≤ η)
    (hell : 0 ≤ ell) (hA : ‖A‖ ≤ ell)
    (hBi : Integrable (fun ω => B ω v) P) (hBm : ∫ ω, B ω v ∂P = A v)
    (hBp : Integrable (fun ω => ‖B ω v - A v‖ ^ p) P)
    (hBbound : (∫ ω, ‖B ω v - A v‖ ^ p ∂P) ≤ σ ^ p * ‖v‖ ^ p) :
    Integrable (fun ω => ‖v + η • B ω v‖ ^ p) P ∧
    (∫ ω, ‖v + η • B ω v‖ ^ p ∂P) ≤
      ((1 + η * ell) ^ p + 6 * η ^ p * σ ^ p) * ‖v‖ ^ p := by
  let e : Ω → E := fun ω => η • (B ω v - A v)
  let w := v + η • A v
  have he : Integrable e P := (hBi.sub (integrable_const _)).smul η
  have heq (ω : Ω) : ‖e ω‖ ^ p = η ^ p * ‖B ω v - A v‖ ^ p := by
    dsimp only [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη,
      Real.mul_rpow hη (norm_nonneg _)]
  have hep : Integrable (fun ω => ‖e ω‖ ^ p) P := by
    simp_rw [heq]
    exact hBp.const_mul _
  have hem : ∫ ω, e ω ∂P = 0 := by
    rw [show e = fun ω => η • (B ω v - A v) from rfl, integral_smul,
      integral_sub hBi (integrable_const _), integral_const, hBm]
    simp
  have hb := HeavyTailedMomentBounds.integral_norm_add_rpow_le (w := w) hp hp2 he hep hem
  have hsum (ω : Ω) : w + e ω = v + η • B ω v := by
    simp only [w, e, smul_sub]
    abel
  have hint := HeavyTailedMomentBounds.integrable_norm_add_rpow w
    (by linarith : 0 < p) he.aestronglyMeasurable hep
  simp_rw [hsum] at hint
  refine ⟨hint, ?_⟩
  simp_rw [hsum, heq] at hb
  rw [integral_const_mul] at hb
  have hn : ‖w‖ ≤ (1 + η * ell) * ‖v‖ := by
    have hav := A.le_opNorm v
    have havel := mul_le_mul_of_nonneg_right hA (norm_nonneg v)
    have hadd := norm_add_le v (η • A v)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη] at hadd
    dsimp [w]
    nlinarith [mul_le_mul_of_nonneg_left (hav.trans havel) hη]
  have hnp := Real.rpow_le_rpow (norm_nonneg w) hn (by linarith : 0 ≤ p)
  rw [Real.mul_rpow (by positivity : 0 ≤ 1 + η * ell) (norm_nonneg v)] at hnp
  have herr := mul_le_mul_of_nonneg_left hBbound
    (by positivity : 0 ≤ 6 * η ^ p)
  nlinarith

omit [IsProbabilityMeasure P] in
lemma projection_moment_control {e : Ω → E} (v : E) {p σ η : ℝ}
    (hp : 0 ≤ p) (hη : 0 ≤ η) (hv : ‖v‖ ≤ η)
    (he : Integrable e P) (hem : (∫ ω, e ω ∂P) = 0)
    (hep : Integrable (fun ω => ‖e ω‖ ^ p) P)
    (hb : (∫ ω, ‖e ω‖ ^ p ∂P) ≤ σ) :
    Integrable (fun ω => ⟪v, e ω⟫) P ∧
    (∫ ω, ⟪v, e ω⟫ ∂P) = 0 ∧
    Integrable (fun ω => ‖⟪v, e ω⟫‖ ^ p) P ∧
    (∫ ω, ‖⟪v, e ω⟫‖ ^ p ∂P) ≤ η ^ p * σ := by
  have hi : Integrable (fun ω => ⟪v, e ω⟫) P := he.const_inner v
  have hm : (∫ ω, ⟪v, e ω⟫ ∂P) = 0 := by rw [integral_inner he, hem, inner_zero_right]
  have hpoint (ω : Ω) : ‖⟪v, e ω⟫‖ ^ p ≤ η ^ p * ‖e ω‖ ^ p := by
    have hh : ‖⟪v, e ω⟫‖ ≤ η * ‖e ω‖ :=
      (norm_inner_le_norm v (e ω)).trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))
    have hpow := Real.rpow_le_rpow (norm_nonneg _) hh hp
    rwa [Real.mul_rpow hη (norm_nonneg _)] at hpow
  have hpi : Integrable (fun ω => ‖⟪v, e ω⟫‖ ^ p) P := by
    apply (hep.const_mul (η ^ p)).mono'
      ((Real.continuous_rpow_const hp).comp_aestronglyMeasurable hi.aestronglyMeasurable.norm)
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) p)]
    exact hpoint ω
  refine ⟨hi, hm, hpi, ?_⟩
  have hh := integral_mono hpi (hep.const_mul (η ^ p)) hpoint
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hη p))

omit [CompleteSpace E] in
lemma log_coefficient_norm {v Av : E} {η : ℝ} (hv : ‖v‖ = 1)
    (hη : 0 ≤ η) (hpos : 0 ≤ ⟪v, Av⟫) :
    ‖(η / ‖v + η • Av‖ ^ 2) • (v + η • Av)‖ ≤ η := by
  have hn : 1 ≤ ‖v + η • Av‖ := by
    have hh := norm_add_sq_real v (η • Av)
    rw [hv, real_inner_smul_right] at hh
    nlinarith [sq_nonneg ‖η • Av‖, mul_nonneg hη hpos, norm_nonneg (v + η • Av)]
  have hn0 : 0 < ‖v + η • Av‖ := by linarith
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hη (sq_nonneg _))]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
  nlinarith [mul_nonneg hη (show 0 ≤ ‖v + η • Av‖ ^ 2 - ‖v + η • Av‖ by nlinarith)]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace Ω] [IsProbabilityMeasure P] in
lemma inflated_power_bound {a b p : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) (n : ℕ) :
    (a ^ p + b) ^ n ≤ (a ^ n) ^ p * Real.exp (n * b) := by
  have ha0 : 0 ≤ a := by linarith
  have hap : 1 ≤ a ^ p := Real.one_le_rpow ha hp
  have he : 1 + b ≤ Real.exp b := by linarith [Real.add_one_le_exp b]
  have hc : a ^ p + b ≤ a ^ p * Real.exp b := by
    have hm := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg ha0 p)
    have hm' := mul_le_mul_of_nonneg_right hap hb
    nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ a ^ p + b) hc n
  rw [mul_pow, ← Real.exp_nat_mul] at hpow
  have heq : (a ^ p) ^ n = (a ^ n) ^ p := by
    rw [← Real.rpow_mul_natCast ha0, ← Real.rpow_natCast_mul ha0]
    congr 1
    ring
  rwa [heq] at hpow

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace Ω] [IsProbabilityMeasure P] in
lemma small_inflation_power {a b p : ℝ} (ha : 1 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p)
    (n : ℕ) (hsmall : n * b ≤ 1 / 2) : (a ^ p + b) ^ n ≤ (2 * a ^ n) ^ p := by
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at hh
    exact hh
  have hexp : Real.exp (n * b) ≤ 2 := by
    have hh := Real.exp_le_exp.mpr (hsmall.trans hlog)
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
  have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ p := by
    simpa using Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hp
  have hh := inflated_power_bound ha hb (by linarith : 0 ≤ p) n
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (pow_nonneg (by linarith : 0 ≤ a) n)]
  exact hh.trans (by nlinarith [Real.rpow_nonneg (pow_nonneg (by linarith : 0 ≤ a) n) p])


lemma shifted_oracle_moments (H : E →L[ℝ] E) (B : Ω → E →L[ℝ] E)
    (v : E) (s p σ : ℝ)
    (hi : Integrable (fun ω => B ω v) P)
    (hm : (∫ ω, B ω v ∂P) = H v)
    (hpi : Integrable (fun ω => ‖B ω v - H v‖ ^ p) P)
    (hb : (∫ ω, ‖B ω v - H v‖ ^ p ∂P) ≤ σ ^ p * ‖v‖ ^ p) :
    let A := s • ContinuousLinearMap.id ℝ E - H
    let C := fun ω => s • ContinuousLinearMap.id ℝ E - B ω
    Integrable (fun ω => C ω v) P ∧ (∫ ω, C ω v ∂P) = A v ∧
      Integrable (fun ω => ‖C ω v - A v‖ ^ p) P ∧
      (∫ ω, ‖C ω v - A v‖ ^ p ∂P) ≤ σ ^ p * ‖v‖ ^ p := by
  intro A C
  have heq (ω : Ω) : C ω v = s • v - B ω v := rfl
  have hnorm (ω : Ω) : ‖C ω v - A v‖ = ‖B ω v - H v‖ := by
    change ‖(s • v - B ω v) - (s • v - H v)‖ = _
    rw [show (s • v - B ω v) - (s • v - H v) = -(B ω v - H v) by abel, norm_neg]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [heq]
    exact (integrable_const _).sub hi
  · simp_rw [heq]
    rw [integral_sub (integrable_const _) hi, integral_const, hm]
    simp only [probReal_univ, one_smul]
    rfl
  · simpa only [hnorm] using hpi
  · simpa only [hnorm] using hb

end LongTails.Proofs.HeavyTailedSpectralMoments
