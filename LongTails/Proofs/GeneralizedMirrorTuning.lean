import LongTails.Algorithms.StochasticGeneralizedMirror
import LongTails.Proofs.GeneralizedMirrorCurvature
import LongTails.Proofs.StochasticCompositeGeneralizedConcentration

open LongTails.Setups.StochasticGeneralizedMirror
open LongTails.Algorithms.StochasticGeneralizedMirror

namespace LongTails.Proofs.GeneralizedMirrorTuning

lemma clipRadius_pos (q : Public) (hR : 0 < q.R) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    0 < clipRadius q := by
  unfold clipRadius
  positivity

lemma clipRadius_pilot (q : Public) (hR : 0 < q.R) (hσ : 0 ≤ q.σ) (hε : 0 < q.ε) :
    96 * q.σ ≤ clipRadius q := by
  unfold clipRadius
  have hp : 0 ≤ (256 * q.σ ^ q.α * q.R / q.ε) ^ (1 / (q.α - 1)) := by positivity
  have he : 0 ≤ q.ε / q.R := by positivity
  linarith

lemma clipRadius_bias (q : Public) (hR : 0 < q.R) (hσ : 0 ≤ q.σ)
    (hα : 1 < q.α) (hε : 0 < q.ε) :
    q.σ ^ q.α / (clipRadius q / 2) ^ (q.α - 1) ≤ q.ε / (256 * q.R) := by
  by_cases hzero : q.σ = 0
  · rw [hzero, Real.zero_rpow (by linarith : q.α ≠ 0), zero_div]
    positivity
  have hσpos : 0 < q.σ := lt_of_le_of_ne hσ (Ne.symm hzero)
  have he : 1048576 * q.σ ^ q.α * q.R * (1 / 4096) / q.ε =
      256 * q.σ ^ q.α * q.R / q.ε := by ring
  have hr : 2 * (256 * q.σ ^ q.α * q.R / q.ε) ^ (1 / (q.α - 1)) ≤ clipRadius q := by
    unfold clipRadius
    have hn : 0 ≤ 96 * q.σ + q.ε / q.R := by positivity
    linarith
  have ht := OracleTemplate.RobustGradient.heavy_clip_bias_tuning hσpos hα hR hε
    (by norm_num : (0 : ℝ) < 1 / 4096) (B := clipRadius q) (by rw [he]; exact hr)
  convert ht using 1
  congr 1
  ring

lemma initialWeight_pos (q : Public) (hR : 0 < q.R) (hΔ : 0 < q.Δ) (hε : 0 < q.ε) :
    0 < initialWeight q := by
  unfold initialWeight
  positivity

lemma initialWeight_gap (q : Public) (hΔ : 0 < q.Δ) (hε : 0 < q.ε) :
    initialWeight q * q.Δ ≤ q.R ^ 2 / 8 := by
  unfold initialWeight
  have hd : 0 < 8 * (q.Δ + q.ε) := by positivity
  apply (mul_le_mul_iff_left₀ hd).mp
  field_simp
  nlinarith [mul_nonneg (sq_nonneg q.R) hε.le]

lemma stepWeight_pos (q : Public) (hq : spec.valid q) {ell A : ℝ}
    (hell : 0 < ell) (hA : 0 < A) : 0 < stepWeight q ell A := by
  rcases hq with ⟨h0, h1, hR, _, hG, hσ, _, _, hε, _, _⟩
  have hc := clipRadius_pos q hR hσ hε
  unfold stepWeight noiseMoment
  positivity

lemma stepWeight_linear (q : Public) (hq : spec.valid q)
    {ell A : ℝ} (hell : 0 < ell) (hA : 0 < A) :
    1024 * q.L1 * q.R * stepWeight q ell A ≤ A := by
  have hw := stepWeight_pos q hq hell hA
  rcases hq with ⟨_, hL1, hR, _⟩
  have hc : 0 < 1024 * (1 + q.L1 * q.R) := by positivity
  have h := min_le_left (A / (1024 * (1 + q.L1 * q.R)))
    (min (Real.sqrt A / (128 * Real.sqrt (q.L0 + q.L1 * q.G)))
      (min (q.R / (65536 * clipRadius q * ell))
        (q.ε / (65536 * (noiseMoment q + q.ε ^ 2 / q.R ^ 2) * ell))))
  change stepWeight q ell A ≤ A / (1024 * (1 + q.L1 * q.R)) at h
  have hm := (le_div_iff₀ hc).mp h
  nlinarith

lemma stepWeight_base (q : Public) (hq : spec.valid q)
    {ell A : ℝ} (hell : 0 < ell) (hA : 0 < A) :
    16384 * (q.L0 + q.L1 * q.G) * stepWeight q ell A ^ 2 ≤ A := by
  have hw := stepWeight_pos q hq hell hA
  rcases hq with ⟨h0, h1, _, _, hG, _⟩
  have hB : 0 < q.L0 + q.L1 * q.G := by positivity
  have hc : 0 < 128 * Real.sqrt (q.L0 + q.L1 * q.G) := by positivity
  have h : stepWeight q ell A ≤ Real.sqrt A / (128 * Real.sqrt (q.L0 + q.L1 * q.G)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hm := (le_div_iff₀ hc).mp h
  have hs := pow_le_pow_left₀ (mul_nonneg hw.le hc.le) hm 2
  rw [mul_pow, mul_pow, Real.sq_sqrt hB.le, Real.sq_sqrt hA.le] at hs
  nlinarith

lemma stepWeight_motion (q : Public) (hq : spec.valid q)
    {ell A : ℝ} (hell : 0 < ell) :
    65536 * clipRadius q * ell * stepWeight q ell A ≤ q.R := by
  rcases hq with ⟨_, _, hR, _, _, hσ, _, _, hε, _⟩
  have hc := clipRadius_pos q hR hσ hε
  have h : stepWeight q ell A ≤ q.R / (65536 * clipRadius q * ell) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht := (le_div_iff₀ (by positivity : 0 < 65536 * clipRadius q * ell)).mp h
  nlinarith

lemma stepWeight_variance (q : Public) (hq : spec.valid q)
    {ell A : ℝ} (hell : 0 < ell) :
    65536 * (noiseMoment q + q.ε ^ 2 / q.R ^ 2) * ell * stepWeight q ell A ≤ q.ε := by
  rcases hq with ⟨_, _, hR, _, _, hσ, _, _, hε, _⟩
  have hc := clipRadius_pos q hR hσ hε
  have hv : 0 ≤ noiseMoment q := by unfold noiseMoment; positivity
  have hd : 0 < 65536 * (noiseMoment q + q.ε ^ 2 / q.R ^ 2) * ell := by positivity
  have h : stepWeight q ell A ≤ q.ε / (65536 * (noiseMoment q + q.ε ^ 2 / q.R ^ 2) * ell) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have ht := (le_div_iff₀ hd).mp h
  nlinarith

lemma stepWeight_relative (q : Public) (hq : spec.valid q)
    {ell A : ℝ} (hell : 0 < ell) (hA : 0 < A) :
    1024 * stepWeight q ell A ≤ A := by
  have hw := stepWeight_pos q hq hell hA
  rcases hq with ⟨_, h1, hR, _⟩
  have hd : 0 < 1024 * (1 + q.L1 * q.R) := by positivity
  have h : stepWeight q ell A ≤ A / (1024 * (1 + q.L1 * q.R)) := min_le_left _ _
  have ht := (le_div_iff₀ hd).mp h
  nlinarith [mul_nonneg (mul_nonneg h1 hR.le) hw.le]

lemma stepWeight_error (q : Public) (hq : spec.valid q)
    {ell A : ℝ} (hell : 1 ≤ ell) (hA : 0 < A) (e : Dual q)
    (he : ‖e‖ ≤ 3 * clipRadius q / 2) : stepWeight q ell A * ‖e‖ ≤ q.R / 32 := by
  have hell0 : 0 < ell := by linarith
  have hw := stepWeight_pos q hq hell0 hA
  have hm := stepWeight_motion q hq (A := A) hell0
  rcases hq with ⟨_, _, hR, _, _, hσ, _, _, hε, _⟩
  have hc := clipRadius_pos q hR hσ hε
  have hl := mul_le_mul_of_nonneg_right hell (mul_nonneg hc.le hw.le)
  have ht := mul_le_mul_of_nonneg_left he hw.le
  nlinarith

end LongTails.Proofs.GeneralizedMirrorTuning
