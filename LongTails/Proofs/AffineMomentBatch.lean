import LongTails.Proofs.PowerMirrorMoments
import LongTails.Proofs.AffineGradientEstimator
import Mathlib.Analysis.MeanInequalitiesPow

open MeasureTheory
open scoped BigOperators
open LongTails.Proofs.PowerMirrorMoments

namespace LongTails.Proofs.AffineMomentBatch

lemma add_power_le_four {p a b : ℝ} (hp : 0 ≤ p) (hp2 : p ≤ 2)
    (ha : 0 ≤ a) (hb : 0 ≤ b) : (a + b) ^ p ≤ 4 * (a ^ p + b ^ p) := by
  have ht : a + b ≤ 2 * max a b := by grind
  have hpow := Real.rpow_le_rpow (add_nonneg ha hb) ht hp
  rw [Real.mul_rpow (by norm_num) (le_trans ha (le_max_left _ _))] at hpow
  have h2 : (2 : ℝ) ^ p ≤ 4 := by
    simpa only [Real.rpow_two, show (2 : ℝ) ^ 2 = 4 by norm_num] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp2
  have hm : (max a b) ^ p ≤ a ^ p + b ^ p := by
    rcases le_total a b with h | h
    · rw [max_eq_right h]; exact le_add_of_nonneg_left (Real.rpow_nonneg ha p)
    · rw [max_eq_left h]; exact le_add_of_nonneg_right (Real.rpow_nonneg hb p)
  exact hpow.trans ((mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg
    (le_trans ha (le_max_left _ _)) p)).trans (mul_le_mul_of_nonneg_left hm (by norm_num)))

lemma affine_scale_bound {p σ σ0 ν Q : ℝ} (hp : 1 ≤ p) (hσ : 0 ≤ σ)
    (hσ0 : 0 ≤ σ0) (hν : 0 < ν) (hQ : 0 ≤ Q) :
    σ0 ^ p + σ ^ p * Q ^ p ≤ (σ + σ0 / ν) ^ p * (Q + ν) ^ p := by
  have hS : 0 ≤ σ + σ0 / ν := by positivity
  have h0 : σ0 ≤ (σ + σ0 / ν) * ν := by
    rw [add_mul, div_mul_cancel₀ _ hν.ne']
    nlinarith [mul_nonneg hσ hν.le]
  have h1 : σ * Q ≤ (σ + σ0 / ν) * Q := by
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hQ
  have h0p := Real.rpow_le_rpow hσ0 h0 (by linarith : 0 ≤ p)
  have h1p := Real.rpow_le_rpow (mul_nonneg hσ hQ) h1 (by linarith : 0 ≤ p)
  rw [Real.mul_rpow hS hν.le] at h0p
  rw [Real.mul_rpow hσ hQ, Real.mul_rpow hS hQ] at h1p
  have hsum := mul_le_mul_of_nonneg_left (Real.add_rpow_le_rpow_add hQ hν.le hp)
    (Real.rpow_nonneg hS p)
  nlinarith only [h0p, h1p, hsum]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma affine_means_failure {p σ α ν : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hν : 0 < ν)
    {V : Ω → E} (hV : Measurable V) (hVi : Integrable V P) (q : E)
    (hmean : (∫ ω, V ω ∂P) = q) (hVp : Integrable (fun ω => ‖V ω - q‖ ^ p) P)
    (hm : (∫ ω, ‖V ω - q‖ ^ p ∂P) ≤ σ ^ p * (‖q‖ + ν) ^ p)
    (hα : 0 < α) (hα1 : α ≤ 1 / 2) (k n : ℕ) (hn : 0 < n)
    (hsize : 6 / (n : ℝ) ^ (p - 1) * σ ^ p ≤ (α / 8) ^ p / 16) :
    (Measure.pi fun _ : Fin k => Measure.pi fun _ : Fin n => P)
      {ξ | 3 * α * (‖q‖ + ν) <
        ‖OracleTemplate.AffineGradient.center α ν
          (fun i => (1 / (n : ℝ)) • ∑ j, V (ξ i j)) - q‖} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  have hp0 : 0 < p := by linarith
  have h := finite_mean_centered_power hp hp2 hV hVi q hVp hmean n hn
  let W := fun ξ : Fin n → Ω => (1 / (n : ℝ)) • ∑ j, V (ξ j)
  have hbound : (∫ ξ, ‖W ξ - q‖ ^ p ∂Measure.pi (fun _ : Fin n => P)) ≤
      (6 / (n : ℝ) ^ (p - 1) * σ ^ p) * (‖q‖ + ν) ^ p := by
    refine h.2.trans ?_
    have ht := mul_le_mul_of_nonneg_left hm (show 0 ≤ 6 / (n : ℝ) ^ (p - 1) by positivity)
    simpa only [mul_assoc] using ht
  apply OracleTemplate.AffineGradient.center_failure_probability
    (P := Measure.pi fun _ : Fin n => P) (V := W) (by dsimp [W]; fun_prop)
    q hν.le hα.le hα1 ?_ k
  have ht := norm_tail_le_power hp0 (show 0 < α * (‖q‖ + ν) / 8 by positivity) h.1 hbound
  apply ht.trans
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (show 0 < α * (‖q‖ + ν) / 8 by positivity) p)).mpr
  have hs := mul_le_mul_of_nonneg_right hsize (Real.rpow_nonneg (by positivity : 0 ≤ ‖q‖ + ν) p)
  have he : (α * (‖q‖ + ν) / 8) ^ p = (α / 8) ^ p * (‖q‖ + ν) ^ p := by
    rw [show α * (‖q‖ + ν) / 8 = (α / 8) * (‖q‖ + ν) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
  rw [he]
  nlinarith

lemma raw_mean_moment {p σ ν : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hν : 0 ≤ ν)
    {V : Ω → E} (hV : Measurable V) (hVi : Integrable V P) (q : E)
    (hmean : (∫ ω, V ω ∂P) = q) (hVp : Integrable (fun ω => ‖V ω - q‖ ^ p) P)
    (hm : (∫ ω, ‖V ω - q‖ ^ p ∂P) ≤ σ ^ p * (‖q‖ + ν) ^ p)
    (n : ℕ) (hn : 0 < n) (hsize : 6 / (n : ℝ) ^ (p - 1) * σ ^ p ≤ 1 / 8) :
    Integrable (fun ξ : Fin n → Ω => ‖(1 / (n : ℝ)) • ∑ i, V (ξ i)‖ ^ p)
      (Measure.pi fun _ : Fin n => P) ∧
    (∫ ξ : Fin n → Ω, ‖(1 / (n : ℝ)) • ∑ i, V (ξ i)‖ ^ p
      ∂Measure.pi (fun _ : Fin n => P)) ≤ 4 * (‖q‖ ^ p + ν ^ p) := by
  have hc := finite_mean_centered_power hp hp2 hV hVi q hVp hmean n hn
  have hmi : (∫ ξ : Fin n → Ω, (1 / (n : ℝ)) • ∑ i, V (ξ i)
      ∂Measure.pi (fun _ : Fin n => P)) = q := (finite_mean_mean hVi n hn).trans hmean
  have hr := raw_power_of_centered hp hp2
    (show Measurable (fun ξ : Fin n → Ω => (1 / (n : ℝ)) • ∑ i, V (ξ i)) by fun_prop)
    (finite_mean_integrable hVi n) q hc.1 hmi
  refine ⟨hr.1, hr.2.trans ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hm (show 0 ≤ 6 / (n : ℝ) ^ (p - 1) by positivity)
  have h2 := mul_le_mul_of_nonneg_right hsize (Real.rpow_nonneg (by positivity : 0 ≤ ‖q‖ + ν) p)
  have h3 := add_power_le_four (by linarith : 0 ≤ p) hp2 (norm_nonneg q) hν
  nlinarith only [hc.2, h1, h2, h3, Real.rpow_nonneg hν p]

end LongTails.Proofs.AffineMomentBatch
