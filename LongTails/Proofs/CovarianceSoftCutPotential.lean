import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace LongTails.Proofs.CovarianceSoftCutPotential

lemma positivePart_le_square_div (z a : ℝ) (ha : 0 < a) :
    max 0 (z - a) ≤ z ^ 2 / (4 * a) := by
  apply max_le
  · positivity
  · apply (le_div_iff₀ (by positivity : 0 < 4 * a)).2
    nlinarith [sq_nonneg (z - 2 * a)]

lemma shiftedHinge_le_noise_square (signal noise ε : ℝ) (hε : 0 < ε)
    (hsignal : signal ≤ -(3 * ε / 4)) :
    max 0 (signal + noise + ε / 2) ≤ noise ^ 2 / ε := by
  calc
    max 0 (signal + noise + ε / 2) ≤ max 0 (noise - ε / 4) := by
      apply max_le_max (le_refl 0)
      linarith
    _ ≤ noise ^ 2 / (4 * (ε / 4)) :=
      positivePart_le_square_div noise (ε / 4) (by positivity)
    _ = noise ^ 2 / ε := by congr 1; ring

lemma integrable_shiftedHinge {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (noise : Ω → ℝ) (signal ε : ℝ)
    (hε : 0 < ε) (hsignal : signal ≤ -(3 * ε / 4))
    (hnoise : Measurable noise) (hsquare : Integrable (fun ω => noise ω ^ 2) μ) :
    Integrable (fun ω => max 0 (signal + noise ω + ε / 2)) μ := by
  have hm : Measurable (fun ω => max 0 (signal + noise ω + ε / 2)) := by fun_prop
  exact (hsquare.div_const ε).mono_nonneg hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun _ => le_max_left _ _))
    (Filter.Eventually.of_forall (fun ω => shiftedHinge_le_noise_square signal (noise ω) ε hε hsignal))

lemma integral_shiftedHinge_le_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (noise : Ω → ℝ) (signal ε variance : ℝ)
    (hε : 0 < ε) (hsignal : signal ≤ -(3 * ε / 4))
    (hnoise : Measurable noise) (hsquare : Integrable (fun ω => noise ω ^ 2) μ)
    (hvariance : (∫ ω, noise ω ^ 2 ∂μ) ≤ variance) :
    (∫ ω, max 0 (signal + noise ω + ε / 2) ∂μ) ≤ variance / ε := by
  have hbound : ∀ ω, max 0 (signal + noise ω + ε / 2) ≤ noise ω ^ 2 / ε :=
    fun ω => shiftedHinge_le_noise_square signal (noise ω) ε hε hsignal
  have hmeas : Measurable (fun ω => max 0 (signal + noise ω + ε / 2)) := by
    fun_prop
  have hint : Integrable (fun ω => max 0 (signal + noise ω + ε / 2)) μ :=
    (hsquare.div_const ε).mono_nonneg hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => le_max_left _ _))
      (Filter.Eventually.of_forall hbound)
  calc
    (∫ ω, max 0 (signal + noise ω + ε / 2) ∂μ) ≤
        ∫ ω, noise ω ^ 2 / ε ∂μ :=
      integral_mono hint (hsquare.div_const ε) hbound
    _ = (∫ ω, noise ω ^ 2 ∂μ) / ε := integral_div ε _
    _ ≤ variance / ε := div_le_div_of_nonneg_right hvariance hε.le

lemma stoppedLoss_failure_bound (loss horizon entropy : ℝ)
    (hentropy : entropy ≤ horizon / 24)
    (hloss : horizon / 6 - entropy ≤ loss) :
    horizon / 8 ≤ loss := by
  linarith

lemma loss_lower_of_mass_bounds (target initial mass loss horizon : ℝ)
    (htarget : 0 < target) (hinitial : 0 < initial)
    (hlower : target * Real.exp (-loss) ≤ mass)
    (hupper : mass ≤ initial * Real.exp (-horizon / 6)) :
    horizon / 6 - (Real.log initial - Real.log target) ≤ loss := by
  have h := Real.log_le_log (mul_pos htarget (Real.exp_pos _)) (hlower.trans hupper)
  rw [Real.log_mul htarget.ne' (Real.exp_ne_zero _), Real.log_exp,
    Real.log_mul hinitial.ne' (Real.exp_ne_zero _), Real.log_exp] at h
  linarith

end LongTails.Proofs.CovarianceSoftCutPotential
