import LongTails.Proofs.HolderNoiseHiding
import LongTails.Proofs.QuasarHardAdmissible
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace LongTails.Proofs.HolderNoiseCoinExposure

open HolderNoiseHiding QuasarCoinLaw QuasarHardAdmissible

lemma exposure_sum (β : ℕ → Bool) (N : ℕ) :
    (exposure β N : ℝ) = ∑ t ∈ Finset.range N, if β t then (1 : ℝ) else 0 := by
  induction N with
  | zero => simp [exposure]
  | succ N ih =>
    rw [Finset.sum_range_succ, exposure, Nat.cast_add, ih]
    cases β N <;> simp

lemma coinIndicator_measurable (t : ℕ) : Measurable (fun β : ℕ → Bool => if β t then (1 : ℝ) else 0) := by
  exact (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp (measurable_pi_apply t)

lemma exposure_measurable (N : ℕ) : Measurable (fun β : ℕ → Bool => (exposure β N : ℝ)) := by
  simp_rw [exposure_sum]
  exact Finset.measurable_sum _ (fun t _ => coinIndicator_measurable t)

lemma coinIndicator_integrable (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ) :
    Integrable (fun β : ℕ → Bool => if β t then (1 : ℝ) else 0) (coinPath p hp hp1 : Measure _) := by
  apply Integrable.of_bound (coinIndicator_measurable t).aestronglyMeasurable 1
  filter_upwards [] with β
  cases β t <;> norm_num

lemma coinIndicator_integral (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ) :
    (∫ β : ℕ → Bool, (if β t then (1 : ℝ) else 0) ∂(coinPath p hp hp1 : Measure _)) = p := by
  have hf : Measurable (fun b : Bool => if b then (1 : ℝ) else 0) := measurable_of_countable _
  have he := integral_map (measurable_pi_apply t).aemeasurable hf.aestronglyMeasurable
    (μ := (coinPath p hp hp1 : Measure (ℕ → Bool)))
  rw [(coinPath_iid hp hp1).marginal t] at he
  rw [← he, coin_integral]
  simp

lemma exposure_integrable (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    Integrable (fun β : ℕ → Bool => (exposure β N : ℝ)) (coinPath p hp hp1 : Measure _) := by
  simp_rw [exposure_sum]
  exact integrable_finsetSum _ (fun t _ => coinIndicator_integrable p hp hp1 t)

lemma exposure_integral (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    (∫ β : ℕ → Bool, (exposure β N : ℝ) ∂(coinPath p hp hp1 : Measure _)) = N * p := by
  simp_rw [exposure_sum]
  rw [integral_finsetSum _ (fun t _ => coinIndicator_integrable p hp hp1 t)]
  simp [coinIndicator_integral]

end LongTails.Proofs.HolderNoiseCoinExposure
