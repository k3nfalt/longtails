import LongTails.Algorithms.StochasticQuasarAcceleration
import LongTails.Proofs.StochasticQuasarEstimatorTuning
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set
open scoped BigOperators

namespace OracleTemplate.StochasticQuasar

lemma exp_unit_chord {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + 2 * x := by
  have hh := convexOn_exp.2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ))
    (by linarith : 0 ≤ 1 - x) hx (by ring : (1 - x) + x = 1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at hh
  nlinarith [Real.exp_one_lt_three]

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} [IsProbabilityMeasure μ]

lemma bounded_work_exp_integrable {W : S → ℝ} (hW : Measurable W)
    (hb : ∀ s, 0 ≤ W s ∧ W s ≤ 1) : Integrable (fun s => Real.exp (W s)) μ := by
  apply Integrable.of_bound (Real.continuous_exp.measurable.comp hW).aestronglyMeasurable 3
  filter_upwards with s
  simp only [Function.comp_apply]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact (exp_unit_chord (hb s).1 (hb s).2).trans (by linarith [(hb s).2])

lemma bounded_work_exp_moment {W : S → ℝ} {c : ℝ} (hW : Measurable W)
    (hb : ∀ s, 0 ≤ W s ∧ W s ≤ 1) (hmean : (∫ s, W s ∂μ) ≤ c) :
    (∫ s, Real.exp (W s) ∂μ) ≤ Real.exp (2 * c) := by
  have hi : Integrable W μ := by
    apply Integrable.of_bound hW.aestronglyMeasurable 1
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_of_nonneg (hb s).1]
    exact (hb s).2
  have hexp := bounded_work_exp_integrable (μ := μ) hW hb
  have hm := integral_mono hexp ((integrable_const (1 : ℝ)).add (hi.const_mul 2))
    (fun s => exp_unit_chord (hb s).1 (hb s).2)
  simp only [Pi.add_apply] at hm
  rw [integral_add (integrable_const (1 : ℝ)) (hi.const_mul 2), integral_const_mul] at hm
  simp only [integral_const, probReal_univ, one_smul] at hm
  exact hm.trans ((by linarith : 1 + 2 * (∫ s, W s ∂μ) ≤ 1 + 2 * c).trans
    (by simpa only [add_comm] using Real.add_one_le_exp (2 * c)))

lemma bounded_work_sum_exp_integrable {W : S → ℝ} (hW : Measurable W)
    (hb : ∀ s, 0 ≤ W s ∧ W s ≤ 1) (k : ℕ) :
    Integrable (fun samples : Fin k → S => Real.exp (∑ i, W (samples i)))
      (Measure.pi fun _ : Fin k => μ) := by
  simp only [Real.exp_sum]
  exact Integrable.fintype_prod (fun _ : Fin k => bounded_work_exp_integrable (μ := μ) hW hb)

lemma bounded_work_sum_tail {W : S → ℝ} {c : ℝ} (hW : Measurable W)
    (hb : ∀ s, 0 ≤ W s ∧ W s ≤ 1) (hmean : (∫ s, W s ∂μ) ≤ c) (k : ℕ) (t : ℝ) :
    (Measure.pi fun _ : Fin k => μ) {samples | 2 * k * c + t < ∑ i, W (samples i)} ≤
      ENNReal.ofReal (Real.exp (-t)) := by
  have hi := (bounded_work_sum_exp_integrable (μ := μ) hW hb k).const_mul
    (Real.exp (-(2 * k * c + t)))
  have hn : 0 ≤ᵐ[Measure.pi fun _ : Fin k => μ]
      (fun samples => Real.exp (-(2 * k * c + t)) * Real.exp (∑ i, W (samples i))) :=
    Filter.Eventually.of_forall (fun _ => by positivity)
  have hh := hi.measure_le_integral hn
    (s := {samples | 2 * k * c + t < ∑ i, W (samples i)}) (by
      intro samples hs
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by change 2 * k * c + t < ∑ i, W (samples i) at hs; linarith))
  rw [integral_const_mul] at hh
  have hprod : (∫ samples : Fin k → S, Real.exp (∑ i, W (samples i))
      ∂Measure.pi (fun _ : Fin k => μ)) = (∫ s, Real.exp (W s) ∂μ) ^ k := by
    simp only [Real.exp_sum]
    simpa only [Fintype.card_fin] using
      (integral_fintype_prod_eq_pow (ι := Fin k) (μ := μ) (fun s => Real.exp (W s)))
  rw [hprod] at hh
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  have hpow := pow_le_pow_left₀ (integral_nonneg (μ := μ) (fun s => (Real.exp_pos (W s)).le))
    (bounded_work_exp_moment hW hb hmean) k
  have hm := mul_le_mul_of_nonneg_left hpow (Real.exp_pos (-(2 * k * c + t))).le
  convert hm using 1
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

lemma bounded_cost_sum_tail {W : S → ℝ} {M C : ℝ} (hM : 0 < M) (hW : Measurable W)
    (hb : ∀ s, 0 ≤ W s ∧ W s ≤ M) (hmean : (∫ s, W s ∂μ) ≤ C) (k : ℕ) (t : ℝ) :
    (Measure.pi fun _ : Fin k => μ) {samples | 2 * k * C + M * t < ∑ i, W (samples i)} ≤
      ENNReal.ofReal (Real.exp (-t)) := by
  have hnorm (s : S) : 0 ≤ W s / M ∧ W s / M ≤ 1 :=
    ⟨div_nonneg (hb s).1 hM.le, (div_le_one hM).mpr (hb s).2⟩
  have hmean' : (∫ s, W s / M ∂μ) ≤ C / M := by
    rw [integral_div]
    exact div_le_div_of_nonneg_right hmean hM.le
  have hh := bounded_work_sum_tail (hW.div_const M) hnorm hmean' k t
  have he (samples : Fin k → S) :
      2 * k * (C / M) + t < ∑ i, W (samples i) / M ↔
        2 * k * C + M * t < ∑ i, W (samples i) := by
    rw [← Finset.sum_div, lt_div_iff₀ hM]
    have ha : (2 * k * (C / M) + t) * M = 2 * k * C + M * t := by
      field_simp
    rw [ha]
  simpa only [he] using hh

lemma acceleration_expected_calls {L v : ℝ} (hL : 0 < L) (hv : 0 < v) (β σ D : ℝ) :
    (∫ j : Fin (estimatorDepth v β + 1), (accelerationJumpCalls L σ D v β j.val : ℝ)
      ∂(mlmcLevelLaw (estimatorDepth v β) : Measure _)) ≤
      12 * innerStageCount D (estimatorRadius L v β) + 17 +
        3840 * (estimatorDepth v β + 1 : ℝ) ^ 2 * σ ^ 2 / v ^ 2 := by
  have hh := tuned_estimator_expected_calls hL hv β σ D
  simp only [accelerationJumpCalls, Nat.cast_add, Nat.cast_one]
  rw [integral_add (integrable_const (1 : ℝ)) Integrable.of_finite]
  simp only [integral_const, probReal_univ, one_smul]
  linarith

lemma acceleration_max_calls {L v β : ℝ} (hL : 0 < L) (hv : 0 < v) (hβ : 0 < β)
    (σ D : ℝ) (j : Fin (estimatorDepth v β + 1)) :
    (accelerationJumpCalls L σ D v β j.val : ℝ) ≤
      12 * innerStageCount D (estimatorRadius L v β) + 8 * (estimatorDepth v β + 1 : ℝ) + 1 +
        40960 * (estimatorDepth v β + 1 : ℝ) * σ ^ 2 * (1 / v ^ 2 + 1 / β ^ 2) := by
  have hh := tuned_estimator_max_calls hL hv hβ σ D j
  simp only [accelerationJumpCalls, Nat.cast_add, Nat.cast_one]
  linarith

lemma acceleration_work_tail {L v β : ℝ} (hL : 0 < L) (hv : 0 < v) (hβ : 0 < β)
    (σ D : ℝ) (k : ℕ) (t : ℝ) :
    let C := 12 * innerStageCount D (estimatorRadius L v β) + 17 +
      3840 * (estimatorDepth v β + 1 : ℝ) ^ 2 * σ ^ 2 / v ^ 2
    let M := 12 * innerStageCount D (estimatorRadius L v β) + 8 * (estimatorDepth v β + 1 : ℝ) + 1 +
      40960 * (estimatorDepth v β + 1 : ℝ) * σ ^ 2 * (1 / v ^ 2 + 1 / β ^ 2)
    (Measure.pi fun _ : Fin k => (mlmcLevelLaw (estimatorDepth v β) : Measure (Fin (estimatorDepth v β + 1))))
      {samples : Fin k → Fin (estimatorDepth v β + 1) | 2 * k * C + M * t < ∑ i, (accelerationJumpCalls L σ D v β (samples i).val : ℝ)} ≤
        ENNReal.ofReal (Real.exp (-t)) := by
  dsimp only
  apply bounded_cost_sum_tail (by positivity) (measurable_of_finite _)
    (fun j => ⟨Nat.cast_nonneg _, acceleration_max_calls hL hv hβ σ D j⟩)
    (acceleration_expected_calls hL hv β σ D)

end OracleTemplate.StochasticQuasar
