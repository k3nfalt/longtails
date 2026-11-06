import LongTails.Proofs.CovarianceAcceleratedClipping
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace LongTails.Proofs.CovarianceAcceleratedGaussian

lemma exponential_tail_majorant {m x t : ℝ} (hm : |m| ≤ 1 / 4) (ht : 1 ≤ t) :
    (if 1 / 2 < |m + x| then Real.exp (1 + |m + x|) else 0) ≤
      Real.exp (3 / 2 - t / 4) * (Real.exp (t * x) + Real.exp (-t * x)) := by
  split_ifs with h
  · have hx : (1 / 4 : ℝ) ≤ |x| := by
      have := abs_add_le m x
      linarith
    have hp := mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hx)
    have he : 1 + |m + x| ≤ (3 / 2 - t / 4) + t * |x| := by
      have := abs_add_le m x
      nlinarith
    have hab : Real.exp (t * |x|) ≤ Real.exp (t * x) + Real.exp (-t * x) := by
      by_cases hpos : 0 ≤ x
      · rw [abs_of_nonneg hpos]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
      · rw [abs_of_neg (lt_of_not_ge hpos), mul_neg, ← neg_mul]
        exact le_add_of_nonneg_left (Real.exp_pos _).le
    calc
      Real.exp (1 + |m + x|) ≤ Real.exp ((3 / 2 - t / 4) + t * |x|) :=
        Real.exp_le_exp.mpr he
      _ = Real.exp (3 / 2 - t / 4) * Real.exp (t * |x|) := Real.exp_add _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hab (Real.exp_pos _).le
  · positivity

lemma shifted_subgaussian_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℝ} {v : ℝ≥0} {m : ℝ}
    (hX : Measurable X) (hsub : HasSubgaussianMGF X v P)
    (hv : 0 < (v : ℝ)) (hvsmall : (v : ℝ) ≤ 1 / 4) (hm : |m| ≤ 1 / 4) :
    Integrable (fun ω => if 1 / 2 < |m + X ω| then Real.exp (1 + |m + X ω|)
      else 0) P ∧
    (∫ ω, if 1 / 2 < |m + X ω| then Real.exp (1 + |m + X ω|) else 0 ∂P) ≤
      18 * Real.exp (-1 / (32 * (v : ℝ))) := by
  let t : ℝ := 1 / (4 * (v : ℝ))
  have ht : 1 ≤ t := (le_div_iff₀ (by positivity : 0 < 4 * (v : ℝ))).mpr (by
    nlinarith)
  have htpos := hsub.integrable_exp_mul t
  have htneg := hsub.integrable_exp_mul (-t)
  have hb : Integrable (fun ω => Real.exp (3 / 2 - t / 4) *
      (Real.exp (t * X ω) + Real.exp (-t * X ω))) P :=
    (htpos.add htneg).const_mul _
  have hmeas : Measurable (fun ω => if 1 / 2 < |m + X ω| then
      Real.exp (1 + |m + X ω|) else 0) := by
    have habs : Measurable (fun ω => |m + X ω|) := by fun_prop
    apply Measurable.ite (measurableSet_lt measurable_const habs)
    · fun_prop
    · exact measurable_const
  have hi : Integrable (fun ω => if 1 / 2 < |m + X ω| then
      Real.exp (1 + |m + X ω|) else 0) P := hb.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
      exact exponential_tail_majorant hm ht)
  refine ⟨hi, ?_⟩
  have h := integral_mono hi hb (fun ω => exponential_tail_majorant (x := X ω) hm ht)
  rw [integral_const_mul, integral_add htpos htneg] at h
  have hp := hsub.mgf_le t
  have hn := hsub.mgf_le (-t)
  simp only [mgf, neg_sq] at hp hn
  have hs : (∫ ω, Real.exp (t * X ω) ∂P) + (∫ ω, Real.exp (-t * X ω) ∂P) ≤
      2 * Real.exp ((v : ℝ) * t ^ 2 / 2) := by linarith
  have hh := h.trans (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le)
  have he : (3 / 2 - t / 4) + (v : ℝ) * t ^ 2 / 2 =
      3 / 2 + (-1 / (32 * (v : ℝ))) := by
    dsimp [t]
    field_simp
    ring
  have hre : Real.exp (3 / 2 - t / 4) * (2 * Real.exp ((v : ℝ) * t ^ 2 / 2)) =
      2 * Real.exp (3 / 2) * Real.exp (-1 / (32 * (v : ℝ))) := by
    calc
      _ = 2 * Real.exp ((3 / 2 - t / 4) + (v : ℝ) * t ^ 2 / 2) := by
        rw [Real.exp_add]
        ring
      _ = _ := by rw [he, Real.exp_add]; ring
  rw [hre] at hh
  have hconst : Real.exp (3 / 2 : ℝ) ≤ 9 :=
    (Real.exp_le_exp.mpr (by norm_num : (3 / 2 : ℝ) ≤ 2)).trans
      CovarianceAcceleratedClipping.exp_two_le_nine
  exact hh.trans (mul_le_mul_of_nonneg_right (by linarith : 2 * Real.exp (3 / 2 : ℝ) ≤ 18)
    (Real.exp_pos _).le)

lemma gaussian_law_subgaussian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {v : ℝ≥0}
    (h : HasLaw X (gaussianReal 0 v) P) : HasSubgaussianMGF X v P where
  integrable_exp_mul t := by
    apply mgf_pos_iff.mp
    rw [mgf_gaussianReal h]
    exact Real.exp_pos _
  mgf_le t := by simp [mgf_gaussianReal h]

lemma gaussian_dual_law {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) :
    HasLaw L (gaussianReal 0 (Real.toNNReal (‖L‖ ^ 2))) (stdGaussian E) := by
  refine ⟨by fun_prop, ?_⟩
  simpa only [integral_strongDual_stdGaussian, variance_dual_stdGaussian] using
    IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) L

lemma gaussian_dual_subgaussian {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) {v : ℝ≥0} (hv : ‖L‖ ^ 2 ≤ (v : ℝ)) :
    HasSubgaussianMGF L v (stdGaussian E) := by
  have hlaw := gaussian_dual_law L
  have hs := gaussian_law_subgaussian hlaw
  refine ⟨hs.integrable_exp_mul, fun t => (hs.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  rw [Real.coe_toNNReal _ (sq_nonneg _)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv (sq_nonneg t)) (by norm_num)

lemma gaussian_dual_second_moment {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (L : StrongDual ℝ E) : (∫ z, (L z) ^ 2 ∂stdGaussian E) = ‖L‖ ^ 2 := by
  have h := variance_dual_stdGaussian L
  rw [variance_eq_integral (by fun_prop), integral_strongDual_stdGaussian] at h
  simpa using h

lemma gaussian_noise_energy {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] (P : Measure Ω) [SFinite P] {ξ : Ω → E}
    (hξ : Measurable ξ) (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) :
    Integrable (fun q : Ω × E => ⟪ξ q.1, q.2⟫ ^ 2) (P.prod (stdGaussian E)) ∧
      (∫ z, ∫ ω, ⟪ξ ω, z⟫ ^ 2 ∂P ∂stdGaussian E) = (∫ ω, ‖ξ ω‖ ^ 2 ∂P) := by
  have hm (ω : Ω) : (∫ z, ⟪ξ ω, z⟫ ^ 2 ∂stdGaussian E) = ‖ξ ω‖ ^ 2 := by
    simpa using gaussian_dual_second_moment (innerSL ℝ (ξ ω))
  have hi : Integrable (fun q : Ω × E => ⟪ξ q.1, q.2⟫ ^ 2)
      (P.prod (stdGaussian E)) := by
    apply (integrable_prod_iff (by fun_prop)).mpr
    constructor
    · exact Filter.Eventually.of_forall fun ω =>
        (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ (ξ ω)) 2 (by norm_num)).integrable_sq
    · simpa only [Real.norm_eq_abs, abs_sq, hm] using h2
  refine ⟨hi, ?_⟩
  rw [← integral_integral_swap hi]
  simp_rw [hm]

end LongTails.Proofs.CovarianceAcceleratedGaussian
