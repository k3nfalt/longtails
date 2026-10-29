import LongTails.Algorithms.CovarianceSoftCut
import LongTails.Proofs.LogConcaveHalfspaces
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.CovarianceSoftCutDensity

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut

@[fun_prop] lemma continuous_hinge (q : Params) (α : ℝ) (cut : Cut q) : Continuous (hinge q α cut) := by
  unfold hinge
  fun_prop

@[fun_prop] lemma continuous_lossSum (q : Params) (α : ℝ) (cuts : List (Cut q)) :
    Continuous (lossSum q α cuts) := by
  unfold lossSum
  fun_prop

@[fun_prop] lemma continuous_coreWeight (q : Params) (α η : ℝ) (cuts : List (Cut q)) :
    Continuous (coreWeight q α η cuts) := by
  unfold coreWeight
  fun_prop

lemma weight_eq_indicator (q : Params) (α η : ℝ) (cuts : List (Cut q)) :
    weight q α η cuts =
      (Metric.closedBall (0 : Space q) (2 * q.R)).indicator (coreWeight q α η cuts) := by
  ext y
  simp [weight, Set.indicator, Metric.mem_closedBall, dist_zero_right]

lemma weight_nonneg (q : Params) (α η : ℝ) (cuts : List (Cut q)) (y : Space q) :
    0 ≤ weight q α η cuts y := by
  unfold weight coreWeight
  split_ifs <;> positivity

lemma integrable_weight (q : Params) (α η : ℝ) (cuts : List (Cut q)) :
    Integrable (weight q α η cuts) := by
  rw [weight_eq_indicator, integrable_indicator_iff measurableSet_closedBall]
  exact (continuous_coreWeight q α η cuts).continuousOn.integrableOn_compact (isCompact_closedBall _ _)

lemma support_weight (q : Params) (α η : ℝ) (cuts : List (Cut q)) :
    Function.support (weight q α η cuts) = Metric.closedBall (0 : Space q) (2 * q.R) := by
  ext y
  simp [Function.mem_support, weight, coreWeight, Metric.mem_closedBall, dist_zero_right]

lemma mass_pos (q : Params) (hR : 0 < q.R) (α η : ℝ) (cuts : List (Cut q)) :
    0 < mass q α η cuts := by
  apply (integral_pos_iff_support_of_nonneg (weight_nonneg q α η cuts)
    (integrable_weight q α η cuts)).mpr
  rw [support_weight]
  exact lt_of_lt_of_le (Metric.measure_ball_pos volume 0 (by positivity : 0 < 2 * q.R))
    (measure_mono Metric.ball_subset_closedBall)

lemma hinge_convex (q : Params) (α : ℝ) (cut : Cut q) :
    ConvexOn ℝ Set.univ (hinge q α cut) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  change max 0 (⟪cut.1, a • x + b • y - cut.2⟫ + α / 2) ≤
    a * max 0 (⟪cut.1, x - cut.2⟫ + α / 2) +
      b * max 0 (⟪cut.1, y - cut.2⟫ + α / 2)
  apply max_le
  · positivity
  · have hv : a • x + b • y - cut.2 = a • (x - cut.2) + b • (y - cut.2) := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
    rw [hv, inner_add_right, inner_smul_right, inner_smul_right]
    have hα : α / 2 = a * (α / 2) + b * (α / 2) := by rw [← add_mul, hab, one_mul]
    calc
      a * ⟪cut.1, x - cut.2⟫ + b * ⟪cut.1, y - cut.2⟫ + α / 2 =
          a * (⟪cut.1, x - cut.2⟫ + α / 2) +
            b * (⟪cut.1, y - cut.2⟫ + α / 2) := by linarith
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_max_right _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)

lemma lossSum_convex (q : Params) (α : ℝ) (cuts : List (Cut q)) :
    ConvexOn ℝ Set.univ (lossSum q α cuts) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [lossSum, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  exact (hinge_convex q α (cuts.getD i (0, 0))).2 hx hy ha hb hab

lemma coreWeight_logConcave (q : Params) (α η : ℝ) (hη : 0 ≤ η)
    (cuts : List (Cut q)) :
    LogConcaveHalfspaces.IsLogConcave (fun y => ENNReal.ofReal (coreWeight q α η cuts y)) := by
  intro x y t ht ht'
  have hc := (lossSum_convex q α cuts).2 (Set.mem_univ x) (Set.mem_univ y)
    (sub_nonneg.mpr ht'.le) ht.le (by ring : 1 - t + t = 1)
  have hc' := mul_le_mul_of_nonneg_left hc hη
  unfold coreWeight
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.rpow_def_of_pos (Real.exp_pos _),
    Real.log_exp, Real.log_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [smul_eq_mul] at hc'
  nlinarith

lemma weight_logConcave (q : Params) (α η : ℝ) (hη : 0 ≤ η)
    (cuts : List (Cut q)) :
    LogConcaveHalfspaces.IsLogConcave (fun y => ENNReal.ofReal (weight q α η cuts y)) := by
  intro x y t ht ht'
  have ha : 0 < 1 - t := sub_pos.mpr ht'
  by_cases hx : ‖x‖ ≤ 2 * q.R
  · by_cases hy : ‖y‖ ≤ 2 * q.R
    · have hxy : ‖(1 - t) • x + t • y‖ ≤ 2 * q.R := by
        have h := (convex_closedBall (0 : Space q) (2 * q.R))
          (by simpa using hx) (by simpa using hy) ha.le ht.le (by ring : 1 - t + t = 1)
        simpa using h
      simpa only [weight, ite_eq_left hx, ite_eq_left hy, ite_eq_left hxy] using
        coreWeight_logConcave q α η hη cuts x y t ht ht'
    · simp [weight, hy, ENNReal.zero_rpow_of_pos ht]
  · simp [weight, hx, ENNReal.zero_rpow_of_pos ha]

@[fun_prop] lemma measurable_weight (q : Params) (α η : ℝ) (cuts : List (Cut q)) :
    Measurable (weight q α η cuts) := by
  rw [weight_eq_indicator]
  exact (continuous_coreWeight q α η cuts).measurable.indicator measurableSet_closedBall

lemma integrable_weight_smul (q : Params) (α η : ℝ) (cuts : List (Cut q)) :
    Integrable (fun y => weight q α η cuts y • y) := by
  have heq : (fun y => weight q α η cuts y • y) =
      (Metric.closedBall (0 : Space q) (2 * q.R)).indicator
        (fun y => coreWeight q α η cuts y • y) := by
    ext y
    simp [weight, Set.indicator, Metric.mem_closedBall, dist_zero_right]
  rw [heq, integrable_indicator_iff measurableSet_closedBall]
  exact ((continuous_coreWeight q α η cuts).smul continuous_id).continuousOn.integrableOn_compact
    (isCompact_closedBall _ _)

def normalizedDensity (q : Params) (α η : ℝ) (cuts : List (Cut q)) (y : Space q) : ENNReal :=
  (ENNReal.ofReal (mass q α η cuts))⁻¹ * ENNReal.ofReal (weight q α η cuts y)

@[fun_prop] lemma measurable_normalizedDensity (q : Params) (α η : ℝ) (cuts : List (Cut q)) :
    Measurable (normalizedDensity q α η cuts) := by
  unfold normalizedDensity
  fun_prop

lemma normalizedDensity_toReal (q : Params) (hR : 0 < q.R) (α η : ℝ)
    (cuts : List (Cut q)) (y : Space q) :
    (normalizedDensity q α η cuts y).toReal = (mass q α η cuts)⁻¹ * weight q α η cuts y := by
  rw [normalizedDensity, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (mass_pos q hR α η cuts).le,
    ENNReal.toReal_ofReal (weight_nonneg q α η cuts y)]

lemma normalizedDensity_lt_top (q : Params) (hR : 0 < q.R) (α η : ℝ)
    (cuts : List (Cut q)) (y : Space q) : normalizedDensity q α η cuts y < ⊤ := by
  apply ENNReal.mul_lt_top
  · exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (mass_pos q hR α η cuts))
  · exact ENNReal.ofReal_lt_top

lemma normalizedDensity_probability (q : Params) (hR : 0 < q.R) (α η : ℝ)
    (cuts : List (Cut q)) : IsProbabilityMeasure (volume.withDensity (normalizedDensity q α η cuts)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  unfold normalizedDensity
  rw [lintegral_const_mul _ (measurable_weight q α η cuts).ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_weight q α η cuts)
      (Filter.Eventually.of_forall (weight_nonneg q α η cuts))]
  change (ENNReal.ofReal (mass q α η cuts))⁻¹ * ENNReal.ofReal (mass q α η cuts) = 1
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (mass_pos q hR α η cuts)).ne' ENNReal.ofReal_ne_top

lemma normalizedDensity_logConcave (q : Params) (hR : 0 < q.R) (α η : ℝ)
    (hη : 0 ≤ η) (cuts : List (Cut q)) :
    LogConcaveHalfspaces.IsLogConcave (normalizedDensity q α η cuts) := by
  intro x y t ht ht'
  let c := (ENNReal.ofReal (mass q α η cuts))⁻¹
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hct : c ≠ ⊤ := ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr (mass_pos q hR α η cuts)).ne'
  change (c * ENNReal.ofReal (weight q α η cuts x)) ^ (1 - t) *
    (c * ENNReal.ofReal (weight q α η cuts y)) ^ t ≤ _
  rw [ENNReal.mul_rpow_of_nonneg _ _ (sub_nonneg.mpr ht'.le),
    ENNReal.mul_rpow_of_nonneg _ _ ht.le]
  calc
    c ^ (1 - t) * ENNReal.ofReal (weight q α η cuts x) ^ (1 - t) *
        (c ^ t * ENNReal.ofReal (weight q α η cuts y) ^ t) =
        (c ^ (1 - t) * c ^ t) * (ENNReal.ofReal (weight q α η cuts x) ^ (1 - t) *
          ENNReal.ofReal (weight q α η cuts y) ^ t) := by ac_rfl
    _ = c * (ENNReal.ofReal (weight q α η cuts x) ^ (1 - t) *
          ENNReal.ofReal (weight q α η cuts y) ^ t) := by
      rw [← ENNReal.rpow_add _ _ hc0 hct, sub_add_cancel, ENNReal.rpow_one]
    _ ≤ _ := mul_le_mul' (le_refl c) (weight_logConcave q α η hη cuts x y t ht ht')

lemma integrable_id_normalizedDensity (q : Params) (hR : 0 < q.R) (α η : ℝ)
    (cuts : List (Cut q)) :
    Integrable (fun y : Space q => y) (volume.withDensity (normalizedDensity q α η cuts)) := by
  rw [integrable_withDensity_iff_integrable_smul' (measurable_normalizedDensity q α η cuts)
    (Filter.Eventually.of_forall (normalizedDensity_lt_top q hR α η cuts))]
  simp_rw [normalizedDensity_toReal q hR α η cuts, mul_smul]
  exact Integrable.smul ((mass q α η cuts)⁻¹) (integrable_weight_smul q α η cuts)

lemma centroid_eq_integral (q : Params) (hR : 0 < q.R) (α η : ℝ)
    (cuts : List (Cut q)) :
    centroid q α η cuts = ∫ y : Space q, y ∂volume.withDensity (normalizedDensity q α η cuts) := by
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_normalizedDensity q α η cuts)
    (Filter.Eventually.of_forall (normalizedDensity_lt_top q hR α η cuts))]
  simp_rw [normalizedDensity_toReal q hR α η cuts, mul_smul]
  rw [integral_smul]
  rfl

lemma normalizedDensity_ae_ball (q : Params) (α η : ℝ) (cuts : List (Cut q)) :
    ∀ᵐ y ∂volume.withDensity (normalizedDensity q α η cuts),
      y ∈ Metric.closedBall (0 : Space q) (2 * q.R) := by
  rw [ae_withDensity_iff (measurable_normalizedDensity q α η cuts)]
  apply Filter.Eventually.of_forall
  intro y hy
  have hnorm : ‖y‖ ≤ 2 * q.R := by
    by_contra h
    exact hy (by simp [normalizedDensity, weight, h])
  simpa using hnorm

lemma norm_centroid_le (q : Params) (hR : 0 < q.R) (α η : ℝ) (cuts : List (Cut q)) :
    ‖centroid q α η cuts‖ ≤ 2 * q.R := by
  have := normalizedDensity_probability q hR α η cuts
  rw [centroid_eq_integral q hR α η cuts]
  have h := (convex_closedBall (0 : Space q) (2 * q.R)).integral_mem Metric.isClosed_closedBall
    (normalizedDensity_ae_ball q α η cuts) (integrable_id_normalizedDensity q hR α η cuts)
  simpa using h

lemma centroid_halfspace_mass (q : Params) (hd : 0 < q.d) (hR : 0 < q.R)
    (α η : ℝ) (hη : 0 ≤ η) (cuts : List (Cut q)) (g : Space q) :
    ENNReal.ofReal (Real.exp (-1)) ≤
      (volume.withDensity (normalizedDensity q α η cuts))
        {y | 0 ≤ ⟪g, y - centroid q α η cuts⟫} := by
  have := normalizedDensity_probability q hR α η cuts
  have hi := integrable_id_normalizedDensity q hR α η cuts
  have h := LogConcaveHalfspaces.euclidean_density_halfspace_mass_pos hd
    (normalizedDensity q α η cuts) (measurable_normalizedDensity q α η cuts)
    (normalizedDensity_logConcave q hR α η hη cuts) (innerSL ℝ g)
    ((innerSL ℝ g).integrable_comp hi)
  have hm : (∫ y, ⟪g, y⟫ ∂volume.withDensity (normalizedDensity q α η cuts)) =
      ⟪g, centroid q α η cuts⟫ := by
    rw [centroid_eq_integral q hR α η cuts]
    exact (innerSL ℝ g).integral_comp_comm hi
  simpa only [innerSL_apply_apply, hm, inner_sub_right, sub_nonneg] using h

lemma lossSum_append (q : Params) (α : ℝ) (cuts : List (Cut q)) (cut : Cut q)
    (y : Space q) :
    lossSum q α (cuts ++ [cut]) y = lossSum q α cuts y + hinge q α cut y := by
  simp only [lossSum, List.length_append, List.length_singleton, Finset.sum_range_succ]
  rw [List.getD_append_right cuts [cut] (0, 0) cuts.length le_rfl]
  simp only [Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [List.getD_append cuts [cut] (0, 0) i (Finset.mem_range.mp hi)]

lemma weight_append (q : Params) (α η : ℝ) (cuts : List (Cut q)) (cut : Cut q)
    (y : Space q) :
    weight q α η (cuts ++ [cut]) y =
      weight q α η cuts y * Real.exp (-η * hinge q α cut y) := by
  by_cases hy : ‖y‖ ≤ 2 * q.R
  · simp only [weight, ite_eq_left hy, coreWeight, lossSum_append, mul_add, Real.exp_add]
  · simp [weight, hy]

lemma weight_append_le (q : Params) (α η : ℝ) (hη : 0 ≤ η)
    (cuts : List (Cut q)) (cut : Cut q) (y : Space q) :
    weight q α η (cuts ++ [cut]) y ≤ weight q α η cuts y := by
  rw [weight_append]
  apply mul_le_of_le_one_right (weight_nonneg q α η cuts y)
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hη) (le_max_left _ _)

lemma weight_append_halfspace_le (q : Params) (α : ℝ) (hα : 0 < α)
    (cuts : List (Cut q)) (g y : Space q)
    (hy : 0 ≤ ⟪g, y - centroid q α (2 / α) cuts⟫) :
    weight q α (2 / α) (cuts ++ [(g, centroid q α (2 / α) cuts)]) y ≤
      weight q α (2 / α) cuts y / 2 := by
  rw [weight_append, div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ (weight_nonneg q α (2 / α) cuts y)
  have hhinge : α / 2 ≤ hinge q α (g, centroid q α (2 / α) cuts) y :=
    le_trans (by dsimp; linarith) (le_max_right _ _)
  have hscaled : -(2 / α) * hinge q α (g, centroid q α (2 / α) cuts) y ≤ -1 := by
    have h := mul_le_mul_of_nonneg_left hhinge (by positivity : 0 ≤ 2 / α)
    have heq : (2 / α) * (α / 2) = 1 := by field_simp
    nlinarith
  apply (Real.exp_le_exp.mpr hscaled).trans
  rw [Real.exp_neg]
  exact (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr Real.exp_one_gt_two.le

lemma normalizedDensity_measure_toReal (q : Params) (hR : 0 < q.R) (α η : ℝ)
    (cuts : List (Cut q)) (s : Set (Space q)) (hs : MeasurableSet s) :
    ((volume.withDensity (normalizedDensity q α η cuts)) s).toReal =
      (mass q α η cuts)⁻¹ * ∫ y in s, weight q α η cuts y := by
  rw [withDensity_apply _ hs]
  simp only [normalizedDensity]
  rw [lintegral_const_mul _ (measurable_weight q α η cuts).ennreal_ofReal,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_weight q α η cuts).restrict)
      (Filter.Eventually.of_forall (weight_nonneg q α η cuts)),
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (mass_pos q hR α η cuts).le,
    ENNReal.toReal_ofReal (integral_nonneg (weight_nonneg q α η cuts))]

lemma mass_append_centroid_contracts (q : Params) (hd : 0 < q.d) (hR : 0 < q.R)
    (α : ℝ) (hα : 0 < α) (cuts : List (Cut q)) (g : Space q) :
    mass q α (2 / α) (cuts ++ [(g, centroid q α (2 / α) cuts)]) ≤
      (5 / 6 : ℝ) * mass q α (2 / α) cuts := by
  let η := 2 / α
  let H := {y : Space q | 0 ≤ ⟪g, y - centroid q α η cuts⟫}
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hs : MeasurableSet H := measurableSet_le measurable_const (by fun_prop)
  have := normalizedDensity_probability q hR α η cuts
  have hprob := ENNReal.toReal_mono
    (measure_ne_top (volume.withDensity (normalizedDensity q α η cuts)) H)
    (centroid_halfspace_mass q hd hR α η hη cuts g)
  rw [ENNReal.toReal_ofReal (Real.exp_pos (-1)).le,
    normalizedDensity_measure_toReal q hR α η cuts H hs] at hprob
  have he : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (inv_le_inv₀ (by norm_num : (0 : ℝ) < 3) (Real.exp_pos 1)).mpr Real.exp_one_lt_three.le
  have hm := mass_pos q hR α η cuts
  have hmass : mass q α η cuts / 3 ≤ ∫ y in H, weight q α η cuts y := by
    have h := mul_le_mul_of_nonneg_left (he.trans hprob) hm.le
    rw [← mul_assoc, mul_inv_cancel₀ hm.ne', one_mul] at h
    linarith
  have hp : ∀ y, weight q α η (cuts ++ [(g, centroid q α η cuts)]) y ≤
      weight q α η cuts y - (1 / 2 : ℝ) * H.indicator (weight q α η cuts) y := by
    intro y
    by_cases hy : y ∈ H
    · rw [Set.indicator_of_mem hy]
      have h := weight_append_halfspace_le q α hα cuts g y hy
      dsimp [η]
      linarith
    · rw [Set.indicator_of_notMem hy, mul_zero, sub_zero]
      exact weight_append_le q α η hη cuts _ y
  have hi := integrable_weight q α η cuts
  have hHi := hi.indicator hs
  have h := integral_mono
    (integrable_weight q α η (cuts ++ [(g, centroid q α η cuts)]))
    (hi.sub (hHi.const_mul (1 / 2 : ℝ))) hp
  change (∫ y, weight q α η (cuts ++ [(g, centroid q α η cuts)]) y) ≤
    ∫ y, weight q α η cuts y - (1 / 2 : ℝ) * H.indicator (weight q α η cuts) y at h
  rw [integral_sub hi (hHi.const_mul (1 / 2 : ℝ)), integral_const_mul,
    integral_indicator hs] at h
  change mass q α η (cuts ++ [(g, centroid q α η cuts)]) ≤
    mass q α η cuts - (1 / 2 : ℝ) * ∫ y in H, weight q α η cuts y at h
  change mass q α η (cuts ++ [(g, centroid q α η cuts)]) ≤ (5 / 6 : ℝ) * mass q α η cuts
  linarith

lemma lossSum_ofFn (q : Params) (α : ℝ) {n : ℕ} (cuts : Fin n → Cut q) (y : Space q) :
    lossSum q α (List.ofFn cuts) y = ∑ i : Fin n, hinge q α (cuts i) y := by
  simp only [lossSum, List.length_ofFn, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [List.getD_eq_getElem (List.ofFn cuts) (0, 0) (by simp)]
  simp

@[fun_prop] lemma continuous_lossSum_ofFn (q : Params) (α : ℝ) (n : ℕ) :
    Continuous (fun p : (Fin n → Cut q) × Space q => lossSum q α (List.ofFn p.1) p.2) := by
  simp_rw [lossSum_ofFn]
  unfold hinge
  fun_prop

@[fun_prop] lemma continuous_coreWeight_ofFn (q : Params) (α η : ℝ) (n : ℕ) :
    Continuous (fun p : (Fin n → Cut q) × Space q => coreWeight q α η (List.ofFn p.1) p.2) := by
  unfold coreWeight
  fun_prop

lemma continuous_mass_ofFn (q : Params) (α η : ℝ) (n : ℕ) :
    Continuous (fun cuts : Fin n → Cut q => mass q α η (List.ofFn cuts)) := by
  have h := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (cuts : Fin n → Cut q) (y : Space q) => coreWeight q α η (List.ofFn cuts) y)
    (continuous_coreWeight_ofFn q α η n) (isCompact_closedBall (0 : Space q) (2 * q.R))
  simpa only [mass, weight_eq_indicator, integral_indicator measurableSet_closedBall] using h

lemma continuous_centroid_ofFn (q : Params) (hR : 0 < q.R) (α η : ℝ) (n : ℕ) :
    Continuous (fun cuts : Fin n → Cut q => centroid q α η (List.ofFn cuts)) := by
  have hm := (continuous_mass_ofFn q α η n).inv₀
    (fun cuts => (mass_pos q hR α η (List.ofFn cuts)).ne')
  have hcore : Continuous (fun p : (Fin n → Cut q) × Space q =>
      coreWeight q α η (List.ofFn p.1) p.2 • p.2) :=
    (continuous_coreWeight_ofFn q α η n).smul continuous_snd
  have hnum := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (cuts : Fin n → Cut q) (y : Space q) => coreWeight q α η (List.ofFn cuts) y • y) hcore
    (isCompact_closedBall (0 : Space q) (2 * q.R))
  have heq (cuts : Fin n → Cut q) :
      (∫ y, weight q α η (List.ofFn cuts) y • y) =
        ∫ y in Metric.closedBall (0 : Space q) (2 * q.R), coreWeight q α η (List.ofFn cuts) y • y := by
    rw [← integral_indicator measurableSet_closedBall]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    simp [weight, Set.indicator, Metric.mem_closedBall, dist_zero_right]
  unfold centroid
  simp_rw [heq]
  exact hm.fun_smul hnum

end LongTails.Proofs.CovarianceSoftCutDensity
