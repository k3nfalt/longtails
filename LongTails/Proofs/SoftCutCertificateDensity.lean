import LongTails.Proofs.CovarianceSoftCutLocalization

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SoftCutCertificateDensity

lemma inward_ball_bounds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y z : E) (R r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R)
    (hy : ‖y‖ ≤ R) (hz : ‖z - (1 - r / R) • y‖ ≤ r) :
    ‖z‖ ≤ R ∧ ‖z - y‖ ≤ 2 * r := by
  have hratio : 0 ≤ r / R := div_nonneg hr hR.le
  have hratio1 : r / R ≤ 1 := (div_le_one hR).2 hrR
  have hcenter : ‖(1 - r / R) • y‖ ≤ R - r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - r / R)]
    have h := mul_le_mul_of_nonneg_left hy (by linarith : 0 ≤ 1 - r / R)
    have heq : (1 - r / R) * R = R - r := by field_simp
    exact h.trans_eq heq
  have hshift : ‖(1 - r / R) • y - y‖ ≤ r := by
    rw [show (1 - r / R) • y - y = -(r / R) • y by module,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hratio]
    have h := mul_le_mul_of_nonneg_left hy hratio
    simpa only [div_mul_cancel₀ r hR.ne'] using h
  constructor
  · have h := norm_add_le (z - (1 - r / R) • y) ((1 - r / R) • y)
    rw [sub_add_cancel] at h
    linarith
  · have h := norm_add_le (z - (1 - r / R) • y) ((1 - r / R) • y - y)
    rw [sub_add_sub_cancel] at h
    linarith

lemma positive_part_difference (a b : ℝ) : |max 0 a - max 0 b| ≤ |a - b| := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · simp only [max_eq_right ha, max_eq_right hb, le_refl]
  · rw [max_eq_right ha, max_eq_left hb, sub_zero, abs_of_nonneg ha,
      abs_of_nonneg (by linarith : 0 ≤ a - b)]
    linarith
  · rw [max_eq_left ha, max_eq_right hb, zero_sub, abs_neg, abs_of_nonneg hb,
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith
  · simp only [max_eq_left ha, max_eq_left hb, sub_self, abs_zero, abs_nonneg]

open LongTails.Setups.CovarianceBoundedConvex
open LongTails.Algorithms.CovarianceSoftCut

lemma hinge_difference (q : Params) (α : ℝ) (cut : Cut q) (y z : Space q) :
    |hinge q α cut y - hinge q α cut z| ≤ ‖cut.1‖ * ‖y - z‖ := by
  have h := positive_part_difference (⟪cut.1, y - cut.2⟫ + α / 2)
    (⟪cut.1, z - cut.2⟫ + α / 2)
  have heq : (⟪cut.1, y - cut.2⟫ + α / 2) -
      (⟪cut.1, z - cut.2⟫ + α / 2) = ⟪cut.1, y - z⟫ := by
    simp only [inner_sub_right]
    ring
  rw [heq] at h
  exact h.trans (abs_real_inner_le_norm cut.1 (y - z))

lemma loss_difference (q : Params) (α : ℝ) (cuts : List (Cut q)) (y z : Space q) :
    |lossSum q α cuts y - lossSum q α cuts z| ≤
      (∑ i ∈ Finset.range cuts.length, ‖(cuts.getD i (0, 0)).1‖) * ‖y - z‖ := by
  unfold lossSum
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => hinge_difference q α (cuts.getD i (0, 0)) y z)

open LongTails.Proofs.CovarianceSoftCutDensity

lemma centroid_mass_contracts_all_dimensions (q : Params) (hR : 0 < q.R)
    (α : ℝ) (hα : 0 < α) (cuts : List (Cut q)) (g : Space q) :
    mass q α (2 / α) (cuts ++ [(g, centroid q α (2 / α) cuts)]) ≤
      (5 / 6 : ℝ) * mass q α (2 / α) cuts := by
  by_cases hd : 0 < q.d
  · exact mass_append_centroid_contracts q hd hR α hα cuts g
  have hd0 : q.d = 0 := Nat.eq_zero_of_not_pos hd
  have hg : g = 0 := by
    ext i
    exact Fin.elim0 (hd0 ▸ i)
  rw [hg]
  have hw (y : Space q) :
      weight q α (2 / α) (cuts ++ [(0, centroid q α (2 / α) cuts)]) y =
        Real.exp (-1) * weight q α (2 / α) cuts y := by
    rw [weight_append]
    have hh : hinge q α (0, centroid q α (2 / α) cuts) y = α / 2 := by
      simp [hinge, max_eq_right (show 0 ≤ α / 2 by positivity)]
    rw [hh]
    have he : -(2 / α) * (α / 2) = -1 := by field_simp
    rw [he, mul_comm]
  unfold mass
  simp_rw [hw]
  rw [integral_const_mul]
  have he : Real.exp (-1) ≤ (5 / 6 : ℝ) := by
    rw [Real.exp_neg]
    have h := (inv_le_inv₀ (Real.exp_pos 1) (by norm_num : (0 : ℝ) < 2)).mpr
      Real.exp_one_gt_two.le
    norm_num at h ⊢
    linarith
  exact mul_le_mul_of_nonneg_right he (integral_nonneg (weight_nonneg q α (2 / α) cuts))

lemma mass_lower_neighborhood (q : Params) (α η r K : ℝ) (cuts : List (Cut q))
    (y : Space q) (hR : 0 < q.R) (hη : 0 ≤ η) (hr : 0 ≤ r)
    (hrR : r ≤ 2 * q.R) (hy : ‖y‖ ≤ 2 * q.R)
    (hcuts : (∑ i ∈ Finset.range cuts.length, ‖(cuts.getD i (0, 0)).1‖) ≤ K) :
    volume.real (Metric.closedBall ((1 - r / (2 * q.R)) • y) r) *
      Real.exp (-η * (lossSum q α cuts y + 2 * r * K)) ≤ mass q α η cuts := by
  let A := Metric.closedBall ((1 - r / (2 * q.R)) • y) r
  let c := Real.exp (-η * (lossSum q α cuts y + 2 * r * K))
  have hc : IntegrableOn (fun _ : Space q => c) A :=
    continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hpoint : ∀ z ∈ A, c ≤ weight q α η cuts z := by
    intro z hz
    have hz' : ‖z - (1 - r / (2 * q.R)) • y‖ ≤ r := by
      simpa only [A, Metric.mem_closedBall, dist_eq_norm] using hz
    have hb := inward_ball_bounds y z (2 * q.R) r (by positivity) hr hrR hy hz'
    have hl := loss_difference q α cuts z y
    have hnonneg : 0 ≤ ∑ i ∈ Finset.range cuts.length, ‖(cuts.getD i (0, 0)).1‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hdist := mul_le_mul_of_nonneg_left hb.2 hnonneg
    have hsize := mul_le_mul_of_nonneg_right hcuts (show 0 ≤ 2 * r by positivity)
    have hupper : lossSum q α cuts z ≤ lossSum q α cuts y + 2 * r * K := by
      have hle := le_abs_self (lossSum q α cuts z - lossSum q α cuts y)
      nlinarith
    simp only [weight, ite_eq_left hb.1, coreWeight]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hupper (neg_nonpos.mpr hη)
  have hi := setIntegral_mono_on hc (integrable_weight q α η cuts).integrableOn
    measurableSet_closedBall hpoint
  have hmass : (∫ z in A, weight q α η cuts z) ≤ mass q α η cuts :=
    setIntegral_le_integral (integrable_weight q α η cuts)
      (Filter.Eventually.of_forall (weight_nonneg q α η cuts))
  have h := hi.trans hmass
  simpa only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, Measure.real, A, c] using h

lemma uniform_penalty_lower (q : Params) (α r K T : ℝ) (cuts : List (Cut q))
    (y : Space q) (hR : 0 < q.R) (hα : 0 < α) (hr : 0 < r)
    (hrR : r ≤ 2 * q.R) (hy : ‖y‖ ≤ 2 * q.R)
    (hcuts : (∑ i ∈ Finset.range cuts.length, ‖(cuts.getD i (0, 0)).1‖) ≤ K)
    (hupper : mass q α (2 / α) cuts ≤
      volume.real (Metric.closedBall (0 : Space q) (2 * q.R)) * Real.exp (-T / 6)) :
    α * T / 12 - α / 2 *
      (Real.log (volume.real (Metric.closedBall (0 : Space q) (2 * q.R))) -
        Real.log (volume.real (Metric.closedBall ((1 - r / (2 * q.R)) • y) r))) -
      2 * r * K ≤ lossSum q α cuts y := by
  have hball (z : Space q) (s : ℝ) (hs : 0 < s) :
      0 < volume.real (Metric.closedBall z s) := by
    apply ENNReal.toReal_pos
    · exact (lt_of_lt_of_le (Metric.measure_ball_pos volume z hs)
        (measure_mono Metric.ball_subset_closedBall)).ne'
    · exact (isCompact_closedBall z s).measure_lt_top.ne
  have hlow := mass_lower_neighborhood q α (2 / α) r K cuts y hR
    (by positivity) hr.le hrR hy hcuts
  have heq : -(2 / α) * (lossSum q α cuts y + 2 * r * K) =
      -((2 / α) * (lossSum q α cuts y + 2 * r * K)) := by ring
  rw [heq] at hlow
  have h := LongTails.Proofs.CovarianceSoftCutPotential.loss_lower_of_mass_bounds
    _ _ _ ((2 / α) * (lossSum q α cuts y + 2 * r * K)) T
    (hball _ r hr) (hball 0 (2 * q.R) (by positivity)) hlow hupper
  have hs := mul_le_mul_of_nonneg_left h (show 0 ≤ α / 2 by positivity)
  have hcancel : α / 2 * ((2 / α) * (lossSum q α cuts y + 2 * r * K)) =
      lossSum q α cuts y + 2 * r * K := by field_simp
  rw [hcancel] at hs
  linarith

lemma generator_mass_bound_all_dimensions (q : Params) (hR : 0 < q.R)
    (α : ℝ) (hα : 0 < α) (b n : ℕ) (replies : ℕ → Space q) :
    mass q α (2/α) (List.ofFn (generatorCuts q α (2/α) b n replies)) ≤
      (5/6 : ℝ)^n * mass q α (2/α) [] := by
  induction n with
  | zero => simp [generatorCuts]
  | succ n ih =>
    rw [CovarianceSoftCutTrajectory.generatorCuts_list_succ]
    apply (centroid_mass_contracts_all_dimensions q hR α hα _ (batchMean q b n replies)).trans
    calc
      (5/6 : ℝ) * mass q α (2/α) (List.ofFn (generatorCuts q α (2/α) b n replies)) ≤
          (5/6 : ℝ) * ((5/6 : ℝ)^n * mass q α (2/α) []) := by gcongr
      _ = _ := by ring

lemma generator_mass_exp_bound_all_dimensions (q : Params) (hR : 0 < q.R)
    (α : ℝ) (hα : 0 < α) (b n : ℕ) (replies : ℕ → Space q) :
    mass q α (2/α) (List.ofFn (generatorCuts q α (2/α) b n replies)) ≤
      volume.real (Metric.closedBall (0 : Space q) (2*q.R)) * Real.exp (-(n : ℝ)/6) := by
  have he : (5/6 : ℝ) ≤ Real.exp (-1/6) := by
    have hh := Real.add_one_le_exp (-1/6)
    linarith
  have hp : (5/6 : ℝ)^n ≤ Real.exp (-(n : ℝ)/6) := by
    calc
      (5/6 : ℝ)^n ≤ Real.exp (-1/6)^n := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hh := (generator_mass_bound_all_dimensions q hR α hα b n replies).trans
    (mul_le_mul_of_nonneg_right hp (mass_pos q hR α (2/α) []).le)
  simpa only [CovarianceSoftCutLocalization.mass_empty, mul_comm] using hh

lemma ball_log_volume_ratio (q : Params) (hR : 0 < q.R) (r : ℝ) (hr : 0 < r) (z : Space q) :
    Real.log (volume.real (Metric.closedBall (0 : Space q) (2*q.R))) -
      Real.log (volume.real (Metric.closedBall z r)) = (q.d : ℝ)*Real.log (2*q.R/r) := by
  have hv : 0 < volume.real (Metric.closedBall (0 : Space q) 1) := by
    apply ENNReal.toReal_pos
    · exact (lt_of_lt_of_le (Metric.measure_ball_pos volume 0 (by norm_num))
        (measure_mono Metric.ball_subset_closedBall)).ne'
    · exact (isCompact_closedBall (0 : Space q) 1).measure_lt_top.ne
  rw [Measure.addHaar_real_closedBall' volume (0 : Space q) (by positivity),
    Measure.addHaar_real_closedBall' volume z hr.le]
  simp only [Space, finrank_euclideanSpace_fin]
  rw [Real.log_mul (by positivity) hv.ne', Real.log_mul (by positivity) hv.ne',
    Real.log_pow, Real.log_pow, Real.log_div (by positivity) hr.ne']
  ring

lemma generatorCuts_coordinates (q : Params) (α η : ℝ) (b n : ℕ) (replies : ℕ → Space q) :
    generatorCuts q α η b n replies =
      fun i : Fin n => (batchMean q b i replies, generatorPoint q α η b i replies) := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [generatorCuts, Fin.append_left]
      rw [ih]
      rfl
    · have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
      subst j
      simp [generatorCuts, Fin.append_right, generatorPoint]

lemma cut_norm_sum_ofFn (q : Params) {n : ℕ} (cuts : Fin n → Cut q) :
    (∑ i ∈ Finset.range (List.ofFn cuts).length, ‖((List.ofFn cuts).getD i (0,0)).1‖) =
      ∑ i, ‖(cuts i).1‖ := by
  simp only [List.length_ofFn, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [List.getD_eq_getElem (List.ofFn cuts) (0,0) (by simp)]
  simp

lemma uniform_generator_penalty (q : Params) (hR : 0 < q.R)
    (α : ℝ) (hα : 0 < α) (b T : ℕ) (replies : ℕ → Space q)
    (M r : ℝ) (hr : 0 < r) (hrR : r ≤ 2*q.R)
    (hcap : ∀ i : Fin T, ‖batchMean q b i replies‖ ≤ M)
    (hlog : (q.d : ℝ)*Real.log (2*q.R/r) ≤ (T : ℝ)/48)
    (hrM : 2*r*M ≤ α/96) (y : Space q) (hy : ‖y‖ ≤ 2*q.R) :
    α*T/16 ≤ ∑ i : Fin T, max 0
      (⟪batchMean q b i replies, y-generatorPoint q α (2/α) b i replies⟫+α/2) := by
  let cuts := List.ofFn (generatorCuts q α (2/α) b T replies)
  have hcuts : (∑ i ∈ Finset.range cuts.length, ‖(cuts.getD i (0,0)).1‖) ≤ (T : ℝ)*M := by
    dsimp only [cuts]
    rw [cut_norm_sum_ofFn, generatorCuts_coordinates]
    exact (Finset.sum_le_sum (fun i _ => hcap i)).trans_eq (by simp)
  have hu := uniform_penalty_lower q α r ((T : ℝ)*M) T cuts y hR hα hr hrR hy hcuts
    (generator_mass_exp_bound_all_dimensions q hR α hα b T replies)
  rw [ball_log_volume_ratio q hR r hr] at hu
  have hl := mul_le_mul_of_nonneg_left hlog (show 0 ≤ α/2 by positivity)
  have hm := mul_le_mul_of_nonneg_right hrM (Nat.cast_nonneg T)
  have hout : α*T/16 ≤ lossSum q α cuts y := by nlinarith
  dsimp only [cuts] at hout
  rw [lossSum_ofFn, generatorCuts_coordinates] at hout
  exact hout

end LongTails.Proofs.SoftCutCertificateDensity
