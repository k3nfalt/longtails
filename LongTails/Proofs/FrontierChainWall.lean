import LongTails.Proofs.FrontierChainGeometry
import LongTails.Proofs.SoftRadialProjection

open scoped RealInnerProductSpace

namespace LongTails.Proofs.FrontierChainWall

open SoftRadialProjection FrontierChainGeometry

variable {d k : ℕ}

noncomputable def wallObjective (π : Fin (k + 1) ↪ Fin d) (R η : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  FrontierChain.objective π (project R x) + η / 2 * ‖x‖ ^ 2

noncomputable def wallField (π : Fin (k + 1) ↪ Fin d) (R η : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  derivative R x (FrontierChain.field π (project R x)) + η • x

lemma wall_gradient (π : Fin (k + 1) ↪ Fin d) {R : ℝ} (hR : 0 < R) (η : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : HasGradientAt (wallObjective π R η) (wallField π R η x) x := by
  have h1 := composition_gradient hR x (FrontierChain.objective_gradient π (project R x))
  have h2 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (η / 2)
  rw [hasGradientAt_iff_hasFDerivAt]
  apply (h1.hasFDerivAt.add h2).congr_fderiv
  ext v
  simp [wallField, InnerProductSpace.toDual_apply_apply]
  ring

lemma wall_gap (π : Fin (k + 1) ↪ Fin d) (R : ℝ) {η : ℝ} (hη : 0 ≤ η)
    (x : EuclideanSpace ℝ (Fin d)) : wallObjective π R η 0 - wallObjective π R η x ≤ 8 * (k + 1) := by
  have hg := FrontierChain.objective_gap π 0 (project R x)
  have hn : 0 ≤ η / 2 * ‖x‖ ^ 2 := by positivity
  have h0 : project R (0 : EuclideanSpace ℝ (Fin d)) = 0 := by simp [project]
  dsimp only [wallObjective]
  rw [h0, norm_zero]
  norm_num only [zero_pow, mul_zero, add_zero]
  linarith

lemma wall_lipschitz (π : Fin (k + 1) ↪ Fin d) {R η : ℝ} (hR : 0 < R) (hη : 0 ≤ η)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖wallField π R η x - wallField π R η y‖ ≤
      (2120 + 108 * Real.sqrt (k + 1) / R + η) * ‖x - y‖ := by
  have h := composition_field_lipschitz hR (by norm_num : (0 : ℝ) ≤ 530)
    (FrontierChain.field π) (field_norm_upper π) (field_lipschitz π) x y
  have he : wallField π R η x - wallField π R η y =
      (derivative R x (FrontierChain.field π (project R x)) -
        derivative R y (FrontierChain.field π (project R y))) + η • (x - y) := by
    unfold wallField
    module
  rw [he]
  calc _ ≤ ‖derivative R x (FrontierChain.field π (project R x)) -
      derivative R y (FrontierChain.field π (project R y))‖ + ‖η • (x - y)‖ := norm_add_le _ _
    _ ≤ (4 * 530 + 6 * (18 * Real.sqrt (k + 1)) / R) * ‖x - y‖ + η * ‖x - y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
      exact add_le_add h le_rfl
    _ = _ := by ring

noncomputable def radius (k : ℕ) : ℝ := 720 * Real.sqrt (k + 1)

lemma radius_lower (k : ℕ) : 720 ≤ radius k := by
  have hs : 1 ≤ Real.sqrt (k + 1) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    simp
  unfold radius
  linarith

lemma radius_pos (k : ℕ) : 0 < radius k := lt_of_lt_of_le (by norm_num) (radius_lower k)

lemma canonical_lipschitz (π : Fin (k + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖wallField π (radius k) (1 / 5) x - wallField π (radius k) (1 / 5) y‖ ≤ 2200 * ‖x - y‖ := by
  have h := wall_lipschitz π (radius_pos k) (by norm_num : (0 : ℝ) ≤ 1 / 5) x y
  have hs : 0 < Real.sqrt (k + 1) := Real.sqrt_pos.mpr (by positivity)
  have he : 108 * Real.sqrt (k + 1) / radius k = 3 / 20 := by unfold radius; field_simp; ring
  rw [he] at h
  nlinarith [norm_nonneg (x - y)]

lemma coordinate_scale (R : ℝ) (x : EuclideanSpace ℝ (Fin d)) (j : Fin d) :
    x j = scale R x * project R x j := by
  change x j = scale R x * ((scale R x)⁻¹ * x j)
  rw [← mul_assoc, mul_inv_cancel₀ (scale_pos R x).ne', one_mul]

lemma small_scale {R : ℝ} (hR : 0 < R) (x : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ ≤ R / 2) : scale R x ≤ 5 / 4 := by
  have hr2 := pow_le_pow_left₀ (norm_nonneg x) hx 2
  have hs2 : scale R x ^ 2 ≤ 5 / 4 := by
    rw [scale_sq]
    have hq : ‖x‖ ^ 2 / R ^ 2 ≤ 1 / 4 := by
      rw [div_le_iff₀ (sq_pos_of_pos hR)]
      nlinarith
    linarith
  nlinarith [scale_pos R x]

lemma small_coordinate {R : ℝ} (x : EuclideanSpace ℝ (Fin d)) (j : Fin d)
    (hj : |project R x j| ≤ 1) : |x j| ≤ scale R x := by
  rw [coordinate_scale R x j, abs_mul, abs_of_pos (scale_pos R x)]
  simpa using mul_le_mul_of_nonneg_left hj (scale_pos R x).le

lemma cross_small {R : ℝ} (hR : 0 < R) (x g : EuclideanSpace ℝ (Fin d)) (j : Fin d)
    (hx : ‖x‖ ≤ R / 2) (hg : ‖g‖ ≤ R / 40) (hj : |project R x j| ≤ 1) :
    |(⟪x, g⟫ / (R ^ 2 * scale R x ^ 3)) * x j| ≤ 1 / 80 := by
  have hd : 0 < R ^ 2 * scale R x ^ 3 := by have := scale_pos R x; positivity
  have hi : |⟪x, g⟫| ≤ R ^ 2 / 80 := by
    calc _ ≤ ‖x‖ * ‖g‖ := abs_real_inner_le_norm _ _
      _ ≤ (R / 2) * (R / 40) := mul_le_mul hx hg (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [abs_mul, abs_div, abs_of_pos hd]
  calc _ ≤ (R ^ 2 / 80) / (R ^ 2 * scale R x ^ 3) * scale R x := by
        gcongr
        exact small_coordinate x j hj
    _ = 1 / (80 * scale R x ^ 2) := by field_simp
    _ ≤ 1 / 80 := by
      rw [div_le_iff₀ (by have := scale_pos R x; positivity)]
      have hs : 1 ≤ scale R x ^ 2 := one_le_pow₀ (scale_one_le R x)
      nlinarith

lemma inner_component_bound {R : ℝ} (hR : 0 < R) (x g : EuclideanSpace ℝ (Fin d)) (j : Fin d)
    (hx : ‖x‖ ≤ R / 2) (hg : ‖g‖ ≤ R / 40) (hj : |project R x j| ≤ 1) (hgj : g j ≤ -1) :
    (derivative R x g + (1 / 5 : ℝ) • x) j ≤ -1 / 2 := by
  have hs := small_scale hR x hx
  have hxj := small_coordinate x j hj
  have hc := cross_small hR x g j hx hg hj
  have hinv : 4 / 5 ≤ (scale R x)⁻¹ := by
    rw [← one_div, le_div_iff₀ (scale_pos R x)]
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hgj (inv_nonneg.mpr (scale_pos R x).le)
  have hw := (le_abs_self (x j)).trans hxj
  have hcross := neg_le_abs ((⟪x, g⟫ / (R ^ 2 * scale R x ^ 3)) * x j)
  rw [derivative_apply]
  change (scale R x)⁻¹ * g j - (⟪x, g⟫ / (R ^ 2 * scale R x ^ 3)) * x j +
    (1 / 5) * x j ≤ -1 / 2
  nlinarith

lemma canonical_gradient_lower (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (htail : |project (radius k) x (π (Fin.last k))| < 1) :
    1 / 2 ≤ ‖wallField π (radius k) (1 / 5) x‖ := by
  let R := radius k
  let g := FrontierChain.field π (project R x)
  have hR : 0 < R := radius_pos k
  have hg : ‖g‖ ≤ R / 40 := by
    have h := field_norm_upper π (project R x)
    dsimp [R, radius]
    linarith
  by_cases hx : ‖x‖ ≤ R / 2
  · obtain ⟨j, hj, hgj⟩ := FrontierChain.exists_deficient π (project R x) htail
    have hc := inner_component_bound hR x g (π j) hx hg hj.le hgj
    have hn := PiLp.norm_apply_le (wallField π R (1 / 5) x) (π j)
    change (wallField π R (1 / 5) x) (π j) ≤ -1 / 2 at hc
    rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)] at hn
    linarith
  · have hcomp := derivative_norm_le hR x g
    have he : (1 / 5 : ℝ) • x = wallField π R (1 / 5) x - derivative R x g := by
      dsimp [wallField, g]
      abel
    have hn := norm_sub_le (wallField π R (1 / 5) x) (derivative R x g)
    rw [← he, norm_smul] at hn
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5)] at hn
    have hr := radius_lower k
    change 720 ≤ R at hr
    linarith

end LongTails.Proofs.FrontierChainWall
