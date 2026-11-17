import LongTails.Proofs.FrontierChainOracle

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HolderNoiseHardScaling

open FrontierChainWall FrontierChainOracle SoftRadialProjection

variable {d k : ℕ}

noncomputable def normalize (b : ℝ) (x0 x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  b⁻¹ • (x - x0)

noncomputable def objective (π : Fin (k + 1) ↪ Fin d) (a b : ℝ)
    (x0 x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  a * wallObjective π (radius k) (1 / 5) (normalize b x0 x)

noncomputable def field (π : Fin (k + 1) ↪ Fin d) (a b : ℝ)
    (x0 x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (a / b) • wallField π (radius k) (1 / 5) (normalize b x0 x)

noncomputable def noise (π : Fin (k + 1) ↪ Fin d) (a b : ℝ)
    (x0 x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  (a / b) • projectedNoise π (normalize b x0 x)

lemma objective_gradient (π : Fin (k + 1) ↪ Fin d) (a b : ℝ)
    (x0 x : EuclideanSpace ℝ (Fin d)) : HasGradientAt (objective π a b x0) (field π a b x0 x) x := by
  have hF := wall_gradient π (radius_pos k) (1 / 5) (normalize b x0 x)
  have hn := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const x0).const_smul b⁻¹
  have h := (hF.hasFDerivAt.comp x hn).const_mul a
  rw [hasGradientAt_iff_hasFDerivAt]
  apply h.congr_fderiv
  ext v
  simp [field, InnerProductSpace.toDual_apply_apply, div_eq_mul_inv]
  ring

lemma normalize_difference {b : ℝ} (hb : 0 < b) (x0 x y : EuclideanSpace ℝ (Fin d)) :
    ‖normalize b x0 x - normalize b x0 y‖ = ‖x - y‖ / b := by
  have he : normalize b x0 x - normalize b x0 y = b⁻¹ • (x - y) := by unfold normalize; module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb)]
  ring

lemma field_lipschitz (π : Fin (k + 1) ↪ Fin d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (x0 x y : EuclideanSpace ℝ (Fin d)) :
    ‖field π a b x0 x - field π a b x0 y‖ ≤ (2200 * a / b ^ 2) * ‖x - y‖ := by
  rw [field, field, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hb.le)]
  calc _ ≤ (a / b) * (2200 * ‖normalize b x0 x - normalize b x0 y‖) :=
      mul_le_mul_of_nonneg_left (canonical_lipschitz π _ _) (div_nonneg ha hb.le)
    _ = _ := by rw [normalize_difference hb]; ring

lemma noise_norm (π : Fin (k + 1) ↪ Fin d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (x0 x : EuclideanSpace ℝ (Fin d)) : ‖noise π a b x0 x‖ ≤ 66 * a / b := by
  rw [noise, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hb.le)]
  exact (mul_le_mul_of_nonneg_left (projectedNoise_norm π _) (div_nonneg ha hb.le)).trans_eq (by ring)

lemma noise_lipschitz (π : Fin (k + 1) ↪ Fin d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (x0 x y : EuclideanSpace ℝ (Fin d)) :
    ‖noise π a b x0 x - noise π a b x0 y‖ ≤ (10242 * a / b ^ 2) * ‖x - y‖ := by
  rw [noise, noise, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hb.le)]
  calc _ ≤ (a / b) * (10242 * ‖normalize b x0 x - normalize b x0 y‖) :=
      mul_le_mul_of_nonneg_left (projectedNoise_lipschitz π _ _) (div_nonneg ha hb.le)
    _ = _ := by rw [normalize_difference hb]; ring

lemma objective_gap (π : Fin (k + 1) ↪ Fin d) {a : ℝ} (ha : 0 ≤ a) (b : ℝ)
    (x0 x : EuclideanSpace ℝ (Fin d)) : objective π a b x0 x0 - objective π a b x0 x ≤ 8 * a * (k + 1) := by
  have h := wall_gap π (radius k) (by norm_num : (0 : ℝ) ≤ 1 / 5) (normalize b x0 x)
  have hn : normalize b x0 x0 = 0 := by simp [normalize]
  simp only [objective, hn, ← mul_sub]
  exact (mul_le_mul_of_nonneg_left h ha).trans_eq (by ring)

lemma field_lower (π : Fin (k + 1) ↪ Fin d) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (x0 x : EuclideanSpace ℝ (Fin d))
    (htail : |project (radius k) (normalize b x0 x) (π (Fin.last k))| < 1) :
    a / (2 * b) ≤ ‖field π a b x0 x‖ := by
  rw [field, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha hb.le)]
  exact (show a / (2 * b) = (a / b) * (1 / 2) by ring).trans_le
    (mul_le_mul_of_nonneg_left (canonical_gradient_lower π _ htail) (div_nonneg ha hb.le))

end LongTails.Proofs.HolderNoiseHardScaling
