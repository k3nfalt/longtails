import LongTails.Proofs.SoftRadialProjection
import LongTails.Proofs.AbcChainProfiles
import LongTails.Proofs.GdConvex

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SampleLossRadial

open SoftRadialProjection AbcChainProfiles

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def alignment (u x : E) : ℝ := ⟪u, project 1 x⟫

noncomputable def gate (z : ℝ) : ℝ := psi (64 * z)

noncomputable def gateSlope (z : ℝ) : ℝ := 64 * dpsi (64 * z)

lemma gate_mem (z : ℝ) : 0 ≤ gate z ∧ gate z ≤ 1 := ⟨psi_nonneg _, psi_le_one _⟩

lemma gateSlope_mem (z : ℝ) : 0 ≤ gateSlope z ∧ gateSlope z ≤ 256 := by
  unfold gateSlope
  constructor <;> linarith [dpsi_nonneg (64 * z), dpsi_le (64 * z)]

lemma gate_flat_below {z : ℝ} (h : z ≤ 1 / 128) : gate z = 0 ∧ gateSlope z = 0 := by
  have hz : 64 * z ≤ 1 / 2 := by linarith
  exact ⟨psi_of_le hz, by simp [gateSlope, dpsi_of_le hz]⟩

lemma gate_flat_above {z : ℝ} (h : 1 / 64 ≤ z) : gate z = 1 ∧ gateSlope z = 0 := by
  have hz : 1 ≤ 64 * z := by linarith
  exact ⟨psi_of_ge hz, by simp [gateSlope, dpsi_of_ge hz]⟩

lemma gate_model (x y : ℝ) :
    |gate y - gate x - gateSlope x * (y - x)| ≤ 131072 * (y - x) ^ 2 := by
  unfold gate gateSlope
  convert psi_model (64 * x) (64 * y) using 1 <;> ring_nf

lemma gateSlope_sq (x : ℝ) : gateSlope x ^ 2 ≤ 524288 * gate x := by
  have h := (abs_le.mp (gate_model x (x - gateSlope x / 262144))).2
  nlinarith [ (gate_mem (x - gateSlope x / 262144)).1 ]

lemma alignment_abs (u x : E) : |alignment u x| ≤ ‖u‖ := by
  calc
    _ ≤ ‖u‖ * ‖project 1 x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * 1 := mul_le_mul_of_nonneg_left (norm_project_le (by norm_num) _) (norm_nonneg _)
    _ = _ := mul_one _

lemma alignment_gradient [CompleteSpace E] (u x : E) :
    HasGradientAt (alignment u) (derivative 1 x u) x := by
  apply composition_gradient (by norm_num : (0 : ℝ) < 1)
  exact (hasGradientAt_iff_hasFDerivAt.mpr (innerSL ℝ u).hasFDerivAt)

lemma alignment_gradient_lipschitz (u x y : E) :
    ‖derivative 1 x u - derivative 1 y u‖ ≤ 6 * ‖u‖ * ‖x - y‖ := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using derivative_difference (by norm_num : (0 : ℝ) < 1) x y u

lemma alignment_sub (u x y : E) :
    |alignment u y - alignment u x| ≤ 2 * ‖u‖ * ‖y - x‖ := by
  unfold alignment
  rw [← inner_sub_right]
  calc
    _ ≤ ‖u‖ * ‖project 1 y - project 1 x‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u‖ * (2 * ‖y - x‖) := mul_le_mul_of_nonneg_left (project_lipschitz (by norm_num) y x) (norm_nonneg _)
    _ = _ := by ring

lemma alignment_model [CompleteSpace E] (u x y : E) :
    |alignment u y - alignment u x - ⟪derivative 1 x u, y - x⟫| ≤
      3 * ‖u‖ * ‖y - x‖ ^ 2 := by
  have h (w : E) := OracleTemplate.Gradient.smooth_upper_bound
    (alignment_gradient w) (alignment_gradient_lipschitz w) x y
  have lo := h (-u)
  simp only [alignment, inner_neg_left, map_neg, norm_neg] at lo
  have hi := h u
  unfold alignment at *
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma gate_alignment_model [CompleteSpace E] {u : E} (hu : ‖u‖ ≤ 1) (x y : E) :
    let q := alignment u x
    let dq := ⟪derivative 1 x u, y - x⟫
    |gateSlope q * dq| ≤ Real.sqrt (gate q) * (2048 * ‖y - x‖) ∧
    |gate (alignment u y) - gate q - gateSlope q * dq| ≤ (2048 * ‖y - x‖) ^ 2 := by
  intro q dq
  have hn := norm_nonneg (y - x)
  have hgn := (gate_mem q).1
  have hgs := (gateSlope_mem q).1
  have hgs' := (gateSlope_mem q).2
  have hs : gateSlope q ≤ 1024 * Real.sqrt (gate q) := by
    nlinarith [gateSlope_sq q, Real.sq_sqrt hgn, Real.sqrt_nonneg (gate q),
      sq_nonneg (gateSlope q - 1024 * Real.sqrt (gate q))]
  have hdq : |dq| ≤ 2 * ‖y - x‖ := (abs_real_inner_le_norm _ _).trans (by
    apply mul_le_mul_of_nonneg_right _ hn
    have h := derivative_norm_le (by norm_num : (0 : ℝ) < 1) x u
    linarith)
  have hδ : |alignment u y - q| ≤ 2 * ‖y - x‖ := (alignment_sub u x y).trans (by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) hn])
  have he : |alignment u y - q - dq| ≤ 3 * ‖y - x‖ ^ 2 := (alignment_model u x y).trans (by
    nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sq_nonneg ‖y - x‖)])
  constructor
  · rw [abs_mul, abs_of_nonneg hgs]
    nlinarith [mul_le_mul hs hdq (abs_nonneg _) (by positivity)]
  · have hid : gate (alignment u y) - gate q - gateSlope q * dq =
        gate (alignment u y) - gate q - gateSlope q * (alignment u y - q) +
        gateSlope q * (alignment u y - q - dq) := by ring
    rw [hid]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_of_nonneg hgs]
    have hpow := pow_le_pow_left₀ (abs_nonneg _) hδ 2
    rw [sq_abs] at hpow
    nlinarith [gate_model q (alignment u y), mul_le_mul hgs' he (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 256)]

private lemma scalar_barrier {n s q c : ℝ} (hn : 0 ≤ n) (hs : 1 ≤ s) (hsq : s ^ 2 = 1 + n ^ 2)
    (hqs : |q| * s ≤ n) (hq : q ≤ 1 / 64) (hc : 1 ≤ c) (hC : c ≤ 513)
    (hr : (2 * n ^ 2 - n / 8) * s ^ 2 ≤ c * q)
    (hu : c * (1 - q ^ 2) ≤ s / 8 + 2 * q * s ^ 2) : False := by
  have hspos : 0 < s := by linarith
  have hab : |q| ≤ n := le_trans (by nlinarith [mul_nonneg (abs_nonneg q) (sub_nonneg.mpr hs)] :
    |q| ≤ |q| * s) hqs
  by_cases hneg : q ≤ 0
  · have hcq : c * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
    have hnsmall : n ≤ 1 / 16 := by
      by_contra! h
      have : 0 < (2 * n ^ 2 - n / 8) * s ^ 2 :=
        mul_pos (by nlinarith [mul_pos (by linarith : 0 < n) (by linarith : 0 < n - 1 / 16)])
          (sq_pos_of_pos hspos)
      linarith
    have hq2 : q ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := sq_le_sq.mpr (by simpa using hab.trans hnsmall)
    have hns : n ^ 2 ≤ (1 / 16 : ℝ) ^ 2 := by gcongr
    have hss : s ≤ 2 := by nlinarith
    have := mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ 1 - q ^ 2 by linarith)
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hneg (sq_nonneg s)]
  · have hq0 : 0 ≤ q := by linarith
    have hq2 : q ^ 2 ≤ (1 / 64 : ℝ) ^ 2 := by gcongr
    have hcq : c * q ≤ 513 * (1 / 64) := mul_le_mul hC hq hq0 (by norm_num)
    have hs2 : s < 2 := by
      by_contra! h
      have hs4 : 4 ≤ s ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : 0 ≤ s + 2)]
      have hd : 4 ≤ 2 * n ^ 2 - n / 8 := by nlinarith [sq_nonneg (n - 1 / 8)]
      nlinarith [mul_le_mul hd hs4 (by norm_num : (0 : ℝ) ≤ 4) (by linarith : 0 ≤ 2*n^2-n/8)]
    have hs4 : s ^ 2 ≤ 4 := by nlinarith [mul_nonneg (by linarith : 0 ≤ 2 - s) (by linarith : 0 ≤ 2 + s)]
    have hprod : q * s ^ 2 ≤ (1 / 64) * 4 := mul_le_mul hq hs4 (sq_nonneg _) (by norm_num)
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (show 0 ≤ 1 - q ^ 2 by linarith)]

lemma radial_barrier (u x : E) (hu : ‖u‖ = 1) (hq : alignment u x ≤ 1 / 64)
    {c : ℝ} (hc : 1 ≤ c) (hC : c ≤ 513) :
    1 / 8 < ‖(2 : ℝ) • x - c • derivative 1 x u‖ := by
  let s := scale 1 x
  let q := alignment u x
  let g := derivative 1 x u
  have hs : 1 ≤ s := scale_one_le _ _
  have hs0 : 0 < s := by linarith
  have hs2 : s ^ 2 = 1 + ‖x‖ ^ 2 := by simpa [s] using scale_sq 1 x
  have hx : ⟪x, u⟫ = q * s := by
    dsimp [q, alignment, project, s]
    rw [inner_smul_right, real_inner_comm x u]
    field_simp [ne_of_gt (scale_pos 1 x)]
  have hab : |q| * s ≤ ‖x‖ := by
    have h := abs_real_inner_le_norm x u
    rwa [hx, abs_mul, abs_of_pos hs0, hu, mul_one] at h
  have h1 : ⟪g, x⟫ * s ^ 2 = q := by
    dsimp only [g]
    rw [derivative_apply, inner_sub_left, inner_smul_left, inner_smul_left,
      real_inner_self_eq_norm_sq]
    simp only [RCLike.conj_to_real]
    change (s⁻¹ * ⟪u, x⟫ - (⟪x, u⟫ / (1 ^ 2 * s ^ 3)) * ‖x‖ ^ 2) * s ^ 2 = q
    rw [show ⟪u, x⟫ = ⟪x, u⟫ from real_inner_comm _ _, hx]
    field_simp
    nlinarith [congrArg (fun z : ℝ => q * z) hs2]
  have h2 : ⟪g, u⟫ * s = 1 - q ^ 2 := by
    dsimp only [g]
    rw [derivative_apply, inner_sub_left, inner_smul_left, inner_smul_left,
      real_inner_self_eq_norm_sq, hu]
    change (s⁻¹ * 1 ^ 2 - (⟪x, u⟫ / (1 ^ 2 * s ^ 3)) * ⟪x, u⟫) * s = _
    rw [hx]
    field_simp
  by_contra! h
  change ‖(2 : ℝ) • x - c • g‖ ≤ 1 / 8 at h
  have hrad := (real_inner_le_norm ((2 : ℝ) • x - c • g) x).trans
    (mul_le_mul_of_nonneg_right h (norm_nonneg x))
  rw [inner_sub_left, inner_smul_left, inner_smul_left, real_inner_self_eq_norm_sq] at hrad
  have hdir := (neg_le_abs ⟪(2 : ℝ) • x - c • g, u⟫).trans (abs_real_inner_le_norm _ _)
  rw [hu, mul_one, inner_sub_left, inner_smul_left, inner_smul_left, hx] at hdir
  simp only [RCLike.conj_to_real] at hrad hdir
  apply scalar_barrier (norm_nonneg x) hs hs2 hab hq hc hC
  · calc
      _ ≤ (c * ⟪g, x⟫) * s ^ 2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg s)
      _ = _ := by rw [mul_assoc, h1]
  · calc
      _ = (c * ⟪g, u⟫) * s := by rw [mul_assoc, h2]
      _ ≤ (1 / 8 + 2 * (q * s)) * s := mul_le_mul_of_nonneg_right (by linarith) hs0.le
      _ = _ := by ring

end LongTails.Proofs.SampleLossRadial
