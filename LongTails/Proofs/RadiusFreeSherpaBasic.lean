import LongTails.Algorithms.RadiusFreeSherpa
import LongTails.Proofs.SymmetricGeneralizedDescent
import LongTails.Proofs.BacktrackingAcceleratedStep
import Mathlib.Analysis.Complex.ExponentialBounds

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.RadiusFreeSherpa

open LongTails.Proofs.SymmetricGeneralizedDescent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev Hyp (f : E → ℝ) (g : E → E) (L0 L1 : ℝ) (u : E) : Prop :=
  ParameterFreeGeneralized.Hyp f g L0 L1 u

lemma Hyp.continuous {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u) :
    Continuous g :=
  H.diff.continuous

lemma Hyp.gmin {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u) : g u = 0 := by
  apply (toDual ℝ E).injective
  simpa using (H.min.isLocalMin Filter.univ_mem).hasFDerivAt_eq_zero (H.grad u).hasFDerivAt

omit [CompleteSpace E] in
lemma segment_bddAbove {g : E → E} (hg : Continuous g) (x y : E) :
    BddAbove ((fun z => ‖g z‖) '' segment ℝ x y) := by
  have hc : IsCompact (segment ℝ x y) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (AffineMap.lineMap_continuous)
  exact (hc.image (continuous_norm.comp hg)).bddAbove

lemma Hyp.segment_lipschitz {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E}
    (H : Hyp f g L0 L1 u) (x y : E) :
    ‖g x - g y‖ ≤ (L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y)) * ‖x - y‖ := by
  have hb := segment_bddAbove H.continuous x y
  have hbound : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ g z‖ ≤ L0 + L1 * sSup ((fun z => ‖g z‖) '' segment ℝ x y) := by
    intro z hz
    have h1 := H.hess z
    have h2 : ‖g z‖ ≤ sSup ((fun z => ‖g z‖) '' segment ℝ x y) :=
      le_csSup hb ⟨z, hz, rfl⟩
    have h3 := mul_le_mul_of_nonneg_left h2 H.L1_nonneg
    linarith
  exact Convex.norm_image_sub_le_of_norm_fderiv_le (f := g) (s := segment ℝ x y)
    (fun z _ => H.diff z) hbound (convex_segment x y) (right_mem_segment ℝ x y)
    (left_mem_segment ℝ x y)

lemma localCurvature_pos {L0 L1 : ℝ} (hL0 : 0 < L0) (hL1 : 0 ≤ L1) {G : ℝ} (hG : 0 ≤ G) :
    0 < localCurvature L0 L1 G := by
  unfold localCurvature
  positivity

lemma entropy_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ (1 + u) * Real.log (1 + u) - u := by
  have h1 : 0 < 1 + u := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr h1)
  rw [Real.log_inv] at h
  have h2 : (1 + u)⁻¹ - 1 = -(u / (1 + u)) := by field_simp; ring
  rw [h2] at h
  have h3 : u / (1 + u) ≤ Real.log (1 + u) := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 h1.le
  rw [mul_div_cancel₀ _ h1.ne'] at h4
  linarith

lemma phiRatio_nonneg {L0 L1 G : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hG : 0 < G) :
    0 ≤ phiRatio L0 L1 G := by
  unfold phiRatio
  have hu : 0 ≤ L1 * G / L0 := by positivity
  have := entropy_nonneg hu
  positivity

lemma weight_pos {L0 L1 G : ℝ} (A : ℝ) (hL0 : 0 < L0) (hL1 : 0 < L1) (hG : 0 < G) :
    0 < weight L0 L1 A G := by
  unfold weight
  have hL := localCurvature_pos hL0 hL1.le hG.le
  have hφ := phiRatio_nonneg hL0 hL1 hG
  have hb : 0 < 1 / (7 * localCurvature L0 L1 G) + phiRatio L0 L1 G := by positivity
  have := Real.sqrt_nonneg ((1 / (7 * localCurvature L0 L1 G) + phiRatio L0 L1 G) ^ 2 +
    4 * A / (7 * localCurvature L0 L1 G))
  simp only
  linarith

lemma quadratic_root (b : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    ((b + Real.sqrt (b ^ 2 + 4 * c)) / 2) ^ 2 = (b + Real.sqrt (b ^ 2 + 4 * c)) / 2 * b + c := by
  have hsq : Real.sqrt (b ^ 2 + 4 * c) ^ 2 = b ^ 2 + 4 * c := Real.sq_sqrt (by positivity)
  nlinarith [hsq]

lemma weight_eq {L0 L1 A G : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hA : 0 ≤ A) (hG : 0 < G) :
    weight L0 L1 A G ^ 2 =
      (A + weight L0 L1 A G) / (7 * localCurvature L0 L1 G) +
        weight L0 L1 A G * phiRatio L0 L1 G := by
  have hL := localCurvature_pos hL0 hL1.le hG.le
  have hφ := phiRatio_nonneg hL0 hL1 hG
  have hc : 0 ≤ A / (7 * localCurvature L0 L1 G) := by positivity
  have hw : weight L0 L1 A G = (1 / (7 * localCurvature L0 L1 G) + phiRatio L0 L1 G +
      Real.sqrt ((1 / (7 * localCurvature L0 L1 G) + phiRatio L0 L1 G) ^ 2 +
        4 * (A / (7 * localCurvature L0 L1 G)))) / 2 := by
    unfold weight
    simp only
    congr 3
    ring
  have hq := quadratic_root (1 / (7 * localCurvature L0 L1 G) + phiRatio L0 L1 G) hc
  rw [hw, hq]
  field_simp
  ring

lemma weight_sq_ge {L0 L1 A G : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hA : 0 ≤ A) (hG : 0 < G) :
    (A + weight L0 L1 A G) / (7 * localCurvature L0 L1 G) ≤ weight L0 L1 A G ^ 2 := by
  have h := weight_eq hL0 hL1 hA hG
  have hw := weight_pos A hL0 hL1 hG
  have hφ := phiRatio_nonneg hL0 hL1 hG
  nlinarith [mul_nonneg hw.le hφ]

lemma phi_inequality {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) (y : E) (hy : 0 < ‖g y‖) :
    f y + ⟪g y, u - y⟫ + phiRatio L0 L1 ‖g y‖ * ‖g y‖ ^ 2 ≤ f u := by
  have hL0 := H.L0_pos
  set G := ‖g y‖ with hGdef
  set s := L1 * G / L0 with hs
  have hs0 : 0 < s := by positivity
  have h1s : 0 < 1 + s := by linarith
  let v : E := G⁻¹ • g y
  have hv : ‖v‖ = 1 := by
    show ‖G⁻¹ • g y‖ = 1
    rw [norm_smul, norm_inv, norm_norm, ← hGdef, inv_mul_cancel₀ hy.ne']
  have hi : ⟪g y, v⟫ = G := by
    show ⟪g y, G⁻¹ • g y⟫ = G
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, ← hGdef, pow_two, ← mul_assoc,
      inv_mul_cancel₀ hy.ne', one_mul]
  set T := Real.log (1 + s) / L1 with hT
  have hT0 : 0 ≤ T := div_nonneg (Real.log_nonneg (by linarith)) hL1.le
  have hgrow := objective_ray_growth H.grad H.continuous hL1 (H.segment_lipschitz) u v H.gmin hv hT0
  have hexp : Real.exp (L1 * T) = 1 + s := by
    rw [hT, mul_div_cancel₀ _ hL1.ne', Real.exp_log h1s]
  rw [hexp] at hgrow
  have hsupp := OracleTemplate.Gradient.convex_support H.convex H.grad y (u + T • v)
  have he : u + T • v - y = (u - y) + T • v := by abel
  rw [he, inner_add_right, real_inner_smul_right, hi] at hsupp
  have hTG : T * G = L0 / L1 ^ 2 * (s * Real.log (1 + s)) := by
    rw [hT, hs]; field_simp
  have hphi : phiRatio L0 L1 G * G ^ 2 = L0 / L1 ^ 2 * ((1 + s) * Real.log (1 + s) - s) := by
    unfold phiRatio
    rw [← hs]
    field_simp
  rw [hphi]
  have hL1T : L1 * T = Real.log (1 + s) := by rw [hT]; field_simp
  rw [hL1T] at hgrow
  nlinarith [hgrow, hsupp, hTG]

lemma phi_log_lower {L0 L1 G : ℝ} (hL0 : 0 < L0) (hL1 : 0 < L1) (hG : 0 < G) :
    Real.log (1 + L1 * G / L0) - 1 ≤ L1 * phiRatio L0 L1 G * G := by
  unfold phiRatio
  set s := L1 * G / L0 with hs
  have hs0 : 0 < s := by positivity
  have hlog : 0 ≤ Real.log (1 + s) := Real.log_nonneg (by linarith)
  have hrw : L1 * (L0 / L1 ^ 2 * ((1 + s) * Real.log (1 + s) - s) / G ^ 2) * G =
      ((1 + s) * Real.log (1 + s) - s) / s := by
    rw [hs]; field_simp
  rw [hrw]
  rw [le_div_iff₀ hs0]
  nlinarith [mul_nonneg hlog hs0.le]

lemma descent_step {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) (y : E) :
    f (y - (1 / (4 * localCurvature L0 L1 ‖g y‖)) • g y) ≤
      f y - 5 * ‖g y‖ ^ 2 / (24 * localCurvature L0 L1 ‖g y‖) :=
  normalized_descent H.grad H.continuous H.L0_pos hL1 H.segment_lipschitz y

lemma descent_dist {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) (y : E) :
    ‖y - (1 / (4 * localCurvature L0 L1 ‖g y‖)) • g y - u‖ ≤ ‖y - u‖ :=
  normalized_distance_le H.grad H.continuous H.convex H.L0_pos hL1 H.segment_lipschitz u y H.min

lemma gradient_pair_bound {f : E → ℝ} {g : E → E} {L0 L1 : ℝ} {u : E} (H : Hyp f g L0 L1 u)
    (hL1 : 0 < L1) (x y : E) (hxy : L1 * ‖x - y‖ ≤ 1 / 2) :
    ‖g x - g y‖ ≤ 2 * localCurvature L0 L1 ‖g y‖ * ‖x - y‖ := by
  have h := LongTails.Proofs.SymmetricGeneralizedSmooth.gradient_difference_bound H.continuous
    H.L0_pos.le hL1 H.segment_lipschitz x y
  have hexp : Real.exp (L1 * ‖x - y‖) ≤ 2 := by
    calc Real.exp (L1 * ‖x - y‖) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hxy
      _ ≤ 2 := by
        have := Real.exp_one_lt_three
        have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; norm_num
        nlinarith [Real.exp_pos (1 / 2)]
  have hL : 0 < localCurvature L0 L1 ‖g y‖ := localCurvature_pos H.L0_pos hL1.le (norm_nonneg _)
  have hn : 0 ≤ ‖x - y‖ := norm_nonneg _
  calc ‖g x - g y‖ ≤ (L0 + L1 * ‖g y‖) * Real.exp (L1 * ‖x - y‖) * ‖x - y‖ := h
    _ ≤ (L0 + L1 * ‖g y‖) * 2 * ‖x - y‖ := by
      apply mul_le_mul_of_nonneg_right _ hn
      exact mul_le_mul_of_nonneg_left hexp hL.le
    _ = 2 * localCurvature L0 L1 ‖g y‖ * ‖x - y‖ := by unfold localCurvature; ring

end OracleTemplate.RadiusFreeSherpa
