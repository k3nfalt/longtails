import LongTails.Proofs.SlidingWireSim
import LongTails.Proofs.SlidingLowerMoreau
import LongTails.Proofs.SlidingLowerGap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SlidingWireGap

open LongTails.Proofs.SlidingLowerChain (Point)

open SlidingWireChain SlidingWireLocal SlidingWireConvex SlidingWireSim SlidingLowerOracle
open SlidingLowerMoreau SmoothConvexFiniteGeometry SmoothConvexFiniteWall SlidingWireGeometry

variable {d : ℕ}

lemma wG_far (r : ℕ) {δ R Λ : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R) (hΛ : 1 ≤ Λ) {k : ℕ}
    (hRk : 4 + 4 * (k : ℝ) + (k + 1) * ((r : ℝ) ^ 2 + 7) ^ 2 ≤ R ^ 2)
    (π : Fin (k + 1) ↪ Fin d) (u : Point d) (hu : 3 * R ≤ ‖u‖) :
    1 / 320 ≤ ‖wG r δ R Λ π u‖ := by
  rw [← wGp_full, wGp_far r hδ hR hΛ hRk π _ u hu, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by linarith)]
  have : 3 * R ≤ 4 * Λ * ‖u‖ := by nlinarith [norm_nonneg u]
  have h3 : (1 : ℝ) / 320 ≤ 3 * R := by
    nlinarith [sq_nonneg R]
  linarith

noncomputable def hB (a s ℓ : ℝ) (r : ℕ) (δ R Λ : ℝ) {k : ℕ} (π : Fin (k + 1) ↪ Fin d)
    (x0 x : Point d) : ℝ :=
  a * wF r δ R Λ π (rescale s x0 x) + ℓ / 2 * ‖x‖ ^ 2

noncomputable def fB (ℓ : ℝ) (x : Point d) : ℝ := -(ℓ / 2 * ‖x‖ ^ 2)

lemma fB_gradient (ℓ : ℝ) (x : Point d) : HasGradientAt (fB ℓ) ((-ℓ) • x) x := by
  have h := SlidingLowerInstance.sq_gradient (d := d) ℓ x
  have := SlidingLowerChain.grad_neg h
  unfold fB
  convert this using 1
  rw [neg_smul]

lemma hB_gradient (a s ℓ : ℝ) (r : ℕ) {δ R Λ : ℝ} (hR : 0 < R) (hΛ : 0 < Λ) {k : ℕ}
    (π : Fin (k + 1) ↪ Fin d) (x0 x : Point d) :
    HasGradientAt (hB a s ℓ r δ R Λ π x0)
      ((a / s) • wG r δ R Λ π (rescale s x0 x) + ℓ • x) x := by
  have h1 := scaled_gradient (F := wF r δ R Λ π) (G := wG r δ R Λ π) a s x0 x
    (wF_gradient r δ hR hΛ π _)
  have h2 := SlidingLowerInstance.sq_gradient (d := d) ℓ x
  exact SlidingLowerChain.grad_add h1 h2


structure GapHyp (W : WScale) (T : ℕ) : Prop where
  r_pos : 1 ≤ W.r
  δ_nonneg : 0 ≤ W.δ
  rδ : (W.r : ℝ) * W.δ ≤ 1 / 4
  R_one : 1 ≤ W.R
  Λ_ge : 1 ≤ W.Λ
  θ_le : W.θ ≤ 1 / 8
  R_k : 8 + 8 * ((T * (W.r ^ 2 + 2) : ℕ) : ℝ) ≤ W.R ^ 2
  R_G : 320 * (4 + 38 * ((T * (W.r ^ 2 + 2) : ℕ) : ℝ)) ≤ W.R
  R_big : 4 + 4 * ((T * (W.r ^ 2 + 2) : ℕ) : ℝ) +
    ((T * (W.r ^ 2 + 2) : ℕ) + 1) * ((W.r : ℝ) ^ 2 + 7) ^ 2 ≤ W.R ^ 2
  a_nonneg : 0 ≤ W.a
  s_pos : 0 < W.s
  smooth : W.a / W.s ^ 2 * 530 = W.ℓ
  ℓ_pos : 0 < W.ℓ

lemma F_eq (W : WScale) {k : ℕ} (π : Fin (k + 1) ↪ Fin d) (x0 x : Point d) :
    fB W.ℓ x + hB W.a W.s W.ℓ W.r W.δ W.R W.Λ π x0 x = W.a * wF W.r W.δ W.R W.Λ π (rescale W.s x0 x) := by
  unfold fB hB; ring

lemma F_weak (W : WScale) {T : ℕ} (hG : GapHyp W T) (π : Fin (T * (W.r ^ 2 + 2) + 1) ↪ Fin d)
    (x0 u v : Point d) :
    W.a * wF W.r W.δ W.R W.Λ π (rescale W.s x0 u) +
        ⟪(W.a / W.s) • wG W.r W.δ W.R W.Λ π (rescale W.s x0 u), v - u⟫ - W.ℓ / 2 * ‖v - u‖ ^ 2 ≤
      W.a * wF W.r W.δ W.R W.Λ π (rescale W.s x0 v) := by
  have h := wF_weak W.r W.δ (by linarith [hG.R_one]) hG.Λ_ge π (rescale W.s x0 u) (rescale W.s x0 v)
  rw [SlidingLowerGap.rescale_sub] at h
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hG.s_pos), real_inner_smul_right] at h
  rw [real_inner_smul_left]
  have hs := hG.s_pos
  have ha := hG.a_nonneg
  have hm := mul_le_mul_of_nonneg_left h ha
  have e1 : W.ℓ / 2 * ‖v - u‖ ^ 2 = W.a * (265 * (W.s⁻¹ * ‖v - u‖) ^ 2) := by
    rw [← hG.smooth]; field_simp; ring
  have e2 : W.a / W.s * ⟪wG W.r W.δ W.R W.Λ π (rescale W.s x0 u), v - u⟫ =
      W.a * (W.s⁻¹ * ⟪wG W.r W.δ W.R W.Λ π (rescale W.s x0 u), v - u⟫) := by ring
  rw [e1, e2]
  nlinarith

lemma gap_lowerB (W : WScale) {T : ℕ} (hG : GapHyp W T) (π : Fin (T * (W.r ^ 2 + 2) + 1) ↪ Fin d)
    (x0 x : Point d)
    (hx : 6 * W.R < ‖rescale W.s x0 x‖ ∨ |rescale W.s x0 x (π (Fin.last _))| ≤ W.θ) :
    min ((W.a / W.s) ^ 2 / (819200 * W.ℓ)) (49 * W.ℓ * W.s ^ 2 / 128) ≤
      (fB W.ℓ x + hB W.a W.s W.ℓ W.r W.δ W.R W.Λ π x0 x) -
        ⨅ v, ((fB W.ℓ v + hB W.a W.s W.ℓ W.r W.δ W.R W.Λ π x0 v) + W.ℓ * ‖v - x‖ ^ 2) := by
  have hR0 : 0 < W.R := by linarith [hG.R_one]
  have hΛ0 : 0 < W.Λ := by linarith [hG.Λ_ge]
  let g : Point d → Point d := fun z => (W.a / W.s) • wG W.r W.δ W.R W.Λ π (rescale W.s x0 z)
  have hF : ∀ z, HasGradientAt (fun z => fB W.ℓ z + hB W.a W.s W.ℓ W.r W.δ W.R W.Λ π x0 z) (g z) z := by
    intro z
    have := SlidingLowerChain.grad_add (fB_gradient W.ℓ z) (hB_gradient W.a W.s W.ℓ W.r (δ := W.δ) hR0 hΛ0 π x0 z)
    convert this using 1
    simp only [g]
    rw [neg_smul]; abel
  have hwc : ∀ u v, (fB W.ℓ u + hB W.a W.s W.ℓ W.r W.δ W.R W.Λ π x0 u) + ⟪g u, v - u⟫ -
      W.ℓ / 2 * ‖v - u‖ ^ 2 ≤ fB W.ℓ v + hB W.a W.s W.ℓ W.r W.δ W.R W.Λ π x0 v := by
    intro u v
    rw [F_eq, F_eq]
    exact F_weak W hG π x0 u v
  obtain ⟨y, hgy, hΓ⟩ := moreau_lower hG.ℓ_pos hF hwc x
  refine le_trans ?_ hΓ
  have hℓ := hG.ℓ_pos
  have hs := hG.s_pos
  set v := rescale W.s x0 y
  set w := rescale W.s x0 x
  by_cases hA : |v (π (Fin.last _))| < 1 ∨ 3 * W.R ≤ ‖v‖
  · have hl : 1 / 320 ≤ ‖wG W.r W.δ W.R W.Λ π v‖ := by
      rcases hA with h | h
      · exact wG_lower W.r hG.r_pos hG.δ_nonneg hG.rδ hR0 hG.Λ_ge hG.R_k hG.R_G π v h
      · exact wG_far W.r hG.δ_nonneg hR0 hG.Λ_ge hG.R_big π v h
    have hn : (W.a / W.s) * (1 / 320) ≤ (2 * W.ℓ) * ‖x - y‖ := by
      have h1 : ‖g y‖ = (W.a / W.s) * ‖wG W.r W.δ W.R W.Λ π v‖ := by
        simp only [g]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hG.a_nonneg hs.le)]
      have h2 : ‖g y‖ = (2 * W.ℓ) * ‖x - y‖ := by
        rw [hgy, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [← h2, h1]
      exact mul_le_mul_of_nonneg_left hl (div_nonneg hG.a_nonneg hs.le)
    have hxy : (W.a / W.s) / (640 * W.ℓ) ≤ ‖x - y‖ := by
      rw [div_le_iff₀ (by linarith)]; linarith
    have hq : ((W.a / W.s) / (640 * W.ℓ)) ^ 2 ≤ ‖x - y‖ ^ 2 :=
      pow_le_pow_left₀ (div_nonneg (div_nonneg hG.a_nonneg hs.le) (by linarith)) hxy 2
    calc min ((W.a / W.s) ^ 2 / (819200 * W.ℓ)) (49 * W.ℓ * W.s ^ 2 / 128)
        ≤ (W.a / W.s) ^ 2 / (819200 * W.ℓ) := min_le_left _ _
      _ = W.ℓ / 2 * ((W.a / W.s) / (640 * W.ℓ)) ^ 2 := by field_simp; ring
      _ ≤ W.ℓ / 2 * ‖x - y‖ ^ 2 := mul_le_mul_of_nonneg_left hq (by linarith)
  · push Not at hA
    obtain ⟨hv1, hv3⟩ := hA
    have hd : 7 / 8 ≤ ‖w - v‖ := by
      rcases hx with h | h
      · have := norm_sub_norm_le w v
        linarith [hG.R_one]
      · have h1 := SlidingLowerChain.coord_le (w - v) (π (Fin.last _))
        simp only [PiLp.sub_apply] at h1
        have h2 := abs_sub_abs_le_abs_sub (v (π (Fin.last _))) (w (π (Fin.last _)))
        rw [abs_sub_comm] at h2
        linarith [hG.θ_le]
    have hwv : w - v = W.s⁻¹ • (x - y) := by
      simp only [w, v]
      rw [← SlidingLowerGap.rescale_sub]
    rw [hwv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)] at hd
    have hxy : 7 * W.s / 8 ≤ ‖x - y‖ := by
      have h3 : W.s * (7 / 8) ≤ W.s * (W.s⁻¹ * ‖x - y‖) := mul_le_mul_of_nonneg_left hd hs.le
      rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at h3
      linarith
    have hq : (7 * W.s / 8) ^ 2 ≤ ‖x - y‖ ^ 2 := pow_le_pow_left₀ (by positivity) hxy 2
    calc min ((W.a / W.s) ^ 2 / (819200 * W.ℓ)) (49 * W.ℓ * W.s ^ 2 / 128)
        ≤ 49 * W.ℓ * W.s ^ 2 / 128 := min_le_right _ _
      _ = W.ℓ / 2 * (7 * W.s / 8) ^ 2 := by ring
      _ ≤ W.ℓ / 2 * ‖x - y‖ ^ 2 := mul_le_mul_of_nonneg_left hq (by linarith)

end LongTails.Proofs.SlidingWireGap
