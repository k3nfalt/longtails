import LongTails.Proofs.CompositeGeneralizedLocal
import LongTails.Proofs.RelativeGeneralizedGeometry

open Set
open scoped RealInnerProductSpace

namespace OracleTemplate.RelativeGeneralized

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma gap_gradient_square {f : E → ℝ} {g : E → E} {L0 L1 D : ℝ} {u x : E}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1)
    (hf : ∀ w, HasGradientAt f (g w) w) (hg : Continuous g)
    (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    (hm : IsMinOn f univ u) (hgap : f x - f u ≤ D) :
    ‖g x‖ ^ 2 ≤ 8 * (L0 + L1 * ‖g x‖) * D := by
  let M := L0 + L1 * ‖g x‖
  have hM : 0 < M := by dsimp [M]; positivity
  let η := 1 / (4 * M)
  have hη : 0 < η := by dsimp [η]; positivity
  let w := x - η • g x
  have hw : w - x = -(η • g x) := by dsimp [w]; abel
  have hdist : ‖w - x‖ = η * ‖g x‖ := by
    rw [hw, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  have hprod : η * M = 1 / 4 := by dsimp [η]; field_simp
  have hr : L1 * (η * ‖g x‖) ≤ 1 / 2 := by
    have : L1 * ‖g x‖ ≤ M := by dsimp [M]; linarith
    nlinarith [mul_le_mul_of_nonneg_left this hη.le]
  have hup := CompositeGeneralized.ball_upper hL0.le hL1 hf hg hs hr
    (x := x) (u := x) (v := w) (by simp; positivity) (le_of_eq hdist)
  rw [hw, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη] at hup
  have hmin := hm (mem_univ w)
  change f u ≤ f w at hmin
  have hηsq : M * (η * ‖g x‖) ^ 2 = η / 4 * ‖g x‖ ^ 2 := by
    calc
      _ = (η * M) * η * ‖g x‖ ^ 2 := by ring
      _ = _ := by rw [hprod]; ring
  change f w ≤ f x - η * ‖g x‖ ^ 2 + M * (η * ‖g x‖) ^ 2 at hup
  rw [hηsq] at hup
  have hkey : η / 2 * ‖g x‖ ^ 2 ≤ D := by
    nlinarith [mul_nonneg hη.le (sq_nonneg ‖g x‖)]
  have hscale := mul_le_mul_of_nonneg_left hkey (show 0 ≤ 8 * M by positivity)
  have heq : 8 * M * (η / 2 * ‖g x‖ ^ 2) = ‖g x‖ ^ 2 := by
    calc
      _ = 4 * (η * M) * ‖g x‖ ^ 2 := by ring
      _ = _ := by rw [hprod]; ring
  rw [heq] at hscale
  exact hscale

lemma scalar_gradient_gap {G L0 L1 D : ℝ} (hG : 0 ≤ G) (h0 : 0 ≤ L0)
    (h1 : 0 ≤ L1) (hD : 0 ≤ D) (hs : G ^ 2 ≤ 8 * (L0 + L1 * G) * D) :
    G ≤ 4 * Real.sqrt (L0 * D) + 16 * L1 * D := by
  have hr := Real.sq_sqrt (mul_nonneg h0 hD)
  have hr0 := Real.sqrt_nonneg (L0 * D)
  have hy := sq_nonneg (G - 8 * L1 * D)
  have hb : G ^ 2 ≤ 16 * L0 * D + 64 * (L1 * D) ^ 2 := by nlinarith
  have ht : 0 ≤ 4 * Real.sqrt (L0 * D) + 16 * L1 * D := by positivity
  have hc : 16 * L0 * D + 64 * (L1 * D) ^ 2 ≤
      (4 * Real.sqrt (L0 * D) + 16 * L1 * D) ^ 2 := by
    nlinarith [mul_nonneg hr0 (mul_nonneg h1 hD)]
  exact (sq_le_sq₀ hG ht).mp (hb.trans hc)

lemma query_gradient_bound {f : E → ℝ} {g : E → E} {L0 L1 D : ℝ} {u x y : E}
    (hL0 : 0 < L0) (hL1 : 0 ≤ L1) (hD : 0 ≤ D)
    (hf : ∀ w, HasGradientAt f (g w) w) (hg : Continuous g)
    (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    (hm : IsMinOn f univ u) (hgap : f x - f u ≤ D)
    (hr : L1 * ‖y - x‖ ≤ 1 / 2)
    (hd : L0 * ‖y - x‖ ≤ Real.sqrt (L0 * D) / 2) :
    ‖g y‖ ≤ 9 * Real.sqrt (L0 * D) + 32 * L1 * D := by
  have hx := scalar_gradient_gap (norm_nonneg (g x)) hL0.le hL1 hD
    (gap_gradient_square hL0 hL1 hf hg hs hm hgap)
  have hy := CompositeGeneralized.segment_gradient_bound hL0.le hL1 hg hs x y hr
  linarith

lemma query_curvature_bound {G L0 L1 D : ℝ} (h0 : 0 ≤ L0) (h1 : 0 ≤ L1)
    (hD : 0 ≤ D) (hG : G ≤ 9 * Real.sqrt (L0 * D) + 32 * L1 * D) :
    L0 + L1 * G ≤ 49 * (L0 + L1 ^ 2 * D) := by
  have hr := Real.sq_sqrt (mul_nonneg h0 hD)
  have hs : L1 * Real.sqrt (L0 * D) ≤ (L0 + L1 ^ 2 * D) / 2 := by
    have hroot := Real.sq_sqrt hD
    have hroot0 := Real.sq_sqrt h0
    have hprod : Real.sqrt (L0 * D) = Real.sqrt L0 * Real.sqrt D :=
      Real.sqrt_mul h0 D
    rw [hprod]
    nlinarith [sq_nonneg (Real.sqrt L0 - L1 * Real.sqrt D)]
  have h := mul_le_mul_of_nonneg_left hG h1
  nlinarith [mul_nonneg (sq_nonneg L1) hD]

lemma local_projected_descent {f : E → ℝ} {g : E → E}
    {c u x y n v e : E} {R α η L0 L1 D : ℝ}
    (hR : 0 < R) (hα : α ≤ 1 / 100) (hη : 0 < η)
    (h0 : 0 ≤ L0) (h1 : 0 ≤ L1) (hD : 0 ≤ D)
    (hf : ∀ w, HasGradientAt f (g w) w) (hg : Continuous g)
    (hs : CompositeGeneralized.SymmetricSmooth g L0 L1)
    (hu : ‖u - c‖ ≤ R) (hx : ‖x - c‖ ≤ 2 * R) (hy : ‖y - c‖ ≤ 2 * R)
    (hn : ∀ w : E, ‖w - c‖ ≤ 2 * R → ⟪n, w - x⟫ ≤ 0)
    (hh : 0 ≤ ⟪g x, x - u⟫) (he : ‖e‖ ≤ α * ‖g y‖)
    (hv : v = g y + e + n) (hxy : y - x = η • v)
    (hdist : ‖x - y‖ ≤ 2 * η * ‖g y‖)
    (hG : ‖g y‖ ≤ 9 * Real.sqrt (L0 * D) + 32 * L1 * D)
    (hstep : η * (L0 + L1 ^ 2 * D) = 1 / 1024) :
    f x ≤ f y - η / 64 * ‖g y‖ ^ 2 := by
  have hcurv := query_curvature_bound h0 h1 hD hG
  have hscale := mul_le_mul_of_nonneg_left hcurv hη.le
  have hsmall : η * (L0 + L1 * ‖g y‖) ≤ 49 / 1024 := by
    nlinarith [hstep]
  have hr : L1 * (2 * η * ‖g y‖) ≤ 1 / 2 := by
    nlinarith [mul_nonneg hη.le h0]
  have hlip := CompositeGeneralized.ball_lipschitz h0 h1 hg hs hr
    (x := y) (u := x) (v := y) hdist (by simp; positivity)
  have hd : ‖x - y‖ = η * ‖v‖ := by
    rw [norm_sub_rev, hxy, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  rw [hd] at hlip
  have hgrad : ‖g x - g y‖ ≤ (1 / 4) * ‖v‖ := by
    have hm := mul_le_mul_of_nonneg_right hsmall (norm_nonneg v)
    nlinarith [norm_nonneg v]
  have hup := CompositeGeneralized.ball_upper h0 h1 hf hg hs hr
    (x := y) (u := y) (v := x) (by simp; positivity) hdist
  have hsub : x - y = -(η • v) := by rw [← hxy]; abel
  rw [hsub, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_pos hη] at hup
  have hupper : f x ≤ f y - η * ⟪g y, v⟫ + η / 8 * ‖v‖ ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hsmall
      (show 0 ≤ η * ‖v‖ ^ 2 by positivity)
    nlinarith [mul_nonneg hη.le (sq_nonneg ‖v‖)]
  exact projected_descent hR hu hx hy hn hh he hgrad hv hα le_rfl hη hxy hupper

end OracleTemplate.RelativeGeneralized
