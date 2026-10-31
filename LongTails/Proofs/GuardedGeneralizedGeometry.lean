import LongTails.Proofs.GeneralizedGradientStep
import LongTails.Proofs.NearestSetLocal
import LongTails.Proofs.HeavyTailedSospDescent

open Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GuardedGeneralizedGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma short_gradient_difference {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖) (x y : E)
    (hsmall : L1 * ‖y - x‖ ≤ 1 / 4) :
    ‖g y - g x‖ ≤ 2 * (L0 + L1 * ‖g x‖) * ‖y - x‖ := by
  have hexp : Real.exp (L1 * ‖y - x‖) ≤ 2 := by
    apply (Real.exp_le_exp.mpr hsmall).trans
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)
    norm_num at h
    linarith
  exact (OracleTemplate.GeneralizedAccelerated.gradient_growth hL0 hL1 hg hH y x).trans
    (by
      calc
        _ ≤ (L0 + L1 * ‖g x‖) * 2 * ‖y - x‖ := by gcongr
        _ = _ := by ring)

lemma short_upper {f : E → ℝ} {g : E → E} {L0 L1 : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖) (x y : E)
    (hsmall : L1 * ‖y - x‖ ≤ 1 / 4) :
    f y ≤ f x + ⟪g x, y - x⟫ + (L0 + L1 * ‖g x‖) * ‖y - x‖ ^ 2 := by
  have h := OracleTemplate.NearestSet.segment_upper_bound
    (L := 2 * (L0 + L1 * ‖g x‖)) hf x y (by
      intro t ht
      have hd : ‖x + t • (y - x) - x‖ ≤ ‖y - x‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2.le
      have hb := short_gradient_difference hL0 hL1 hg hH x (x + t • (y - x))
        ((mul_le_mul_of_nonneg_left hd hL1).trans hsmall)
      simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1, mul_assoc] using hb)
  nlinarith only [h]

omit [CompleteSpace E] in
lemma short_gradient_growth {g : E → E} {L0 L1 M η : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖) (x y : E)
    (hd : ‖y - x‖ ≤ η) (hsmall : L1 * η ≤ 1 / 4)
    (hbase : L0 * η ≤ M / 4) : ‖g y‖ ≤ 2 * max ‖g x‖ M := by
  have hs := short_gradient_difference hL0 hL1 hg hH x y
    ((mul_le_mul_of_nonneg_left hd hL1).trans hsmall)
  have ht := norm_le_norm_sub_add (g y) (g x)
  have hd' := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 2 * (L0 + L1 * ‖g x‖) by positivity)
  have hc := mul_le_mul_of_nonneg_right hsmall (norm_nonneg (g x))
  have hmaxg : ‖g x‖ ≤ max ‖g x‖ M := le_max_left _ _
  have hmaxM : M ≤ max ‖g x‖ M := le_max_right _ _
  nlinarith

lemma normalized_descent {f : E → ℝ} {g : E → E} {L0 L1 η : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hη : 0 ≤ η)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (hsmall : L1 * η ≤ 1 / 4) (x z : E) :
    f (x - η • (‖z‖⁻¹ • z)) ≤
      f x - η * ‖g x‖ / 2 + 2 * η * ‖g x - z‖ + L0 * η ^ 2 := by
  let v := ‖z‖⁻¹ • z
  have hv := LongTails.Proofs.MatrixPolarCharacterization.normalized_norm_le_one z
  have hvsq := LongTails.Proofs.MatrixPolarCharacterization.normalized_norm_sq_le z
  have heq : x - η • v - x = -(η • v) := by abel
  have hd : ‖x - η • v - x‖ ≤ η := by
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    exact mul_le_of_le_one_right hη hv
  have hu := short_upper hL0 hL1 hf hg hH x (x - η • v)
    ((mul_le_mul_of_nonneg_left hd hL1).trans hsmall)
  rw [heq, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hη] at hu
  have ha := mul_le_mul_of_nonneg_left
    (LongTails.Proofs.HeavyTailedSospDescent.normalized_alignment (g x) z) hη
  have hquad := mul_le_mul_of_nonneg_left hvsq
    (show 0 ≤ (L0 + L1 * ‖g x‖) * η ^ 2 by positivity)
  have hc := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ η * ‖g x‖ by positivity)
  dsimp only [v] at hu
  nlinarith [mul_nonneg hη (norm_nonneg (g x))]

lemma gradient_gap {f : E → ℝ} {g : E → E} {L0 L1 A m : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (hm : ∀ x, m ≤ f x) (x : E) (hA : 0 < A)
    (hcurv : L0 + L1 * ‖g x‖ ≤ A) :
    ‖g x‖ ^ 2 ≤ 8 * A * (f x - m) := by
  let t := (4 * A)⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  have htA : t * A = 1 / 4 := by dsimp [t]; field_simp
  have heq : x - t • g x - x = -(t • g x) := by abel
  have hs : L1 * ‖x - t • g x - x‖ ≤ 1 / 4 := by
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith [mul_le_mul_of_nonneg_left hcurv ht.le]
  have hu := short_upper hL0 hL1 hf hg hH x (x - t • g x) hs
  rw [heq, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hu
  have hquad := mul_le_mul_of_nonneg_right hcurv (sq_nonneg (t * ‖g x‖))
  have hl := hm (x - t • g x)
  have hdec : t * ‖g x‖ ^ 2 / 2 ≤ f x - m := by
    nlinarith [sq_nonneg ‖g x‖]
  have hscaled := mul_le_mul_of_nonneg_left hdec (show 0 ≤ 8 * A by positivity)
  nlinarith [sq_nonneg ‖g x‖]

lemma gradient_gap_exact {f : E → ℝ} {g : E → E} {L0 L1 m : ℝ}
    (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1)
    (hf : ∀ x, HasGradientAt f (g x) x) (hg : Differentiable ℝ g)
    (hH : ∀ x, ‖fderiv ℝ g x‖ ≤ L0 + L1 * ‖g x‖)
    (hm : ∀ x, m ≤ f x) (x : E) :
    ‖g x‖ ^ 2 ≤ 8 * (L0 + L1 * ‖g x‖) * (f x - m) := by
  by_contra hn
  have hd : 0 < ‖g x‖ ^ 2 - 8 * (L0 + L1 * ‖g x‖) * (f x - m) := by
    linarith
  let δ := (‖g x‖ ^ 2 - 8 * (L0 + L1 * ‖g x‖) * (f x - m)) /
    (16 * (f x - m + 1))
  have hden : 0 < 16 * (f x - m + 1) := by linarith [hm x]
  have hδ : 0 < δ := div_pos hd hden
  have he : δ * (16 * (f x - m + 1)) =
      ‖g x‖ ^ 2 - 8 * (L0 + L1 * ‖g x‖) * (f x - m) :=
    div_mul_cancel₀ _ hden.ne'
  have hb := gradient_gap hL0 hL1 hf hg hH hm x
    (A := L0 + L1 * ‖g x‖ + δ) (by positivity) (by linarith)
  nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr (hm x))]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma norm_bound_of_gap {G a b D M : ℝ}
    (hG : 0 ≤ G) (hM : 0 ≤ M)
    (hgap : G ^ 2 ≤ 8 * (a + b * G) * D)
    (hlinear : 16 * b * D ≤ M) (hconstant : 16 * a * D ≤ M ^ 2) :
    G ≤ M := by
  by_contra hn
  have hMG : M < G := lt_of_not_ge hn
  have hc := mul_le_mul_of_nonneg_right hlinear hG
  have hm := mul_nonneg (sub_nonneg.mpr hMG.le) hM
  nlinarith [sq_nonneg (G - M)]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma threshold_gap {G M a b D : ℝ} (hM : 0 < M) (hMG : M ≤ G)
    (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hgap : G ^ 2 ≤ 8 * (a + b * G) * D) :
    M ^ 2 ≤ 8 * (a + b * M) * D := by
  by_contra hn
  have hlin : 8 * b * D < M := by
    nlinarith [mul_nonneg ha hD]
  have hprod := mul_nonneg (sub_nonneg.mpr hMG)
    (show 0 ≤ G + M - 8 * b * D by linarith)
  nlinarith

end LongTails.Proofs.GuardedGeneralizedGeometry
