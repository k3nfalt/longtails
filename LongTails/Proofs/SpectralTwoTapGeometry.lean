import LongTails.Setups.SpectralTwoTapLogistic
import LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open InnerProductSpace
open scoped RealInnerProductSpace
open LongTails.Setups.SpectralTwoTapLogistic LongTails.Setups.TwoSampleQuadraticPerceptron
open LongTails.Proofs.TwoSampleQuadraticPerceptronEmbedding

namespace LongTails.Proofs.SpectralTwoTapGeometry

variable {d : ℕ}

private lemma taps_sq (c : Taps) : ‖c‖^2 = c.fst^2+c.snd^2 := by
  simp [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs]

private lemma tap_bound (x : Features d) (c : Taps) :
    ‖c.fst • x + c.snd • shift x‖ ≤ curvature x * ‖c‖ := by
  have hcur : 0 ≤ curvature x := Real.sqrt_nonneg _
  have hr : (curvature x)^2 = ‖x‖^2 + |⟪x,shift x⟫| :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (abs_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hcur (norm_nonneg _))).mp
  rw [norm_add_sq_real, norm_smul, norm_smul, norm_shift, real_inner_smul_left,
      real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
      sq_abs, sq_abs, mul_pow, hr, taps_sq]
  rcases le_total 0 ⟪x,shift x⟫ with h | h
  · rw [abs_of_nonneg h]
    nlinarith only [mul_nonneg (sq_nonneg (c.fst-c.snd)) h]
  · rw [abs_of_nonpos h]
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (c.fst+c.snd)) h]

private lemma adjoint_bound (x v : Features d) :
    ‖(WithLp.toLp 2 (⟪x,v⟫,⟪shift x,v⟫) : Taps)‖ ≤ curvature x * ‖v‖ := by
  let c : Taps := WithLp.toLp 2 (⟪x,v⟫,⟪shift x,v⟫)
  change ‖c‖ ≤ _
  have hh : ‖c‖^2 = ⟪c.fst • x + c.snd • shift x,v⟫ := by
    rw [taps_sq, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    change _ = ⟪x,v⟫*⟪x,v⟫ + ⟪shift x,v⟫*⟪shift x,v⟫
    simp [c, sq]
  have h := (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (tap_bound x c) (norm_nonneg v))
  rw [← hh] at h
  by_cases hc : 0 < ‖c‖
  · exact le_of_mul_le_mul_right (by linarith only [h] : ‖c‖*‖c‖ ≤ (curvature x*‖v‖)*‖c‖) hc
  · have := Real.sqrt_nonneg (‖x‖^2 + |⟪x,shift x⟫|)
    exact (le_of_not_gt hc).trans (mul_nonneg this (norm_nonneg _))

lemma action_bound (x : Features d) (z : State d) : ‖action x z‖ ≤ curvature x * ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [WithLp.prod_norm_sq_eq_of_L2 (action x z), mul_pow, WithLp.prod_norm_sq_eq_of_L2 z]
  have h₁ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr
    (adjoint_bound x z.snd)
  have h₂ := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr
    (tap_bound x z.fst)
  refine (add_le_add h₁ h₂).trans_eq ?_
  ring

lemma quadratic (x : Features d) (z u : State d) :
    ⟪action x z,u-z⟫ = score x u - score x z - score x (u-z) := by
  simp [action, score, margin, direction, WithLp.prod_inner_apply, inner_sub_right, inner_add_left,
    real_inner_smul_left, RCLike.inner_apply]
  ring

lemma score_abs (x : Features d) (z : State d) :
    |score x z| ≤ curvature x * ‖z‖^2/2 := by
  have hh : ⟪action x z,z⟫ = 2*score x z := by
    simp [action,score,margin,direction,
      WithLp.prod_inner_apply, inner_add_left, real_inner_smul_left, RCLike.inner_apply]
    ring
  have h := (abs_real_inner_le_norm (action x z) z).trans
    (mul_le_mul_of_nonneg_right (action_bound x z) (norm_nonneg _))
  rw [hh,abs_mul,abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))] at h
  linarith only [h]

lemma score_near (x : Features d) (z y : State d) {r : ℝ} (hr : ‖y-z‖ ≤ r) :
    |score x y-score x z| ≤ scoreError x z r := by
  have h := quadratic x z y
  rw [show score x y - score x z = ⟪action x z,y-z⟫ + score x (y-z) by linarith only [h]]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hr (norm_nonneg _))
  · apply (score_abs x (y-z)).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hr _) (Real.sqrt_nonneg _))
      (by norm_num)

lemma score_gradient (x : Features d) (z : State d) :
    HasGradientAt (score x) (action x z) z := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsBigO.trans_isLittleO _ (Asymptotics.isLittleO_norm_pow_id (n := 2) (by decide))
  apply Asymptotics.IsBigO.of_bound (curvature x/2)
  filter_upwards with v
  have h := quadratic x z (z+v)
  rw [add_sub_cancel_left] at h
  rw [show score x (z+v)-score x z-⟪action x z,v⟫ = score x v by linarith only [h]]
  simp only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖v‖)]
  linarith only [score_abs x v]

lemma risk_gradient {u : Input} (X : Images u) (z : State u.d) :
    HasGradientAt (risk X) (-descent X z) z := by
  let f (i : Fin u.n) (w : State u.d) := Real.log (1+Real.exp (-score (X i) w))
  let D (i : Fin u.n) := (Real.sigmoid (-score (X i) z)) • action (X i) z
  have single (i : Fin u.n) : HasFDerivAt (f i) (toDual ℝ _ (-(D i))) z := by
    have hs := (score_gradient (X i) z).hasFDerivAt.neg.exp.const_add (1:ℝ)
    have hl := hs.log (by positivity)
    convert hl using 1
    ext v
    simp [D,Real.sigmoid,Real.exp_neg,InnerProductSpace.toDual_apply_apply]
    field_simp
    ring
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (HasFDerivAt.sum (u := Finset.univ) (fun i _ => single i)).const_mul ((u.n:ℝ)⁻¹)
  convert h using 1
  · funext v
    simp [risk,f,Finset.sum_apply]
  · simp [D,descent,map_smul,map_sum,Finset.sum_neg_distrib]


end LongTails.Proofs.SpectralTwoTapGeometry
