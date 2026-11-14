import LongTails.Proofs.PointwiseHessianGeometry
import LongTails.Proofs.FrozenJacobianSplitting

open scoped RealInnerProductSpace

namespace LongTails.Proofs.PointwiseHessianNewton

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma linear_inverse_bounds [FiniteDimensional ℝ E] (H : E →L[ℝ] E)
    (hH : ∀ v, 0 ≤ ⟪H v, v⟫) {b : ℝ} (hb : 0 ≤ b) (r : E) :
    let d := Function.invFun (ContinuousLinearMap.id ℝ E + b • H) r
    d + b • H d = r ∧ ‖d‖ ≤ ‖r‖ ∧ ‖b • H d‖ ≤ ‖r‖ := by
  let J := ContinuousLinearMap.id ℝ E + b • H
  let d := Function.invFun J r
  have hsurj : Function.Surjective J := by
    simpa [J] using LongTails.Proofs.FrozenJacobianSplitting.op_surjective H hH
      (β := 1) (τ := b) one_pos hb
  have he : d + b • H d = r := by
    change J d = r
    exact Function.invFun_eq (hsurj r)
  change d + b • H d = r ∧ ‖d‖ ≤ ‖r‖ ∧ ‖b • H d‖ ≤ ‖r‖
  have hn := LongTails.Proofs.FrozenJacobianSplitting.op_norm_ge H hH
    (β := 1) hb d
  have hd : ‖d‖ ≤ ‖r‖ := by
    simpa [J, he] using hn
  have hs := congrArg (fun v : E => ‖v‖ ^ 2) he
  rw [norm_add_sq_real, inner_smul_right] at hs
  have hp : 0 ≤ b * ⟪d, H d⟫ := by
    rw [real_inner_comm]
    exact mul_nonneg hb (hH d)
  refine ⟨he, hd, ?_⟩
  nlinarith [sq_nonneg ‖d‖, norm_nonneg (b • H d), norm_nonneg r]

lemma forward_segment_bound {v v' v'' : ℝ → E} {r e L₀ L₁ : ℝ}
    (hv : ∀ t, HasDerivAt v (v' t) t)
    (hv' : ∀ t, HasDerivAt v' (v'' t) t)
    (hr : 0 ≤ r) (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁)
    (hzero : ‖v 0‖ ≤ 3 * r) (hfirst : ‖v' 0‖ ≤ r / 8)
    (hbase : L₀ * e ^ 2 ≤ r / 8) (hrelative : L₁ * e ^ 2 ≤ 1 / 8)
    (hsecond : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖v'' t‖ ≤ e ^ 2 * (L₀ + L₁ * ‖v t‖)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖v t‖ ≤ 4 * r := by
  have hc : Continuous (fun t => ‖v t‖) :=
    (continuous_iff_continuousAt.mpr (fun t => (hv t).continuousAt)).norm
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩) hc.continuousOn
  let M := e ^ 2 * (L₀ + L₁ * ‖v u‖)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖v'' t‖ ≤ M := by
    intro t ht
    apply (hsecond t ht).trans
    dsimp [M]
    gcongr
    exact hmax ht
  have hrem := LongTails.Proofs.GradientDependentCurvature.second_order_vector_remainder
    hv hv' hM hb hu
  have hrem' : ‖v u - v 0 - u • v' 0‖ ≤ M := by
    apply hrem.trans
    have hu2 : u ^ 2 ≤ 1 := by nlinarith [hu.1, hu.2]
    nlinarith
  have he : v u = (v u - v 0 - u • v' 0) + v 0 + u • v' 0 := by abel
  have hn := norm_add_le (v u - v 0 - u • v' 0) (v 0)
  have hn' := norm_add_le ((v u - v 0 - u • v' 0) + v 0) (u • v' 0)
  rw [← he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu.1] at hn'
  have hfirst' : u * ‖v' 0‖ ≤ r / 8 := by
    have := mul_le_mul_of_nonneg_right hu.2 (norm_nonneg (v' 0))
    linarith
  have hrel := mul_le_mul_of_nonneg_right hrelative (norm_nonneg (v u))
  have hfinal : ‖v u‖ ≤ 4 * r := by
    dsimp [M] at hrem'
    nlinarith
  exact fun t ht => (hmax ht).trans hfinal

lemma continuation_smallness {a r e b lam M₀ M₁ : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r) (he : 0 ≤ e) (hb : 0 ≤ b)
    (hbl : b ≤ lam) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (htune : a * (1 + M₁ * r ^ 2 + lam * M₀ * r) ≤ 1 / 64)
    (hstep : e ≤ 2 * a * r) :
    e ≤ r / 8 ∧ M₁ * e ^ 2 ≤ 1 / 8 ∧
      (b * M₀) * e ^ 2 ≤ r / 8 ∧ e * (b * M₀ + 4 * M₁ * r) ≤ 1 / 4 := by
  have hlam : 0 ≤ lam := hb.trans hbl
  have hX : 0 ≤ M₁ * r ^ 2 := by positivity
  have hY : 0 ≤ lam * M₀ * r := by positivity
  have ha1 : a ≤ 1 / 64 := by
    nlinarith [mul_nonneg ha hX, mul_nonneg ha hY]
  have haX : a * (M₁ * r ^ 2) ≤ 1 / 64 := by
    nlinarith [mul_nonneg ha hY]
  have haY : a * (lam * M₀ * r) ≤ 1 / 64 := by
    nlinarith [mul_nonneg ha hX]
  have he2 := pow_le_pow_left₀ he hstep 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_right ha1 hr
    nlinarith
  · calc
      M₁ * e ^ 2 ≤ M₁ * (2 * a * r) ^ 2 := mul_le_mul_of_nonneg_left he2 hM₁
      _ = 4 * a * (a * (M₁ * r ^ 2)) := by ring
      _ ≤ 4 * (1 / 64 : ℝ) * (1 / 64) := by gcongr
      _ ≤ 1 / 8 := by norm_num
  · calc
      b * M₀ * e ^ 2 ≤ lam * M₀ * (2 * a * r) ^ 2 := by gcongr
      _ = (4 * a * r) * (a * (lam * M₀ * r)) := by ring
      _ ≤ (4 * (1 / 64 : ℝ) * r) * (1 / 64) := by gcongr
      _ ≤ r / 8 := by nlinarith
  · calc
      e * (b * M₀ + 4 * M₁ * r) ≤ (2 * a * r) * (lam * M₀ + 4 * M₁ * r) := by
        gcongr
      _ = 2 * (a * (lam * M₀ * r)) + 8 * (a * (M₁ * r ^ 2)) := by ring
      _ ≤ 2 * (1 / 64 : ℝ) + 8 * (1 / 64) := by linarith
      _ ≤ 1 / 4 := by norm_num

lemma pointwise_newton_contraction {g : E → E} {H : E → E →L[ℝ] E}
    {T : E → E →L[ℝ] (E →L[ℝ] E)} {b r M₀ M₁ : ℝ}
    (hg : ∀ x, HasFDerivAt g (H x) x) (hH : ∀ x, HasFDerivAt H (T x) x)
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hT : ∀ x, ‖T x‖ ≤ M₀ + M₁ * ‖g x‖)
    (c x d : E) (hzero : ‖b • g x‖ ≤ 3 * r)
    (hfirst : ‖b • H x d‖ ≤ r / 8)
    (hbase : (b * M₀) * ‖d‖ ^ 2 ≤ r / 8)
    (hrelative : M₁ * ‖d‖ ^ 2 ≤ 1 / 8)
    (hsmall : ‖d‖ * (b * M₀ + 4 * M₁ * r) ≤ 1 / 4)
    (hstep : d + b • H x d = -(b • g x + x - c)) :
    ‖b • g (x + d) + (x + d) - c‖ ≤ ‖d‖ / 4 := by
  let v := fun t : ℝ => b • g (x + t • d)
  let v' := fun t : ℝ => b • H (x + t • d) d
  let v'' := fun t : ℝ => b • T (x + t • d) d d
  have hl (t : ℝ) : HasDerivAt (fun u : ℝ => x + u • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hv (t : ℝ) : HasDerivAt v (v' t) t :=
    ((hg _).comp_hasDerivAt t (hl t)).const_smul b
  have hv' (t : ℝ) : HasDerivAt v' (v'' t) t := by
    have hd : HasDerivAt (fun u : ℝ => H (x + u • d) d) (T (x + t • d) d d) t := by
      simpa using ((hH _).comp_hasDerivAt t (hl t)).clm_apply (hasDerivAt_const t d)
    convert (hasDerivAt_const t b).smul hd using 1
    simp [v'']
  have hn (t : ℝ) : ‖v t‖ = b * ‖g (x + t • d)‖ := by
    simp only [v, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
  have hsecond (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖v'' t‖ ≤ ‖d‖ ^ 2 * (b * M₀ + M₁ * ‖v t‖) := by
    have h1 := (T (x + t • d) d).le_opNorm d
    have h2 := mul_le_mul_of_nonneg_right ((T (x + t • d)).le_opNorm d) (norm_nonneg d)
    have h3 := mul_le_mul_of_nonneg_right (hT (x + t • d)) (sq_nonneg ‖d‖)
    have h4 : ‖T (x + t • d) d d‖ ≤ (M₀ + M₁ * ‖g (x + t • d)‖) * ‖d‖ ^ 2 := by
      nlinarith
    have h5 := mul_le_mul_of_nonneg_left h4 hb
    simp only [v'', norm_smul, Real.norm_eq_abs, abs_of_nonneg hb, hn]
    nlinarith
  have hbound := forward_segment_bound hv hv' hr (mul_nonneg hb hM₀) hM₁
    (by simpa [v] using hzero) (by simpa [v'] using hfirst) hbase hrelative hsecond
  have hM : 0 ≤ ‖d‖ ^ 2 * (b * M₀ + M₁ * (4 * r)) := by positivity
  have hrem := LongTails.Proofs.GradientDependentCurvature.second_order_vector_remainder
    hv hv' hM (fun t ht => (hsecond t ht).trans (by gcongr; exact hbound t ht))
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp)
  have he : b • g (x + d) + (x + d) - c = v 1 - v 0 - (1 : ℝ) • v' 0 := by
    simp only [v, v', one_smul, zero_smul, add_zero]
    apply sub_eq_zero.mp
    calc
      (b • g (x + d) + (x + d) - c) - (b • g (x + d) - b • g x - b • H x d) =
          (d + b • H x d) + (b • g x + x - c) := by module
      _ = 0 := by rw [hstep, neg_add_cancel]
  rw [he]
  apply hrem.trans
  have hh := mul_le_mul_of_nonneg_left hsmall (norm_nonneg d)
  nlinarith

end LongTails.Proofs.PointwiseHessianNewton
