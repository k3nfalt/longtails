import LongTails.Proofs.PointwiseHessianGeometry
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

namespace LongTails.Proofs.PointwiseHessianGrowth

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma second_order_growth {v v' v'' : ℝ → E} {a M₀ M₁ d : ℝ}
    (hv : ∀ t, HasDerivAt v (v' t) t)
    (hv' : ∀ t, HasDerivAt v' (v'' t) t)
    (ha : 0 < a) (hM₀ : 0 ≤ M₀) (hM₁ : M₁ ≤ a ^ 2) (hd : 0 ≤ d)
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) d, ‖v'' t‖ ≤ M₀ + M₁ * ‖v t‖) :
    ‖v d‖ ≤ (‖v 0‖ + ‖v' 0‖ / a + M₀ / a ^ 2) * Real.exp (a * d) := by
  let w := fun t : ℝ => (v t, a⁻¹ • v' t)
  let w' := fun t : ℝ => (v' t, a⁻¹ • v'' t)
  have hw (t : ℝ) : HasDerivAt w (w' t) t :=
    (hv t).prodMk ((hv' t).const_smul a⁻¹)
  have hn (y : E) : ‖a⁻¹ • y‖ = ‖y‖ / a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    ring
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) d) :
      ‖w' t‖ ≤ a * ‖w t‖ + M₀ / a := by
    have hfst : ‖v t‖ ≤ ‖w t‖ := norm_fst_le (w t)
    have hsnd : ‖v' t‖ / a ≤ ‖w t‖ := by simpa only [w, Prod.snd, hn] using norm_snd_le (w t)
    have hsnd' : ‖v' t‖ ≤ a * ‖w t‖ := by
      have := (div_le_iff₀ ha).mp hsnd
      nlinarith
    have hthird : ‖v'' t‖ / a ≤ a * ‖w t‖ + M₀ / a := by
      apply (div_le_iff₀ ha).mpr
      have h1 := mul_le_mul_of_nonneg_right hM₁ (norm_nonneg (v t))
      have h2 := mul_le_mul_of_nonneg_left hfst (sq_nonneg a)
      have he : M₀ / a * a = M₀ := div_mul_cancel₀ _ ha.ne'
      nlinarith [hb t ht]
    change max ‖v' t‖ ‖a⁻¹ • v'' t‖ ≤ _
    rw [hn]
    apply max_le
    · have : 0 ≤ M₀ / a := div_nonneg hM₀ ha.le
      linarith
    · exact hthird
  have hinit : ‖w 0‖ ≤ ‖v 0‖ + ‖v' 0‖ / a := by
    change max ‖v 0‖ ‖a⁻¹ • v' 0‖ ≤ _
    rw [hn]
    apply max_le
    · exact le_add_of_nonneg_right (by positivity)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  have hh := norm_le_gronwallBound_of_norm_deriv_right_le
    (show ContinuousOn w (Set.Icc 0 d) from
      (continuous_iff_continuousAt.mpr (fun t => (hw t).continuousAt)).continuousOn)
    (fun t _ => (hw t).hasDerivWithinAt) hinit
    (fun t ht => hbound t ⟨ht.1, ht.2.le⟩) d ⟨hd, le_rfl⟩
  have hfst : ‖v d‖ ≤ ‖w d‖ := norm_fst_le (w d)
  rw [sub_zero, gronwallBound_of_K_ne_0 ha.ne'] at hh
  have he : M₀ / a / a = M₀ / a ^ 2 := by ring
  rw [he] at hh
  have hnM : 0 ≤ M₀ / a ^ 2 := div_nonneg hM₀ (sq_nonneg a)
  nlinarith

end General

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma gradient_growth {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {M₀ M₁ : ℝ} (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁)
    (hT : ∀ x, ‖fderiv ℝ (fderiv ℝ (gradient f)) x‖ ≤ M₀ + M₁ * ‖gradient f x‖)
    (x d : E) :
    ‖gradient f (x + d)‖ ≤
      (‖gradient f x‖ + ‖fderiv ℝ (gradient f) x‖ * ‖d‖ + M₀ * ‖d‖ ^ 2) *
        Real.exp (1 + Real.sqrt M₁ * ‖d‖) := by
  obtain ⟨_, hg, hH⟩ := LongTails.Proofs.GradientDependentLocal.derivative_chain hf
  let v := fun t : ℝ => gradient f (x + t • d)
  let v' := fun t : ℝ => fderiv ℝ (gradient f) (x + t • d) d
  let v'' := fun t : ℝ => fderiv ℝ (fderiv ℝ (gradient f)) (x + t • d) d d
  let a := 1 + Real.sqrt M₁ * ‖d‖
  have ha1 : 1 ≤ a := by
    dsimp [a]
    exact le_add_of_nonneg_right (by positivity)
  have ha : 0 < a := by linarith
  have hl (t : ℝ) : HasDerivAt (fun u : ℝ => x + u • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hv (t : ℝ) : HasDerivAt v (v' t) t := (hg _).comp_hasDerivAt t (hl t)
  have hv' (t : ℝ) : HasDerivAt v' (v'' t) t := by
    simpa [v', v''] using ((hH _).comp_hasDerivAt t (hl t)).clm_apply (hasDerivAt_const t d)
  have hs : (Real.sqrt M₁ * ‖d‖) ^ 2 = M₁ * ‖d‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hM₁]
  have hrel : M₁ * ‖d‖ ^ 2 ≤ a ^ 2 := by
    have hn : 0 ≤ Real.sqrt M₁ * ‖d‖ := by positivity
    dsimp [a]
    nlinarith
  have hsecond (t : ℝ) (_ : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖v'' t‖ ≤ M₀ * ‖d‖ ^ 2 + (M₁ * ‖d‖ ^ 2) * ‖v t‖ := by
    have h1 := (fderiv ℝ (fderiv ℝ (gradient f)) (x + t • d) d).le_opNorm d
    have h2 := mul_le_mul_of_nonneg_right
      ((fderiv ℝ (fderiv ℝ (gradient f)) (x + t • d)).le_opNorm d) (norm_nonneg d)
    have h3 := mul_le_mul_of_nonneg_right (hT (x + t • d)) (sq_nonneg ‖d‖)
    dsimp [v'', v]
    nlinarith
  have hh := second_order_growth hv hv' ha (mul_nonneg hM₀ (sq_nonneg ‖d‖)) hrel
    (by norm_num : (0 : ℝ) ≤ 1) hsecond
  have hfirst := div_le_self (norm_nonneg (v' 0)) ha1
  have hbase := div_le_self (mul_nonneg hM₀ (sq_nonneg ‖d‖))
    (show 1 ≤ a ^ 2 by nlinarith)
  have hnorm : ‖v' 0‖ ≤ ‖fderiv ℝ (gradient f) x‖ * ‖d‖ := by
    simpa [v'] using (fderiv ℝ (gradient f) x).le_opNorm d
  have hp : ‖v 0‖ + ‖v' 0‖ / a + M₀ * ‖d‖ ^ 2 / a ^ 2 ≤
      ‖gradient f x‖ + ‖fderiv ℝ (gradient f) x‖ * ‖d‖ + M₀ * ‖d‖ ^ 2 := by
    simp only [v, zero_smul, add_zero]
    linarith
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos a).le
  simp only [mul_one] at hh
  simpa [v, a] using hh.trans hm

end LongTails.Proofs.PointwiseHessianGrowth
