import LongTails.Proofs.CubicRegularization
import LongTails.Proofs.MixedNoiseGeometry
import LongTails.Proofs.HessianAdaptiveCubicInvariants
import LongTails.Proofs.HessianAdaptiveCubicStep

namespace LongTails.Proofs.HessianAdaptiveCubicResidual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma gradient_taylor_on {C : Set E} (hC : Convex ℝ C) {g : E → E} {A : E → E →L[ℝ] E} {H : ℝ}
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x ∈ C, ∀ y ∈ C, ‖A x - A y‖ ≤ H * ‖x - y‖)
    (x d : E) (hx : x ∈ C) (hxd : x + d ∈ C) :
    ‖g (x + d) - g x - A x d‖ ≤ H * ‖d‖ ^ 2 / 2 := by
  let R : ℝ → E := fun t => g (x + t • d) - g x - t • A x d
  let D : ℝ → E := fun t => (A (x + t • d) - A x) d
  have hd (t : ℝ) : HasDerivAt R (D t) t := by
    have hline : HasDerivAt (fun t : ℝ => x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have ht := ((hg (x + t • d)).comp_hasDerivAt t hline).sub_const (g x)
    convert ht.sub ((hasDerivAt_id t).smul_const (A x d)) using 1
    · ext t
      rfl
    · simp [D]
  have hB (t : ℝ) : HasDerivAt (fun t : ℝ => H * ‖d‖ ^ 2 / 2 * t ^ 2)
      (H * ‖d‖ ^ 2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_mul (H * ‖d‖ ^ 2 / 2) using 1
    · ext t
      rfl
    · simp
      ring
  have hb (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ‖D t‖ ≤ H * ‖d‖ ^ 2 * t := by
    have h₁ := (A (x + t • d) - A x).le_opNorm d
    have hpath : x + t • d ∈ C := by
      simpa only [add_sub_cancel_left] using hC.add_smul_sub_mem hx hxd ⟨ht.1, ht.2.le⟩
    have h₂ := hLip (x + t • d) hpath x hx
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h₂
    have h₃ := mul_le_mul_of_nonneg_right h₂ (norm_nonneg d)
    dsimp [D]
    nlinarith only [h₁, h₃]
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := 0) (b := 1) (f := R) (f' := D)
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt)
    (B := fun t => H * ‖d‖ ^ 2 / 2 * t ^ 2)
    (by simp [R]) hB hb (x := 1) (by norm_num)
  simpa [R] using h


lemma residual_decomposition_bound (g0 gd gx gy s : E) (H A : E →L[ℝ] E)
    (ρ : ℝ) (htaylor : ‖gy - gx - A s‖ ≤ ρ * ‖s‖ ^ 2 / 2) :
    ‖gd - g0 - H s‖ ^ 2 ≤
      4 * ‖gd - gy‖ ^ 2 + 4 * ‖g0 - gx‖ ^ 2 +
      4 * ‖H - A‖ ^ 2 * ‖s‖ ^ 2 + ρ ^ 2 * ‖s‖ ^ 4 := by
  have hsum := OracleTemplate.MixedNoise.norm_sum_sq_le (Finset.univ : Finset (Fin 4))
    ![gd - gy, gy - gx - A s, -(g0 - gx), -((H - A) s)]
  have hid : (gd - gy) + (gy - gx - A s) + -(g0 - gx) + -((H - A) s) =
      gd - g0 - H s := by simp only [sub_apply]; abel
  simp only [Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat, Fin.sum_univ_zero,
    add_zero, norm_neg] at hsum
  have hvec : (gd - gy) + ((gy - gx - A s) + (-(g0 - gx) + -((H - A) s))) =
      gd - g0 - H s := by simpa only [add_assoc] using hid
  rw [hvec] at hsum
  have hop := (H - A).le_opNorm s
  have hsq := mul_self_le_mul_self (norm_nonneg _) htaylor
  have hopsq := mul_self_le_mul_self (norm_nonneg _) hop
  nlinarith

open LongTails.Setups.HessianAdaptiveStochasticConvex
open LongTails.Algorithms.HessianAdaptiveCubic
open LongTails.Proofs.HessianAdaptiveCubicInvariants

lemma model_residual_bound (p : Public) (s : State p.d) (gd : Point p.d)
    (f : Point p.d → ℝ) (hs : Invariant p s) (hdiff : Differentiable ℝ (gradient f))
    (hLip : ∀ x ∈ p.C, ∀ y ∈ p.C,
      ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖) :
    ‖gd - s.modelGradient - s.modelHessian (displacement s)‖ ^ 2 ≤
      4 * ‖gd - gradient f (queryPoint s)‖ ^ 2 +
      4 * ‖s.modelGradient - gradient f (center s)‖ ^ 2 +
      4 * ‖s.modelHessian - fderiv ℝ (gradient f) (center s)‖ ^ 2 * ‖displacement s‖ ^ 2 +
      p.ρ ^ 2 * ‖displacement s‖ ^ 4 := by
  have ht := gradient_taylor_on p.C.convex (fun x => (hdiff x).hasFDerivAt) hLip
    (center s) (displacement s) (center_mem p s hs) (queryPoint_mem p s hs)
  exact residual_decomposition_bound s.modelGradient gd (gradient f (center s))
    (gradient f (queryPoint s)) (displacement s) s.modelHessian
    (fderiv ℝ (gradient f) (center s)) p.ρ ht

lemma weighted_model_residual_bound (p : Public) (s : State p.d) (gd : Point p.d)
    (f : Point p.d → ℝ) (hD : 0 < p.D) (hs : Invariant p s)
    (hdiff : Differentiable ℝ (gradient f))
    (hLip : ∀ x ∈ p.C, ∀ y ∈ p.C,
      ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖) :
    residualWeight p s * ‖gd - s.modelGradient - s.modelHessian (displacement s)‖ ^ 2 ≤
      4 * ((s.iteration : ℝ) ^ 5 / p.D ^ 2) * ‖gd - gradient f (queryPoint s)‖ ^ 2 +
      4 * ((s.iteration : ℝ) ^ 5 / p.D ^ 2) * ‖s.modelGradient - gradient f (center s)‖ ^ 2 +
      4 * (s.iteration : ℝ) ^ 2 * ‖s.modelHessian - fderiv ℝ (gradient f) (center s)‖ ^ 2 +
      p.ρ ^ 2 * HessianAdaptiveCubicStep.movement p s := by
  have hW := residualWeight_nonneg p s hD hs
  have hraw := mul_le_mul_of_nonneg_left (model_residual_bound p s gd f hs hdiff hLip) hW
  have hwcap := HessianAdaptiveCubicWeights.residualWeight_upper_bound p s hD hs.scale hs.iteration
  have hcaps := HessianAdaptiveCubicStep.residual_movement_caps p s hD hs
  have hg₁ := mul_le_mul_of_nonneg_right hwcap (sq_nonneg ‖gd - gradient f (queryPoint s)‖)
  have hg₂ := mul_le_mul_of_nonneg_right hwcap (sq_nonneg ‖s.modelGradient - gradient f (center s)‖)
  have hh := mul_le_mul_of_nonneg_right hcaps.1
    (sq_nonneg ‖s.modelHessian - fderiv ℝ (gradient f) (center s)‖)
  have ht := mul_le_mul_of_nonneg_left hcaps.2 (sq_nonneg p.ρ)
  nlinarith only [hraw, hg₁, hg₂, hh, ht]

lemma model_scale_square_bound (p : Public) (s : State p.d) (gd : Point p.d)
    (f : Point p.d → ℝ) (hD : 0 < p.D) (hσ : 0 ≤ p.σg) (hs : Invariant p s)
    (hfloor : p.σg * (s.iteration : ℝ) ^ 3 / p.D ^ 2 ≤ s.scale)
    (hdiff : Differentiable ℝ (gradient f))
    (hLip : ∀ x ∈ p.C, ∀ y ∈ p.C,
      ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ p.ρ * ‖x - y‖) :
    (advance p s gd).scale ^ 2 ≤ s.scale ^ 2 +
      (4 * ((s.iteration : ℝ) ^ 5 / p.D ^ 2) * ‖gd - gradient f (queryPoint s)‖ ^ 2 +
      4 * ((s.iteration : ℝ) ^ 5 / p.D ^ 2) * ‖s.modelGradient - gradient f (center s)‖ ^ 2 +
      4 * (s.iteration : ℝ) ^ 2 * ‖s.modelHessian - fderiv ℝ (gradient f) (center s)‖ ^ 2 +
      p.ρ ^ 2 * HessianAdaptiveCubicStep.movement p s) / p.D ^ 2 +
      (p.σg * ((s.iteration + 1 : ℕ) : ℝ) ^ 3 / p.D ^ 2) ^ 2 -
      (p.σg * (s.iteration : ℝ) ^ 3 / p.D ^ 2) ^ 2 := by
  have hr : 0 ≤ residualWeight p s *
      ‖gd - s.modelGradient - s.modelHessian (displacement s)‖ ^ 2 / p.D ^ 2 :=
    div_nonneg (mul_nonneg (residualWeight_nonneg p s hD hs) (sq_nonneg _)) (sq_nonneg _)
  have hf : 0 ≤ p.σg * (s.iteration : ℝ) ^ 3 / p.D ^ 2 := by positivity
  have hnext : p.σg * (s.iteration : ℝ) ^ 3 / p.D ^ 2 ≤
      p.σg * ((s.iteration + 1 : ℕ) : ℝ) ^ 3 / p.D ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    apply mul_le_mul_of_nonneg_left _ hσ
    apply pow_le_pow_left₀ (Nat.cast_nonneg _)
    exact_mod_cast (Nat.le_succ s.iteration)
  have he := HessianAdaptiveCubicNormalization.scale_square_increment hr hf hfloor hnext
  have hw := div_le_div_of_nonneg_right
    (weighted_model_residual_bound p s gd f hD hs hdiff hLip) (sq_nonneg p.D)
  change (max _ _) ^ 2 ≤ _
  linarith

end LongTails.Proofs.HessianAdaptiveCubicResidual
