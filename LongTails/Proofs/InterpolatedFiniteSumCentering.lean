import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Calculus.FDeriv.Add

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.InterpolatedFiniteSumCentering

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

noncomputable def centered (f : E → ℝ) (v : E) (x : E) : ℝ := f x - ⟪v, x⟫

lemma centered_gradient (f : E → ℝ) (g : E → E) (v x : E)
    (hg : HasGradientAt f (g x) x) :
    HasGradientAt (centered f v) (g x - v) x := by
  rw [hasGradientAt_iff_hasFDerivAt, map_sub]
  exact hg.hasFDerivAt.sub ((InnerProductSpace.toDual ℝ E v).hasFDerivAt)

omit [CompleteSpace E] in
lemma centered_convex (f : E → ℝ) (v : E) (hf : ConvexOn ℝ Set.univ f) :
    ConvexOn ℝ Set.univ (centered f v) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hf.2 hx hy ha hb hab
  simp only [centered, inner_add_right, inner_smul_right, smul_eq_mul] at *
  linarith

lemma centered_minimizer (f : E → ℝ) (g : E → E) (z : E)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasGradientAt f (g x) x) :
    IsMinOn (centered f (g z)) Set.univ z := by
  intro x _
  have h := OracleTemplate.Gradient.convex_support hf hg z x
  change f z - ⟪g z, z⟫ ≤ f x - ⟪g z, x⟫
  rw [inner_sub_right] at h
  linarith

omit [CompleteSpace E] in
lemma centered_curvature (g : E → E) (v x : E) (L₀ L₁ : ℝ)
    (hL₁ : 0 ≤ L₁)
    (h : ‖fderiv ℝ g x‖ ≤ L₀ + L₁ * ‖g x‖) :
    ‖fderiv ℝ (fun y => g y - v) x‖ ≤
      (L₀ + L₁ * ‖v‖) + L₁ * ‖g x - v‖ := by
  rw [fderiv_sub_const]
  have hn : ‖g x‖ ≤ ‖g x - v‖ + ‖v‖ := by
    simpa only [sub_add_cancel] using norm_add_le (g x - v) v
  nlinarith [mul_le_mul_of_nonneg_left hn hL₁]

omit [CompleteSpace E] in
lemma centered_sum {ι : Type*} [Fintype ι] (f : ι → E → ℝ) (v : ι → E)
    (hv : ∑ i, v i = 0) (x : E) :
    ∑ i, centered (f i) (v i) x = ∑ i, f i x := by
  simp only [centered, Finset.sum_sub_distrib, ← sum_inner, hv, inner_zero_left, sub_zero]

omit [CompleteSpace E] in
lemma centered_reply_equal (f₁ f₂ : E → ℝ) (g₁ g₂ : E → E) (v x : E)
    (hf : f₁ x = f₂ x) (hg : g₁ x = g₂ x) :
    (centered f₁ v x, g₁ x - v) = (centered f₂ v x, g₂ x - v) := by
  simp only [centered, hf, hg]

end LongTails.Proofs.InterpolatedFiniteSumCentering
