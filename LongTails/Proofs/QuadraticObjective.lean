import LongTails.Proofs.QuadraticSpectralBounds
import Mathlib.Analysis.Calculus.Gradient.Basic

open scoped RealInnerProductSpace

namespace OracleTemplate.BatchedChebyshev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma quadratic_recenter {f : E → ℝ} (A : E →L[ℝ] E) (u xstar : E) (c : ℝ)
    (hf : ∀ x, f x = c + ‖A (x - u)‖ ^ 2 / 2)
    (hmin : IsMinOn f Set.univ xstar) :
    ∀ x, f x = f xstar + ‖A (x - xstar)‖ ^ 2 / 2 := by
  have hfu : f u = c := by simp [hf]
  have hs : f xstar ≤ f u := hmin (Set.mem_univ u)
  have hnorm : ‖A (xstar - u)‖ = 0 := by
    rw [hf xstar, hfu] at hs
    nlinarith [norm_nonneg (A (xstar - u))]
  have hzero : A (xstar - u) = 0 := norm_eq_zero.mp hnorm
  have hstar : f xstar = c := by simp [hf, hzero]
  intro x
  have he : A (x - u) = A (x - xstar) := by
    have heq : x - u = (x - xstar) + (xstar - u) := by abel
    rw [heq, map_add, hzero, add_zero]
  rw [hf, he, hstar]

lemma quadratic_gradient {f : E → ℝ} (A : E →L[ℝ] E) (u : E) (c : ℝ)
    (hf : ∀ x, f x = c + ‖A (x - u)‖ ^ 2 / 2) (x : E) :
    gradient f x = A.adjoint (A (x - u)) := by
  have h := TemporalDiscrepancy.factorized_quadratic_gradient A u x
  have hh : HasGradientAt f (A.adjoint (A (x - u))) x := by
    rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
    have hconst := h.const_add c
    convert hconst using 1
    funext y
    exact hf y
  exact hh.gradient

lemma quadratic_factor_upper {f : E → ℝ} (A : E →L[ℝ] E) (u : E) (c L : ℝ)
    (hf : ∀ x, f x = c + ‖A (x - u)‖ ^ 2 / 2)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    ∀ x, ‖A x‖ ^ 2 ≤ L * ‖x‖ ^ 2 := by
  intro x
  have h := hlip (u + x) u
  simp only [quadratic_gradient A u c hf, add_sub_cancel_left, sub_self, map_zero, sub_zero] at h
  calc
    ‖A x‖ ^ 2 = ⟪A.adjoint (A x), x⟫ := by
      rw [ContinuousLinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq]
    _ ≤ ‖A.adjoint (A x)‖ * ‖x‖ := real_inner_le_norm _ _
    _ ≤ (L * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = L * ‖x‖ ^ 2 := by ring

end OracleTemplate.BatchedChebyshev
