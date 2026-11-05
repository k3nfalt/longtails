import LongTails.Setups.StrongGrowthFiniteSumSecondOrder
import LongTails.Proofs.HessianLipschitzModel
import LongTails.Proofs.SvrgConvex
import LongTails.Proofs.ReshufflingPermutationMoments

namespace LongTails.Proofs.CoupledCubicPopulation

open LongTails.Setups.FiniteSumSmoothAndConvex
open OracleTemplate.NonlinearTemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

omit [FiniteDimensional ℝ E] in
lemma objective_contDiff_two (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i)) :
    ContDiff ℝ 2 (objective f) :=
  contDiff_const.mul (ContDiff.sum (fun i _ => hf i))

lemma objective_gradient (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (x : E) :
    gradient (objective f) x = (n : ℝ)⁻¹ • ∑ i, gradient (f i) x :=
  (OracleTemplate.FiniteSum.objective_gradient
    (oracle := fun ix => gradient (f ix.1) ix.2)
    (fun i y => ((hf i).differentiable (by norm_num) y).hasGradientAt) x).gradient

lemma component_gradient_derivative (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (i : Fin n) (x : E) :
    HasFDerivAt (gradient (f i)) (fderiv ℝ (gradient (f i)) x) x :=
  ((gradient_contDiff_one (hf i)).differentiable (by norm_num) x).hasFDerivAt

lemma objective_hessian (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 2 (f i)) (x : E) :
    fderiv ℝ (gradient (objective f)) x = (n : ℝ)⁻¹ • ∑ i, fderiv ℝ (gradient (f i)) x := by
  have hg : gradient (objective f) = fun y => (n : ℝ)⁻¹ • ∑ i, gradient (f i) y :=
    funext (objective_gradient f hf)
  rw [hg]
  have hd : HasFDerivAt (fun y => (n : ℝ)⁻¹ • ∑ i, gradient (f i) y)
      ((n : ℝ)⁻¹ • ∑ i, fderiv ℝ (gradient (f i)) x) x := by
    convert ((HasFDerivAt.sum (u := Finset.univ)
      (fun i _ => component_gradient_derivative f hf i x)).const_smul ((n : ℝ)⁻¹)) using 1
    funext y
    simp
  exact hd.fderiv

lemma objective_hessian_lipschitz [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 2 (f i)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hRMS : ∀ x y, (n : ℝ)⁻¹ * ∑ i,
      ‖fderiv ℝ (gradient (f i)) x - fderiv ℝ (gradient (f i)) y‖ ^ 2 ≤
        ρ ^ 2 * ‖x - y‖ ^ 2) (x y : E) :
    ‖fderiv ℝ (gradient (objective f)) x - fderiv ℝ (gradient (objective f)) y‖ ≤
      ρ * ‖x - y‖ := by
  have hn : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  let D : Fin n → E →L[ℝ] E := fun i =>
    fderiv ℝ (gradient (f i)) x - fderiv ℝ (gradient (f i)) y
  rw [objective_hessian f hf x, objective_hessian f hf y, ← smul_sub,
    ← Finset.sum_sub_distrib]
  change ‖(n : ℝ)⁻¹ • ∑ i, D i‖ ≤ ρ * ‖x - y‖
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hρ (norm_nonneg _))).mp
  have hsum := OracleTemplate.Reshuffling.norm_sum_sq_le_card Finset.univ D
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  calc
    ‖(n : ℝ)⁻¹ • ∑ i, D i‖ ^ 2 = (n : ℝ)⁻¹ ^ 2 * ‖∑ i, D i‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, mul_pow]
    _ ≤ (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ∑ i, ‖D i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = (n : ℝ)⁻¹ * ∑ i, ‖D i‖ ^ 2 := by field_simp
    _ ≤ ρ ^ 2 * ‖x - y‖ ^ 2 := hRMS x y
    _ = (ρ * ‖x - y‖) ^ 2 := by ring

end LongTails.Proofs.CoupledCubicPopulation
