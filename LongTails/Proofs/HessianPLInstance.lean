import LongTails.Proofs.HessianPLLocalized
import LongTails.Proofs.RelativeHessianInstance
import LongTails.Setups.HighDimensionalHessianLipschitzPL

namespace LongTails.Proofs.HessianPLInstance

open scoped RealInnerProductSpace
open OracleTemplate RelativeHessianScaling RelativeHessianSimulation RelativeHessianOracle
open RelativeHessianInstance HessianPLWell HessianPLLocalized
open LongTails.Setups.HighDimensionalHessianLipschitzPL

variable {d m : ℕ}

noncomputable def optimum (β : ℝ) (π : Fin (m + 1) ↪ Fin d) : EuclideanSpace ℝ (Fin d) :=
  (1 / β) • minimizer (axes π)

lemma scaled_optimum {a β : ℝ} (hβ : 0 < β) (π : Fin (m + 1) ↪ Fin d) :
    scaled a β π (optimum β π) = a * ((m + 1 : ℕ) * bottom) := by
  unfold scaled optimum
  rw [smul_smul, mul_one_div_cancel hβ.ne', one_smul, value_minimizer (axes_orthonormal π)]

lemma scaled_lower {a β : ℝ} (ha : 0 ≤ a) (π : Fin (m + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) : a * ((m + 1 : ℕ) * bottom) ≤ scaled a β π x := by
  unfold scaled
  exact mul_le_mul_of_nonneg_left (value_lower (axes_orthonormal π) (β • x)) ha

lemma optimum_isMin {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (π : Fin (m + 1) ↪ Fin d) :
    IsMinOn (scaled a β π) Set.univ (optimum β π) := by
  intro x _
  change scaled a β π (optimum β π) ≤ scaled a β π x
  rw [scaled_optimum hβ]
  exact scaled_lower ha π x

lemma minimum_value {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (π : Fin (m + 1) ↪ Fin d)
    {z : EuclideanSpace ℝ (Fin d)} (hz : IsMinOn (scaled a β π) Set.univ z) :
    scaled a β π z = a * ((m + 1 : ℕ) * bottom) := by
  apply le_antisymm
  · rw [← scaled_optimum (a := a) hβ π]
    exact hz (Set.mem_univ _)
  · exact scaled_lower ha π z

lemma scaled_initial_gap {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (π : Fin (m + 1) ↪ Fin d) :
    scaled a β π 0 - scaled a β π (optimum β π) ≤ a * (4 * (m + 1 : ℕ)) := by
  rw [scaled_optimum hβ]
  unfold scaled
  rw [smul_zero, RelativeHessianLocalized.initial_value]
  have hb := bottom_bounds
  have hm : (0 : ℝ) ≤ (m + 1 : ℕ) := by positivity
  have hpi := Real.pi_pos
  nlinarith [mul_nonneg (mul_nonneg ha hm) (show (0 : ℝ) ≤ bottom + 4 by linarith),
    mul_nonneg ha hpi.le]

lemma scaled_pl {a β μ : ℝ} (ha : 0 ≤ a) (hβ : 0 < β) (hμ : 0 ≤ μ)
    (hPL : 2 ^ 10 * μ * (m + 1 : ℕ) ≤ a * β ^ 2) (π : Fin (m + 1) ↪ Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    2 * μ * (scaled a β π x - scaled a β π (optimum β π)) ≤
      ‖gradient (scaled a β π) x‖ ^ 2 := by
  rw [scaled_optimum hβ, RelativeHessianScaling.gradient_norm ha hβ.le]
  have hp := value_pl (axes_orthonormal π) (β • x)
  unfold scaled
  have hQ : 0 ≤ ‖gradient (RelativeHessianLocalized.value (axes π)) (β • x)‖ ^ 2 := sq_nonneg _
  have h1 := mul_le_mul_of_nonneg_left hp
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hμ) ha)
  have h2 := mul_le_mul_of_nonneg_right hPL (mul_nonneg ha hQ)
  nlinarith

lemma scaled_hessian_lipschitz {a β : ℝ} (ha : 0 ≤ a) (hβ : 0 ≤ β)
    (π : Fin (m + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (gradient (scaled a β π)) x - fderiv ℝ (gradient (scaled a β π)) y‖ ≤
      2 ^ 56 * a * β ^ 3 * ‖x - y‖ := by
  have hd := (GradientDependentLocal.derivative_chain (scaled_smooth a β π)).2.2
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hd z).hasFDerivWithinAt)
    (fun z _ => RelativeHessianScaling.absolute_third ha hβ π z) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)

lemma admissible (q : Params) {a β : ℝ} {m : ℕ} (ha : 0 ≤ a) (hβ : 0 < β) (hμ : 0 ≤ q.μ)
    (hH : 2 ^ 56 * a * β ^ 3 ≤ q.H) (hPL : 2 ^ 10 * q.μ * (m + 1 : ℕ) ≤ a * β ^ 2)
    (hgap : a * (4 * (m + 1 : ℕ)) ≤ q.Δ) (π : Fin (m + 1) ↪ Fin q.d) :
    spec.admissible q (scaled a β π) (oracle a β π) := by
  refine ⟨fun x => ((scaled_smooth a β π).differentiable (by norm_num) x).hasGradientAt,
    fun x => ((GradientDependentLocal.derivative_chain (scaled_smooth a β π)).2.1 x).differentiableAt,
    ?_, ?_, ?_⟩
  · intro x y
    exact (scaled_hessian_lipschitz ha hβ.le π x y).trans
      (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  · exact ⟨optimum β π, optimum_isMin ha hβ π, (scaled_initial_gap ha hβ π).trans hgap,
      fun x => scaled_pl ha hβ hμ hPL π x⟩
  · intro history seed x
    exact (jet_scale a β π x).symm

end LongTails.Proofs.HessianPLInstance
