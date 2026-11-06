import LongTails.Algorithms.CovarianceAcceleratedGrid
import LongTails.Proofs.CovarianceAcceleratedGeometry
import LongTails.Proofs.GdConvex
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Convexity
open scoped RealInnerProductSpace
open LongTails.Algorithms.CovarianceAcceleratedGrid

namespace LongTails.Proofs.CovarianceAcceleratedGrid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma grid_properties {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) :
    0 ∈ grid (E := E) R ε ∧ (∀ z ∈ grid (E := E) R ε, ‖z‖ ≤ R) ∧
      ∀ x : E, ‖x‖ ≤ R → ∃ z ∈ grid (E := E) R ε, ‖x - z‖ ≤ ε := by
  classical
  exact Classical.epsilon_spec (CovarianceAcceleratedGeometry.finite_ball_net hR hε)

omit [FiniteDimensional ℝ E] in
lemma centers_zero (R ε a : ℝ) : centers (E := E) R ε a 0 = 0 := rfl

lemma centers_norm_le {R ε a : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (ha : 0 < a)
    (i : Fin (Fintype.card ↥(grid (E := E) R ε) + 1)) :
    ‖centers (E := E) R ε a i‖ ≤ R / a := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [centers_zero, norm_zero]
    exact div_nonneg hR ha.le
  · change ‖a⁻¹ • ((Fintype.equivFin ↥(grid (E := E) R ε)).symm j).val‖ ≤ R / a
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    have hz := (grid_properties (E := E) hR hε).2.1
      ((Fintype.equivFin ↥(grid (E := E) R ε)).symm j).val
      ((Fintype.equivFin ↥(grid (E := E) R ε)).symm j).property
    simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr ha.le)

lemma centers_cover {R ε a : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (ha : 0 < a)
    {x : E} (hx : ‖x‖ ≤ R) :
    ∃ i : Fin (Fintype.card ↥(grid (E := E) R ε) + 1), ‖x - a • centers R ε a i‖ ≤ ε := by
  obtain ⟨z, hz, hdist⟩ := (grid_properties hR hε).2.2 x hx
  let j := Fintype.equivFin ↥(grid (E := E) R ε) ⟨z, hz⟩
  refine ⟨j.succ, ?_⟩
  change ‖x - a • (a⁻¹ • ((Fintype.equivFin ↥(grid (E := E) R ε)).symm j).val)‖ ≤ ε
  simp only [j, Equiv.symm_apply_apply, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
  exact hdist

lemma comparator_error {R ε a L : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (ha : 0 < a) (hL : 0 ≤ L)
    {f : E → ℝ} (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x0 xstar : E) (hmin : IsMinOn f Set.univ xstar) (hdist : ‖x0 - xstar‖ ≤ R) :
    ∃ i : Fin (Fintype.card ↥(grid (E := E) R ε) + 1),
      f (x0 + a • centers R ε a i) - f xstar ≤ L * ε ^ 2 / 2 := by
  have hxs : ‖xstar - x0‖ ≤ R := by simpa only [norm_sub_rev] using hdist
  obtain ⟨i, hi⟩ := centers_cover hR hε ha hxs
  have hi' : ‖x0 + a • centers R ε a i - xstar‖ ≤ ε := by
    have he : x0 + a • centers R ε a i - xstar = -((xstar - x0) - a • centers R ε a i) := by abel
    rw [he, norm_neg]
    exact hi
  have hzero : gradient f xstar = 0 := by
    apply (InnerProductSpace.toDual ℝ E).injective
    rw [toDual_gradient, map_zero]
    exact (hmin.isLocalMin Filter.univ_mem).fderiv_eq_zero
  have hs := OracleTemplate.Gradient.smooth_upper_bound hg hlip xstar (x0 + a • centers R ε a i)
  simp only [hzero, inner_zero_left, add_zero] at hs
  have hn : ‖x0 + a • centers R ε a i - xstar‖ ^ 2 ≤ ε ^ 2 := by
    nlinarith [norm_nonneg (x0 + a • centers R ε a i - xstar)]
  refine ⟨i, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hn (show 0 ≤ L / 2 by positivity)]

variable [MeasurableSpace E] [BorelSpace E]

lemma initial_potential_le {R ε a β γ : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (ha : 0 < a)
    (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (i : Fin (Fintype.card ↥(grid (E := E) R ε) + 1)) :
    LongTails.Algorithms.CovarianceAcceleratedMixture.potential (centers (E := E) R ε a) a β γ
      (StdSimplex.single i) (StdSimplex.single 0) ≤ R ^ 2 / (2 * a ^ 2) + β * R ^ 2 / 2 + γ := by
  have h := CovarianceAcceleratedGeometry.initial_potential_le (centers (E := E) R ε a) i 0
    (a := a) hβ hγ (div_nonneg hR ha.le) (centers_zero R ε a) (centers_norm_le hR hε ha i)
  have he : (R / a) ^ 2 / 2 + β * a ^ 2 / 2 * (R / a) ^ 2 + γ =
      R ^ 2 / (2 * a ^ 2) + β * R ^ 2 / 2 + γ := by
    field_simp
  exact h.trans_eq he

end LongTails.Proofs.CovarianceAcceleratedGrid
