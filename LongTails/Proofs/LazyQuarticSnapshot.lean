import LongTails.Proofs.LazyQuarticParameters
import LongTails.Proofs.HessianSnapshotGeometry
import LongTails.Proofs.HessianLipschitzModel

namespace LongTails.Proofs.LazyQuarticSnapshot

open LongTails.Setups.ThirdDerivativeSmoothNonconvex
open LongTails.Algorithms.LazyQuarticMetric
open scoped RealInnerProductSpace

lemma sigma_relations (p : Params) (hp : spec.valid p) :
    0 < beta p / p.L₃ ∧ p.Δ = p.L₃ * (beta p / p.L₃) ^ 2 ∧ p.L₃ * (beta p / p.L₃) = beta p := by
  have hb := LazyQuarticParameters.beta_pos p hp
  have hs := LazyQuarticParameters.beta_square p hp
  refine ⟨div_pos hb hp.1, ?_, ?_⟩
  · rw [div_pow]
    field_simp [hp.1.ne']
    nlinarith only [hs]
  · field_simp [hp.1.ne']

lemma coordinates_metric (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ContDiff ℝ 3 f)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
      fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ p.L₃ * ‖x - y‖)
    (x : p.E) (hgap : ∀ y, f x - f y ≤ p.Δ) (v : p.E) :
    ‖coordinates p (fderiv ℝ (_root_.gradient f) x) v‖ ^ 2 =
      ⟪fderiv ℝ (_root_.gradient f) x v, v⟫ + 8 * beta p * ‖v‖ ^ 2 := by
  let H := fderiv ℝ (_root_.gradient f) x
  let B := H + (8 * beta p) • ContinuousLinearMap.id ℝ p.E
  have hH := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric (hf.of_le (by norm_num)) x
  have hB : B.toLinearMap.IsSymmetric := by
    intro u v
    change ⟪B u, v⟫ = ⟪u, B v⟫
    simp only [B, add_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    exact congrArg (fun z : ℝ => z + 8 * beta p * ⟪u, v⟫) (hH u v)
  have hs := sigma_relations p hp
  have hpos (u : p.E) : beta p * ‖u‖ ^ 2 ≤ ⟪B u, u⟫ := by
    have hh := ThirdOrderObjectiveGeometry.hessian_quadratic_lower hf hp.1 hs.1 hs.2.1 hT x u hgap
    rw [mul_assoc 4 p.L₃ (beta p / p.L₃), hs.2.2] at hh
    simp only [B, add_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    dsimp [H]
    nlinarith [mul_nonneg (LazyQuarticParameters.beta_pos p hp).le (sq_nonneg ‖u‖)]
  have hh := HessianSnapshotGeometry.coordinates_spec B hB (LazyQuarticParameters.beta_pos p hp) hpos v
  simpa only [coordinates, B, H, add_apply, smul_apply, ContinuousLinearMap.id_apply,
    inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] using hh

lemma coordinates_lower (p : Params) (hp : spec.valid p) (f : p.E → ℝ)
    (hf : ContDiff ℝ 3 f)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
      fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ p.L₃ * ‖x - y‖)
    (x : p.E) (hgap : ∀ y, f x - f y ≤ p.Δ) (v : p.E) :
    beta p * ‖v‖ ^ 2 ≤ ‖coordinates p (fderiv ℝ (_root_.gradient f) x) v‖ ^ 2 := by
  have hs := sigma_relations p hp
  have hh := ThirdOrderObjectiveGeometry.hessian_quadratic_lower hf hp.1 hs.1 hs.2.1 hT x v hgap
  rw [mul_assoc 4 p.L₃ (beta p / p.L₃), hs.2.2] at hh
  rw [coordinates_metric p hp f hf hT x hgap v]
  nlinarith [mul_nonneg (LazyQuarticParameters.beta_pos p hp).le (sq_nonneg ‖v‖)]

end LongTails.Proofs.LazyQuarticSnapshot
