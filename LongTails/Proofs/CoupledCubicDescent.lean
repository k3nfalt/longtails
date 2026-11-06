import LongTails.Proofs.CoupledCubicSelection
import LongTails.Proofs.HessianLipschitzModel
import LongTails.Proofs.CubicRegularization

open scoped RealInnerProductSpace

namespace LongTails.Proofs.CoupledCubicDescent

open LongTails.Setups.StrongGrowthFiniteSumSecondOrder
open LongTails.Algorithms.CoupledCubicTournament
open LongTails.Proofs.CoupledCubicExecution
open LongTails.Proofs.CoupledCubicSelection
open OracleTemplate.NonlinearTemporalDiscrepancy

lemma accurate_step (p : Params) (F : p.E → ℝ) (hf : ContDiff ℝ 2 F)
    (hρ : 0 < p.ρ) (hLip : ∀ y z, ‖fderiv ℝ (gradient F) y - fderiv ℝ (gradient F) z‖ ≤
      p.ρ * ‖y - z‖) (x : p.E) (sampled : Model p) (η : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 10000)
    (href : (fderiv ℝ (gradient F) x).toLinearMap.IsSymmetric)
    (hsampled : sampled.2.toLinearMap.IsSymmetric)
    (hacc : relativeModelAccurate p (gradient F x, fderiv ℝ (gradient F) x) sampled href η) :
    let u := modelStep p sampled
    ‖gradient F (x + u)‖ ≤ 20 * p.ρ * ‖u‖ ^ 2 ∧
      (∀ v : p.E, -5 * p.ρ * ‖u‖ * ‖v‖ ^ 2 ≤ ⟪v, fderiv ℝ (gradient F) (x + u) v⟫) ∧
      F (x + u) ≤ F x - p.ρ * ‖u‖ ^ 3 / 128 := by
  let reference : Model p := (gradient F x, fderiv ℝ (gradient F) x)
  let s := modelStep p reference
  let u := modelStep p sampled
  have hs := modelStep_stationary p hρ reference (fun a b => (href a b).symm)
  have hpsd (v : p.E) : 0 ≤ ⟪v, reference.2 v⟫ + p.ρ * ‖s‖ / 2 * ‖v‖ ^ 2 := by
    have hh := modelStep_psd p hρ reference (fun a b => (href a b).symm) v
    simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq] at hh
    change 0 ≤ ⟪v, reference.2 v⟫ + p.ρ * ‖modelStep p reference‖ / 2 * ‖v‖ ^ 2
    nlinarith
  by_cases hz : s = 0
  · have hsz := (zero_good_model_step p reference sampled η hρ hη0 (by linarith)
      href hsampled hz hacc.1 hacc.2).2.2
    have hg : gradient F x = 0 := by simpa [hz, reference, s] using hs
    have hp (v : p.E) : 0 ≤ ⟪v, fderiv ℝ (gradient F) x v⟫ := by
      have hh := hpsd v
      simpa [hz, reference] using hh
    simpa [hsz, hg] using And.intro (show (0 : ℝ) ≤ 0 by rfl) (And.intro hp (le_refl (F x)))
  · have hpos : 0 < ‖s‖ := norm_pos_iff.mpr hz
    have hform := modelStep_relative_error_form p reference sampled η hρ hη0 href hsampled hacc.2
    have hstable := modelStep_stable_decrease p reference sampled η hρ hη0 hη
      href hsampled hpos hacc.1 hform
    have hgeom := good_model_geometry p reference sampled η hρ hη0 hη href hsampled hacc.1 hacc.2
    have hb (y : p.E) : HasFDerivAt (gradient F) (fderiv ℝ (gradient F) y) y :=
      ((gradient_contDiff_one hf).differentiable (by norm_num) y).hasFDerivAt
    have hrem : ‖gradient F (x + u) - (reference.1 + reference.2 u)‖ ≤ p.ρ / 2 * ‖u‖ ^ 2 := by
      simpa only [sub_add_eq_sub_sub, div_mul_eq_mul_div] using CubicRegularization.gradient_taylor hb hLip x u
    have heH : reference.2 + (sampled.2 - reference.2) = sampled.2 := by abel
    have heg : reference.1 + (sampled.1 - reference.1) = sampled.1 := by abel
    have hu : reference.1 + (sampled.1 - reference.1) +
        (reference.2 + (sampled.2 - reference.2)) u + (p.ρ / 2 * ‖u‖) • u = 0 := by
      rw [heH, heg]
      exact modelStep_stationary p hρ sampled (fun a b => (hsampled a b).symm)
    have herr : ‖(sampled.2 - reference.2) (u - s)‖ ≤ 6 * η * p.ρ * ‖s‖ ^ 2 := by
      have hh := (hacc.2 (u - s)).trans (mul_le_mul_of_nonneg_left hgeom.2.2 hη0)
      nlinarith
    have hg := CoupledCubicStability.stable_gradient_bound reference.2 (sampled.2 - reference.2)
      reference.1 (sampled.1 - reference.1) s u (gradient F (x + u)) p.ρ p.ρ η hρ.le le_rfl
      hη hu hgeom.1.2 hacc.1 herr hrem
    have hr : ‖s‖ ^ 2 ≤ 4 * ‖u‖ ^ 2 := by
      have hh := hgeom.1.1
      change ‖s‖ / 2 ≤ ‖u‖ at hh
      nlinarith [norm_nonneg s, norm_nonneg u]
    refine ⟨?_, ?_, ?_⟩
    · have hh := mul_le_mul_of_nonneg_left hr hρ.le
      nlinarith
    · intro v
      have hchange : ‖fderiv ℝ (gradient F) (x + u) - reference.2‖ ≤ p.ρ * ‖u‖ := by
        simpa only [add_sub_cancel_left] using hLip (x + u) x
      have hh := CoupledCubicStability.stable_curvature_bound reference.2
        (fderiv ℝ (gradient F) (x + u)) s u p.ρ p.ρ hρ.le le_rfl hpsd hgeom.1.2 hchange v
      have hr' := mul_le_mul_of_nonneg_right hgeom.1.1
        (show 0 ≤ p.ρ * ‖v‖ ^ 2 by positivity)
      change ‖s‖ / 2 * (p.ρ * ‖v‖ ^ 2) ≤ ‖u‖ * (p.ρ * ‖v‖ ^ 2) at hr'
      nlinarith
    · have ht := CubicRegularization.objective_taylor
        (fun y => ((hf.differentiable (by norm_num)) y).hasGradientAt.hasFDerivAt) hb hLip x u
      have hupper := (abs_le.mp ht).2
      have hmodel := hstable.2.2
      change CappedCubicModel.model reference.2 reference.1 0 (p.ρ / 2) u ≤ -p.ρ * ‖s‖ ^ 3 / 16 at hmodel
      simp only [CappedCubicModel.model, zero_mul, add_zero] at hmodel
      have ht3 := pow_le_pow_left₀ (norm_nonneg u) hgeom.1.2 3
      change ‖u‖ ^ 3 ≤ (2 * ‖s‖) ^ 3 at ht3
      have hm := mul_le_mul_of_nonneg_left ht3 hρ.le
      change F (x + u) ≤ F x - p.ρ * ‖u‖ ^ 3 / 128
      change F (x + u) - F x - ⟪reference.1, u⟫ - ⟪u, reference.2 u⟫ / 2 ≤ p.ρ * ‖u‖ ^ 3 / 6 at hupper
      nlinarith

end LongTails.Proofs.CoupledCubicDescent
