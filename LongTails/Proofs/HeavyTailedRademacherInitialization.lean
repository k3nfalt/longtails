import LongTails.Proofs.HeavyTailedProbeGeometry
import LongTails.Proofs.HeavyTailedMomentBounds
import LongTails.Proofs.SvrgConvex
import Mathlib.Analysis.InnerProductSpace.Adjoint

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedRademacherInitialization

open OracleTemplate.MatrixGeneralizedZO

lemma scalar_sign_amplification {d : ℕ} (g : EuclideanSpace ℝ (Fin d)) (hg : g ≠ 0) :
    ((PMF.uniformOfFintype (Fin d → Bool)).toMeasure).real
      {s | ‖g‖ ^ 2 / 2 ≤ ⟪g, signVec s⟫ ^ 2} ≥ 1 / 16 := by
  let P := (PMF.uniformOfFintype (Fin d → Bool)).toMeasure
  let X : (Fin d → Bool) → ℝ := fun s => ⟪g, signVec s⟫ ^ 2
  let A := {s | ‖g‖ ^ 2 / 2 ≤ X s}
  have hLp : MemLp X (ENNReal.ofReal 2) P := by
    apply (integrable_norm_rpow_iff (measurable_of_finite X).aestronglyMeasurable
      (by norm_num) (by simp)).mp
    exact Integrable.of_finite
  have hmean : (∫ s, X s ∂P) = ‖g‖ ^ 2 := by
    exact (OracleTemplate.FiniteSum.uniform_integral X).trans (expect_inner_vec_sq g)
  have hfour : (∫ s, X s ^ (2 : ℝ) ∂P) ≤ 3 * (‖g‖ ^ 2) ^ 2 := by
    simp only [Real.rpow_two]
    have heq : (fun s => X s ^ 2) = fun s => ⟪g, signVec s⟫ ^ 4 := by
      funext s
      dsimp [X]
      ring
    rw [heq, OracleTemplate.FiniteSum.uniform_integral]
    exact expect_inner_vec_four g
  have hroot : (∫ s, X s ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) ≤ 2 * ‖g‖ ^ 2 := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg (‖g‖ ^ 2)]
  have hb := HeavyTailedMomentBounds.positive_tail_of_moments
    (P := P) (A := A) Real.HolderConjugate.two_two hLp Integrable.of_finite
    (fun s => sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr hg))
    (Set.toFinite A).measurableSet (fun s hs => le_of_not_ge hs) hmean.ge hroot
  norm_num at hb
  exact hb

lemma sign_image_amplification {d : ℕ} (hd : 0 < d)
    (M : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (hMu : M u ≠ 0) :
    ((PMF.uniformOfFintype (Fin d → Bool)).toMeasure).real
      {s | ‖M u‖ ^ 2 / (2 * d) ≤
        ‖M (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector s)‖ ^ 2} ≥ 1 / 16 := by
  let w := ‖M u‖⁻¹ • M u
  let g := M.adjoint w
  have hMu0 : 0 < ‖M u‖ := norm_pos_iff.mpr hMu
  have hw : ‖w‖ = 1 := by
    dsimp only [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hMu0),
      inv_mul_cancel₀ hMu0.ne']
  have hinner : ⟪w, M u⟫ = ‖M u‖ := by
    dsimp only [w]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  have hgle : ‖M u‖ ≤ ‖g‖ := by
    have hh := real_inner_le_norm g u
    dsimp only [g] at hh
    rw [M.adjoint_inner_left, hinner, hu, mul_one] at hh
    exact hh
  have hg : g ≠ 0 := norm_pos_iff.mp (hMu0.trans_le hgle)
  have hb := scalar_sign_amplification g hg
  apply hb.trans (measureReal_mono ?_)
  intro s hs
  have hab : |⟪g, signVec s⟫| ≤ ‖M (signVec s)‖ := by
    dsimp only [g]
    rw [M.adjoint_inner_left]
    simpa [hw] using abs_real_inner_le_norm w (M (signVec s))
  have habsq : ⟪g, signVec s⟫ ^ 2 ≤ ‖M (signVec s)‖ ^ 2 := by
    nlinarith [sq_abs ⟪g, signVec s⟫, abs_nonneg ⟪g, signVec s⟫,
      norm_nonneg (M (signVec s))]
  have hraw : ‖M u‖ ^ 2 / 2 ≤ ‖M (signVec s)‖ ^ 2 := by
    change ‖g‖ ^ 2 / 2 ≤ ⟪g, signVec s⟫ ^ 2 at hs
    nlinarith [norm_nonneg g]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
  have hscale : ‖M (LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector s)‖ ^ 2 =
      ‖M (signVec s)‖ ^ 2 / d := by
    rw [LongTails.Algorithms.HeavyTailedEnergyProbe.initialVector, map_smul,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrt), mul_pow,
      inv_pow, Real.sq_sqrt hd0.le]
    ring
  change ‖M u‖ ^ 2 / (2 * d) ≤ _
  rw [hscale]
  have hh := div_le_div_of_nonneg_right hraw hd0.le
  convert hh using 1
  ring

end LongTails.Proofs.HeavyTailedRademacherInitialization
