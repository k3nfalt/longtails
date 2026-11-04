import LongTails.Proofs.NormBallGeometry
import Mathlib

namespace LongTails.Proofs.UscgSharpScalar

open MeasureTheory
open scoped RealInnerProductSpace
open LongTails.Setups.UscgConstant (Space Problem IsBallLMO dualNorm)
open OracleTemplate.NormBallLMO

noncomputable def axis : Space 1 := EuclideanSpace.single 0 1

lemma axis_norm : ‖axis‖ = 1 := by simp [axis]

lemma axis_inner : ⟪axis, axis⟫ = 1 := by rw [real_inner_self_eq_norm_sq, axis_norm]; norm_num

lemma axis_repr (x : Space 1) : x = ⟪axis, x⟫ • axis := by
  ext i
  fin_cases i
  simp [axis, EuclideanSpace.inner_single_left]

noncomputable def lift (f : ℝ → ℝ) (x : Space 1) : ℝ := f ⟪axis, x⟫

lemma lift_gradient {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (x : Space 1) :
    HasGradientAt (lift f) (f' ⟪axis, x⟫ • axis) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hh := (hf ⟪axis, x⟫).hasFDerivAt.comp x
    (InnerProductSpace.toDual ℝ (Space 1) axis).hasFDerivAt
  convert hh using 1
  · rfl
  · ext y
    simp [InnerProductSpace.toDual_apply_apply, mul_comm]

lemma lift_gradient_eq {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (x : Space 1) :
    gradient (lift f) x = f' ⟪axis, x⟫ • axis := (lift_gradient hf x).gradient

lemma dual_axis (z : ℝ) : dualNorm (normSeminorm ℝ (Space 1)) (z • axis) = |z| := by
  have hR : ∀ x : Space 1, normSeminorm ℝ (Space 1) x ≤ 1 → ‖x‖ ≤ 1 := fun _ hx => hx
  apply le_antisymm
  · simpa [norm_smul, axis_norm, Real.norm_eq_abs] using dualNorm_le_norm hR (z • axis)
  · rcases le_total 0 z with hz | hz
    · have hh := inner_le_dualNorm hR (z • axis) (v := axis) (by simpa using axis_norm.le)
      simpa [inner_smul_left, axis_norm, abs_of_nonneg hz] using hh
    · have hh := inner_le_dualNorm hR (z • axis) (v := -axis) (by simp [axis_norm])
      simpa [inner_smul_left, inner_neg_right, axis_norm, abs_of_nonpos hz] using hh

lemma lmo_negative {lmo : Space 1 → Space 1}
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo) {z : ℝ} (hz : z < 0) :
    lmo (z • axis) = axis := by
  have hb := hlmo.feasible (z • axis)
  have hh := hlmo.minimal (z • axis) axis (by simpa using axis_norm.le)
  have hnorm : |⟪axis, lmo (z • axis)⟫| ≤ 1 := by
    have hh := abs_real_inner_le_norm axis (lmo (z • axis))
    simp only [axis_norm, one_mul] at hh
    exact hh.trans hb
  have he : ⟪axis, lmo (z • axis)⟫ = 1 := by
    simp only [inner_smul_left, conj_trivial, axis_inner] at hh
    have hu := (abs_le.mp hnorm).2
    nlinarith
  rw [axis_repr (lmo (z • axis)), he, one_smul]

lemma lmo_coordinate_lower {lmo : Space 1 → Space 1}
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo) (m : Space 1) :
    -1 ≤ ⟪axis, lmo m⟫ := by
  have hh := abs_real_inner_le_norm axis (lmo m)
  simp only [axis_norm, one_mul] at hh
  exact (abs_le.mp (hh.trans (hlmo.feasible m))).1

noncomputable def oracle {Ω : Type} (f' : ℝ → ℝ) (noise : Ω → ℝ)
    (x : Space 1) (ω : Ω) : Space 1 := (f' ⟪axis, x⟫ + noise ω) • axis

lemma problem {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
    {f f' : ℝ → ℝ} {L σ Δ x₀ fmin : ℝ} {noise : Ω → ℝ}
    (hL : 0 ≤ L) (hf : ∀ x, HasDerivAt f (f' x) x) (hfmeas : Measurable f')
    (hlip : ∀ x y, |f' x - f' y| ≤ L * |x - y|)
    (hlower : ∀ x, fmin ≤ f x) (hgap : f x₀ - fmin ≤ Δ)
    (hnmeas : Measurable noise) (hnint : Integrable noise p) (hnmean : ∫ ω, noise ω ∂p = 0)
    (hvint : Integrable (fun ω => noise ω ^ 2) p) (hvar : ∫ ω, noise ω ^ 2 ∂p ≤ σ ^ 2) :
    Problem (normSeminorm ℝ (Space 1)) L L σ Δ (x₀ • axis)
      (lift f) (oracle f' noise) p := by
  have hcoord : Measurable (fun x : Space 1 => ⟪axis, x⟫) :=
    (continuous_const.inner continuous_id).measurable
  have hnorm (x y : Space 1) : |⟪axis, x⟫ - ⟪axis, y⟫| ≤ ‖x - y‖ := by
    simpa [inner_sub_right, axis_norm] using abs_real_inner_le_norm axis (x - y)
  have hgrad (x y : Space 1) : gradient (lift f) x - gradient (lift f) y =
      (f' ⟪axis, x⟫ - f' ⟪axis, y⟫) • axis := by rw [lift_gradient_eq hf, lift_gradient_eq hf]; module
  have herr (x : Space 1) (ω : Ω) : oracle f' noise x ω - gradient (lift f) x = noise ω • axis := by
    rw [lift_gradient_eq hf]
    unfold oracle
    module
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [lift_gradient_eq hf]
    exact lift_gradient hf x
  · intro x y
    rw [hgrad, dual_axis]
    exact (hlip _ _).trans (mul_le_mul_of_nonneg_left (hnorm x y) hL)
  · intro x y
    rw [hgrad, norm_smul, axis_norm, mul_one, Real.norm_eq_abs]
    exact (hlip _ _).trans (mul_le_mul_of_nonneg_left (hnorm x y) hL)
  · refine ⟨fmin, fun x => hlower _, ?_⟩
    simpa [lift, inner_smul_right, axis_norm] using hgap
  · exact ((hfmeas.comp (hcoord.comp measurable_fst)).add (hnmeas.comp measurable_snd)).smul_const axis
  · intro x
    exact ((integrable_const _).add hnint).smul_const axis
  · intro x
    rw [lift_gradient_eq hf]
    unfold oracle
    rw [integral_smul_const, integral_add (integrable_const _) hnint, hnmean]
    simp
  · intro x
    simpa only [herr, norm_smul, axis_norm, mul_one, Real.norm_eq_abs, sq_abs] using hvint
  · intro x
    simpa only [herr, norm_smul, axis_norm, mul_one, Real.norm_eq_abs, sq_abs] using hvar

end LongTails.Proofs.UscgSharpScalar
