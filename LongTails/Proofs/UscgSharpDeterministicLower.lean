import LongTails.Proofs.UscgSharpScalarPath
import LongTails.Proofs.UscgSharpInstances

namespace LongTails.Proofs.UscgSharpDeterministicLower

open scoped RealInnerProductSpace
open LongTails.Setups.UscgConstant (Space IsBallLMO dualNorm)
open UscgSharpScalar UscgSharpScalarPath UscgSharpInstances

lemma position_lower {Ω : Type} {α η : ℝ} (f' : ℝ → ℝ) (noise : Ω → ℝ)
    (lmo : Space 1 → Space 1) (ξ : ℕ → Ω) (he : 0 ≤ η)
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo) (t : ℕ) :
    -η * t ≤ position α η f' noise lmo ξ t := by
  induction t with
  | zero => simpa using (initial (α := α) (η := η) f' noise lmo ξ).1.ge
  | succ t ih =>
    have hh := position_succ_lower (α := α) f' noise lmo ξ he hlmo t
    push_cast
    linarith

lemma slow_stationarity {Ω : Type} {α η L g a : ℝ} {T : ℕ} (noise : Ω → ℝ)
    (lmo : Space 1 → Space 1) (ξ : ℕ → Ω) (he : 0 ≤ η) (hg : 0 ≤ g)
    (hlmo : IsBallLMO (normSeminorm ℝ (Space 1)) 1 lmo) (hslow : η * T ≤ a) :
    ∑ t ∈ Finset.range T, dualNorm (normSeminorm ℝ (Space 1))
      (gradient (lift (ramp L g a)) (trajectory α η (rampSlope L g a) noise lmo ξ t).1) = T * g := by
  calc
    _ = ∑ t ∈ Finset.range T, g := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [lift_gradient_eq (ramp_derivative L g a), dual_axis]
      change |rampSlope L g a (position α η (rampSlope L g a) noise lmo ξ t)| = g
      have hp := position_lower (α := α) (rampSlope L g a) noise lmo ξ he hlmo t
      have ht' : (t : ℝ) ≤ T := by exact_mod_cast (Finset.mem_range.mp ht).le
      have hh := mul_le_mul_of_nonneg_left ht' he
      rw [ramp_plateau (by linarith), abs_of_nonneg hg]
    _ = _ := by simp

lemma initial_stationarity {Ω : Type} {α η L g : ℝ} {T : ℕ} (noise : Ω → ℝ)
    (lmo : Space 1 → Space 1) (ξ : ℕ → Ω) (hg : 0 ≤ g) (hT : 0 < T) :
    g ≤ ∑ t ∈ Finset.range T, dualNorm (normSeminorm ℝ (Space 1))
      (gradient (lift (ramp L g 0)) (trajectory α η (rampSlope L g 0) noise lmo ξ t).1) := by
  simp_rw [lift_gradient_eq (ramp_derivative L g 0), dual_axis]
  have hh := Finset.single_le_sum (fun t (_ : t ∈ Finset.range T) =>
    abs_nonneg (rampSlope L g 0 ⟪axis, (trajectory α η (rampSlope L g 0) noise lmo ξ t).1⟫))
    (Finset.mem_range.mpr hT)
  simpa [trajectory, OracleTemplate.NormBallLMO.path_zero, rampSlope, UscgSharpRamp.slope, abs_of_nonneg hg] using hh

end LongTails.Proofs.UscgSharpDeterministicLower
