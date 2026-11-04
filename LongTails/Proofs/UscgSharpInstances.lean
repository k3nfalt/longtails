import LongTails.Proofs.UscgSharpRamp
import LongTails.Proofs.UscgSharpScalar

namespace LongTails.Proofs.UscgSharpInstances

open MeasureTheory
open LongTails.Setups.UscgConstant (Space Problem)
open UscgSharpScalar

noncomputable def ramp (L g a x : ℝ) : ℝ := UscgSharpRamp.objective L g (x + a)

noncomputable def rampSlope (L g a x : ℝ) : ℝ := UscgSharpRamp.slope L g (x + a)

lemma ramp_derivative (L g a x : ℝ) : HasDerivAt (ramp L g a) (rampSlope L g a x) x := by
  convert (UscgSharpRamp.derivative L g (x + a)).comp x ((hasDerivAt_id x).add_const a) using 1
  · rfl
  · simp [rampSlope]

lemma rampSlope_continuous (L g a : ℝ) : Continuous (rampSlope L g a) := by
  unfold rampSlope UscgSharpRamp.slope
  fun_prop

lemma ramp_problem {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
    {L g a σ Δ : ℝ} {noise : Ω → ℝ} (hL : 0 < L) (hg : 0 ≤ g) (ha : 0 ≤ a)
    (hgap : g * a + g ^ 2 / (2 * L) ≤ Δ)
    (hnmeas : Measurable noise) (hnint : Integrable noise p) (hnmean : ∫ ω, noise ω ∂p = 0)
    (hvint : Integrable (fun ω => noise ω ^ 2) p) (hvar : ∫ ω, noise ω ^ 2 ∂p ≤ σ ^ 2) :
    Problem (normSeminorm ℝ (Space 1)) L L σ Δ 0
      (lift (ramp L g a)) (oracle (rampSlope L g a) noise) p := by
  have hh := problem (x₀ := 0) (fmin := -(g ^ 2 / (2 * L))) hL.le (ramp_derivative L g a)
    (rampSlope_continuous L g a).measurable
    (fun x y => by simpa [rampSlope] using UscgSharpRamp.slope_lipschitz hL.le g (x + a) (y + a))
    (fun x => UscgSharpRamp.lower_bound hL hg (x + a))
    (show ramp L g a 0 - -(g ^ 2 / (2 * L)) ≤ Δ by
      simpa [ramp, UscgSharpRamp.objective, min_eq_right ha] using hgap)
    hnmeas hnint hnmean hvint hvar
  simpa using hh

noncomputable def quadratic (L x : ℝ) : ℝ := L / 2 * x ^ 2

lemma quadratic_derivative (L x : ℝ) : HasDerivAt (quadratic L) (L * x) x := by
  convert ((hasDerivAt_id x).pow 2).const_mul (L / 2) using 1
  · rfl
  · simp only [id_eq]
    ring

lemma quadratic_problem {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]
    {L σ Δ : ℝ} {noise : Ω → ℝ} (hL : 0 ≤ L) (hΔ : 0 ≤ Δ)
    (hnmeas : Measurable noise) (hnint : Integrable noise p) (hnmean : ∫ ω, noise ω ∂p = 0)
    (hvint : Integrable (fun ω => noise ω ^ 2) p) (hvar : ∫ ω, noise ω ^ 2 ∂p ≤ σ ^ 2) :
    Problem (normSeminorm ℝ (Space 1)) L L σ Δ 0
      (lift (quadratic L)) (oracle (fun x => L * x) noise) p := by
  have hh := problem (x₀ := 0) (fmin := 0) hL (quadratic_derivative L) (measurable_const.mul measurable_id)
    (fun x y => by rw [← mul_sub, abs_mul, abs_of_nonneg hL])
    (fun x => show 0 ≤ quadratic L x by unfold quadratic; positivity)
    (show quadratic L 0 - 0 ≤ Δ by simpa [quadratic] using hΔ)
    hnmeas hnint hnmean hvint hvar
  simpa using hh

lemma ramp_plateau {L g a x : ℝ} (hx : -a ≤ x) : rampSlope L g a x = g := by
  exact UscgSharpRamp.plateau (by linarith)

end LongTails.Proofs.UscgSharpInstances
