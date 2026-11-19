import LongTails.Setups.DistributedJacobianStrongGrowth
import LongTails.Proofs.DistributedJacobianStrongGrowthBudgetCharacterization
import LongTails.Proofs.DistributedJacobianStrongGrowthExecutionAccuracy

namespace LongTails.Theorems.DistributedJacobianLocalExtragradient

open DistributedTemplate
open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Proofs.DistributedJacobianStrongGrowthBudgetCharacterization

noncomputable def budget (p : Params) : Time :=
  let κ := p.L / p.μ
  let G := 2 + p.ρ / 8 + p.ρ ^ 2 / 128
  if p.R ≤ p.ε then 0
  else if 64 * κ * G ≤ (p.n : ℝ) then
    let T := min ⌊κ⌋₊ ⌊Real.log ((p.n : ℝ) / (64 * κ)) / Real.log G⌋₊
    let q := 1 + 32 * p.ρ * p.M * p.R * G ^ T / p.μ
    (65536 * (
      ((p.computeTime : ℝ) * p.ρ * κ ^ 2 + p.height *
        ((p.latency : ℝ) + p.timePerBit * (64 + p.d * Real.log (2 * (p.n : ℝ))))) *
        (1 + Real.log (p.d * q)) +
      (p.computeTime : ℝ) * κ * Real.log (p.R / p.ε) +
      p.height * ((p.latency : ℝ) + p.timePerBit *
        (64 + p.d * Real.log (2 + (p.n : ℝ) * p.d * p.R / (p.ε * q)))) *
        (κ / T * max (Real.log (2 * p.R / (p.ε * q))) 0))).toNNReal
  else p.computeTime * ⌈p.ρ * κ ^ 2 * Real.log (p.R ^ 2 / p.ε ^ 2)⌉₊

attribute [-instance] LongTails.Setups.AdaptiveHeavyTailSimplex.instMeasurableSpaceVector in
theorem result : DistributedTemplate.TimedConvergence
    LongTails.Setups.DistributedJacobianStrongGrowth.spec budget := by
  refine ⟨fun p => algorithm p (budget p + 1), ?_⟩
  dsimp only [spec]
  intro p hp
  refine ⟨trivial, ?_⟩
  intro I O hO
  obtain ⟨hI, g, S, rfl, hg⟩ := hO
  have hidle : budget p < budget p + 1 := by simp
  constructor
  · exact Filter.Eventually.of_forall (fun seed =>
      LongTails.Proofs.DistributedJacobianStrongGrowthTerminationExecution.finiteEvents
        p hp g S (budget p + 1) (budget p) seed hidle)
  · apply LongTails.Proofs.DistributedJacobianStrongGrowthExecutionAccuracy.execute_accuracy
      p hp I hI g S hg (budget p + 1) (budget p) hidle
    · intro hε hn
      change 64 * (p.L / p.μ) * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ≤ (p.n : ℝ) at hn
      have hb : budget p = envelopeTime p (localDepth p) (p.R / radius p (localDepth p)) := by
        simp only [budget, ite_eq_right (not_le_of_gt hε)]
        rw [ite_eq_left hn]
        exact envelopeTime_explicit_eq p hp
      rw [hb]
      exact envelopeTime_suffices p hp hn hε
    · intro hε hn
      change ¬ 64 * (p.L / p.μ) * (2 + p.ρ / 8 + p.ρ ^ 2 / 128) ≤ (p.n : ℝ) at hn
      simp only [budget, ite_eq_right (not_le_of_gt hε), ite_eq_right hn, baselineCount]
      exact le_of_eq (mul_comm _ _)

end LongTails.Theorems.DistributedJacobianLocalExtragradient
