import LongTailsOnline.Setups.StationaryTaskAllocation
import LongTailsOnline.Proofs.TaskAllocationRegret

namespace LongTailsOnline.Theorems.ParallelTaskAllocation

open LongTailsOnline.Setups.StationaryTaskAllocation
open LongTailsOnline.Algorithms.ParallelTaskAllocation
open LongTailsOnline.Proofs.TaskAllocation

noncomputable def method : (p : spec.Public) →
    OnlineTemplate.Algorithm (spec.Observation p) (spec.Action p) (spec.Feedback p) :=
  LongTailsOnline.Algorithms.ParallelTaskAllocation.algorithm

noncomputable def bound : (p : spec.Params) → spec.Bound p := fun p =>
  let n := p.config.k + 1
  let B := p.config.B
  let K := p.config.T
  let σ : ℝ := max 1 p.config.σ
  let t := Real.log (64 * (n : ℝ) * (B : ℝ) ^ 2 * (K : ℝ) ^ 3 * (1 + σ))
  let χ := (1 + σ * Real.sqrt (2 * t)) * t
  let d := (B : ℝ) / n + (n : ℝ) / B
  let ε := Real.sqrt (d / K)
  let J := 1 + Nat.log2 (⌈256 * χ * (B : ℝ) ^ 2 * (K : ℝ) ^ 2 + 32 * χ * B * K⌉₊ + 1)
  let H := 1 + Nat.log2 (B * K)
  (100000 * χ * J * d * (1 + 1 / ε) * H + K * ε + 1) / K

theorem result : OnlineTemplate.Guarantee
    LongTailsOnline.Setups.StationaryTaskAllocation.spec method bound := by
  refine ⟨fun _ _ => trivial, ?_⟩
  rintro p ⟨hB, hT, hμ⟩ P E ⟨hP, rfl⟩
  refine ⟨Filter.Eventually.of_forall (fun _ _ => trivial), integrable_regret p hμ _, ?_⟩
  have hh := div_le_div_of_nonneg_right (expected_regret_le hP hB hT hμ)
    (Nat.cast_nonneg p.config.T : (0 : ℝ) ≤ p.config.T)
  simpa only [method, bound, phaseAllowance, phaseLimit, groupLimit, quotaMaximum, scale,
    clipLevel, confidenceLog, noise, imbalance, accuracy, Nat.cast_add, Nat.cast_one] using hh

end LongTailsOnline.Theorems.ParallelTaskAllocation
