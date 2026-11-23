import LongTails.Proofs.DistributedGrowthConvergence
import LongTails.Proofs.DistributedBudgetPrecision

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.DistributedGrowthBudget

open DistributedTemplate Setups.DistributedMeanStrongGrowth
open Algorithms.StrongGrowthWeights Algorithms.DistributedGrowthSgd
open DistributedGrowthSchedule StrongGrowthWeights

variable {p : Params}

lemma info_sum (p : Params) : information p = ∑ i, signal p i^2 / p.h i := by
  unfold information weight
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma condition_eq (hp : spec.valid p) : WeightedInterpolationCost.condition (schedule p) =
    6 * p.n * p.L * peak p * (∑ i, (p.h i : ℝ)⁻¹) / (p.μ * information p) := by
  unfold WeightedInterpolationCost.condition Algorithms.WeakInterpolationDesign.smoothness
  rw [largest_eq hp,info_eq hp]
  change 2 * (∑ i, (p.h i : ℝ)⁻¹) * _ / _ = _
  field_simp [hp.2.1.ne', (information_pos hp).ne']
  ring

lemma noise_eq (hp : spec.valid p) : Algorithms.WeakInterpolationDesign.noiseRadius (schedule p) =
    p.σ / (3*p.n*p.L) := by
  have he : Finset.univ.sup' Finset.univ_nonempty (Algorithms.WeakInterpolationDesign.profile (schedule p)) =
      p.μ * peak p := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      rw [profile_eq hp]
      exact mul_le_mul_of_nonneg_left (Finset.le_sup' (signal p) (Finset.mem_univ i)) hp.2.1.le
    · obtain ⟨i,hi,hm⟩ := Finset.univ.exists_mem_eq_sup' Finset.univ_nonempty (signal p)
      unfold peak
      rw [hm, ← profile_eq hp]
      exact Finset.le_sup' _ hi
  unfold Algorithms.WeakInterpolationDesign.noiseRadius
  rw [he, largest_eq hp]
  change p.σ * (p.μ * peak p) / _ = _
  field_simp [(peak_pos hp).ne',hp.2.1.ne',(hp.2.1.trans_le hp.2.2.1).ne']

lemma sufficient (hp : spec.valid p) (T : Time)
    (h : let I := ∑ i, signal p i^2 / p.h i
         let A := 6 * p.n * p.L * peak p * (∑ i, (p.h i : ℝ)⁻¹) / (p.μ * I)
         let w := Real.log (3 + p.d + A + (p.R^2 + (p.σ/(3*p.n*p.L))^2)/p.ε)
         2048 * (p.σ^2/(p.μ^2*I*p.ε) + A*(1+Real.log (1+p.R^2/p.ε))*
           (((Finset.univ.sup p.h : Time) : ℝ)+p.l+p.b*(64+4096*(p.d:ℝ)*w))) ≤ T) :
    Algorithms.DistributedBatchedSgd.timeBudget (Algorithms.WeightedInterpolationSgd.transport (schedule p))
      (Algorithms.WeightedInterpolationSgd.config (schedule p) T) = T := by
  apply WeightedInterpolationRuntime.time_suffices (valid hp)
  dsimp only at h
  unfold WeightedInterpolationCost.magnitude WeightedInterpolationCost.burn
  rw [condition_eq hp,noise_eq hp,info_eq hp,info_sum]
  let I := ∑ i, signal p i^2 / p.h i
  let A := 6 * p.n * p.L * peak p * (∑ i, (p.h i : ℝ)⁻¹) / (p.μ * I)
  let D := (p.R^2 + (p.σ/(3*p.n*p.L))^2)/p.ε
  have hI : 0 < I := by simpa only [I, ← info_sum] using information_pos hp
  have hμ := hp.2.1
  have hL := hμ.trans_le hp.2.2.1
  have hε := hp.2.2.2.2.2.2
  have hpeak := peak_pos hp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hw := DistributedBudgetPrecision.size_ceil_le_log (2 + p.d + A + D) (by positivity)
  rw [show 1 + (2 + (p.d : ℝ) + A + D) = 3 + p.d + A + D by ring] at hw
  have hlow := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at hlow
  have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
    (show 2 ≤ 3 + (p.d : ℝ) + A + D by linarith [Nat.cast_nonneg (α := ℝ) p.d])
  have hbits : (Nat.size ⌈2 + p.d + A + D⌉₊ : ℝ) ≤ 4 * Real.log (3 + p.d + A + D) := by
    linarith only [hw,hlow,htwo]
  have hlog := Real.log_nonneg (show 1 ≤ 1 + p.R^2/p.ε by linarith [div_nonneg (sq_nonneg p.R) hε.le])
  apply le_trans _ h
  change 2048 * (p.σ^2/(p.μ^2*I*p.ε) + A * (1+Real.log (1+p.R^2/p.ε)) *
      (((Finset.univ.sup p.h : Time) : ℝ) + p.l + (p.b : ℝ) * (64 + 1024*(p.d:ℝ)*(Nat.size ⌈2+p.d+A+D⌉₊:ℝ)))) ≤
    2048 * (p.σ^2/(p.μ^2*I*p.ε) + A * (1+Real.log (1+p.R^2/p.ε)) *
      (((Finset.univ.sup p.h : Time) : ℝ) + p.l + (p.b : ℝ) * (64 + 4096*(p.d:ℝ)*Real.log (3+p.d+A+D))))
  have he : 4096*(p.d:ℝ)*Real.log (3+p.d+A+D) = 1024*(p.d:ℝ)*(4*Real.log (3+p.d+A+D)) := by ring
  rw [he]
  gcongr

end LongTails.Proofs.DistributedGrowthBudget
