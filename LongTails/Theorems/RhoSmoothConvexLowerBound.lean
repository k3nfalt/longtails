import LongTails.TemplateLowerBound
import LongTails.Setups.RhoSmoothConvexFull
import LongTails.Proofs.RhoSmoothLowerBranches

namespace LongTails.Theorems.RhoSmoothConvexLowerBound

open OracleTemplate LongTails.Proofs.RhoSmoothLowerBranches

noncomputable def budget :
    (let S := LongTails.Setups.RhoSmoothConvexFull.spec; S.Params → Fin S.numOracles → ℕ) :=
  fun p _ =>
    let G := (p.L0 / p.L1) ^ (1 / p.ρ)
    ⌊(Real.sqrt (p.L0 * p.R ^ 2 / p.ε) + (p.ρ - 1) ^ 2 * (p.L0 * p.R / G) ^ 2) / 1073741824⌋₊

theorem result : NonConvergence LongTails.Setups.RhoSmoothConvexFull.spec budget := by
  intro p hp A _ b hb
  have hN := hb 0
  have heq : b = fun _ => b 0 := funext fun i => congrArg b (Subsingleton.elim i 0)
  rw [heq]
  set s := Real.sqrt (p.L0 * p.R ^ 2 / p.ε)
  set q := (p.ρ - 1) ^ 2 * LongTails.Proofs.RhoSmoothHardParameters.quad p / 16
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hq : 0 ≤ q := by
    unfold q LongTails.Proofs.RhoSmoothHardParameters.quad
    positivity
  have hbudget : b 0 ≤ ⌊(s + q) / 67108864⌋₊ := by
    apply hN.trans
    apply Nat.floor_le_floor
    change (s + (p.ρ - 1) ^ 2 * (p.L0 * p.R / (p.L0 / p.L1) ^ (1 / p.ρ)) ^ 2) / 1073741824 ≤ _
    have he : (p.ρ - 1) ^ 2 * (p.L0 * p.R / (p.L0 / p.L1) ^ (1 / p.ρ)) ^ 2 = 16 * q := by
      unfold q LongTails.Proofs.RhoSmoothHardParameters.quad
        LongTails.Proofs.RhoSmoothHardParameters.scale
      ring
    rw [he]
    linarith
  obtain hzero | haccuracy | hchain :=
    LongTails.Proofs.TailEntropyBudget.budget_cases s q hs hq (b 0) hbudget
  · rw [hzero]
    exact transfer_failure p hp 0 A
      (LongTails.Proofs.FullGeneralizedSmoothZeroQuery.exists_failure (smoothParams p)
        (smoothParams_valid p hp)
        (LongTails.Proofs.FullGeneralizedSmoothParameters.dimension_pos (smoothParams p)
          (smoothParams_valid p hp)) A)
  · exact transfer_failure p hp (b 0) A
      (LongTails.Proofs.MollifiedSmoothLowerBound.exists_failure (smoothParams p)
        (smoothParams_valid p hp) (b 0) haccuracy.1 haccuracy.2 A)
  · exact chain_failure p hp (b 0) (links_bound p hp (b 0) hchain.1 hchain.2) A

end LongTails.Theorems.RhoSmoothConvexLowerBound
