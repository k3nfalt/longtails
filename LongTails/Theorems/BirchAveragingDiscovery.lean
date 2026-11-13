import LongTails.Algorithms.BirchAveragingDiscovery
import LongTails.Setups.BirchAveragingDiscovery
import LongTails.Proofs.BirchAveragingConvergence
import LongTails.Proofs.BirchAveragingCounterexample
open MeasureTheory

namespace OracleTemplate.BirchAveragingDiscovery

open OracleTemplate
open OracleTemplate.Rennala (Point)
open LongTails.Setups.BirchNonIID
open LongTails.Setups.BirchAveragingDiscovery

/-- Calls per worker; all tuning variables are explicit public quantities. -/
noncomputable def budget (n : ℕ) (p : Parameters (n + 1)) (_ : Fin (n + 1)) : ℕ := max 1 p.localSteps * max 1 ⌈if p.base.δ = 0 then 8 * p.base.L * p.base.Δ / ((max 1 p.localSteps : ℕ) * p.base.ε) else max (8 * p.base.L * p.base.Δ / ((max 1 p.localSteps : ℕ) * p.base.ε)) (16 * p.base.L * p.base.Δ / (p.base.ε * Real.log (1 + p.base.L / p.base.δ)))⌉₊

/-- Main convergence theorem, uniformly covering every positive worker count.
The supporting lower theorem proves the logarithmic horizon obstruction for this method. -/
theorem result (n : ℕ) : Convergence (LongTails.Setups.BirchAveragingDiscovery.spec n) (budget n) := by
  unfold Convergence
  dsimp only [LongTails.Setups.BirchAveragingDiscovery.spec]
  refine ⟨makeAlgorithm n, ?_, ?_⟩
  · intro p hp I O ho
    change (LongTails.Setups.BirchNonIID.spec (n + 1)).successful p.base I
      (fun seed : (makeAlgorithm n p).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (makeAlgorithm n p) (budget n p) seed.1 seed.2)
      ⟨((makeAlgorithm n p).law : Measure _).prod (O.law : Measure _), inferInstance⟩
    change Valid p.base ∧ 0 < p.localSteps ∧ (∀ i, p.base.σ i = 0) ∧
      (p.base.similarity = .secondOrder ∨ p.base.similarity = .firstAndSecondOrder) at hp
    have hK : 0 < horizon p := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    by_cases hd : p.base.δ = 0
    · have h := zeroSimilarity_public_budget p.base hp.1 hK hp.2.2.1 hd hp.2.2.2 I O ho
      have hr : rounds p = max 1 ⌈8 * p.base.L * p.base.Δ / ((horizon p : ℝ) * p.base.ε)⌉₊ := by
        simp [rounds, hd]
      have hs : step p = 1 / (4 * p.base.L) := by simp [step, hd]
      have hA : makeAlgorithm n p = correctedAveraging (n + 1) p.base.d (horizon p)
          (max 1 ⌈8 * p.base.L * p.base.Δ / ((horizon p : ℝ) * p.base.ε)⌉₊)
          (Nat.succ_pos n) hK (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
          p.base.x0 (1 / (4 * p.base.L)) := by
        unfold makeAlgorithm
        congr 1
      have hb : budget n p = fun _ => horizon p * max 1
          ⌈8 * p.base.L * p.base.Δ / ((horizon p : ℝ) * p.base.ε)⌉₊ := by
        funext i
        change horizon p * rounds p = _
        rw [hr]
      rw [hA, hb]
      exact h
    · have hδ : 0 < p.base.δ := lt_of_le_of_ne hp.1.2.2.2.2.2.2.2 (Ne.symm hd)
      have h := correctedAveraging_public_budget p.base hp.1 hK hp.2.2.1 hδ hp.2.2.2 I O ho
      have hr : rounds p = max 1 ⌈max (8 * p.base.L * p.base.Δ / ((horizon p : ℝ) * p.base.ε))
          (16 * p.base.L * p.base.Δ / (p.base.ε * Real.log (1 + p.base.L / p.base.δ)))⌉₊ := by
        simp [rounds, hd]
      have hs : step p = logarithmicStep p.base.L p.base.δ (horizon p) := by simp [step, hd]
      have hA : makeAlgorithm n p = correctedAveraging (n + 1) p.base.d (horizon p)
          (max 1 ⌈max (8 * p.base.L * p.base.Δ / ((horizon p : ℝ) * p.base.ε))
            (16 * p.base.L * p.base.Δ / (p.base.ε * Real.log (1 + p.base.L / p.base.δ)))⌉₊)
          (Nat.succ_pos n) hK (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
          p.base.x0 (logarithmicStep p.base.L p.base.δ (horizon p)) := by
        unfold makeAlgorithm
        congr 1
      have hb : budget n p = fun _ => horizon p * max 1
          ⌈max (8 * p.base.L * p.base.Δ / ((horizon p : ℝ) * p.base.ε))
            (16 * p.base.L * p.base.Δ / (p.base.ε * Real.log (1 + p.base.L / p.base.δ)))⌉₊ := by
        funext i
        change horizon p * rounds p = _
        rw [hr]
      rw [hA, hb]
      exact h
  · intro p hp
    trivial

end OracleTemplate.BirchAveragingDiscovery
