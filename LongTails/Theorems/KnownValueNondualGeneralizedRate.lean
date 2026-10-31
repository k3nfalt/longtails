import LongTails.Setups.KnownValueNondualGeneralizedConvex
import LongTails.Algorithms.KnownValueNondual
import LongTails.Proofs.KnownValueNondualBudget

namespace LongTails.Theorems.KnownValueNondualGeneralizedRate

open OracleTemplate
open LongTails.Setups.KnownValueNondualGeneralizedConvex
open LongTails.Algorithms.KnownValueNondual
open LongTails.Proofs.KnownValueNondualBudget
open LongTails.Proofs.KnownValueNondualControl
open LongTails.Proofs.KnownValueNondualExecution
open LongTails.Proofs.KnownValueNondualCounting

noncomputable def budget : (let S := LongTails.Setups.KnownValueNondualGeneralizedConvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(2 : ℝ) ^ 36 * (1 + (p.L0 * p.R ^ 2 / p.ε) ^ (1 / 3 : ℝ) + (p.L1 * p.R) ^ (2 / 3 : ℝ)) * (1 + Real.log (2 * (p.d : ℝ)) + Real.log (2 + p.L0 * p.R ^ 2 / p.ε + p.L1 * p.R)) ^ 2⌉₊

theorem result : Convergence LongTails.Setups.KnownValueNondualGeneralizedConvex.spec budget := by
  refine ⟨algorithm, ?_, ?_⟩
  · intro p hp f O hO
    obtain ⟨hconv, hgrad, hg, hgs, hanswer, xstar, hmin, hval, hprior⟩ := hO
    refine ⟨xstar, hmin, hval, ?_⟩
    apply Filter.Eventually.of_forall
    rintro ⟨seed, ξ⟩
    cases seed
    have hfinished := rounds_finished p hp hconv hgrad hg hgs xstar hmin hval hprior
    have hbudget : rounds p * lineCalls p ≤ budget p 0 := by
      simpa only [budget, size, logScale, totalScale, aScale, bScale] using budget_covers_blocks p hp
    have hout := execute_after_finished_block p O f (gradient f) (fun history x seed => hanswer history seed x) (rounds p) (budget p 0)
      hbudget hfinished ξ
    have hinv := iterate_invariant p hp.1 hconv hgrad hg hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
      hgs xstar hmin hval hprior (rounds p)
    change f (execute O (algorithm p) (fun _ => budget p 0) () ξ) - f xstar ≤ p.ε
    rw [hout]
    exact hinv.certified hfinished
  · intro p hp
    trivial

end LongTails.Theorems.KnownValueNondualGeneralizedRate
