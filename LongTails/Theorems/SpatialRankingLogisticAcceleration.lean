import LongTails.Setups.SpatialRankingLogistic
import LongTails.Proofs.SpatialRankingThirdStep

open OracleTemplate
open LongTails.Setups.SpatialRankingLogistic
open LongTails.Algorithms.SpatialRankingLogistic
open LongTails.Proofs.SpatialRankingExecution
open LongTails.Proofs.SpatialRankingMargins
open LongTails.Proofs.SpatialRankingThirdStep

namespace LongTails.Theorems.SpatialRankingLogisticAcceleration

def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => 6*p.n

theorem result : Convergence (LongTails.Setups.SpatialRankingLogistic.spec) budget := by
  refine ⟨algorithm, ?_, fun p hp => in_family p (by change 8 ≤ p.n at hp; omega)⟩
  intro p hp D O hO
  change ∀ ω : Unit × ((k : ℕ) → O.Seed k), Separates p D (output p O (6*p.n) ω.2)
  intro ω
  have hn : 8 ≤ p.n := hp
  rw [show 6*p.n=3*(2*p.n) by omega, output_passes p D O (fun h q s => hO.2 h (0,q) s)
    (by omega) 3]
  change Separates p D (batch p D (batch p D (batch p D ((1,0),0))))
  rw [step₂ hO.1 hn, step₃ hO.1 hn]
  exact separates₃ hO.1 hn

end LongTails.Theorems.SpatialRankingLogisticAcceleration
