import LongTails.TemplateLowerBound
import LongTails.Setups.SpatialRankingFrozenFilter
import LongTails.Proofs.SpatialRankingRealization
import LongTails.Proofs.FrozenRankingExecution

open OracleTemplate
open LongTails.Setups.SpatialRankingLogistic
open LongTails.Proofs.SpatialRankingDictionary
open LongTails.Proofs.SpatialRankingRealization
open LongTails.Proofs.FrozenRankingExecution

namespace LongTails.Theorems.SpatialRankingFrozenFilterLowerBound

def budget : (let S := LongTails.Setups.SpatialRankingFrozenFilter.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.n*(p.n-3)

theorem result : NonConvergence (LongTails.Setups.SpatialRankingFrozenFilter.spec) budget := by
  intro p hp A hA b hb
  change Fin 1 → ℕ at b
  let D := dictionary p
  let O : Oracle (Query p) (Point p) := { answer := fun _ q _ => answer p D q.2 }
  have hn : 8 ≤ p.n := hp.1
  have hD : Geometry p D := realizes p hn hp.2
  refine ⟨D, O, ⟨hD, fun _ _ _ => rfl⟩, ?_⟩
  change ¬∀ s : A.Seed × ((k : ℕ) → O.Seed k), Separates p D (execute O A b s.1 s.2)
  intro h
  let seed := Classical.choice A.law.nonempty
  have hit := h (seed, fun _ => ())
  have he : b = fun _ => b 0 := funext fun j => congrArg b (Subsingleton.elim j 0)
  rw [he] at hit
  exact execution_fails hn hD A hA (b 0) (hb (0 : Fin 1)) seed hit

end LongTails.Theorems.SpatialRankingFrozenFilterLowerBound
