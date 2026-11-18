import LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
import LongTails.Proofs.DashaDistributedClosedBudget
import LongTails.Proofs.DashaDistributedDeadline

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Theorems.DashaFreeBroadcastDeterministicSimplified

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Proofs.DashaDistributedClosedBudget

noncomputable def budget (p : Params) : Time := (2 ^ 22 : Time) * (if min (2 * min p.L p.Lhat * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2 then 0 else if p.n = 1 then Real.toNNReal (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2) * ((Finset.univ.sup p.h + p.l + 64 * p.b) + p.b * p.d * Real.toNNReal (2 + Real.log (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2) + Real.log (1 + Real.log p.d))) else Real.toNNReal (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2) * (Finset.univ.sup p.h + p.l + 64 * p.b) + p.b * Real.toNNReal ((2 + Real.log (1 + p.Δ * (min p.L p.Lhat + p.Lhat / Real.sqrt p.n) / p.ε ^ 2) + Real.log (1 + Real.log ((p.n : ℝ) * p.d))) * (1 + p.Δ * (min p.L p.Lhat + p.d * min (min p.L p.Lhat) (p.Lhat / Real.sqrt p.n)) / p.ε ^ 2) + p.d * (min (p.G / (p.ε * Real.sqrt p.n) * Real.sqrt ((2 + Real.log (1 + p.Δ * (min p.L p.Lhat + p.Lhat / Real.sqrt p.n) / p.ε ^ 2) + Real.log (1 + Real.log ((p.n : ℝ) * p.d))) * (1 + Real.log (1 + Real.log ((p.d : ℝ) * (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2)))))) (min ((1 + Real.log (1 + Real.log ((p.d : ℝ) * (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2)))) + Real.log (1 + p.G ^ 2 * (2 + Real.log (1 + p.Δ * (min p.L p.Lhat + p.Lhat / Real.sqrt p.n) / p.ε ^ 2) + Real.log (1 + Real.log ((p.n : ℝ) * p.d))) / (p.n * p.ε ^ 2))) (1 + Real.log ((p.n : ℝ) * p.d * (1 + min p.L p.Lhat * p.Δ / p.ε ^ 2)))))))

theorem result : TimedConvergence LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex.spec budget := by
  classical
  refine ⟨fun p => LongTails.Algorithms.DashaDistributedDeadline.tunedAtDeadline p (budget p), ?_⟩
  intro p hp
  refine ⟨trivial, ?_⟩
  intro f O hO
  have hb : budget p = closedDeadline p := by
    unfold budget closedDeadline
    rw [initialCharge_eq hp]
    simp only [packetScale_eq]
    rfl
  apply LongTails.Proofs.DashaDistributedDeadline.tuned_atDeadline_guarantee (budget p) hp
  · intro hz
    rw [hb]
    exact closedDeadline_zero hz
  · rw [hb]
    exact closedDeadline_suffices hp
  · exact hO

end LongTails.Theorems.DashaFreeBroadcastDeterministicSimplified
