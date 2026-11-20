import LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
import LongTails.Proofs.DashaDistributedClosedBudget
import LongTails.Proofs.DashaDistributedDeadline

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Theorems.DashaFreeBroadcastDeterministicSimplified

open DistributedTemplate
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Proofs.DashaDistributedClosedBudget

noncomputable def budget (p : Params) : Time :=
  let Λ := min p.L p.Lhat
  let A := 1 + Λ * p.Δ / p.ε ^ 2
  let H := Finset.univ.sup p.h + p.l + 64 * p.b
  let V := p.Lhat / Real.sqrt p.n
  let s := 2 + Real.log (1 + p.Δ * (Λ + V) / p.ε ^ 2) + Real.log (1 + Real.log ((p.n : ℝ) * p.d))
  let t := 1 + Real.log (1 + Real.log ((p.d : ℝ) * A))
  let P := s * (1 + p.Δ * (Λ + p.d * min Λ V) / p.ε ^ 2) +
    p.d * min (p.G / (p.ε * Real.sqrt p.n) * Real.sqrt (s * t))
      (min (t + Real.log (1 + p.G ^ 2 * s / (p.n * p.ε ^ 2))) (1 + Real.log ((p.n : ℝ) * p.d * A)))
  (2 ^ 22 : Time) * (if min (2 * Λ * p.Δ) (p.G ^ 2) ≤ p.ε ^ 2 then 0
    else if p.n = 1 then A.toNNReal * (H + p.b * p.d * (2 + Real.log A + Real.log (1 + Real.log p.d)).toNNReal)
    else A.toNNReal * H + p.b * P.toNNReal)

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
