import LongTails.Setups.DistributedAggregateSmoothNonconvex
import LongTails.Proofs.MultiscaleAggregateExecution
import LongTails.Proofs.MultiscaleAggregateAccuracy
import LongTails.Proofs.MultiscaleAggregateRuntime

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Theorems.MultiscaleAggregateStationarity

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedAggregateSmoothNonconvex
open LongTails.Algorithms.MultiscaleAggregate
open LongTails.Proofs.MultiscaleAggregateExecution
open LongTails.Proofs.MultiscaleAggregateAccuracy

noncomputable def budget (p : Params) : Time :=
  let K := 1 + ⌈2 ^ 19 * p.L * p.Δ / p.ε ^ 2⌉₊
  let V := Real.toNNReal (2 ^ 18 * (∑ i, (p.h i : ℝ) * p.σ i ^ 2) / ((p.n : ℝ) ^ 2 * p.ε ^ 2))
  let C := p.l + p.b * (clockBits + p.d * (5 + Nat.size ((p.n : ℕ) * (p.d + 1))) : ℕ)
  (2 * K : ℕ) * (Finset.univ.sup p.h + V + 2 * C)

theorem result : DistributedTemplate.TimedConvergence LongTails.Setups.DistributedAggregateSmoothNonconvex.spec budget := by
  refine ⟨fun p => algorithm p (budget p), ?_⟩
  intro p hp
  change Params at p
  obtain ⟨hh, hL, _, _, hε⟩ := hp
  refine ⟨trivial, ?_⟩
  intro f O hO
  change Functions p at f
  obtain ⟨hg, hlip, ⟨lower, hlower, hgap⟩, g, μ, P, rfl, hw, ho⟩ := hO
  let : NeZero (rounds p) := ⟨(rounds_pos p).ne'⟩
  have hbudget : executionTime p ≤ budget p := by
    simpa only [budget, show (2 : ℝ) ^ 19 = 524288 by norm_num, show (2 : ℝ) ^ 18 = 262144 by norm_num] using runtime_bound hh
  have he : (fun seed : Indices p × Samples p =>
      execute (system p g P) (algorithm p (budget p)) (budget p) seed.1 seed.2) = output p g :=
    funext fun seed => execute_output p (budget p) g P seed.2 seed.1 hbudget
  have ha := output_integral (p := p) (P : Measure (Samples p)) g (fun i => (ho i).2.measurable) (objective p f)
    (average_gradient (p := p) (P : Measure (Samples p)) μ hw (fun i => (ho i).1) g f
      (fun i => (ho i).2) hg hh hε hlip hL lower hlower hgap)
  have hsuccess : spec.successful p f (output p g) (law (system p g P) (algorithm p (budget p))) := ha
  refine ⟨Filter.Eventually.of_forall (fun seed => finiteEvents p (budget p) g P seed.2 seed.1), ?_⟩
  exact he.symm ▸ hsuccess

end LongTails.Theorems.MultiscaleAggregateStationarity
