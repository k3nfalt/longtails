import LongTails.Setups.DistributedSmoothNonconvex
import LongTails.Proofs.DistributedBatchedExecution
import LongTails.Proofs.DistributedBatchedBudget

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Theorems.DistributedBatchedSgd

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedSmoothNonconvex
open LongTails.Algorithms.DistributedBatchedSgd

noncomputable def budget (p : Params) : Time := 262144 * (1 + ⌈p.L * p.Δ / p.ε⌉₊ : ℕ) * (sInf (Set.range (fun i : Fin p.n => p.h i + (1 + ⌈p.σ ^ 2 / p.ε⌉₊ : ℕ) / (∑ j, if p.h j ≤ p.h i then (p.h j)⁻¹ else 0))) + p.l + p.b * (p.d * (1 + Nat.log2 (2 + p.d + ⌈p.L * p.Δ / p.ε⌉₊ + ⌈p.σ ^ 2 / p.ε⌉₊)) + clockBits : ℕ))

theorem result : TimedConvergence LongTails.Setups.DistributedSmoothNonconvex.spec budget := by
  refine ⟨fun p => algorithm p (withBudget p (budget p)), ?_⟩
  intro p hp
  change Params at p
  obtain ⟨hn, hh, hL, hΔ, _, hε⟩ := hp
  refine ⟨trivial, ?_⟩
  intro f O hO
  change Point p → ℝ at f
  obtain ⟨hg, hlip, ⟨lower, hlower, hgap⟩, g, μ, P, rfl, hworkers, horacle⟩ := hO
  have hB : 0 < totalBatch p (config p) := by
    have hlarge := LongTails.Proofs.DistributedBatchedSgd.configured_batch_large hn hh
    have hone : 1 ≤ targetBatch p := le_max_left _ _
    omega
  have hactive : (active p (config p)).Nonempty := by
    obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hB
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have hbudget : timeBudget p (withBudget p (budget p)) = budget p :=
    LongTails.Proofs.DistributedBatchedBudget.withBudget_time _
      (LongTails.Proofs.DistributedBatchedBudget.simple_budget_le hn hh hL hΔ hε)
  refine ⟨Filter.Eventually.of_forall (fun seed => ?_), ?_⟩
  · change FiniteEvents (system p g P) (algorithm p (withBudget p (budget p))) (budget p) (seed.1, seed.2)
    have hfinite := LongTails.Proofs.DistributedBatchedExecution.finiteEvents
      (withBudget p (budget p)) g P hactive seed.1 seed.2
    rw [hbudget] at hfinite
    exact hfinite
  · have he : (fun seed => execute (system p g P) (algorithm p (withBudget p (budget p))) (budget p) seed.1 seed.2) =
        output p (config p) g := by
      funext seed
      have hex := LongTails.Proofs.DistributedBatchedExecution.execute_output
        (withBudget p (budget p)) g P seed.2 seed.1 hactive
      rw [hbudget] at hex
      exact hex.trans (LongTails.Proofs.DistributedBatchedBudget.withBudget_output _ g seed)
    have hacc := LongTails.Proofs.DistributedBatchedSgd.configured_output_accuracy (p := p) (P : Measure (Samples p)) μ hworkers
      (fun i => (horacle i).1) g f (fun i => (horacle i).2) hn hh hL hΔ hε hg hlip lower hlower hgap
    change Measurable _ ∧ Integrable _ _ ∧ _ ≤ p.ε
    change Measurable _ ∧ Integrable _ ((PMF.uniformOfFintype (Fin (config p).iterations)).toMeasure.prod (P : Measure (Samples p))) ∧ _ ≤ p.ε
    erw [he]
    exact hacc

end LongTails.Theorems.DistributedBatchedSgd
