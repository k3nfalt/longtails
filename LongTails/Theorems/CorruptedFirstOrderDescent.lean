import LongTails.Setups.CorruptedFirstOrderNonconvex
import LongTails.Proofs.CorruptedFirstOrderExecution

open MeasureTheory OracleTemplate
open LongTails.Setups.CorruptedFirstOrderNonconvex LongTails.Algorithms.CorruptedFirstOrderDescent

namespace LongTails.Theorems.CorruptedFirstOrderDescent

noncomputable def budget : (let S := LongTails.Setups.CorruptedFirstOrderNonconvex.spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈16 * p.L * p.Δ / p.ε ^ 2⌉₊ + 5 * p.k + 4

theorem result : Convergence LongTails.Setups.CorruptedFirstOrderNonconvex.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O ho
  have h : ∀ z : (algorithm p).Seed × ((j : ℕ) → O.Seed j),
      ‖gradient f (execute O (algorithm p) (budget p) z.1 z.2)‖ ≤ p.ε := by
    rintro ⟨⟨⟩, ξ⟩
    exact LongTails.Proofs.CorruptedFirstOrderExecution.execution_accuracy p f O hp ho _ le_rfl ξ
  have hempty : {z | p.ε < ‖gradient f (execute O (algorithm p) (budget p) z.1 z.2)‖} =
      (∅ : Set ((algorithm p).Seed × ((j : ℕ) → O.Seed j))) :=
    Set.eq_empty_iff_forall_notMem.mpr (fun z => not_lt_of_ge (h z))
  simp only [spec, hempty, measure_empty, zero_le]

end LongTails.Theorems.CorruptedFirstOrderDescent
