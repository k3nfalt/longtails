import LongTails.Setups.GradientDependentHessian
import LongTails.Proofs.HessianReuseModelFlowExecution

namespace LongTails.Theorems.HessianReuseModelFlow

open OracleTemplate MeasureTheory LongTails.Setups.GradientDependentHessian
open LongTails.Algorithms.HessianReuseModelFlow
open LongTails.Proofs.HessianReuseModelFlowExecution
open LongTails.Proofs.EnergyHessianExecution (replies counts counts_map execute_of_counts)

noncomputable def budget : (let S := LongTails.Setups.GradientDependentHessian.spec; S.Params → Fin S.numOracles → ℕ) := fun p i =>
  let S := p.Δ * Real.sqrt (p.L₀ + p.L₁ * p.ε) / (p.ε * Real.sqrt p.ε)
  let C := 9 / (2 * Real.sqrt 2)
  if i = 0 then ⌊C * Real.sqrt p.m * S⌋₊ + 1 else ⌊C * S / Real.sqrt p.m⌋₊ + 1

theorem result : Convergence LongTails.Setups.GradientDependentHessian.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O hO
  obtain ⟨hf, hT, hgap, _, hg, hH⟩ := hO
  have hanswer : ∀ k q seed, O.answer k q seed = replies p f q := by
    rintro k ⟨i,x⟩ seed
    fin_cases i
    · simpa [replies] using hg k x seed
    · simpa [replies] using hH k x seed
  let plan := QueryPlan.map point (steps p (horizon p)).2
  have hb (i : Fin 2) : counts (replies p f) plan i ≤ budget p i := by
    change counts (replies p f) (QueryPlan.map point (steps p (horizon p)).2) i ≤ _
    rw [counts_map]
    unfold horizon
    rw [counts_steps]
    by_cases hi : i = 0
    · simp [hi, budget, ratio hp, curvature]
    · have hm := LongTails.Proofs.HessianReuseModelFlowPath.m_pos hp
      have cancel (a s : ℝ) : a * Real.sqrt p.m * s / p.m = a * s / Real.sqrt p.m := by
        apply (div_eq_div_iff hm.ne' (Real.sqrt_pos.2 hm).ne').2
        linear_combination a * s * Real.sq_sqrt hm.le
      simp only [budget, hi, ite_false, ← Nat.floor_div_natCast, ratio hp, cancel, curvature,
        le_refl]
  apply Filter.Eventually.of_forall
  intro seed
  change ‖gradient f (execute O (algorithm p) (budget p) seed.1 seed.2)‖ ≤ p.ε
  unfold algorithm
  rw [execute_of_counts (replies p f) (0, p.x0) p.x0 plan O (budget p) hanswer hb,
    QueryPlan.eval_map]
  exact steps_accuracy hp hf hT hgap

end LongTails.Theorems.HessianReuseModelFlow
