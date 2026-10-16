import LongTails.Setups.DiagonalSmoothStronglyConvex
import LongTails.Proofs.Execution
import LongTails.Proofs.OnlineMetricBudget

namespace OracleTemplate.OnlineMetricAccelerated

open LongTails.Setups.DiagonalSmoothStronglyConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 2 * (q.d + 1 + ⌈Real.logb 2 (q.Δ / q.ε)⌉₊ * ⌈24 * Real.sqrt (1 / q.μ) + Real.logb 2 q.d + 2⌉₊ + (q.d * ⌈Real.logb 2 (1 / q.μ)⌉₊ + 1) * ⌈110 * q.d ^ 2 * (1 + Real.log (2 * q.d)) ^ 2 * Real.sqrt (1 / q.μ)⌉₊)

theorem result : Convergence LongTails.Setups.DiagonalSmoothStronglyConvex.spec budget := by
  apply convergence_of_block_budget (S := spec) (fun q => q.d + 1 + ⌈Real.logb 2 (q.Δ / q.ε)⌉₊ * ⌈24 * Real.sqrt (1 / q.μ) + Real.logb 2 q.d + 2⌉₊ + (q.d * ⌈Real.logb 2 (1 / q.μ)⌉₊ + 1) * ⌈110 * q.d ^ 2 * (1 + Real.log (2 * q.d)) ^ 2 * Real.sqrt (1 / q.μ)⌉₊)
    (fun _ => 2)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro q ⟨hμ, hμ1, hw, hΔ, hε⟩ N hN f oracle
    ⟨hg, hor, hsmooth, hsc, ⟨xstar, hmin, hfx⟩, hgap⟩
  have H : Hyp f q.w q.μ q.fstar xstar := ⟨hw, hμ, hμ1, hg, hsmooth, hsc, hmin, hfx⟩
  have hd : (1 : ℝ) ≤ q.d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q.d)
  have hacc := accuracy (x0 := q.x0) H hd hgap hε N hN
  have hexec (seed : (algorithm q.toPublic).Seed × ((k : ℕ) → oracle.Seed k)) :
      execute oracle (algorithm q.toPublic) (fun _ => (2 * N)) seed.1 seed.2 =
        ((macroStep q.fstar q.x0 f)^[N] (initialCore q.x0)).xs := by
    rw [execute_eq_of_answer_eq oracle (fun x => (f x, gradient f x))
      (fun k x sample => hor k sample x)]
    exact execute_algorithm q.toPublic f N
  refine ⟨xstar, hmin, hfx, Filter.Eventually.of_forall ?_⟩
  intro seed
  change f (execute oracle (algorithm q.toPublic) (fun _ => (2 * N)) seed.1 seed.2) - f xstar ≤ q.ε
  rw [hexec, hfx]
  exact hacc

end OracleTemplate.OnlineMetricAccelerated
