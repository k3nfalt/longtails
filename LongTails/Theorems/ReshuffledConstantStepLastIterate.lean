import LongTails.Setups.ConstantStepReshuffledSmoothConvex
import LongTails.Proofs.ConstantStepReshuffledExecution

namespace OracleTemplate.ConstantStepReshuffledConvex

open LongTails.Setups.ConstantStepReshuffledSmoothConvex

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => p.n * ⌈1 + 32768 * (1 + Real.log p.n) * (p.Lmax * p.ε + p.σ ^ 2) * p.R ^ 2 * (1 + Real.log (p.n + 2 + (p.Lmax * p.ε + p.σ ^ 2) * p.R ^ 2 / p.ε ^ 2)) / (p.n * p.ε ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.ConstantStepReshuffledSmoothConvex.spec budget := by
  have hb : budget = fun p _ => p.n * epochCount p := by
    funext p i
    unfold budget epochCount scale
    congr 2
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hb]
  exact convergence

end OracleTemplate.ConstantStepReshuffledConvex
