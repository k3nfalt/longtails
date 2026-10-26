import LongTails.Setups.HessianLipschitzSecondOrder
import LongTails.Algorithms.MonotoneHessianReuse
import LongTails.Proofs.MonotoneHessianBudget
import LongTails.Proofs.MonotoneHessianConvergence

namespace LongTails.Theorems.MonotoneHessianSecondOrder

open OracleTemplate MeasureTheory
open LongTails.Setups.HessianLipschitzSecondOrder
open LongTails.Algorithms.MonotoneHessianReuse
open LongTails.Proofs.MonotoneHessianRates
open scoped RealInnerProductSpace

noncomputable def budget : (let S := LongTails.Setups.HessianLipschitzSecondOrder.spec; S.Params → Fin S.numOracles → ℕ) := fun p i => if i = 0 then ⌈2 ^ 120 * p.m ^ (1 / 3 : ℝ) * (1 + p.Δ * Real.sqrt p.H / (p.ε * Real.sqrt p.ε)) * Real.log (2 + (Module.finrank ℝ p.E + 1 : ℝ) * p.m * (1 + p.Δ * Real.sqrt p.H / (p.ε * Real.sqrt p.ε)) / p.ρ) ^ 2⌉₊ else ⌈2 ^ 44 * (1 + p.Δ * Real.sqrt p.H / (p.m ^ (2 / 3 : ℝ) * p.ε * Real.sqrt p.ε))⌉₊

theorem result : Convergence LongTails.Setups.HessianLipschitzSecondOrder.spec budget := by
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f Or hadm
  obtain ⟨hc, hLip, hgap, hgrad, hhess⟩ := hadm
  let O : Fin 2 × p.E → LongTails.Algorithms.QuarticMetricStage.Reply p.E :=
    fun q => if q.1 = 0 then .inl (f q.2, gradient f q.2) else .inr (fderiv ℝ (gradient f) q.2)
  have hO (x : p.E) : O (0, x) = .inl (f x, gradient f x) := by simp [O]
  have hH (x : p.E) : O (1, x) = .inr (fderiv ℝ (gradient f) x) := by simp [O]
  have hanswer : ∀ k q seed, Or.answer k q seed = O q := by
    rintro k ⟨i, x⟩ seed
    fin_cases i
    · simpa [O] using hgrad k x seed
    · simpa [O] using hhess k x seed
  have hf (x : p.E) : HasFDerivAt f (innerSL ℝ (gradient f x)) x :=
    (hc.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt
  have hg (x : p.E) : HasFDerivAt (gradient f) (fderiv ℝ (gradient f) x) x :=
    ((OracleTemplate.NonlinearTemporalDiscrepancy.gradient_contDiff_one hc).differentiable (by norm_num) x).hasFDerivAt
  have hA := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric hc
  apply LongTails.Proofs.MonotoneHessianConvergence.execution_probability p hp f hf hg hA hLip O hO hH hgap Or (budget p) hanswer
  intro signs i
  fin_cases i
  · have hsum := LongTails.Proofs.EnergyHessianExecution.counts_sum O (plan p signs)
    have hle : LongTails.Proofs.EnergyHessianExecution.counts O (plan p signs) 0 ≤
        (stageCalls p + searchCalls p + 2) * stages p + 1 := by
      exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)).trans_eq hsum
    exact hle.trans (by simpa [budget, rootCost, size, logArgument] using total_calls_bound p hp)
  · have hb := LongTails.Proofs.MonotoneHessianCost.initial_hessian_bound p hp f hf hg hA hLip O hO hH hgap signs
    have he := LongTails.Proofs.MonotoneHessianBudget.hessian_envelope p hp
    have hid : size p / p.m ^ (2 / 3 : ℝ) =
        p.Δ * Real.sqrt p.H / (p.m ^ (2 / 3 : ℝ) * p.ε * Real.sqrt p.ε) := by
      unfold size
      ring
    rw [hid] at he
    apply (Nat.cast_le (α := ℝ)).mp
    exact (hb.trans he).trans (by simpa [budget] using
      (Nat.le_ceil (2 ^ 44 * (1 + p.Δ * Real.sqrt p.H / (p.m ^ (2 / 3 : ℝ) * p.ε * Real.sqrt p.ε)))))

end LongTails.Theorems.MonotoneHessianSecondOrder
