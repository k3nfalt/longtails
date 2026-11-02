import LongTails.Setups.ComparisonHessianLipschitz
import LongTails.Proofs.ComparisonTrustExecution
import LongTails.Proofs.ComparisonTrustVisits

namespace OracleTemplate.ComparisonTrustAccelerated

open LongTails.Setups.ComparisonHessianLipschitz LongTails.Algorithms.ComparisonTrustRegion
  LongTails.Proofs.ComparisonTrustTaylor LongTails.Proofs.ComparisonTrustGuess
  LongTails.Proofs.ComparisonTrustOuter LongTails.Proofs.ComparisonTrustTuning
  LongTails.Proofs.ComparisonTrustExecution LongTails.Proofs.ComparisonTrustVisits

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => (⌊400 * p.Δ * Real.sqrt p.ρ / p.ε ^ (3 / 2 : ℝ)⌋₊ + 1) * ⌈250000 * (Module.finrank ℝ p.E + 1) * Real.sqrt (2 * p.L / Real.sqrt (p.ρ * p.ε) + 4) * Real.log (2 + Module.finrank ℝ p.E + p.L / Real.sqrt (p.ρ * p.ε) + Real.sqrt (2 * p.L * p.Δ) / p.ε) ^ 3⌉₊

theorem result : Convergence LongTails.Setups.ComparisonHessianLipschitz.spec budget := by
  refine ⟨algorithm, ?_, fun p _ => ?_⟩
  swap
  · intro O b seed oseed
    exact trace_visits _ p.x0 _ _ (fun _ => outer_cov (tuning p) p.x0) O b seed oseed
  intro p hp f O ho _ _ ω
  obtain ⟨hf, hlip, hhess, hgap, hO⟩ := ho
  have hsm := Smooth.of_contDiff hf hlip hhess
  have hK : epochLen (tuning p) (Module.finrank ℝ p.E) * (tuning p).T ≤ budget p 0 := by
    have h1 : epochLen (tuning p) (Module.finrank ℝ p.E) ≤ ⌈bigX p⌉₊ := by
      exact_mod_cast (epochLen_real p hp).trans (Nat.le_ceil _)
    show _ ≤ (tuning p).T * ⌈bigX p⌉₊
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ h1
  show ∃ x ∈ execute O (algorithm p) (budget p) ω.1 ω.2, ‖gradient f x‖ ≤ p.ε
  erw [execute_eq_of_answer_eq O (fun q => decide (f q.1 ≤ f q.2)) (fun k q s => hO k (0, q) s)]
  change ∃ x ∈ execute { answer := fun _ (_, q) _ => cmpOf f q }
      (QueryPlan.algorithm ⟨MeasureTheory.Measure.dirac (), inferInstance⟩ (p.x0, p.x0) []
        (epochLen (tuning p) (Module.finrank ℝ p.E) * (tuning p).T)
        (fun _ : Unit => QueryPlan.map Prod.snd (outerPlan (tuning p) p.x0)))
      (fun _ => budget p 0) ω.1, ‖gradient f x‖ ≤ p.ε
  have hexec := QueryPlan.execute_plan_of_le
    (⟨MeasureTheory.Measure.dirac (), inferInstance⟩ : MeasureTheory.ProbabilityMeasure Unit)
    (p.x0, p.x0) ([] : List p.E) _ _
    (fun _ : Unit => QueryPlan.map Prod.snd (outerPlan (tuning p) p.x0)) (cmpOf f) ω.1 hK
  beta_reduce at hexec
  rw [QueryPlan.eval_map, eval_outerPlan] at hexec
  refine (congrArg (fun l => ∃ x ∈ l, ‖gradient f x‖ ≤ p.ε) hexec).mpr ?_
  dsimp only
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ p.E) with h0 | hpos
  · refine ⟨p.x0, x0_mem f _ _ _, ?_⟩
    have : Subsingleton p.E := Module.finrank_zero_iff.mp h0
    rw [Subsingleton.elim (gradient f p.x0) 0, norm_zero]
    exact hp.2.2.2.le
  · have hG : 2 * p.L * p.Δ ≤ (absOf p).G ^ 2 := by
      show _ ≤ Real.sqrt (2 * p.L * p.Δ) ^ 2
      exact (Real.sq_sqrt (by have := hp.1; have := hp.2.2.1; positivity)).ge
    exact outer_visits hsm (rel_tuning p hp hpos) hgap hG (T_spec p hp)

end OracleTemplate.ComparisonTrustAccelerated
