import LongTails.Setups.CompositeGeneralizedSmooth
import LongTails.Proofs.Execution
import LongTails.Proofs.CompositeGeneralizedRun

namespace OracleTemplate.CompositeGeneralized

open LongTails.Setups.CompositeGeneralizedSmooth

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => 3 * ⌈10 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) + (6 + 128 * q.L1 * q.R) * Real.log (2 + (3 + 96 * q.L1 * q.R) * Real.sqrt (q.Δ / (q.L0 * q.R ^ 2)))⌉₊

theorem result : Convergence LongTails.Setups.CompositeGeneralizedSmooth.spec budget := by
  apply convergence_of_block_budget (S := spec) (fun q => ⌈10 * Real.sqrt ((q.L0 + q.L1 * q.G) * q.R ^ 2 / q.ε) + (6 + 128 * q.L1 * q.R) * Real.log (2 + (3 + 96 * q.L1 * q.R) * Real.sqrt (q.Δ / (q.L0 * q.R ^ 2)))⌉₊) (fun _ => 3)
  refine ⟨fun p => accelerated p, ?_, fun _ _ => trivial⟩
  rintro q ⟨hL0, hL1, hR, hΔ, hG, hε⟩
  intro K hK
  rintro I oracle
    ⟨hgradAns, hproxAns, hc, hgrad, hcont, hsmooth, hQ, hψ, hprox, hx0, xs, hxs, hmin,
      hdist, hgap, hGx⟩
  have hyp : Hyp I.f I.ψ I.grad I.Q I.prox q.L0 q.L1 :=
    ⟨hL0, hL1, hc, hgrad, hcont, hsmooth, hQ, hψ, hprox⟩
  have hacc := run_accuracy hyp hR hΔ hε hx0 hxs hmin hdist hgap hGx K ((Nat.le_ceil _).trans (Nat.cast_le.mpr hK))
  have hans : ∀ k query seed, oracle.answer k (0, query) seed =
      answerOf q.toPublic I.grad I.prox query := by
    intro k query seed
    cases query with
    | gradient x => exact hgradAns k seed x
    | prox a z v => exact hproxAns k seed a z v
  have hexec : ∀ ξ : (k : ℕ) → oracle.Seed k,
      execute oracle (accelerated q.toPublic) (fun _ => (3 * K)) () ξ =
        (run q.L0 q.L1 q.R q.Δ I.grad I.prox q.x0 K).2.1 := fun ξ =>
    (execute_eq_of_answer_eq oracle _ hans (accelerated q.toPublic) (3 * K) () ξ).trans
      (execute_accelerated q.toPublic I.grad I.prox K)
  refine ⟨xs, hxs, hmin, Filter.Eventually.of_forall fun seed => ?_⟩
  · obtain ⟨⟨⟩, ξ⟩ := seed
    change (execute oracle (accelerated q.toPublic) (fun _ => (3 * K)) () ξ) ∈ I.Q ∧
      objective I (execute oracle (accelerated q.toPublic) (fun _ => (3 * K)) () ξ) -
        objective I xs ≤ q.ε
    have e : (execute oracle (accelerated q.toPublic) (fun _ => (3 * K)) () ξ) =
        (run q.L0 q.L1 q.R q.Δ I.grad I.prox q.x0 K).2.1 := (hexec ξ)
    rw [e]
    exact hacc

end OracleTemplate.CompositeGeneralized
