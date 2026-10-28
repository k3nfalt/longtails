import LongTails.Setups.GradientOnlyGeneralizedQuasar
import LongTails.Proofs.GradientOnlyQuasarConvergence

open MeasureTheory

namespace OracleTemplate.GradientOnlyQuasar

open LongTails.Setups.GradientOnlyGeneralizedQuasar

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => ⌈65536 * (1 + Nat.clog 2 ⌈4 / q.δ⌉₊) * (1 + Real.sqrt (q.L0 * q.R ^ 2 / q.ε) + q.L1 * q.R * (1 + Nat.clog 2 ⌈8 * q.Δ / q.ε⌉₊)) / q.γ⌉₊

theorem result : Convergence LongTails.Setups.GradientOnlyGeneralizedQuasar.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun q => budget q 0)
  refine ⟨accelerated, ?_, fun _ _ => trivial⟩
  intro q hv f O hadm
  obtain ⟨hf, hg, ho, hs, u, hm, hR, hΔ, hq⟩ := hadm
  have ha := run_accuracy hv hf hg hs hm hR hΔ hq
  have he (seed : (accelerated q).Seed) (ξ : (k : ℕ) → O.Seed k) :
      output q O (seed, ξ) = (run q (gradient f) (calls q) (0, q.x0, q.x0) seed).2.1 :=
    output_eq_run q O (gradient f) ho (seed, ξ)
  change spec.successful q f (output q O) _
  refine ⟨u, hm, ?_⟩
  simp only [he]
  have hset : {ω : (Fin (calls q) → ℝ) × ((k : ℕ) → O.Seed k) |
      q.ε < f (run q (gradient f) (calls q) (0, q.x0, q.x0) ω.1).2.1 - f u} =
      {samples : Fin (calls q) → ℝ |
        q.ε < f (run q (gradient f) (calls q) (0, q.x0, q.x0) samples).2.1 - f u} ×ˢ Set.univ := by
    ext ω
    simp
  change ((RelativeQuasar.samplesLaw (calls q) : Measure (Fin (calls q) → ℝ)).prod
    (O.law : Measure ((k : ℕ) → O.Seed k)))
      {ω : (Fin (calls q) → ℝ) × ((k : ℕ) → O.Seed k) |
        q.ε < f (run q (gradient f) (calls q) (0, q.x0, q.x0) ω.1).2.1 - f u} ≤ ENNReal.ofReal q.δ
  rw [hset, Measure.prod_prod, measure_univ, mul_one]
  exact ha

end OracleTemplate.GradientOnlyQuasar
