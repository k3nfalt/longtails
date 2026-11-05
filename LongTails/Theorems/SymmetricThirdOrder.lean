import LongTails.Setups.StochasticThirdDerivativeConvex
import LongTails.Proofs.SymmetricThirdOrderStopping

namespace LongTails.Theorems.SymmetricThirdOrder

open MeasureTheory OracleTemplate
open LongTails.Setups.StochasticThirdDerivativeConvex
open LongTails.Algorithms.SymmetricThirdOrder

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈(2 : ℝ) ^ 100 * (1 + Real.sqrt (p.σh * p.R ^ 2 / p.ε) + (p.L₃ * p.R ^ 4 / p.ε) ^ (1 / 5 : ℝ) + p.σg ^ 2 * p.R ^ 2 / p.ε ^ 2) * (1 + Real.log (2 + p.Δ / p.ε + p.σh * p.R ^ 2 / p.ε + p.L₃ * p.R ^ 4 / p.ε)) ^ 4⌉₊

theorem result : Convergence LongTails.Setups.StochasticThirdDerivativeConvex.spec budget := by
  classical
  refine ⟨fun p => tunedAlgorithm p.x0 p.L₃ p.R p.Δ p.ε p.σg p.σh, ?_, fun _ _ => trivial⟩
  intro p hp I O ho
  rcases hp with ⟨hL, hR, hΔ, hε, hσg, hσh⟩
  rcases ho with ⟨hf, hc, hthird, hmin, hdist, hgap, g, H, p0, P, hIID, rfl, hg, hH, hhi, hhm⟩
  let cfg := tunedConfig p.x0 p.L₃ p.R p.Δ p.ε p.σg p.σh
  let T := iterationCount p.L₃ p.R p.Δ p.ε p.σh
  let oracle := fun x ω => (g x ω, H x ω)
  let F := fun ξ : ℕ → p.Ω => (sampledState cfg oracle ξ T).point
  have hh := LongTails.Proofs.SymmetricThirdOrderStopping.tuned_accuracy (p0 : Measure _) hIID
    p.x0 p.L₃ p.R p.Δ p.ε p.σg p.σh hL hR hΔ.le hε hσh
    I.1 hf hc I.2 (fun x => hmin (Set.mem_univ x)) hdist hgap hthird oracle
    (hg.measurable.prodMk hH) hg.integrable hg.unbiased hg.variance_integrable hg.variance hhi hhm
  change Measurable F ∧ (∀ ξ, ‖F ξ - p.x0‖ ≤ p.R) ∧
    (2 / 3 : ENNReal) ≤ (P : Measure _) {ξ | I.1 (F ξ) - I.1 I.2 ≤ p.ε} at hh
  have hK := LongTails.Proofs.SymmetricThirdOrderBudget.tuned_call_budget
    p.x0 p.L₃ p.R p.Δ p.ε p.σg p.σh hL.le hΔ.le hε hσh
  have he (w : Unit × (ℕ → p.Ω)) : execute
      { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => (g x ω, H x ω) }
      (tunedAlgorithm p.x0 p.L₃ p.R p.Δ p.ε p.σg p.σh) (budget p) w.1 w.2 = F w.2 := by
    rcases w with ⟨⟨⟩, ξ⟩
    exact LongTails.Proofs.SymmetricThirdOrderHistory.output_eq_sampledState cfg oracle P ξ T (budget p 0) hK
  let out := fun w : Unit × (ℕ → p.Ω) => execute
    { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => (g x ω, H x ω) }
    (tunedAlgorithm p.x0 p.L₃ p.R p.Δ p.ε p.σg p.σh) (budget p) w.1 w.2
  change Measurable out ∧ (∀ w, ‖out w - p.x0‖ ≤ p.R) ∧
    (2 / 3 : ENNReal) ≤ ((Measure.dirac ()).prod (P : Measure _)) {w | I.1 (out w) - I.1 I.2 ≤ p.ε}
  have heq : out = fun w => F w.2 := funext he
  rw [heq]
  refine ⟨hh.1.comp measurable_snd, fun w => hh.2.1 w.2, ?_⟩
  have hset : MeasurableSet {ξ | I.1 (F ξ) - I.1 I.2 ≤ p.ε} :=
    measurableSet_le ((hf.continuous.measurable.comp hh.1).sub measurable_const) measurable_const
  change (2 / 3 : ENNReal) ≤ ((Measure.dirac ()).prod (P : Measure _))
    (Prod.snd ⁻¹' {ξ | I.1 (F ξ) - I.1 I.2 ≤ p.ε})
  rw [(measurePreserving_snd (μ := Measure.dirac ()) (ν := (P : Measure _))).measure_preimage hset.nullMeasurableSet]
  exact hh.2.2

end LongTails.Theorems.SymmetricThirdOrder
