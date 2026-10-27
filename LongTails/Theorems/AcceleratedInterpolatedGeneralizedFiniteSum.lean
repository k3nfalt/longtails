import LongTails.Setups.InterpolatedGeneralizedFiniteSum
import LongTails.Proofs.ComponentEnvelopeGuarantee
import LongTails.Proofs.ComponentEnvelopeBudget

open Set MeasureTheory
open scoped BigOperators
namespace OracleTemplate.AcceleratedInterpolatedGeneralizedFiniteSum
open LongTails.Setups.InterpolatedGeneralizedFiniteSum

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈1073741824 * ((p.n : ℝ) * (1 + p.L1 ^ 2 * p.R ^ 2) + Real.sqrt (p.n * p.L0 * p.R ^ 2 / p.ε)) * Real.log (2 + p.n + p.L0 * p.R ^ 2 / p.ε + p.L1 ^ 2 * p.R ^ 2)⌉₊

theorem result : Convergence LongTails.Setups.InterpolatedGeneralizedFiniteSum.spec budget := by
  refine ⟨ComponentEnvelope.algorithm, ?_, fun _ _ => trivial⟩
  intro p hp I oracle hadm
  rcases hp with ⟨h0, h1, hR, he⟩
  rcases hadm with ⟨horacle, hc, hg, hcont, hs, u, hmin, hu⟩
  have hmin' i x : I.loss i u ≤ I.loss i x := hmin i (mem_univ x)
  have hs' i : CompositeGeneralized.SymmetricSmooth (I.grad i) p.L0 p.L1 := hs i
  let K := budget p 0
  have hK : 0 < K := by
    apply Nat.ceil_pos.mpr
    have hn : 0 < (p.n : ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
    have hX : 1 < 2 + p.n + p.L0 * p.R ^ 2 / p.ε + p.L1 ^ 2 * p.R ^ 2 := by
      have hκ : 0 ≤ p.L0 * p.R ^ 2 / p.ε := by positivity
      have hQ : 0 ≤ p.L1 ^ 2 * p.R ^ 2 := by positivity
      linarith
    have hlog := Real.log_pos hX
    positivity
  have hcost := ComponentEnvelope.instance_plan_cost p I h0 h1 he hR hc hg hcont hs' u hmin' hu
  have hbudget := ComponentEnvelope.public_budget_suffices p h0 h1 he hR
  have hcostK : (𝔼 seed : ComponentEnvelope.Seeds p,
      (ComponentEnvelope.Program.cost (fun q => I.grad q.1 q.2) (ComponentEnvelope.plan p seed) : ℝ)) ≤ (K : ℝ) / 6 := by
    change _ ≤ (K : ℝ) at hbudget
    nlinarith
  have hprob := ComponentEnvelope.execute_accuracy_probability p I h0 h1 he hR hc hg hcont hs' u hmin' hu oracle
    (fun history query seed => horacle history seed query.1 query.2) K hK hcostK
  exact ⟨u, hmin, hprob⟩

end OracleTemplate.AcceleratedInterpolatedGeneralizedFiniteSum
