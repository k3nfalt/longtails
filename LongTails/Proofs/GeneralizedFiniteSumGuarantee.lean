import LongTails.Proofs.GeneralizedFiniteSumExecution
import LongTails.Proofs.GeneralizedFiniteSumBudget
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set

namespace OracleTemplate.GeneralizedFiniteSum

open LongTails.Setups.GeneralizedSmoothFiniteSum
open LongTails.Setups.FiniteSumSmoothAndConvex (objective)

lemma localAcceleration_success (p : Params) (hp : spec.valid p)
    (f : spec.Instance p) (O : Oracle (spec.Query p) (spec.Reply p))
    (h : spec.admissible p f O) (K : ℕ)
    (hK : p.n + trialCount p * (2 * p.n * epochCount p + p.n) ≤ K) :
    spec.successful p f
      (fun seed : (localAcceleration p).Seed × ((k : ℕ) → O.Seed k) =>
        execute O (localAcceleration p) (fun _ => K) seed.1 seed.2)
      ⟨((localAcceleration p).law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  rcases hp with ⟨h0, h1, hG, hR, hΔ, hε⟩
  rcases h with ⟨hc, hv, hg, hcont, hsmooth, u, hmin, hdist, hgap, hhetero⟩
  let g := fun i => gradient (f i)
  have hO : ∀ history i x seed, O.answer history (0, (i, x)) seed = (f i x, g i x) := by
    intro history i x seed
    apply Prod.ext
    · exact hv history seed i x
    · exact (hg history seed i x).gradient.symm
  let seed0 := (Classical.choice O.law.nonempty) 0
  have hgrad : ∀ i x, HasGradientAt (f i) (g i x) x := by
    intro i x
    have hh := hg [] seed0 i x
    rw [hO] at hh
    exact hh
  have H : Hyp p f g u := ⟨h0, h1, hG, hR, hΔ, hε, hc, hgrad, hcont, hsmooth,
    hmin, hdist, hgap, hhetero⟩
  have hexec := execute_localAcceleration p f g O hO
  change spec.successful p f
    (fun seed : LocalSeeds p × ((k : ℕ) → O.Seed k) => execute O (localAcceleration p) (fun _ => K) seed.1 seed.2)
    ⟨(PMF.uniformOfFintype (LocalSeeds p)).toMeasure.prod (O.law : Measure _), inferInstance⟩
  simp only [hexec _ _ K hK]
  refine ⟨(measurable_of_finite (amplifiedOutput p f g)).comp measurable_fst,
    u, hmin, ?_, ?_⟩
  · exact measurePreserving_fst.integrable_comp_of_integrable
      (Integrable.of_finite (f := fun ξ : LocalSeeds p => objective f (amplifiedOutput p f g ξ) - objective f u)
        (μ := (PMF.uniformOfFintype (LocalSeeds p)).toMeasure))
  · change (∫ seed : LocalSeeds p × ((k : ℕ) → O.Seed k),
      objective f (amplifiedOutput p f g seed.1) - objective f u
      ∂(PMF.uniformOfFintype (LocalSeeds p)).toMeasure.prod (O.law : Measure _)) ≤ p.ε
    rw [integral_fun_fst (fun ξ => objective f (amplifiedOutput p f g ξ) - objective f u)]
    simp only [probReal_univ, one_smul]
    rw [FiniteSum.uniform_integral]
    exact amplified_accuracy p f g u H

end OracleTemplate.GeneralizedFiniteSum
