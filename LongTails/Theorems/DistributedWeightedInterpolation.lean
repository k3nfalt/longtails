import LongTails.Setups.DistributedWeakInterpolation
import LongTails.Proofs.WeightedInterpolationConvergence
import LongTails.Proofs.WeightedInterpolationRuntime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Theorems.DistributedWeightedInterpolation

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedWeakInterpolation
open LongTails.Algorithms.WeightedInterpolationSgd LongTails.Algorithms.WeakInterpolationDesign
open LongTails.Proofs

noncomputable def budget (p : Params) : Time := (2048 * (p.σ^2 / (information p * p.ε) + smoothness p / information p * (1 + Real.log (1 + p.R^2 / p.ε)) * (((Finset.univ.sup p.h : Time) : ℝ) + p.l + p.b * (64 + 1024 * (p.d : ℝ) * Nat.size ⌈2 + p.d + smoothness p / information p + (p.R^2 + noiseRadius p^2) / p.ε⌉₊)))).toNNReal

theorem result : TimedConvergence LongTails.Setups.DistributedWeakInterpolation.spec budget := by
  refine ⟨fun p => algorithm p (budget p), ?_⟩
  intro p hp
  change Params at p
  refine ⟨trivial, ?_⟩
  intro f O hO
  change Functions p at f
  obtain ⟨hf, ⟨z,hz,hR,hq⟩, g, ν, P, rfl, hw, hi⟩ := hO
  have D : WeightedInterpolationStep.Data p f g z (P : Measure _) ν :=
    ⟨hp,fun i => (hf i).1,fun i => (hf i).2.1,fun i => (hf i).2.2,hz,hR,hq,hw,
      fun i => (hi i).1,fun i => (hi i).2⟩
  have ht := WeightedInterpolationRuntime.time_suffices hp (budget p) (Real.le_coe_toNNReal _)
  have hex s := WeightedInterpolationExecution.executed (budget p) g P s ht
  refine ⟨Filter.Eventually.of_forall (fun seed => ?_), ?_⟩
  · exact (hex seed.2).1
  · let out := output p (budget p) g
    have hout : Measurable out := WeightedInterpolationSampling.iterate_measurable _ _ (fun i => ((hi i).2).measurable) _
    let loss := fun x => Metric.infDist x (solutions p f)^2
    have hloss : Measurable loss := ((Metric.continuous_infDist_pt _).pow 2).measurable
    have hint : Integrable (fun s => loss (out s)) (P : Measure _) :=
      DistributedBatchedSgd.integrable_finite_range _ _ (hloss.comp hout)
        (WeightedInterpolationAdaptive.finite_comp out loss (WeightedInterpolationSampling.iterate_finite _ _ _))
    have hacc := WeightedInterpolationConvergence.accuracy D (budget p)
    have H : MeasurePreserving Prod.snd ((Measure.dirac ()).prod (P : Measure (Samples p))) (P : Measure (Samples p)) :=
      measurePreserving_snd
    have hlaw : ProbabilityTheory.HasLaw Prod.snd (P : Measure (Samples p)) ((Measure.dirac ()).prod (P : Measure (Samples p))) :=
      ⟨H.measurable.aemeasurable,H.map_eq⟩
    let actual := fun seed : Unit × Samples p => execute (system p g P) (algorithm p (budget p))
        (budget p) seed.1 seed.2
    have he : actual = out ∘ Prod.snd := by
      funext seed
      exact (hex seed.2).2
    let Q := (Measure.dirac ()).prod (P : Measure (Samples p))
    change Measurable actual ∧ Integrable (fun s => loss (actual s)) Q ∧ (∫ s, loss (actual s) ∂Q) ≤ p.ε
    rw [he]
    exact ⟨hout.comp measurable_snd, hlaw.integrable_comp hint,
      (hlaw.integral_comp hint.aestronglyMeasurable).trans_le hacc⟩

end LongTails.Theorems.DistributedWeightedInterpolation
