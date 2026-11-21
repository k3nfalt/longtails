import LongTails.Setups.DistributedMeanStrongGrowth
import LongTails.Proofs.DistributedGrowthBudget

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Theorems.DistributedStrongGrowthTime

open MeasureTheory DistributedTemplate Setups.DistributedMeanStrongGrowth
open Algorithms.DistributedGrowthSgd Proofs

noncomputable def budget (p : Params) : Time := by
  classical
  let v (t : ℝ) (i : Fin p.n) := (p.h i : ℝ) / ((1-t)*p.h i+t)
  let u (t : ℝ) (i : Fin p.n) := p.n * v t i / ∑ j, v t j
  let t := if h : ∃ t : ℝ, 0 ≤ t ∧ min (1-t) (p.n*p.ρ - ∑ i, u t i^2) = 0
    then h.choose else 0
  let I := ∑ i, u t i^2 / p.h i
  let A := 6*p.n*p.L*(Finset.univ.sup' Finset.univ_nonempty (u t))*(∑ i, (p.h i : ℝ)⁻¹)/(p.μ*I)
  let w := Real.log (3+p.d+A+(p.R^2+(p.σ/(3*p.n*p.L))^2)/p.ε)
  exact (2048 * (p.σ^2/(p.μ^2*I*p.ε) + A*(1+Real.log (1+p.R^2/p.ε))*
    (((Finset.univ.sup p.h : Time) : ℝ)+p.l+p.b*(64+4096*(p.d:ℝ)*w)))).toNNReal

theorem result : TimedConvergence LongTails.Setups.DistributedMeanStrongGrowth.spec budget := by
  refine ⟨fun p => algorithm p (budget p), ?_⟩
  intro p hp
  change Params at p
  refine ⟨trivial, ?_⟩
  intro f O hO
  change Functions p at f
  obtain ⟨hf,hL,hg,⟨z,hz,hR,hQ⟩,g,ν,P,rfl,hw,hi⟩ := hO
  let D : DistributedGrowthGeometry.Geometry p f :=
    ⟨hp, fun i => (hf i).1, fun i => (hf i).2,hL,hg⟩
  have B := DistributedGrowthConvergence.bounds D hz hR hQ g P ν hw hi
  have ht := DistributedGrowthBudget.sufficient hp (budget p) (Real.le_coe_toNNReal _)
  have hex s := WeightedInterpolationExecution.executed (p := schedule p) (budget p) g P s ht
  refine ⟨Filter.Eventually.of_forall (fun s => (hex s.2).1), ?_⟩
  let out := output p (budget p) g
  have hout : Measurable out := WeightedInterpolationSampling.iterate_measurable _ _
    (fun i => ((hi i).2).measurable) _
  let loss := fun x => Metric.infDist x (solutions p f)^2
  have hloss : Measurable loss := ((Metric.continuous_infDist_pt _).pow 2).measurable
  have hint : Integrable (fun s => loss (out s)) (P : Measure (Samples p)) :=
    DistributedBatchedSgd.integrable_finite_range _ _ (hloss.comp hout)
      (WeightedInterpolationAdaptive.finite_comp out loss (WeightedInterpolationSampling.iterate_finite _ _ _))
  have hacc := WeightedInterpolationConvergence.accuracy_of_bounds B (budget p)
  rw [DistributedGrowthConvergence.solution_eq D] at hacc
  have H : MeasurePreserving Prod.snd ((Measure.dirac ()).prod (P : Measure (Samples p))) (P : Measure (Samples p)) :=
    measurePreserving_snd
  have hlaw : ProbabilityTheory.HasLaw Prod.snd (P : Measure (Samples p))
      ((Measure.dirac ()).prod (P : Measure (Samples p))) := ⟨H.measurable.aemeasurable,H.map_eq⟩
  let actual := fun s : Unit × Samples p => execute (Setups.DistributedWeakInterpolation.system (schedule p) g P)
    (algorithm p (budget p)) (budget p) s.1 s.2
  have he : actual = out ∘ Prod.snd := funext (fun s => (hex s.2).2)
  let Q := (Measure.dirac ()).prod (P : Measure (Samples p))
  change Measurable actual ∧ Integrable (fun s => loss (actual s)) Q ∧ (∫ s, loss (actual s) ∂Q) ≤ p.ε
  rw [he]
  exact ⟨hout.comp measurable_snd,hlaw.integrable_comp hint,
    (hlaw.integral_comp hint.aestronglyMeasurable).trans_le hacc⟩

end LongTails.Theorems.DistributedStrongGrowthTime
