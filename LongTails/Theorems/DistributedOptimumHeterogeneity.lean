import LongTails.Setups.DistributedOptimumHeterogeneity
import LongTails.Proofs.OptimumHeterogeneityConvergence
import LongTails.Proofs.OptimumHeterogeneityRuntime
import LongTails.Proofs.OptimumHeterogeneitySupport

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Theorems.DistributedOptimumHeterogeneity

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedOptimumHeterogeneity
open LongTails.Algorithms.OptimumHeterogeneitySgd LongTails.Algorithms.OptimumHeterogeneityDesign
open LongTails.Proofs

noncomputable abbrev argmin {α : Type} [Nonempty α] (S : α → Prop) (V : α → ℝ) : α :=
  minimizer S V

noncomputable def budget (p : Params) : Time := by
  classical
  let S (w : Fin p.n → ℝ) := Finset.univ.sup' Finset.univ_nonempty (fun j =>
    p.n * p.μ * w j - ∑ i, p.L i * max (w j - w i) 0)
  let W (w : Fin p.n → ℝ) : Prop := 0 ≤ Finset.univ.inf' Finset.univ_nonempty w ∧
    1 ≤ S w ∧ 4096 * p.n * p.ζ ^ 2 * ∑ i, (w i - (∑ j, w j) / p.n) ^ 2 ≤ p.ε ^ 2
  let V (v : Fin p.n → ℝ) := ∑ i, (p.h i : ℝ) * v i ^ 2
  let w := argmin W V
  let u (i : Fin p.n) := (p.h i : ℝ) * w i
  let M := Finset.univ.sup' Finset.univ_nonempty (fun i => u i * p.L i)
  let κ := 2 * (∑ i, (p.h i : ℝ)⁻¹) * M
  let G := Finset.univ.sup' Finset.univ_nonempty u * (p.σ + Real.sqrt p.n * p.ζ) / M
  let q := Nat.size ⌈2 + p.d + κ + ((p.R + G) / p.ε) ^ 2⌉₊
  exact (24576 * (p.σ ^ 2 * V w / p.ε ^ 2) +
    8192 * κ * (1 + Real.log (1 + (p.R / p.ε) ^ 2)) *
    (((Finset.univ.sup p.h : Time) : ℝ) + p.l + p.b * (64 + 1024 * (p.d : ℝ) * q))).toNNReal

theorem result : TimedConvergence LongTails.Setups.DistributedOptimumHeterogeneity.spec budget := by
  refine ⟨fun p => algorithm p (budget p), ?_⟩
  intro p hp
  change Params at p
  refine ⟨trivial, ?_⟩
  intro f O hO
  change Functions p at f
  obtain ⟨hf, ⟨z,hz,hR,hoff,hq⟩, g, ν, P, rfl, hw, hi⟩ := hO
  have D : OptimumHeterogeneityStep.Data p f g z (P : Measure _) ν :=
    ⟨⟨hp,fun i => (hf i).1,fun i => (hf i).2.1,fun i => (hf i).2.2,hz,hR,hoff,hq⟩,hw,
      fun i => (hi i).1,fun i => (hi i).2⟩
  have ht := OptimumHeterogeneityRuntime.time_suffices hp (budget p) (by
    apply le_trans _ (Real.le_coe_toNNReal _)
    unfold OptimumHeterogeneityCost.magnitude
    rw [OptimumHeterogeneityCost.amplitude_eq hp]
    unfold OptimumHeterogeneityCost.condition capacity weights
    rw [OptimumHeterogeneitySupport.designs_eq hp]
    exact le_rfl)
  have hex s := OptimumHeterogeneityExecution.executed (budget p) g P s ht
  refine ⟨Filter.Eventually.of_forall (fun seed => ?_), ?_⟩
  · exact (hex seed.2).1
  · let out := output p (budget p) g
    have hout : Measurable out := OptimumHeterogeneitySampling.iterate_measurable _ _ (fun i => ((hi i).2).measurable) _
    let loss := fun x => Metric.infDist x (solutions p f)^2
    have hloss : Measurable loss := ((Metric.continuous_infDist_pt _).pow 2).measurable
    have hint : Integrable (fun s => loss (out s)) (P : Measure _) :=
      DistributedBatchedSgd.integrable_finite_range _ _ (hloss.comp hout)
        (OptimumHeterogeneityAdaptive.finite_comp out loss (OptimumHeterogeneitySampling.iterate_finite _ _ _))
    have hacc := OptimumHeterogeneityConvergence.accuracy D (budget p)
    have H : MeasurePreserving Prod.snd ((Measure.dirac ()).prod (P : Measure (Samples p))) (P : Measure (Samples p)) :=
      measurePreserving_snd
    have hlaw : ProbabilityTheory.HasLaw Prod.snd (P : Measure (Samples p)) ((Measure.dirac ()).prod (P : Measure (Samples p))) :=
      ⟨H.measurable.aemeasurable,H.map_eq⟩
    let actual := fun seed : Unit × Samples p => execute (Setups.DistributedWeakInterpolation.system p.toParams g P) (algorithm p (budget p))
        (budget p) seed.1 seed.2
    have he : actual = out ∘ Prod.snd := by
      funext seed
      exact (hex seed.2).2
    let Q := (Measure.dirac ()).prod (P : Measure (Samples p))
    change Measurable actual ∧ Integrable (fun s => loss (actual s)) Q ∧ (∫ s, loss (actual s) ∂Q) ≤ p.ε^2
    rw [he]
    exact ⟨hout.comp measurable_snd, hlaw.integrable_comp hint,
      (hlaw.integral_comp hint.aestronglyMeasurable).trans_le hacc⟩

end LongTails.Theorems.DistributedOptimumHeterogeneity
