import LongTails.Proofs.RelativeGrowthCertificate
import LongTails.Proofs.WeightedInterpolationRuntime
import LongTails.Proofs.DashaDistributedSimplification

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.RelativeGrowthRuntime

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedRelativeGrowth
open LongTails.Setups.DistributedWeakInterpolation (solutions system)
open LongTails.Algorithms.RelativeGrowthBatches
open LongTails.Algorithms.WeakInterpolationDesign (smoothness information noiseRadius)
open WeightedInterpolationCost RelativeGrowthTuning

variable {p : Params}

lemma enough (hp : spec.valid p) (T : Time)
    (hT : let a := signal p
      let I := ∑ i, a i ^ 2 / (p.h i : ℝ)
      let M := scale p
      let κ := 2 * (∑ i, (p.h i : ℝ)⁻¹) * M / I
      let w := 1 + 2 * Real.log (4 + p.d + κ +
        (p.R^2 + (p.σ * Finset.univ.sup' Finset.univ_nonempty a / M)^2) / p.ε)
      2048 * (p.σ^2 / (I*p.ε) + κ*(1+Real.log (1+p.R^2/p.ε)) *
        (((Finset.univ.sup p.h : Time) : ℝ) + p.l + p.b*(64+1024*(p.d : ℝ)*w))) ≤ (T : ℝ)) :
    Algorithms.DistributedBatchedSgd.timeBudget (Algorithms.WeightedInterpolationSgd.transport (tuning p))
      (Algorithms.WeightedInterpolationSgd.config (tuning p) T) = T := by
  let q := tuning p
  apply WeightedInterpolationRuntime.time_suffices (valid hp)
  have he : information q = ∑ i, signal p i^2 / (p.h i : ℝ) := by
    rw [energy_eq hp]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hs : noiseRadius q = p.σ * Finset.univ.sup' Finset.univ_nonempty (signal p) / scale p := by
    unfold noiseRadius
    rw [scale_eq hp]
    have H : Algorithms.WeakInterpolationDesign.profile q = signal p := funext (profile_eq hp)
    rw [H]
    rfl
  have hv := valid hp
  have hκ : 1 ≤ condition q := condition_one hv
  have hb : 1 ≤ burn q := burn_one hv
  have hε : 0 < q.ε := hp.2.2.2.2.2.2
  have hmag : 0 ≤ magnitude q := by
    have := div_nonneg (add_nonneg (sq_nonneg q.R) (sq_nonneg (noiseRadius q))) hε.le
    unfold magnitude
    linarith [Nat.cast_nonneg (α := ℝ) q.d]
  have hw := DashaDistributedSimplification.size_ceil_le_log (magnitude q) hmag
  have hb' : 0 ≤ condition q * burn q := mul_nonneg (by linarith) (by linarith)
  refine le_trans ?_ hT
  change 2048*(q.σ^2/(information q*q.ε)+condition q*burn q*(_+_+_*(_+_*_*_))) ≤ _
  have heq : condition q = 2*(∑ i, (p.h i : ℝ)⁻¹)*scale p/(∑ i, signal p i ^ 2 / (p.h i : ℝ)) := by
    unfold condition smoothness
    rw [scale_eq hp, he]
    rfl
  have hew : 2+magnitude q = 4+(p.d : ℝ)+condition q+
      (p.R^2+(p.σ * Finset.univ.sup' Finset.univ_nonempty (signal p) / scale p)^2)/p.ε := by
    unfold magnitude
    rw [hs]
    rw [show q.R = p.R from rfl, show q.ε = p.ε from rfl, show q.d = p.d from rfl]
    ring
  rw [hew] at hw
  rw [← heq, ← he]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ hb'
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ p.b.coe_nonneg
  exact add_le_add_right (mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ 1024*(p.d : ℝ))) 64

lemma successful (hp : spec.valid p) (T : Time) (f : Functions p)
    (O : Oracle (Setups.StarNetwork.ComputeQuery (Point p)) (Setups.StarNetwork.ComputeReply (Point p) (Point p))
      (Setups.StarNetwork.CommReply p.n) (p.n+1)) (hO : spec.admissible p f O)
    (ht : Algorithms.DistributedBatchedSgd.timeBudget (Algorithms.WeightedInterpolationSgd.transport (tuning p))
      (Algorithms.WeightedInterpolationSgd.config (tuning p) T) = T) :
    (∀ᵐ s ∂(law O (algorithm p T) : Measure _), FiniteEvents O (algorithm p T) T s) ∧
    spec.successful p f (fun s => execute O (algorithm p T) T s.1 s.2) (law O (algorithm p T)) := by
  obtain ⟨hf, ⟨z,hz,hR,hq⟩,hr,g,ν,P,rfl,hw,hi⟩ := hO
  have he := RelativeGrowthGeometry.solutions_eq (p := p) (f := f) (fun i => (hf i).1) (fun i => (hf i).2.1) hr
  rw [he] at hz hq
  have D := RelativeGrowthCertificate.certificate hp (fun i => (hf i).1) (fun i => (hf i).2.1)
    (fun i => (hf i).2.2) hr hz hR hq hw hi
  have hex s := WeightedInterpolationExecution.executed (p := tuning p) T g P s ht
  refine ⟨Filter.Eventually.of_forall (fun seed => (hex seed.2).1), ?_⟩
  let out : Samples p → Point p := output p T g
  have hout : Measurable out := WeightedInterpolationSampling.iterate_measurable (p := tuning p) _ _ (fun i => ((hi i).2).measurable) _
  let loss := fun x => Metric.infDist x (solutions p.toParams f)^2
  have hloss : Measurable loss := ((Metric.continuous_infDist_pt _).pow 2).measurable
  have hint : Integrable (fun s => loss (out s)) (P : Measure (Samples p)) :=
    DistributedBatchedSgd.integrable_finite_range _ _ (hloss.comp hout)
      (WeightedInterpolationAdaptive.finite_comp out loss (WeightedInterpolationSampling.iterate_finite (p := tuning p) _ _ _))
  have hacc := WeightedInterpolationConvergence.accuracy_certified D T
  let Q := (Measure.dirac ()).prod (P : Measure (Samples p))
  have hlaw : ProbabilityTheory.HasLaw Prod.snd (P : Measure (Samples p)) Q :=
    ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩
  let actual := fun s : Unit × Samples p => execute (system p.toParams g P) (algorithm p T) T s.1 s.2
  have heq : actual = out ∘ Prod.snd := funext fun s => (hex s.2).2
  change Measurable actual ∧ Integrable (fun s => Metric.infDist (actual s) (minimizers p f)^2) Q ∧
    ∫ s, Metric.infDist (actual s) (minimizers p f)^2 ∂Q ≤ p.ε
  rw [heq, he]
  exact ⟨hout.comp measurable_snd, hlaw.integrable_comp hint,
    (hlaw.integral_comp hint.aestronglyMeasurable).trans_le hacc⟩

end LongTails.Proofs.RelativeGrowthRuntime
