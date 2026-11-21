import LongTails.Proofs.GradientDiversityGeometry
import LongTails.Proofs.WeightedInterpolationConvergence
import LongTails.Proofs.WeightedInterpolationRuntime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.GradientDiversityConvergence

open LongTails.Setups.DistributedGradientDiversity MeasureTheory DistributedTemplate
open LongTails.Algorithms.GradientDiversitySgd
open GradientDiversitySchedule GradientDiversityGeometry
open LongTails.Algorithms.WeightedInterpolationSgd (stepSize fraction)

variable {p : Params} {f : Functions p} {z : Point p}

lemma radius (H : Geometry p f) (hz : z ∈ solutions p f) (hR : ‖p.x0-z‖ ≤ p.R)
    (k : ℕ) (i : Fin p.n) (x : Point p) :
    ‖(stepSize (schedule p) k * W.weights (schedule p) i / fraction (schedule p) i) •
      gradient (f i) x‖ ≤ ‖x-p.x0‖ + p.R := by
  let q := schedule p
  let a := stepSize q k * W.weights q i / fraction q i
  have hp := schedule_valid H.valid
  obtain ⟨ht,hstep⟩ := WeightedInterpolationAllocation.step_bounds hp k
  have ha := (WeightedInterpolationPrecision.alpha_bounds hp k i).1
  have hprofile := WeightedInterpolationPrecision.alpha_profile hp i
  rw [tuned H.valid] at hprofile
  change W.weights q i / fraction q i ≤ 2 * speed p * curvature p i at hprofile
  have hL := H.valid.2.1.trans_le H.valid.2.2.1
  have hs : 0 ≤ p.L * spread p := mul_nonneg hL.le (by unfold spread; positivity)
  have hsum := speed_sum_pos H.valid
  have h : a * (p.L * spread p) ≤ 1 := calc
    _ = stepSize q k * ((W.weights q i / fraction q i) * (p.L * spread p)) := by dsimp [a]; ring
    _ ≤ stepSize q k * (2 * speed p * (curvature p i * (p.L * spread p))) := by
      rw [← mul_assoc (2 * speed p)]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hprofile hs) ht
    _ ≤ stepSize q k * (2 * speed p * scale p) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (scale_signal H.valid i) (by positivity)) ht
    _ ≤ 1 := by rw [← smooth_eq H.valid]; linarith only [hstep]
  change ‖a • gradient (f i) x‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have hg := mul_le_mul_of_nonneg_left (local_norm H hz i x) ha
  have hd := norm_sub_le_norm_sub_add_norm_sub x p.x0 z
  nlinarith only [hg, mul_le_mul_of_nonneg_right h (norm_nonneg (x-z)), hd, hR]

lemma peak_eq (p : Params) : gain p (peak p) = Finset.univ.sup' Finset.univ_nonempty (gain p) :=
  le_antisymm (Finset.le_sup' _ (Finset.mem_univ _)) (Finset.sup'_le _ _ fun i _ => le_peak p i)

lemma runtime (hp : spec.valid p) (T : Time)
    (hT : let I := ∑ i, curvature p i ^ 2 / p.h i
          let A := 2 * speed p * scale p / I
          let w := Nat.size ⌈2 + p.d + A + (p.R^2 + (p.σ * largest p / scale p)^2)/p.ε⌉₊
          2048 * (p.σ^2/(I*p.ε) + A * (1 + Real.log (1+p.R^2/p.ε)) *
            (((Finset.univ.sup p.h : Time) : ℝ) + p.l + p.b*(64 + 1024*(p.d : ℝ)*w))) ≤ (T : ℝ)) :
    Algorithms.DistributedBatchedSgd.timeBudget (Algorithms.WeightedInterpolationSgd.transport (schedule p))
      (Algorithms.WeightedInterpolationSgd.config (schedule p) T) = T := by
  apply WeightedInterpolationRuntime.time_suffices (schedule_valid hp)
  have hI : W.information (schedule p) = ∑ i, curvature p i ^ 2 / p.h i := by
    unfold LongTails.Algorithms.WeakInterpolationDesign.information
    simp_rw [weights_eq hp, tuned hp]
    exact Finset.sum_congr rfl (fun i _ => by unfold gain; ring)
  have hn : W.noiseRadius (schedule p) = p.σ * largest p / scale p := by
    unfold LongTails.Algorithms.WeakInterpolationDesign.noiseRadius
    rw [largest_eq hp, funext (tuned hp)]
    rfl
  unfold WeightedInterpolationCost.magnitude WeightedInterpolationCost.condition WeightedInterpolationCost.burn
  rw [hI, smooth_eq hp, hn]
  exact hT

lemma success (hp : spec.valid p) (T : Time)
    (ht : Algorithms.DistributedBatchedSgd.timeBudget (Algorithms.WeightedInterpolationSgd.transport (schedule p))
      (Algorithms.WeightedInterpolationSgd.config (schedule p) T) = T)
    (f : Functions p) (O : Oracle (spec.ComputeQuery p) (spec.ComputeReply p) (spec.CommReply p) (spec.numWorkers p))
    (hO : spec.admissible p f O) :
    (∀ᵐ seed ∂(law O (algorithm p T) : Measure _), FiniteEvents O (algorithm p T) T seed) ∧
    spec.successful p f (fun seed => execute O (algorithm p T) T seed.1 seed.2) (law O (algorithm p T)) := by
  obtain ⟨hf, hL, hρ, ⟨z,hz,hR,hq⟩, g, ν, P, rfl, hw, hi⟩ := hO
  have G : GradientDiversityGeometry.Geometry p f :=
    ⟨hp, fun i => (hf i).1, fun i => (hf i).2, hL, hρ⟩
  have hv := GradientDiversitySchedule.schedule_valid hp
  have heq := GradientDiversityGeometry.common_solutions G
  have D : WeightedInterpolationStep.Model (schedule p) f g z (P : Measure (Samples p)) ν := by
    constructor
    · exact hv
    · exact G.convex
    · exact G.differentiable
    · rw [← heq]
      exact hz
    · exact hR
    · exact radius G hz hR
    · intro x y hy
      exact StrongGrowthAlignment.gradient_sq_of_upper (WeakInterpolationDesign.smoothness_pos hv)
        (upper G) (WeakInterpolationGeometry.surrogate_min (WeakInterpolationDesign.weight_nonneg hv) hy) x
    · exact fun x => growth G hz x (hq x)
    · exact hw
    · exact fun i => (hi i).1
    · exact fun i => (hi i).2
  have hex s := WeightedInterpolationExecution.executed (p := schedule p) T g P s ht
  refine ⟨Filter.Eventually.of_forall (fun seed => ?_), ?_⟩
  · exact (hex seed.2).1
  · let out := output p T g
    have hout : Measurable out := WeightedInterpolationSampling.iterate_measurable (p := schedule p) _ _ (fun i => ((hi i).2).measurable) _
    let loss := fun x => Metric.infDist x (solutions p f)^2
    have hloss : Measurable loss := ((Metric.continuous_infDist_pt _).pow 2).measurable
    have hint : Integrable (fun s => loss (out s)) (P : Measure (Samples p)) :=
      DistributedBatchedSgd.integrable_finite_range _ _ (hloss.comp hout)
        (WeightedInterpolationAdaptive.finite_comp out loss (WeightedInterpolationSampling.iterate_finite (p := schedule p) _ _ _))
    have hacc := WeightedInterpolationConvergence.accuracy_of_model D T
    rw [← heq] at hacc
    have H : MeasurePreserving Prod.snd ((Measure.dirac ()).prod (P : Measure (Samples p))) (P : Measure (Samples p)) :=
      measurePreserving_snd
    have hlaw : ProbabilityTheory.HasLaw Prod.snd (P : Measure (Samples p)) ((Measure.dirac ()).prod (P : Measure (Samples p))) :=
      ⟨H.measurable.aemeasurable,H.map_eq⟩
    let actual := fun seed : Unit × Samples p => execute (system p g P) (algorithm p T)
        T seed.1 seed.2
    have he : actual = out ∘ Prod.snd := by
      funext seed
      exact (hex seed.2).2
    let Q := (Measure.dirac ()).prod (P : Measure (Samples p))
    change Measurable actual ∧ Integrable (fun s => loss (actual s)) Q ∧ (∫ s, loss (actual s) ∂Q) ≤ p.ε
    rw [he]
    exact ⟨hout.comp measurable_snd, hlaw.integrable_comp hint,
      (hlaw.integral_comp hint.aestronglyMeasurable).trans_le hacc⟩

end LongTails.Proofs.GradientDiversityConvergence
