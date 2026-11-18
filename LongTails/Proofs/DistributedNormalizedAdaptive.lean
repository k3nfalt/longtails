import LongTails.Proofs.DistributedNormalizedInnovations
import LongTails.Proofs.DistributedNormalizedMeasurability
import LongTails.Proofs.DistributedNormalizedPath
import LongTails.Proofs.DistributedNormalizedConsensus

open MeasureTheory

namespace LongTails.Proofs.DistributedNormalizedAdaptive

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedDownlink
open DistributedNormalizedBlocks

attribute [local irreducible] LongTails.Algorithms.DistributedNormalizedCompression.fullReceive
  LongTails.Algorithms.DistributedRandomRounding.message

abbrev State (p : Params) := Point p × (Fin p.n → Point p)
abbrev SamplesUp (p : Params) (cfg : Config) :=
  (Fin p.n → Fin cfg.batch → p.Ω) × WorkerDraws p

noncomputable def freshIncrement (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (k : ℕ)
    (s : State p) (z : SamplesUp p cfg) : Point p :=
  let ξ := fun _ : ℕ => (z.1, (z.2, z.2))
  increment cfg (estimator p cfg (assembledDraws p cfg ξ) g (assembledSamples p cfg ξ) k
    ⟨s.1, s.2⟩)

lemma freshIncrement_norm (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (k : ℕ)
    (s : State p) (z : SamplesUp p cfg) (hη : 0 ≤ cfg.stepSize) :
    ‖freshIncrement p cfg g k s z‖ ≤ cfg.stepSize :=
  DistributedNormalizedPath.increment_norm p cfg hη _

lemma measurable_freshIncrement (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) :
    Measurable (Function.uncurry (freshIncrement p cfg g k)) := by
  let B := fun z : State p × SamplesUp p cfg => (z.2.1, (z.2.2, z.2.2))
  have hB : Measurable B := (measurable_fst.comp measurable_snd).prodMk
    ((measurable_snd.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd))
  have hξ : Measurable (fun z : State p × SamplesUp p cfg => fun _ : ℕ => B z) :=
    Measurable.of_eval fun _ => hB
  have hD := (measurable_assembledDraws p cfg).comp hξ
  have hS := (measurable_assembledSamples p cfg).comp hξ
  have hs (i : Fin p.n) : Measurable (fun z : State p × SamplesUp p cfg => z.1.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
  have he := DistributedNormalizedMeasurability.measurable_estimator p cfg g hg hD hS
    (s := fun z : State p × SamplesUp p cfg => ⟨z.1.1, z.1.2⟩) hs k
  exact DistributedNormalizedMeasurability.measurable_increment p cfg he

lemma increment_independent_down (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (k : ℕ)
    (s : State p) (z : RoundBlock p cfg) :
    increment cfg (estimator p cfg (assembledDraws p cfg (fun _ => z)) g
      (assembledSamples p cfg (fun _ => z)) k ⟨s.1, s.2⟩) =
      freshIncrement p cfg g k s (z.1, z.2.1) := by
  unfold freshIncrement estimator uplinkReceive uplinkMessage
  simp only [assembled_draws_even]
  rfl

lemma freshIncrement_actual (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (ξ : ℕ → RoundBlock p cfg)
    (k : ℕ) (s : State p) :
    increment cfg (estimator p cfg (assembledDraws p cfg ξ) g
      (assembledSamples p cfg ξ) k ⟨s.1, s.2⟩) =
      freshIncrement p cfg g k s ((ξ k).1, (ξ k).2.1) := by
  apply Eq.trans _ (increment_independent_down p cfg g k s (ξ k))
  have h := congrArg Iterate.root (assembled_next_local p cfg g ξ k ⟨s.1, s.2⟩)
  exact add_left_cancel h

noncomputable def meanNoise (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (k : ℕ)
    (s : State p) (z : RoundBlock p cfg) : Point p :=
  (p.n : ℝ)⁻¹ • ∑ i, DistributedNormalizedInnovations.guardedNoise p cfg k s.1
    (freshIncrement p cfg g k s (z.1, z.2.1)) (z.2.2 i)

lemma measurable_meanNoise (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) :
    Measurable (Function.uncurry (meanNoise p cfg g k)) := by
  have hF : Measurable (fun z : State p × RoundBlock p cfg => (z.1, (z.2.1, z.2.2.1))) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hu := (measurable_freshIncrement p cfg g hg k).comp hF
  have hnoise (i : Fin p.n) : Measurable (fun z : State p × RoundBlock p cfg =>
      DistributedNormalizedInnovations.guardedNoise p cfg k z.1.1
        (freshIncrement p cfg g k z.1 (z.2.1, z.2.2.1)) (z.2.2.2 i)) :=
    DistributedNormalizedInnovations.measurable_guardedNoise p cfg k
      (measurable_fst.comp measurable_fst) hu
      ((measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))
  exact (Finset.measurable_sum Finset.univ (fun i _ => hnoise i)).fun_const_smul _

attribute [local irreducible] freshIncrement meanNoise

set_option maxHeartbeats 800000 in
lemma meanNoise_moments (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (K k : ℕ) (hk : k < K)
    (s : State p) (hη : 0 ≤ cfg.stepSize)
    (hsr : 0 < cfg.refreshSpacing) (hsi : 0 < cfg.incrementSpacing)
    (hcapi : p.d * cfg.stepSize ≤ cfg.incrementSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hcapr : K * cfg.stepSize ≤ cfg.refreshSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hvr : p.d * cfg.refreshSpacing ^ 2 ≤ cfg.stepSize ^ 2 / 16)
    (hvi : cfg.incrementSpacing ^ 2 ≤ p.d * cfg.stepSize ^ 2) :
    let P := (roundLaw p cfg μ : Measure (RoundBlock p cfg))
    Integrable (meanNoise p cfg g k s) P ∧
      (∫ z, meanNoise p cfg g k s z ∂P) = 0 ∧
      Integrable (fun z => ‖meanNoise p cfg g k s z‖ ^ 2) P ∧
      (∫ z, ‖meanNoise p cfg g k s z‖ ^ 2 ∂P) ≤
        (if refresh cfg k then cfg.stepSize ^ 2 / 64
        else 2 * p.d * cfg.stepSize ^ 2 / cfg.downlinkCount) / p.n := by
  intro P
  let Q := (workerDrawsLaw p : Measure (WorkerDraws p))
  let B := Measure.pi fun i : Fin p.n => Measure.pi fun _ : Fin cfg.batch => (μ i : Measure p.Ω)
  let v : ℝ := (if refresh cfg k then cfg.stepSize ^ 2 / 64
    else 2 * p.d * cfg.stepSize ^ 2 / cfg.downlinkCount) / p.n
  have hinner (b : Fin p.n → Fin cfg.batch → p.Ω) :
      Integrable (fun z : WorkerDraws p × WorkerDraws p => meanNoise p cfg g k s (b, z)) (Q.prod Q) ∧
      (∫ z : WorkerDraws p × WorkerDraws p, meanNoise p cfg g k s (b, z) ∂Q.prod Q) = 0 ∧
      Integrable (fun z : WorkerDraws p × WorkerDraws p => ‖meanNoise p cfg g k s (b, z)‖ ^ 2) (Q.prod Q) ∧
      (∫ z : WorkerDraws p × WorkerDraws p, ‖meanNoise p cfg g k s (b, z)‖ ^ 2 ∂Q.prod Q) ≤ v := by
    have hmap : Measurable (fun z : WorkerDraws p × WorkerDraws p => (s, (b, z))) :=
      measurable_const.prodMk (measurable_const.prodMk measurable_id)
    have hm : Measurable (fun z : WorkerDraws p × WorkerDraws p => meanNoise p cfg g k s (b, z)) :=
      (measurable_meanNoise p cfg g hg k).comp hmap
    have ht (up : WorkerDraws p) := DistributedNormalizedInnovations.guarded_average_noise_moments
      p cfg K k hk s.1 (freshIncrement p cfg g k s (b, up)) hη
      (freshIncrement_norm p cfg g k s (b, up) hη) hsr hsi hcapi hcapr hvr hvi
    exact DistributedCompressionIntegration.product_centered_moments Q Q
      (fun up down => meanNoise p cfg g k s (b, (up, down))) v hm
      (fun up => by simpa only [meanNoise, Q] using (ht up).2.2.1)
      (fun up => by simpa only [meanNoise, Q] using (ht up).2.1)
      (fun up => by simpa only [meanNoise, Q, v] using (ht up).2.2.2)
  have hmap : Measurable (fun z : RoundBlock p cfg => (s, z)) := measurable_const.prodMk measurable_id
  have hm : Measurable (fun z : RoundBlock p cfg => meanNoise p cfg g k s z) :=
    (measurable_meanNoise p cfg g hg k).comp hmap
  exact DistributedCompressionIntegration.product_centered_moments B (Q.prod Q)
    (fun b z => meanNoise p cfg g k s (b, z)) v hm
    (fun b => (hinner b).2.2.1) (fun b => (hinner b).2.1) (fun b => (hinner b).2.2.2)

noncomputable def pairTrajectory (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (ξ : ℕ → RoundBlock p cfg) (k : ℕ) : State p :=
  let s := trajectory p cfg (assembledDraws p cfg ξ) g (assembledSamples p cfg ξ) k
  (s.root, s.workers)

lemma measurable_pairTrajectory (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) :
    Measurable (fun ξ => pairTrajectory p cfg g ξ k) := by
  have h := DistributedNormalizedMeasurability.measurable_trajectory p cfg g hg
    (measurable_assembledDraws p cfg) (measurable_assembledSamples p cfg) k
  exact h.1.prodMk (Measurable.of_eval h.2)

lemma pairTrajectory_prefix (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (ξ ζ : ℕ → RoundBlock p cfg)
    (k : ℕ) (h : ∀ j, j < k → ξ j = ζ j) :
    pairTrajectory p cfg g ξ k = pairTrajectory p cfg g ζ k := by
  unfold pairTrajectory
  rw [assembled_trajectory_prefix p cfg g ξ ζ k h]

noncomputable def meanError (p : Params) (s : State p) : Point p :=
  (p.n : ℝ)⁻¹ • ∑ i, (s.2 i - s.1)

lemma measurable_meanError (p : Params) : Measurable (meanError p) := by
  apply Measurable.fun_const_smul
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_pi_apply i).comp measurable_snd).sub measurable_fst

lemma meanError_initial (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (ξ : ℕ → RoundBlock p cfg) :
    meanError p (pairTrajectory p cfg g ξ 0) = 0 := by
  simp [meanError, pairTrajectory, trajectory, initial]

noncomputable def pairNext (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (k : ℕ)
    (s : State p) (z : RoundBlock p cfg) : State p :=
  let t := next p cfg (assembledDraws p cfg (fun _ => z)) g
    (assembledSamples p cfg (fun _ => z)) k ⟨s.1, s.2⟩
  (t.root, t.workers)

lemma pairTrajectory_succ (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (ξ : ℕ → RoundBlock p cfg) (k : ℕ) :
    pairTrajectory p cfg g ξ (k + 1) = pairNext p cfg g k (pairTrajectory p cfg g ξ k) (ξ k) := by
  unfold pairTrajectory pairNext
  rw [assembled_trajectory_step]

lemma meanError_pairNext (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (k : ℕ)
    (s : State p) (z : RoundBlock p cfg) (hroot : ‖s.1 - p.x0‖ ≤ k * cfg.stepSize) :
    meanError p (pairNext p cfg g k s z) =
      (if refresh cfg k then (0 : ℝ) else 1) • meanError p s + meanNoise p cfg g k s z := by
  let u := freshIncrement p cfg g k s (z.1, z.2.1)
  let D := assembledDraws p cfg (fun _ => z)
  have hi (i : Fin p.n) :
      downlinkReceive p cfg D k i (s.2 i) (downlinkMessage p cfg D k i (s.1 + u) u) - (s.1 + u) =
        if refresh cfg k then DistributedNormalizedInnovations.guardedNoise p cfg k s.1 u (z.2.2 i)
        else (s.2 i - s.1) + DistributedNormalizedInnovations.guardedNoise p cfg k s.1 u (z.2.2 i) := by
    rw [DistributedNormalizedInnovations.downlink_error_identity]
    have hd : D (2 * k + 1) = z.2.2 := assembled_draws_odd p cfg (fun _ => z) k
    rw [hd, ← DistributedNormalizedInnovations.guardedNoise_eq p cfg k s.1 u (z.2.2 i) hroot]
  unfold meanError pairNext next
  simp only [increment_independent_down]
  change (p.n : ℝ)⁻¹ • ∑ i,
    (downlinkReceive p cfg D k i (s.2 i) (downlinkMessage p cfg D k i (s.1 + u) u) - (s.1 + u)) = _
  simp_rw [hi]
  cases h : refresh cfg k <;>
    simp only [Bool.false_eq_true, ↓reduceIte, zero_smul, zero_add, one_smul,
      Finset.sum_add_distrib, smul_add, meanNoise, u]

lemma mean_error_energy (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (K : ℕ) (hη : 0 ≤ cfg.stepSize)
    (hsr : 0 < cfg.refreshSpacing) (hsi : 0 < cfg.incrementSpacing)
    (hcapi : p.d * cfg.stepSize ≤ cfg.incrementSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hcapr : K * cfg.stepSize ≤ cfg.refreshSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hvr : p.d * cfg.refreshSpacing ^ 2 ≤ cfg.stepSize ^ 2 / 16)
    (hvi : cfg.incrementSpacing ^ 2 ≤ p.d * cfg.stepSize ^ 2) :
    ∀ k, k ≤ K →
      Integrable (fun ξ => ‖meanError p (pairTrajectory p cfg g ξ k)‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => (roundLaw p cfg μ : Measure (RoundBlock p cfg))) ∧
      (∫ ξ, ‖meanError p (pairTrajectory p cfg g ξ k)‖ ^ 2
        ∂Measure.infinitePi (fun _ : ℕ => (roundLaw p cfg μ : Measure (RoundBlock p cfg)))) ≤
          cfg.stepSize ^ 2 / (64 * p.n) + (k % cfg.refreshPeriod : ℕ) *
            (2 * p.d * cfg.stepSize ^ 2 / ((cfg.downlinkCount : ℝ) * p.n)) := by
  have hm (j : ℕ) (hj : j < K) (s : State p) :=
    meanNoise_moments p cfg g hg μ K j hj s hη hsr hsi hcapi hcapr hvr hvi
  refine DistributedNormalizedConsensus.periodic_fresh_energy
    (roundLaw p cfg μ : Measure (RoundBlock p cfg)) cfg.refreshPeriod K
    (fun k ξ => pairTrajectory p cfg g ξ k) (meanError p) (meanNoise p cfg g)
    (cfg.stepSize ^ 2 / (64 * p.n))
    (2 * p.d * cfg.stepSize ^ 2 / ((cfg.downlinkCount : ℝ) * p.n)) (by positivity)
    (fun k => measurable_pairTrajectory p cfg g hg k)
    (fun k ξ ζ h => pairTrajectory_prefix p cfg g ξ ζ k h) (measurable_meanError p)
    (fun k _ => measurable_meanNoise p cfg g hg k)
    (fun j hj s => (hm j hj s).1) (fun j hj s => (hm j hj s).2.2.1)
    (fun j hj s => (hm j hj s).2.1) ?_ (fun ξ => meanError_initial p cfg g ξ) ?_
  · intro j hj s
    have hv := (hm j hj s).2.2.2
    by_cases hr : (j + 1) % (cfg.refreshPeriod : ℕ) = 0
    · simpa [refresh, hr, div_div] using hv
    · simpa [refresh, hr, div_div] using hv
  · intro j _ ξ
    rw [pairTrajectory_succ]
    have hroot : ‖(pairTrajectory p cfg g ξ j).1 - p.x0‖ ≤ j * cfg.stepSize :=
      DistributedNormalizedPath.root_path p cfg hη (assembledDraws p cfg ξ) g (assembledSamples p cfg ξ) j
    simpa [refresh] using meanError_pairNext p cfg g j (pairTrajectory p cfg g ξ j) (ξ j) hroot

noncomputable def workerNoise (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (k : ℕ) (i : Fin p.n)
    (s : State p) (z : RoundBlock p cfg) : Point p :=
  DistributedNormalizedInnovations.guardedNoise p cfg k s.1
    (freshIncrement p cfg g k s (z.1, z.2.1)) (z.2.2 i)

lemma measurable_workerNoise (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i))) (k : ℕ) (i : Fin p.n) :
    Measurable (Function.uncurry (workerNoise p cfg g k i)) := by
  have hF : Measurable (fun z : State p × RoundBlock p cfg => (z.1, (z.2.1, z.2.2.1))) :=
    measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  have hu := (measurable_freshIncrement p cfg g hg k).comp hF
  exact DistributedNormalizedInnovations.measurable_guardedNoise p cfg k
    (measurable_fst.comp measurable_fst) hu
    ((measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp measurable_snd)))

noncomputable def workerError (p : Params) (i : Fin p.n) (s : State p) : Point p := s.2 i - s.1

lemma measurable_workerError (p : Params) (i : Fin p.n) : Measurable (workerError p i) :=
  ((measurable_pi_apply i).comp measurable_snd).sub measurable_fst

lemma workerError_initial (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (ξ : ℕ → RoundBlock p cfg) (i : Fin p.n) :
    workerError p i (pairTrajectory p cfg g ξ 0) = 0 := by
  simp [workerError, pairTrajectory, trajectory, initial]

lemma workerError_pairNext (p : Params) (cfg : Config)
    (g : Fin p.n → Point p → p.Ω → Point p) (k : ℕ) (i : Fin p.n)
    (s : State p) (z : RoundBlock p cfg) (hroot : ‖s.1 - p.x0‖ ≤ k * cfg.stepSize) :
    workerError p i (pairNext p cfg g k s z) =
      (if refresh cfg k then (0 : ℝ) else 1) • workerError p i s + workerNoise p cfg g k i s z := by
  unfold workerError pairNext next
  simp only [increment_independent_down]
  rw [DistributedNormalizedInnovations.downlink_error_identity, assembled_draws_odd,
    ← DistributedNormalizedInnovations.guardedNoise_eq p cfg k s.1
      (freshIncrement p cfg g k s (z.1, z.2.1)) (z.2.2 i) hroot]
  cases h : refresh cfg k <;>
    simp only [Bool.false_eq_true, ↓reduceIte, zero_smul, zero_add, one_smul, workerNoise]

attribute [local irreducible] workerNoise

set_option maxHeartbeats 800000 in
lemma workerNoise_moments (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (K k : ℕ) (hk : k < K)
    (i : Fin p.n) (s : State p) (hη : 0 ≤ cfg.stepSize)
    (hsr : 0 < cfg.refreshSpacing) (hsi : 0 < cfg.incrementSpacing)
    (hcapi : p.d * cfg.stepSize ≤ cfg.incrementSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hcapr : K * cfg.stepSize ≤ cfg.refreshSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hvr : p.d * cfg.refreshSpacing ^ 2 ≤ cfg.stepSize ^ 2 / 16)
    (hvi : cfg.incrementSpacing ^ 2 ≤ p.d * cfg.stepSize ^ 2) :
    let P := (roundLaw p cfg μ : Measure (RoundBlock p cfg))
    Integrable (workerNoise p cfg g k i s) P ∧
      (∫ z, workerNoise p cfg g k i s z ∂P) = 0 ∧
      Integrable (fun z => ‖workerNoise p cfg g k i s z‖ ^ 2) P ∧
      (∫ z, ‖workerNoise p cfg g k i s z‖ ^ 2 ∂P) ≤
        (if refresh cfg k then cfg.stepSize ^ 2 / 64
        else 2 * p.d * cfg.stepSize ^ 2 / cfg.downlinkCount) := by
  intro P
  let Q := (workerDrawsLaw p : Measure (WorkerDraws p))
  let B := Measure.pi fun i : Fin p.n => Measure.pi fun _ : Fin cfg.batch => (μ i : Measure p.Ω)
  let v : ℝ := (if refresh cfg k then cfg.stepSize ^ 2 / 64
    else 2 * p.d * cfg.stepSize ^ 2 / cfg.downlinkCount)
  have hl : ProbabilityTheory.HasLaw (fun θ : WorkerDraws p => θ i)
      (Measure.infinitePi fun _ : ℕ => (drawLaw p : Measure (Fin p.d × ℝ))) Q :=
    ⟨(measurable_pi_apply i).aemeasurable, (worker_stream_law p i).map_eq⟩
  have hinner (b : Fin p.n → Fin cfg.batch → p.Ω) :
      Integrable (fun z : WorkerDraws p × WorkerDraws p => workerNoise p cfg g k i s (b, z)) (Q.prod Q) ∧
      (∫ z : WorkerDraws p × WorkerDraws p, workerNoise p cfg g k i s (b, z) ∂Q.prod Q) = 0 ∧
      Integrable (fun z : WorkerDraws p × WorkerDraws p => ‖workerNoise p cfg g k i s (b, z)‖ ^ 2) (Q.prod Q) ∧
      (∫ z : WorkerDraws p × WorkerDraws p, ‖workerNoise p cfg g k i s (b, z)‖ ^ 2 ∂Q.prod Q) ≤ v := by
    have hmap : Measurable (fun z : WorkerDraws p × WorkerDraws p => (s, (b, z))) :=
      measurable_const.prodMk (measurable_const.prodMk measurable_id)
    have hm : Measurable (fun z : WorkerDraws p × WorkerDraws p => workerNoise p cfg g k i s (b, z)) :=
      (measurable_workerNoise p cfg g hg k i).comp hmap
    have ht (up : WorkerDraws p) := DistributedNormalizedInnovations.guarded_noise_moments
      p cfg K k hk s.1 (freshIncrement p cfg g k s (b, up)) hη
      (freshIncrement_norm p cfg g k s (b, up) hη) hsr hsi hcapi hcapr hvr hvi
    exact DistributedCompressionIntegration.product_centered_moments Q Q
      (fun up down => workerNoise p cfg g k i s (b, (up, down))) v hm
      (fun up => by simpa only [workerNoise, Q, Function.comp_def] using hl.integrable_comp (ht up).2.2.1)
      (fun up => by simpa only [workerNoise, Q, Function.comp_def] using
        (hl.integral_comp (ht up).1.aestronglyMeasurable).trans (ht up).2.1)
      (fun up => by simpa only [workerNoise, Q, v, Function.comp_def] using
        (hl.integral_comp (ht up).2.2.1.aestronglyMeasurable).trans_le (ht up).2.2.2)
  have hmap : Measurable (fun z : RoundBlock p cfg => (s, z)) := measurable_const.prodMk measurable_id
  have hm : Measurable (fun z : RoundBlock p cfg => workerNoise p cfg g k i s z) :=
    (measurable_workerNoise p cfg g hg k i).comp hmap
  exact DistributedCompressionIntegration.product_centered_moments B (Q.prod Q)
    (fun b z => workerNoise p cfg g k i s (b, z)) v hm
    (fun b => (hinner b).2.2.1) (fun b => (hinner b).2.1) (fun b => (hinner b).2.2.2)

lemma worker_error_energy (p : Params) (cfg : Config) [Nonempty (Fin p.d)]
    (g : Fin p.n → Point p → p.Ω → Point p)
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (μ : Fin p.n → ProbabilityMeasure p.Ω) (K : ℕ) (i : Fin p.n) (hη : 0 ≤ cfg.stepSize)
    (hsr : 0 < cfg.refreshSpacing) (hsi : 0 < cfg.incrementSpacing)
    (hcapi : p.d * cfg.stepSize ≤ cfg.incrementSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hcapr : K * cfg.stepSize ≤ cfg.refreshSpacing *
      (((2 ^ cfg.downlinkWidth - 1 : ℕ) : ℝ) / 2 - 1))
    (hvr : p.d * cfg.refreshSpacing ^ 2 ≤ cfg.stepSize ^ 2 / 16)
    (hvi : cfg.incrementSpacing ^ 2 ≤ p.d * cfg.stepSize ^ 2) :
    ∀ k, k ≤ K →
      Integrable (fun ξ => ‖workerError p i (pairTrajectory p cfg g ξ k)‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => (roundLaw p cfg μ : Measure (RoundBlock p cfg))) ∧
      (∫ ξ, ‖workerError p i (pairTrajectory p cfg g ξ k)‖ ^ 2
        ∂Measure.infinitePi (fun _ : ℕ => (roundLaw p cfg μ : Measure (RoundBlock p cfg)))) ≤
          cfg.stepSize ^ 2 / 64 + (k % cfg.refreshPeriod : ℕ) *
            (2 * p.d * cfg.stepSize ^ 2 / (cfg.downlinkCount : ℝ)) := by
  have hm (j : ℕ) (hj : j < K) (s : State p) :=
    workerNoise_moments p cfg g hg μ K j hj i s hη hsr hsi hcapi hcapr hvr hvi
  refine DistributedNormalizedConsensus.periodic_fresh_energy
    (roundLaw p cfg μ : Measure (RoundBlock p cfg)) cfg.refreshPeriod K
    (fun k ξ => pairTrajectory p cfg g ξ k) (workerError p i) (fun k => workerNoise p cfg g k i)
    (cfg.stepSize ^ 2 / 64)
    (2 * p.d * cfg.stepSize ^ 2 / (cfg.downlinkCount : ℝ)) (by positivity)
    (fun k => measurable_pairTrajectory p cfg g hg k)
    (fun k ξ ζ h => pairTrajectory_prefix p cfg g ξ ζ k h) (measurable_workerError p i)
    (fun k _ => measurable_workerNoise p cfg g hg k i)
    (fun j hj s => (hm j hj s).1) (fun j hj s => (hm j hj s).2.2.1)
    (fun j hj s => (hm j hj s).2.1) ?_ (fun ξ => workerError_initial p cfg g ξ i) ?_
  · intro j hj s
    have hv := (hm j hj s).2.2.2
    by_cases hr : (j + 1) % (cfg.refreshPeriod : ℕ) = 0
    · simpa [refresh, hr, div_div] using hv
    · simpa [refresh, hr, div_div] using hv
  · intro j _ ξ
    rw [pairTrajectory_succ]
    have hroot : ‖(pairTrajectory p cfg g ξ j).1 - p.x0‖ ≤ j * cfg.stepSize :=
      DistributedNormalizedPath.root_path p cfg hη (assembledDraws p cfg ξ) g (assembledSamples p cfg ξ) j
    simpa [refresh] using workerError_pairNext p cfg g j i (pairTrajectory p cfg g ξ j) (ξ j) hroot

end LongTails.Proofs.DistributedNormalizedAdaptive
