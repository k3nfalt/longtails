import LongTails.Proofs.DashaScalingMeasurability
import LongTails.Proofs.DashaProcess
import LongTails.Proofs.DashaScalingInitialization

namespace LongTails.Proofs.DashaScalingConvergence

open MeasureTheory
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaScalingPotential
open LongTails.Proofs.DashaScalingMeasurability

variable {p : Params}

lemma totalReward_bound (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (lower : ℝ) (hlower : ∀ x, lower ≤ objective p f x)
    (K : ℕ) (s : Reduced p) :
    let R := fun s : Reduced p => stepSize p c / 2 * ‖gradient (objective p f) s.1‖ ^ 2
    let total := DashaProcess.totalReward (reducedStep p c f) (potential c f lower) R K s
    Integrable total (Measure.infinitePi fun _ : ℕ => (sampleLaw p : Measure _)) ∧
      (∫ seed, total seed ∂Measure.infinitePi (fun _ : ℕ => (sampleLaw p : Measure _))) ≤
        potential c f lower s + K * (stepSize p c * p.ε ^ 2 / 32) := by
  have hfm : Measurable (objective p f) := by
    apply Continuous.measurable
    rw [continuous_iff_continuousAt]
    intro x
    exact (DashaScalingDescent.objective_gradient f hg x).continuousAt
  have hgm : Measurable (gradient (objective p f)) :=
    OracleTemplate.SublevelRobustGradient.gradient_measurable hL hlip
  have hγ := DashaScalingParameters.stepSize_pos c hL hH
  exact DashaProcess.totalReward_bound (sampleLaw p : Measure _)
    (reducedStep p c f) (potential c f lower)
    (fun s : Reduced p => stepSize p c / 2 * ‖gradient (objective p f) s.1‖ ^ 2)
    (reducedStep_measurable c f (local_gradient_measurable f hH hs))
    (potential_measurable c f lower hfm hgm (local_gradient_measurable f hH hs))
    (measurable_const.mul ((hgm.comp measurable_fst).norm.pow_const 2))
    (potential_nonneg c f lower hL hH hlower) (fun _ => by positivity)
    (next_potential_integrable c hε f hg lower) (stepSize p c * p.ε ^ 2 / 32)
    (next_potential_drift c hε hL hH f hg hlip hs lower) K s

lemma process_trajectory_eq (c : Choice p) (f : Functions p) (seed : ℕ → Sample p) (K : ℕ) :
    HeavyTailedProductProcess.trajectory (reducedStep p c f) K (initialReduced p c f (seed 0))
      (fun k => seed (k + 1)) = reduce p (trajectory p c f seed K) := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [HeavyTailedProductProcess.trajectory_succ_last, ih]
    exact reduced_trajectory_step c f seed K

lemma initialized_reward_eq (c : Choice p) (f : Functions p) (lower : ℝ)
    (seed : ℕ → Sample p) (K : ℕ) :
    DashaProcess.totalReward (reducedStep p c f) (potential c f lower)
      (fun s : Reduced p => stepSize p c / 2 * ‖gradient (objective p f) s.1‖ ^ 2)
      K (initialReduced p c f (seed 0)) (fun k => seed (k + 1)) =
    potential c f lower (reduce p (trajectory p c f seed K)) +
      stepSize p c / 2 * ∑ j ∈ Finset.range K, ‖gradient (objective p f) (trajectory p c f seed j).point‖ ^ 2 := by
  rw [DashaProcess.totalReward_eq]
  simp_rw [process_trajectory_eq]
  rw [Finset.mul_sum]
  rfl

lemma initialized_residual_sum_bound (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (lower : ℝ) (hlower : ∀ x, lower ≤ objective p f x)
    (init : Sample p → Reduced p) (hinit : Measurable init)
    (hIi : Integrable (fun seed => potential c f lower (init seed)) (sampleLaw p : Measure _)) (K : ℕ) :
    let total := fun seed : ℕ → Sample p => ∑ j ∈ Finset.range K,
      stepSize p c / 2 * ‖gradient (objective p f)
        (HeavyTailedProductProcess.trajectory (reducedStep p c f) j (init (seed 0))
          (fun k => seed (k + 1))).1‖ ^ 2
    Integrable total (Measure.infinitePi fun _ : ℕ => (sampleLaw p : Measure _)) ∧
      (∫ seed, total seed ∂Measure.infinitePi (fun _ : ℕ => (sampleLaw p : Measure _))) ≤
        (∫ seed, potential c f lower (init seed) ∂(sampleLaw p : Measure _)) +
          K * (stepSize p c * p.ε ^ 2 / 32) := by
  have hfm : Measurable (objective p f) := by
    apply Continuous.measurable
    rw [continuous_iff_continuousAt]
    intro x
    exact (DashaScalingDescent.objective_gradient f hg x).continuousAt
  have hgm : Measurable (gradient (objective p f)) :=
    OracleTemplate.SublevelRobustGradient.gradient_measurable hL hlip
  have hγ := DashaScalingParameters.stepSize_pos c hL hH
  exact DashaProcess.initialized_reward_sum_bound (sampleLaw p : Measure _)
    (reducedStep p c f) init (potential c f lower)
    (fun s : Reduced p => stepSize p c / 2 * ‖gradient (objective p f) s.1‖ ^ 2)
    (reducedStep_measurable c f (local_gradient_measurable f hH hs)) hinit
    (potential_measurable c f lower hfm hgm (local_gradient_measurable f hH hs))
    (measurable_const.mul ((hgm.comp measurable_fst).norm.pow_const 2))
    (potential_nonneg c f lower hL hH hlower) (fun _ => by positivity)
    (next_potential_integrable c hε f hg lower) hIi (stepSize p c * p.ε ^ 2 / 32)
    (next_potential_drift c hε hL hH f hg hlip hs lower) K

lemma dense_residual_sum_bound (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (lower : ℝ) (hlower : ∀ x, lower ≤ objective p f x)
    (hgap : objective p f p.x0 - lower ≤ p.Δ) (K : ℕ) :
    let total := fun seed : ℕ → Sample p => stepSize p c / 2 * ∑ j ∈ Finset.range K,
      ‖gradient (objective p f) (trajectory p c f seed j).point‖ ^ 2
    Integrable total (Measure.infinitePi fun _ : ℕ => (sampleLaw p : Measure _)) ∧
      (∫ seed, total seed ∂Measure.infinitePi (fun _ : ℕ => (sampleLaw p : Measure _))) ≤
        p.Δ + stepSize p c * p.ε ^ 2 / 64 + K * (stepSize p c * p.ε ^ 2 / 32) := by
  have hinit := DashaScalingInitialization.dense_initial_potential c hε hL hH f hg lower
  have hb := initialized_residual_sum_bound c hε hL hH f hg hlip hs lower hlower
    (initialReduced p c f) (initialReduced_measurable c f) hinit.1 K
  simp only [process_trajectory_eq, reduce, ← Finset.mul_sum] at hb
  exact ⟨hb.1, by linarith only [hb.2, hinit.2, hgap]⟩

lemma dense_output_accuracy (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (lower : ℝ) (hlower : ∀ x, lower ≤ objective p f x)
    (hgap : objective p f p.x0 - lower ≤ p.Δ) :
    Measurable (output p c f) ∧
    Integrable (fun seed => ‖gradient (objective p f) (output p c f seed)‖ ^ 2)
      (seedLaw p c : Measure _) ∧
    (∫ seed, ‖gradient (objective p f) (output p c f seed)‖ ^ 2 ∂(seedLaw p c : Measure _)) ≤ p.ε ^ 2 := by
  let μ : Measure (ℕ → Sample p) := Measure.infinitePi fun _ : ℕ => (sampleLaw p : Measure _)
  have hγ := DashaScalingParameters.stepSize_pos c hL hH
  have hw := dense_residual_sum_bound c hε hL hH f hg hlip hs lower hlower hgap (iterations p c)
  have hS : Integrable (fun seed : ℕ → Sample p => ∑ j ∈ Finset.range (iterations p c : ℕ),
      ‖gradient (objective p f) (trajectory p c f seed j).point‖ ^ 2) μ := by
    have hi := hw.1.const_mul (2 / stepSize p c)
    convert hi using 1
    funext seed
    field_simp
  have hgm := OracleTemplate.SublevelRobustGradient.gradient_measurable hL hlip
  have hlocal := local_gradient_measurable f hH hs
  have hX (i : Fin (iterations p c)) : Measurable (fun seed : ℕ → Sample p =>
      ‖gradient (objective p f) (trajectory p c f seed i.val).point‖ ^ 2) :=
    (hgm.comp (measurable_fst.comp (reduced_trajectory_measurable c f hlocal i.val))).norm.pow_const 2
  have hsum (seed : ℕ → Sample p) :
      (∑ i : Fin (iterations p c), ‖gradient (objective p f) (trajectory p c f seed i.val).point‖ ^ 2) =
      ∑ j ∈ Finset.range (iterations p c : ℕ), ‖gradient (objective p f) (trajectory p c f seed j).point‖ ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun j => ‖gradient (objective p f) (trajectory p c f seed j).point‖ ^ 2)
      (iterations p c : ℕ)
  have hSF : Integrable (fun seed : ℕ → Sample p => ∑ i : Fin (iterations p c),
      ‖gradient (objective p f) (trajectory p c f seed i.val).point‖ ^ 2) μ := by
    simpa only [hsum] using hS
  have hu := DashaProcess.uniform_average μ (iterations p c)
    (fun i seed => ‖gradient (objective p f) (trajectory p c f seed i.val).point‖ ^ 2)
    hX (fun _ _ => sq_nonneg _) hSF
  refine ⟨output_measurable c f hlocal, hu.1, ?_⟩
  change (∫ z : Fin (iterations p c) × (ℕ → Sample p),
    ‖gradient (objective p f) (trajectory p c f z.2 z.1.val).point‖ ^ 2
    ∂((PMF.uniformOfFintype (Fin (iterations p c))).toMeasure.prod μ)) ≤ _
  rw [hu.2]
  simp_rw [hsum]
  apply DashaScalingParameters.dense_average_accuracy c hε hL hH
  have hb := hw.2
  rw [integral_const_mul] at hb
  exact hb

lemma process_sparse_trajectory_eq (c initializer : Choice p) (f : Functions p)
    (seed : ℕ → Sample p) (K : ℕ) :
    HeavyTailedProductProcess.trajectory (reducedStep p c f) K
      (reduce p (sparseInitialIterate p c initializer f (seed 0))) (fun k => seed (k + 1)) =
      reduce p (sparseTrajectory p c initializer f seed K) := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [HeavyTailedProductProcess.trajectory_succ_last, ih]
    exact reduced_sparse_trajectory_step c initializer f seed K

lemma sparse_residual_sum_bound (c initializer : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G)
    (lower : ℝ) (hlower : ∀ x, lower ≤ objective p f x)
    (hgap : objective p f p.x0 - lower ≤ p.Δ) (K : ℕ) :
    let total := fun seed : ℕ → Sample p => stepSize p c / 2 * ∑ j ∈ Finset.range K,
      ‖gradient (objective p f) (sparseTrajectory p c initializer f seed j).point‖ ^ 2
    Integrable total (Measure.infinitePi fun _ : ℕ => (sampleLaw p : Measure _)) ∧
      (∫ seed, total seed ∂Measure.infinitePi (fun _ : ℕ => (sampleLaw p : Measure _))) ≤
        p.Δ + stepSize p c * initialPenalty p c initializer + stepSize p c * p.ε ^ 2 / 32 +
          K * (stepSize p c * p.ε ^ 2 / 32) := by
  have hinit := DashaScalingInitialization.sparse_initial_potential c initializer hε hL hH f hg hG lower
  have hb := initialized_residual_sum_bound c hε hL hH f hg hlip hs lower hlower
    (fun seed => reduce p (sparseInitialIterate p c initializer f seed))
    (sparseInitialReduced_measurable c initializer f) hinit.1 K
  dsimp only at hb
  simp_rw [process_sparse_trajectory_eq] at hb
  simp only [reduce, ← Finset.mul_sum] at hb
  dsimp only [reduce] at hinit
  exact ⟨hb.1, by linarith only [hb.2, hinit.2, hgap]⟩

lemma sparse_output_accuracy (c initializer : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (hG : ∀ i, ‖gradient (f i) p.x0‖ ≤ p.G) (lower : ℝ) (hlower : ∀ x, lower ≤ objective p f x)
    (hgap : objective p f p.x0 - lower ≤ p.Δ) :
    Measurable (sparseOutput p c initializer f) ∧
    Integrable (fun seed => ‖gradient (objective p f) (sparseOutput p c initializer f seed)‖ ^ 2)
      (sparseSeedLaw p c initializer : Measure _) ∧
    (∫ seed, ‖gradient (objective p f) (sparseOutput p c initializer f seed)‖ ^ 2 ∂(sparseSeedLaw p c initializer : Measure _)) ≤ p.ε ^ 2 := by
  let μ : Measure (ℕ → Sample p) := Measure.infinitePi fun _ : ℕ => (sampleLaw p : Measure _)
  have hγ := DashaScalingParameters.stepSize_pos c hL hH
  have hw := sparse_residual_sum_bound c initializer hε hL hH f hg hlip hs hG lower hlower hgap (sparseIterations p c initializer)
  have hS : Integrable (fun seed : ℕ → Sample p => ∑ j ∈ Finset.range (sparseIterations p c initializer : ℕ),
      ‖gradient (objective p f) (sparseTrajectory p c initializer f seed j).point‖ ^ 2) μ := by
    have hi := hw.1.const_mul (2 / stepSize p c)
    convert hi using 1
    funext seed
    field_simp
  have hgm := OracleTemplate.SublevelRobustGradient.gradient_measurable hL hlip
  have hlocal := local_gradient_measurable f hH hs
  have hX (i : Fin (sparseIterations p c initializer)) : Measurable (fun seed : ℕ → Sample p =>
      ‖gradient (objective p f) (sparseTrajectory p c initializer f seed i.val).point‖ ^ 2) :=
    (hgm.comp (measurable_fst.comp (reduced_sparse_trajectory_measurable c initializer f hlocal i.val))).norm.pow_const 2
  have hsum (seed : ℕ → Sample p) :
      (∑ i : Fin (sparseIterations p c initializer), ‖gradient (objective p f) (sparseTrajectory p c initializer f seed i.val).point‖ ^ 2) =
      ∑ j ∈ Finset.range (sparseIterations p c initializer : ℕ), ‖gradient (objective p f) (sparseTrajectory p c initializer f seed j).point‖ ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun j => ‖gradient (objective p f) (sparseTrajectory p c initializer f seed j).point‖ ^ 2)
      (sparseIterations p c initializer : ℕ)
  have hSF : Integrable (fun seed : ℕ → Sample p => ∑ i : Fin (sparseIterations p c initializer),
      ‖gradient (objective p f) (sparseTrajectory p c initializer f seed i.val).point‖ ^ 2) μ := by
    simpa only [hsum] using hS
  have hu := DashaProcess.uniform_average μ (sparseIterations p c initializer)
    (fun i seed => ‖gradient (objective p f) (sparseTrajectory p c initializer f seed i.val).point‖ ^ 2)
    hX (fun _ _ => sq_nonneg _) hSF
  refine ⟨sparse_output_measurable c initializer f hlocal, hu.1, ?_⟩
  change (∫ z : Fin (sparseIterations p c initializer) × (ℕ → Sample p),
    ‖gradient (objective p f) (sparseTrajectory p c initializer f z.2 z.1.val).point‖ ^ 2
    ∂((PMF.uniformOfFintype (Fin (sparseIterations p c initializer))).toMeasure.prod μ)) ≤ _
  rw [hu.2]
  simp_rw [hsum]
  apply DashaScalingParameters.sparse_average_accuracy c initializer hε hL hH
  have hb := hw.2
  rw [integral_const_mul] at hb
  exact hb

end LongTails.Proofs.DashaScalingConvergence
