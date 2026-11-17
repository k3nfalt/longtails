import LongTails.Proofs.DashaScalingMoments
import LongTails.Proofs.DashaScalingDescent

namespace LongTails.Proofs.DashaScalingPotential

open MeasureTheory
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling

variable {p : Params}

noncomputable def localError (c : Choice p) (f : Functions p) (s : Reduced p) (i : Fin p.n) : Point p :=
  LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.2 i) - gradient (f i) s.1

noncomputable def localEnergy (c : Choice p) (f : Functions p) (s : Reduced p) : ℝ :=
  (1 / (p.n : ℝ)) * ∑ i, ‖localError c f s i‖ ^ 2

noncomputable def aggregateEnergy (c : Choice p) (f : Functions p) (s : Reduced p) : ℝ :=
  ‖estimate p c (lift p f s) - gradient (objective p f) s.1‖ ^ 2

noncomputable def potential (c : Choice p) (f : Functions p) (lower : ℝ) (s : Reduced p) : ℝ :=
  objective p f s.1 - lower + stepSize p c / momentum p c * aggregateEnergy c f s +
    2 * stepSize p c * variance p c / p.n * localEnergy c f s

lemma localEnergy_nonneg (c : Choice p) (f : Functions p) (s : Reduced p) :
    0 ≤ localEnergy c f s := by unfold localEnergy; positivity

lemma aggregateEnergy_nonneg (c : Choice p) (f : Functions p) (s : Reduced p) :
    0 ≤ aggregateEnergy c f s := sq_nonneg _

lemma potential_nonneg (c : Choice p) (f : Functions p) (lower : ℝ)
    (hL : 0 < p.L) (hH : 0 < p.Lhat) (hlower : ∀ x, lower ≤ objective p f x) (s : Reduced p) :
    0 ≤ potential c f lower s := by
  have hg := DashaScalingParameters.stepSize_pos c hL hH
  have ha := DashaScalingParameters.momentum_pos c
  have hw := DashaScalingParameters.variance_nonneg c
  have he := aggregateEnergy_nonneg c f s
  have hv := localEnergy_nonneg c f s
  have hf := sub_nonneg.mpr (hlower s.1)
  unfold potential
  positivity

lemma lift_reduce_trajectory (c : Choice p) (f : Functions p) (seed : ℕ → Sample p) (k : ℕ) :
    lift p f (reduce p (trajectory p c f seed k)) = trajectory p c f seed k := by
  cases h : trajectory p c f seed k with
  | mk x gradient code =>
    have hg : (fun i => _root_.gradient (f i) x) = gradient := by
      funext i
      simpa only [h] using (DashaScalingDescent.trajectory_gradient c f seed k i).symm
    simp only [reduce, lift, hg]

lemma reduced_trajectory_step (c : Choice p) (f : Functions p) (seed : ℕ → Sample p) (k : ℕ) :
    reducedStep p c f (reduce p (trajectory p c f seed k)) (seed (k + 1)) =
      reduce p (trajectory p c f seed (k + 1)) := by
  unfold reducedStep
  rw [lift_reduce_trajectory]
  rfl

lemma aggregateEnergy_eq (c : Choice p) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (s : Reduced p) :
    aggregateEnergy c f s = ‖(1 / (p.n : ℝ)) • ∑ i, localError c f s i‖ ^ 2 := by
  unfold aggregateEnergy
  rw [DashaScalingDescent.estimate_eq_mean, DashaScalingDescent.objective_gradient_eq f hg,
    ← smul_sub, ← Finset.sum_sub_distrib]
  rfl

lemma trajectory_prefix (c : Choice p) (f : Functions p) (seed seed' : ℕ → Sample p)
    (k : ℕ) (hseed : ∀ j ≤ k, seed j = seed' j) :
    trajectory p c f seed k = trajectory p c f seed' k := by
  induction k with
  | zero => simp only [trajectory, hseed 0 le_rfl]
  | succ k ih =>
    simp only [trajectory, ih (fun j hj => hseed j (Nat.le_trans hj (Nat.le_succ k))),
      hseed (k + 1) le_rfl]

lemma output_prefix (c : Choice p) (f : Functions p)
    (t : Fin (iterations p c)) (seed seed' : ℕ → Sample p)
    (hseed : ∀ j < (iterations p c : ℕ), seed j = seed' j) :
    output p c f (t, seed) = output p c f (t, seed') := by
  unfold output
  rw [trajectory_prefix c f seed seed' t.val (fun j hj => hseed j (lt_of_le_of_lt hj t.isLt))]

lemma potential_drift_algebra (c : Choice p) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    {F Fnext e enext v vnext r s : ℝ} (he : 0 ≤ e) (hs : 0 ≤ s)
    (hf : Fnext ≤ F - stepSize p c / 2 * r -
      (stepSize p c / 2 - min p.L p.Lhat * stepSize p c ^ 2 / 2) * s + stepSize p c / 2 * e)
    (hec : enext ≤ (1 - momentum p c) ^ 2 * e +
      2 * variance p c / p.n * (p.Lhat ^ 2 * stepSize p c ^ 2) * s +
      2 * momentum p c ^ 2 * variance p c / p.n * v +
      (2 * (c.block.val + 1) * spacing p c ^ 2) / p.n)
    (hvc : vnext ≤ (1 - momentum p c) * v +
      2 * variance p c * (p.Lhat ^ 2 * stepSize p c ^ 2) * s +
      2 * (c.block.val + 1) * spacing p c ^ 2) :
    Fnext + stepSize p c / momentum p c * enext +
      2 * stepSize p c * variance p c / p.n * vnext ≤
    F + stepSize p c / momentum p c * e + 2 * stepSize p c * variance p c / p.n * v -
      stepSize p c / 2 * r + stepSize p c * p.ε ^ 2 / 32 := by
  have hb := DashaTracking.potential_step
    (DashaScalingParameters.momentum_pos c) (DashaScalingParameters.momentum_le_one c)
    (DashaScalingParameters.stepSize_pos c hL hH).le (DashaScalingParameters.variance_nonneg c)
    (show (0 : ℝ) < p.n by exact_mod_cast p.n.pos) he hs hf hec hvc
    (DashaScalingParameters.potential_absorption c hL hH)
  have hn := DashaScalingParameters.round_noise_bound c hL hH
  rw [← mul_div_assoc] at hn
  exact hb.trans (add_le_add le_rfl hn)

lemma next_localError (c : Choice p) (f : Functions p) (s : Reduced p) (seed : Sample p)
    (i : Fin p.n) :
    let xnext := s.1 - stepSize p c • estimate p c (lift p f s)
    let g := LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.2 i)
    let h := gradient (f i) s.1
    let hnext := gradient (f i) xnext
    localError c f (reducedStep p c f s seed) i =
      g + LongTails.Algorithms.DashaCyclic.compress c.block c.precision (spacing p c)
        (hnext - h - momentum p c • (g - h)) (seed i) - hnext := by
  dsimp only [localError, reducedStep, reduce]
  rw [DashaScalingDescent.next_local_code]
  rfl

lemma next_localError_moment (c : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (s : Reduced p) (i : Fin p.n) :
    Integrable (fun seed => ‖localError c f (reducedStep p c f s seed) i‖ ^ 2)
      (sampleLaw p : Measure _) ∧
    (∫ seed, ‖localError c f (reducedStep p c f s seed) i‖ ^ 2 ∂(sampleLaw p : Measure _)) ≤
      (1 - momentum p c) * ‖localError c f s i‖ ^ 2 +
      2 * variance p c * ‖gradient (f i) (s.1 - stepSize p c • estimate p c (lift p f s)) -
        gradient (f i) s.1‖ ^ 2 + 2 * (c.block.val + 1) * spacing p c ^ 2 := by
  simp_rw [next_localError]
  exact DashaScalingMoments.local_tracking c hε
    (fun j => LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.2 j))
    (fun j => gradient (f j) s.1)
    (fun j => gradient (f j) (s.1 - stepSize p c • estimate p c (lift p f s))) i

lemma next_localEnergy_integrable (c : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (s : Reduced p) :
    Integrable (fun seed => localEnergy c f (reducedStep p c f s seed))
      (sampleLaw p : Measure _) := by
  exact (integrable_finsetSum _ (fun i _ => (next_localError_moment c hε f s i).1)).const_mul _

lemma next_localEnergy_bound (c : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (s : Reduced p) :
    (∫ seed, localEnergy c f (reducedStep p c f s seed) ∂(sampleLaw p : Measure _)) ≤
      (1 - momentum p c) * localEnergy c f s +
      2 * variance p c * ((1 / (p.n : ℝ)) * ∑ i,
        ‖gradient (f i) (s.1 - stepSize p c • estimate p c (lift p f s)) - gradient (f i) s.1‖ ^ 2) +
      2 * (c.block.val + 1) * spacing p c ^ 2 := by
  unfold localEnergy
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => (next_localError_moment c hε f s i).1)]
  have hb := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (next_localError_moment c hε f s i).2))
    (show 0 ≤ 1 / (p.n : ℝ) by positivity)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hb
  convert hb using 1
  field_simp

lemma next_localEnergy_smooth (c : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (s : Reduced p) :
    (∫ seed, localEnergy c f (reducedStep p c f s seed) ∂(sampleLaw p : Measure _)) ≤
      (1 - momentum p c) * localEnergy c f s +
      2 * variance p c * (p.Lhat ^ 2 * stepSize p c ^ 2) *
        ‖estimate p c (lift p f s)‖ ^ 2 + 2 * (c.block.val + 1) * spacing p c ^ 2 := by
  have hw := DashaScalingParameters.variance_nonneg c
  have hb := next_localEnergy_bound c hε f s
  have hm := mul_le_mul_of_nonneg_left
    (hs (s.1 - stepSize p c • estimate p c (lift p f s)) s.1)
    (show 0 ≤ 2 * variance p c by positivity)
  have he : s.1 - stepSize p c • estimate p c (lift p f s) - s.1 =
      -(stepSize p c) • estimate p c (lift p f s) := by module
  rw [he] at hm
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at hm
  nlinarith only [hb, hm]

lemma next_aggregateEnergy_bound (c : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (s : Reduced p) :
    (∫ seed, aggregateEnergy c f (reducedStep p c f s seed) ∂(sampleLaw p : Measure _)) ≤
      (1 - momentum p c) ^ 2 * aggregateEnergy c f s +
      (2 * variance p c / p.n) * ((1 / (p.n : ℝ)) * ∑ i,
        ‖gradient (f i) (s.1 - stepSize p c • estimate p c (lift p f s)) - gradient (f i) s.1‖ ^ 2) +
      2 * momentum p c ^ 2 * variance p c / p.n * localEnergy c f s +
      (2 * (c.block.val + 1) * spacing p c ^ 2) / p.n := by
  simp_rw [aggregateEnergy_eq c f hg, next_localError]
  have hb := DashaScalingMoments.aggregate_tracking c hε
    (fun j => LongTails.Algorithms.DashaQuantization.reconstruct (spacing p c) (s.2 j))
    (fun j => gradient (f j) s.1)
    (fun j => gradient (f j) (s.1 - stepSize p c • estimate p c (lift p f s)))
  dsimp only at hb
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hb
  convert hb using 1
  dsimp only [localEnergy, localError]
  field_simp
  ring

lemma next_aggregateEnergy_smooth (c : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (s : Reduced p) :
    (∫ seed, aggregateEnergy c f (reducedStep p c f s seed) ∂(sampleLaw p : Measure _)) ≤
      (1 - momentum p c) ^ 2 * aggregateEnergy c f s +
      2 * variance p c / p.n * (p.Lhat ^ 2 * stepSize p c ^ 2) *
        ‖estimate p c (lift p f s)‖ ^ 2 +
      2 * momentum p c ^ 2 * variance p c / p.n * localEnergy c f s +
      (2 * (c.block.val + 1) * spacing p c ^ 2) / p.n := by
  have hw := DashaScalingParameters.variance_nonneg c
  have hb := next_aggregateEnergy_bound c hε f hg s
  have hm := mul_le_mul_of_nonneg_left
    (hs (s.1 - stepSize p c • estimate p c (lift p f s)) s.1)
    (show 0 ≤ 2 * variance p c / (p.n : ℝ) by positivity)
  have he : s.1 - stepSize p c • estimate p c (lift p f s) - s.1 =
      -(stepSize p c) • estimate p c (lift p f s) := by module
  rw [he] at hm
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq] at hm
  nlinarith only [hb, hm]

lemma next_localError_measurable (c : Choice p) (f : Functions p) (s : Reduced p)
    (i : Fin p.n) : Measurable (fun seed => localError c f (reducedStep p c f s seed) i) := by
  simp_rw [next_localError]
  exact (measurable_const.add ((DashaCompression.measurable_compress c.block c.precision
    (spacing p c) _).comp (measurable_pi_apply i))).sub measurable_const

lemma next_aggregateEnergy_integrable (c : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (s : Reduced p) :
    Integrable (fun seed => aggregateEnergy c f (reducedStep p c f s seed))
      (sampleLaw p : Measure _) := by
  simp_rw [aggregateEnergy_eq c f hg]
  have hi (i : Fin p.n) : MemLp (fun seed => localError c f (reducedStep p c f s seed) i)
      2 (sampleLaw p : Measure _) :=
    (memLp_two_iff_integrable_sq_norm (next_localError_measurable c f s i).aestronglyMeasurable).mpr
      (next_localError_moment c hε f s i).1
  have hsum := memLp_finsetSum Finset.univ (fun i _ => hi i)
  have hscaled := hsum.const_smul (1 / (p.n : ℝ))
  exact (memLp_two_iff_integrable_sq_norm hscaled.aestronglyMeasurable).mp hscaled

lemma next_potential_integrable (c : Choice p) (hε : 0 < p.ε) (f : Functions p)
    (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x) (lower : ℝ) (s : Reduced p) :
    Integrable (fun seed => potential c f lower (reducedStep p c f s seed))
      (sampleLaw p : Measure _) := by
  have he := (next_aggregateEnergy_integrable c hε f hg s).const_mul (stepSize p c / momentum p c)
  have hv := (next_localEnergy_integrable c hε f s).const_mul (2 * stepSize p c * variance p c / p.n)
  exact ((integrable_const (objective p f (s.1 - stepSize p c • estimate p c (lift p f s)) - lower)).add he).add hv

lemma next_potential_drift (c : Choice p) (hε : 0 < p.ε) (hL : 0 < p.L) (hH : 0 < p.Lhat)
    (f : Functions p) (hg : ∀ i x, HasGradientAt (f i) (gradient (f i) x) x)
    (hlip : ∀ x y, ‖gradient (objective p f) x - gradient (objective p f) y‖ ≤ p.L * ‖x - y‖)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (lower : ℝ) (s : Reduced p) :
    (∫ seed, potential c f lower (reducedStep p c f s seed) ∂(sampleLaw p : Measure _)) ≤
      potential c f lower s - stepSize p c / 2 * ‖gradient (objective p f) s.1‖ ^ 2 +
        stepSize p c * p.ε ^ 2 / 32 := by
  have hgrad : ∀ x, HasGradientAt (objective p f) (gradient (objective p f) x) x := by
    intro x
    rw [DashaScalingDescent.objective_gradient_eq f hg x]
    exact DashaScalingDescent.objective_gradient f hg x
  have hd := DashaTracking.inexact_descent hgrad
    (DashaScalingDescent.objective_lipschitz_effective f hg hH.le hlip hs)
    s.1 (estimate p c (lift p f s)) (stepSize p c)
  have hf : objective p f (s.1 - stepSize p c • estimate p c (lift p f s)) - lower ≤
      objective p f s.1 - lower - stepSize p c / 2 * ‖gradient (objective p f) s.1‖ ^ 2 -
      (stepSize p c / 2 - min p.L p.Lhat * stepSize p c ^ 2 / 2) *
        ‖estimate p c (lift p f s)‖ ^ 2 + stepSize p c / 2 * aggregateEnergy c f s := by
    dsimp only [aggregateEnergy]
    linarith only [hd]
  have hb := potential_drift_algebra c hL hH (aggregateEnergy_nonneg c f s) (sq_nonneg _)
    hf (next_aggregateEnergy_smooth c hε f hg hs s) (next_localEnergy_smooth c hε f hs s)
  have he := (next_aggregateEnergy_integrable c hε f hg s).const_mul (stepSize p c / momentum p c)
  have hv := (next_localEnergy_integrable c hε f s).const_mul (2 * stepSize p c * variance p c / p.n)
  have hc : Integrable (fun _ : Sample p =>
      objective p f (s.1 - stepSize p c • estimate p c (lift p f s)) - lower)
      (sampleLaw p : Measure _) := integrable_const _
  change (∫ seed, (objective p f (s.1 - stepSize p c • estimate p c (lift p f s)) - lower) +
      stepSize p c / momentum p c * aggregateEnergy c f (reducedStep p c f s seed) +
      2 * stepSize p c * variance p c / p.n * localEnergy c f (reducedStep p c f s seed)
      ∂(sampleLaw p : Measure _)) ≤ _
  have hce : Integrable (fun seed : Sample p =>
      objective p f (s.1 - stepSize p c • estimate p c (lift p f s)) - lower +
      stepSize p c / momentum p c * aggregateEnergy c f (reducedStep p c f s seed))
      (sampleLaw p : Measure _) := hc.add he
  rw [integral_add hce hv, integral_add hc he, integral_const, integral_const_mul,
    integral_const_mul]
  simpa only [probReal_univ, one_smul, potential] using hb

lemma lift_reduce_sparse_trajectory (c initializer : Choice p) (f : Functions p)
    (seed : ℕ → Sample p) (k : ℕ) :
    lift p f (reduce p (sparseTrajectory p c initializer f seed k)) = sparseTrajectory p c initializer f seed k := by
  cases h : sparseTrajectory p c initializer f seed k with
  | mk x gradient code =>
    have hg : (fun i => _root_.gradient (f i) x) = gradient := by
      funext i
      simpa only [h] using (DashaScalingDescent.sparse_trajectory_gradient c initializer f seed k i).symm
    simp only [reduce, lift, hg]

lemma reduced_sparse_trajectory_step (c initializer : Choice p) (f : Functions p)
    (seed : ℕ → Sample p) (k : ℕ) :
    reducedStep p c f (reduce p (sparseTrajectory p c initializer f seed k)) (seed (k + 1)) =
      reduce p (sparseTrajectory p c initializer f seed (k + 1)) := by
  unfold reducedStep
  rw [lift_reduce_sparse_trajectory]
  rfl

lemma sparse_trajectory_prefix (c initializer : Choice p) (f : Functions p) (seed seed' : ℕ → Sample p)
    (k : ℕ) (hseed : ∀ j ≤ k, seed j = seed' j) :
    sparseTrajectory p c initializer f seed k = sparseTrajectory p c initializer f seed' k := by
  induction k with
  | zero => simp only [sparseTrajectory, hseed 0 le_rfl]
  | succ k ih =>
    simp only [sparseTrajectory, ih (fun j hj => hseed j (Nat.le_trans hj (Nat.le_succ k))),
      hseed (k + 1) le_rfl]

lemma sparse_output_prefix (c initializer : Choice p) (f : Functions p)
    (t : Fin (sparseIterations p c initializer)) (seed seed' : ℕ → Sample p)
    (hseed : ∀ j < (sparseIterations p c initializer : ℕ), seed j = seed' j) :
    sparseOutput p c initializer f (t, seed) = sparseOutput p c initializer f (t, seed') := by
  unfold sparseOutput
  rw [sparse_trajectory_prefix c initializer f seed seed' t.val
    (fun j hj => hseed j (lt_of_le_of_lt hj t.isLt))]

end LongTails.Proofs.DashaScalingPotential
