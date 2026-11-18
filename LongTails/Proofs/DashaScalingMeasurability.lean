import LongTails.Proofs.DashaScalingPotential
import LongTails.Proofs.DashaScalingRange
import LongTails.Proofs.SublevelPLConvergence

namespace LongTails.Proofs.DashaScalingMeasurability

open MeasureTheory
open LongTails.Setups.DistributedFreeBroadcastSmoothNonconvex
open LongTails.Algorithms.DashaScaling
open LongTails.Proofs.DashaScalingPotential

variable {p : Params}

lemma local_gradient_measurable (f : Functions p) (hH : 0 < p.Lhat)
    (hs : ∀ x y, (1 / (p.n : ℝ)) * (∑ i, ‖gradient (f i) x - gradient (f i) y‖ ^ 2) ≤
      p.Lhat ^ 2 * ‖x - y‖ ^ 2) (i : Fin p.n) : Measurable (gradient (f i)) := by
  have hn : (0 : ℝ) < p.n := by exact_mod_cast p.n.pos
  apply OracleTemplate.SublevelRobustGradient.gradient_measurable
    (show 0 < Real.sqrt (p.n : ℝ) * p.Lhat by positivity)
  intro x y
  exact DashaScalingRange.local_norm_of_mean_square
    (fun j => gradient (f j) x - gradient (f j) y) p.Lhat ‖x - y‖ hH.le (norm_nonneg _) (hs x y) i

lemma estimate_measurable (c : Choice p) (f : Functions p) :
    Measurable (fun s : Reduced p => estimate p c (lift p f s)) := by
  simp_rw [DashaScalingDescent.estimate_eq_mean]
  exact (measurable_const (a := (1 / (p.n : ℝ)))).smul (Finset.measurable_sum Finset.univ (fun (i : Fin p.n) _ =>
    (DashaQuantization.measurable_reconstruct p.d (spacing p c)).comp
      ((measurable_pi_apply i).comp measurable_snd)))

lemma reducedStep_measurable (c : Choice p) (f : Functions p)
    (hg : ∀ i, Measurable (gradient (f i))) :
    Measurable (Function.uncurry (reducedStep p c f)) := by
  have hx : Measurable (fun z : Reduced p × Sample p =>
      z.1.1 - stepSize p c • estimate p c (lift p f z.1)) :=
    (measurable_fst.comp measurable_fst).sub
      ((measurable_const (a := stepSize p c)).smul ((estimate_measurable c f).comp measurable_fst))
  have hcodes : Measurable (fun z : Reduced p × Sample p =>
      (nextIterate p c f (lift p f z.1) z.2).localCode) := by
    apply Measurable.of_eval
    intro i
    have hcode : Measurable (fun z : Reduced p × Sample p => z.1.2 i) :=
      (measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)
    have hh : Measurable (fun z : Reduced p × Sample p => gradient (f i) z.1.1) :=
      (hg i).comp (measurable_fst.comp measurable_fst)
    have hnext := (hg i).comp hx
    have hgcode := (DashaQuantization.measurable_reconstruct p.d (spacing p c)).comp hcode
    have hu := (hnext.sub hh).sub ((measurable_const (a := momentum p c)).smul (hgcode.sub hh))
    have hc := (DashaCompression.measurable_compressedIndex_joint c.block c.precision (spacing p c)).comp
      (hu.prodMk ((measurable_pi_apply i).comp measurable_snd))
    exact hcode.add hc
  exact hx.prodMk hcodes

lemma localEnergy_measurable (c : Choice p) (f : Functions p)
    (hg : ∀ i, Measurable (gradient (f i))) : Measurable (localEnergy c f) := by
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro i _
  exact (((DashaQuantization.measurable_reconstruct p.d (spacing p c)).comp
    ((measurable_pi_apply i).comp measurable_snd)).sub ((hg i).comp measurable_fst)).norm.pow_const 2

lemma aggregateEnergy_measurable (c : Choice p) (f : Functions p)
    (hg : Measurable (gradient (objective p f))) : Measurable (aggregateEnergy c f) :=
  ((estimate_measurable c f).sub (hg.comp measurable_fst)).norm.pow_const 2

lemma potential_measurable (c : Choice p) (f : Functions p) (lower : ℝ)
    (hf : Measurable (objective p f)) (hg : Measurable (gradient (objective p f)))
    (hi : ∀ i, Measurable (gradient (f i))) : Measurable (potential c f lower) :=
  (((hf.comp measurable_fst).sub measurable_const).add
    (measurable_const.mul (aggregateEnergy_measurable c f hg))).add
      (measurable_const.mul (localEnergy_measurable c f hi))

lemma initialReduced_measurable (c : Choice p) (f : Functions p) :
    Measurable (initialReduced p c f) := by
  apply measurable_const.prodMk
  apply Measurable.of_eval
  intro i
  exact (DashaQuantization.measurable_indices p.d false (spacing p c)).comp
    (measurable_const.prodMk (measurable_snd.comp (measurable_pi_apply i)))

lemma sparseInitialReduced_measurable (c initializer : Choice p) (f : Functions p) :
    Measurable (fun seed => reduce p (sparseInitialIterate p c initializer f seed)) := by
  apply measurable_const.prodMk
  apply Measurable.of_eval
  intro i
  exact (DashaCompression.measurable_compressedIndex_joint initializer.block initializer.precision
    (spacing p c)).comp (measurable_const.prodMk (measurable_pi_apply i))

lemma reduced_trajectory_measurable (c : Choice p) (f : Functions p)
    (hg : ∀ i, Measurable (gradient (f i))) (k : ℕ) :
    Measurable (fun seed : ℕ → Sample p => reduce p (trajectory p c f seed k)) := by
  induction k with
  | zero => exact (initialReduced_measurable c f).comp (measurable_pi_apply 0)
  | succ k ih =>
    have he : (fun seed : ℕ → Sample p => reduce p (trajectory p c f seed (k + 1))) =
        fun seed => reducedStep p c f (reduce p (trajectory p c f seed k)) (seed (k + 1)) := by
      funext seed
      exact (reduced_trajectory_step c f seed k).symm
    rw [he]
    exact (reducedStep_measurable c f hg).comp (ih.prodMk (measurable_pi_apply (k + 1)))

lemma output_measurable (c : Choice p) (f : Functions p)
    (hg : ∀ i, Measurable (gradient (f i))) : Measurable (output p c f) :=
  measurable_from_prod_countable_right (fun i =>
    measurable_fst.comp (reduced_trajectory_measurable c f hg i.val))

lemma reduced_sparse_trajectory_measurable (c initializer : Choice p) (f : Functions p)
    (hg : ∀ i, Measurable (gradient (f i))) (k : ℕ) :
    Measurable (fun seed : ℕ → Sample p => reduce p (sparseTrajectory p c initializer f seed k)) := by
  induction k with
  | zero => exact (sparseInitialReduced_measurable c initializer f).comp (measurable_pi_apply 0)
  | succ k ih =>
    have he : (fun seed : ℕ → Sample p => reduce p (sparseTrajectory p c initializer f seed (k + 1))) =
        fun seed => reducedStep p c f (reduce p (sparseTrajectory p c initializer f seed k)) (seed (k + 1)) := by
      funext seed
      exact (reduced_sparse_trajectory_step c initializer f seed k).symm
    rw [he]
    exact (reducedStep_measurable c f hg).comp (ih.prodMk (measurable_pi_apply (k + 1)))

lemma sparse_output_measurable (c initializer : Choice p) (f : Functions p)
    (hg : ∀ i, Measurable (gradient (f i))) : Measurable (sparseOutput p c initializer f) :=
  measurable_from_prod_countable_right (fun i =>
    measurable_fst.comp (reduced_sparse_trajectory_measurable c initializer f hg i.val))

end LongTails.Proofs.DashaScalingMeasurability
