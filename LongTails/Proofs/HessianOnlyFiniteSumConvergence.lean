import LongTails.Proofs.AcceleratedQuarticProbability
import LongTails.Proofs.HessianOnlyFiniteSumTuning

set_option synthInstance.maxSize 256

namespace LongTails.Proofs.HessianOnlyFiniteSumConvergence

open LongTails.Setups.FiniteSumThirdSmoothConvex
open LongTails.Setups.FiniteSumSmoothAndConvex (objective)
open LongTails.Algorithms.HessianOnlyFiniteSumThirdSmooth
open LongTails.Proofs.HessianOnlyFiniteSumTuning
open LongTails.Proofs.AcceleratedQuarticProbability
open LongTails.Algorithms.QuarticProximalTrial
open OracleTemplate OracleTemplate.QueryPlan
open scoped BigOperators Classical

lemma plan_failure (p : Params) (hp : spec.valid p) (F : Problem p)
    (hf : ∀ i, ContDiff ℝ 3 (F.component i)) (hc : ∀ i, ConvexOn ℝ Set.univ (F.component i))
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (F.component i))) x -
      fderiv ℝ (fderiv ℝ (gradient (F.component i))) y‖ ≤ p.L * ‖x - y‖)
    (hmin : ∀ x, objective F.component F.xstar ≤ objective F.component x)
    (hx0 : ‖p.x0 - F.xstar‖ ≤ p.R)
    (hG : ‖gradient (objective F.component) p.x0‖ ≤ p.G)
    (hH : ‖fderiv ℝ (gradient (objective F.component)) p.x0‖ ≤ p.H) :
    (𝔼 seed : Seeds p,
      (if ¬objective F.component (eval (fun q : Fin p.n × p.E =>
        (gradient (F.component q.1) q.2, fderiv ℝ (gradient (F.component q.1)) q.2)) (plan p seed)) -
          objective F.component F.xstar ≤ p.ε then (1 : ℝ) else 0)) ≤ 1 / 4 := by
  have hs := scale_bounds p hp
  have hM := padding_bounds p hp
  have hγ := regularization_bounds p hp
  have hN := iterations_bounds p hp
  have hR := hp.2.1
  have hε := hp.2.2.1
  have hLp : p.L ≤ padding p := by unfold padding; exact le_add_of_nonneg_right (by positivity)
  have hT' : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (F.component i))) x -
      fderiv ℝ (fderiv ℝ (gradient (F.component i))) y‖ ≤ padding p * ‖x - y‖ := by
    intro i x y
    exact (hT i x y).trans (mul_le_mul_of_nonneg_right hLp (norm_nonneg _))
  let oracle := fun q : Fin p.n × p.E => (gradient (F.component q.1) q.2, fderiv ℝ (gradient (F.component q.1)) q.2)
  have hbase := FiniteSumThirdSmoothGeometry.objective_contDiff F.component hf
  have hcbase := OracleTemplate.FiniteSum.objective_convex hc
  have hbad := run_good_probability (hbase.differentiable (by norm_num)) hcbase hε hR hs.1 hγ.1
    p.x0 F.xstar hx0 hmin oracle (iterations p) hN.1 hN.2.1 (fun c hcenter =>
      QuarticTrialGuarantee.trial_guarantee F.component hf hc hε hR hs.1 hM.2.1 hM.2.2
        hγ.2.1 hγ.2.2.1 hγ.2.2.2.1 hγ.2.2.2.2 hT' p.x0 F.xstar c hmin hx0 hcenter
        (hG.trans hs.2.2.2.1) (hH.trans hs.2.2.2.2) (iterations p) hN.1 hs.2.1 hN.2.1)
  have hout := output_failure_bound hcbase hε hγ.1 hR p.x0 F.xstar hx0 hmin hN.2.2
    (fun seed : Seeds p => eval oracle (LongTails.Algorithms.AcceleratedQuarticNewton.run
      p.ε p.R (scale p) (padding p + 6 * regularization p) (regularization p) p.x0 (iterations p) seed .initial)) hbad
  unfold plan calls
  simp only [eval_map]
  exact hout

end LongTails.Proofs.HessianOnlyFiniteSumConvergence
