import LongTails.Proofs.GeneralCovarianceReverseFisherDescent
import LongTails.Proofs.GeneralCovarianceReverseFisherRate
import LongTails.Algorithms.GeneralCovarianceReverseFisherGD

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralCovarianceReverseFisherStep

open LongTails.Setups.GeneralCovarianceReverseFisher
open LongTails.Algorithms.GeneralCovarianceReverseFisherGD
open LongTails.Proofs.GeneralCovarianceReverseFisherScore
open LongTails.Proofs.GeneralCovarianceReverseFisherDerivative
open LongTails.Proofs.GeneralCovarianceReverseFisherParts
open LongTails.Proofs.GeneralCovarianceReverseFisherBilinear
open LongTails.Proofs.GeneralCovarianceReverseFisherLoss
open LongTails.Proofs.GeneralCovarianceReverseFisherDescent

variable {p : Params}

lemma lower_bound_symm (M : Model p) (hs : spectralBounds p M) (hlo : 0 < p.lower) (w : Space p) :
    p.lower * ‖M.covarianceRoot.symm w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  set A := M.covarianceRoot
  set B := ContinuousLinearMap.adjoint (A : Space p →L[ℝ] Space p)
  have hB : B (precision A w) = A.symm w := by
    apply ext_inner_right ℝ
    intro z
    rw [ContinuousLinearMap.adjoint_inner_left, precision_inner]
    simp
  have h1 := (hs (precision A w)).1
  rw [hB] at h1
  have h2 : ‖A.symm w‖ ^ 2 ≤ ‖precision A w‖ * ‖w‖ := by
    have e : ‖A.symm w‖ ^ 2 = ⟪precision A w, w⟫ := by
      rw [precision_inner, real_inner_self_eq_norm_sq]
    rw [e]
    exact real_inner_le_norm _ _
  have hq := norm_nonneg (A.symm w)
  refine sq_le_of_quartic hlo hq (sq_nonneg _) ?_
  have h3 : ‖A.symm w‖ ^ 2 * ‖A.symm w‖ ^ 2 ≤ (‖precision A w‖ * ‖w‖) * (‖precision A w‖ * ‖w‖) :=
    mul_self_le_mul_self (sq_nonneg _) h2
  have h4 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖w‖)
  nlinarith

lemma upper_bound_symm (M : Model p) (hs : spectralBounds p M) (hhi : 0 < p.upper) (w : Space p) :
    ‖w‖ ^ 2 ≤ p.upper * ‖M.covarianceRoot.symm w‖ ^ 2 := by
  set A := M.covarianceRoot
  set B := ContinuousLinearMap.adjoint (A : Space p →L[ℝ] Space p)
  have h1 : ‖w‖ ^ 2 ≤ ‖A.symm w‖ * ‖B w‖ := by
    have : ‖w‖ ^ 2 = ⟪A.symm w, B w⟫ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
      simp
    rw [this]
    exact real_inner_le_norm _ _
  have h2 := (hs w).2
  have hw := norm_nonneg w
  have h3 : ‖w‖ ^ 2 * ‖w‖ ^ 2 ≤ (‖A.symm w‖ * ‖B w‖) * (‖A.symm w‖ * ‖B w‖) :=
    mul_self_le_mul_self (sq_nonneg _) h1
  have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg ‖A.symm w‖)
  have := sq_le_of_quartic one_pos hw (by positivity : 0 ≤ p.upper * ‖A.symm w‖ ^ 2) (by nlinarith)
  simpa using this

instance (p : Params) : NeZero (p.dimension : ℕ) := ⟨p.dimension.ne_zero⟩

instance (p : Params) : Nontrivial (Space p) := by
  unfold Space; infer_instance

lemma gd_step (M : Model p) (hs : spectralBounds p M) (hlo : 0 < p.lower) (hlh : p.lower ≤ p.upper)
    (θ : Means p) :
    vnorm M.covarianceRoot (fun i => (θ - stepSize p • gradient (loss M) θ) i - M.target) ≤
      vnorm M.covarianceRoot (fun i => θ i - M.target) -
        p.lower ^ 2 / ((1 + 8 * Real.log p.components) * p.upper ^ 2) *
          min (vnorm M.covarianceRoot (fun i => θ i - M.target) / 2)
            (vnorm M.covarianceRoot (fun i => θ i - M.target) ^ 2 /
              (4 * (p.components * (min p.components (Module.finrank ℝ (Space p)) : ℕ)))) := by
  set A := M.covarianceRoot with hA
  set t := M.target with ht
  set G := gradient (loss M) θ
  set U : Fin p.components → Space p := fun i => θ i - t
  set Gf : Fin p.components → Space p := fun i => G i
  set c₀ := (1 + 8 * Real.log p.components) / p.lower ^ 2
  have hhi : 0 < p.upper := lt_of_lt_of_le hlo hlh
  have hl := lower_bound_symm M hs hlo
  have hh := upper_bound_symm M hs hhi
  have hn1 : (1 : ℝ) ≤ p.components := by exact_mod_cast p.components.pos
  have hlogn : 0 ≤ Real.log p.components := Real.log_nonneg hn1
  have hc0 : 0 < c₀ := by positivity
  have hn : (0 : ℝ) < p.components := by linarith
  have hG : ∀ Y : Fin p.components → Space p,
      ∑ i, ⟪G i, precision A (Y i)⟫ = 2 / p.components * beta A θ Y U := by
    intro Y
    have h := inner_gradient_loss M θ (WithLp.toLp 2 (fun i => precision A (Y i)))
    rw [PiLp.inner_apply, ← hA, ← ht] at h
    rw [h]
    have hp : ∀ x, pairing A t θ x (WithLp.toLp 2 (fun i => precision A (Y i))) =
        2 * (total A (fun l => θ l) x * bpt A θ x Y U) := fun x => by
      rw [pairing_eq A θ x t Y]; ring
    simp_rw [hp]
    unfold beta
    rw [integral_const_mul]
    ring
  have hV1 : vnorm A (fun i => (θ - stepSize p • G) i - t) =
      vnorm A U - 2 * stepSize p * ∑ i, ⟪G i, precision A (U i)⟫ +
        stepSize p ^ 2 * ∑ i, ⟪G i, precision A (G i)⟫ := by
    unfold vnorm
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have e : (θ - stepSize p • G) i - t = U i - stepSize p • G i := by
      simp only [PiLp.sub_apply, PiLp.smul_apply, U]; abel
    dsimp only
    rw [e, map_sub, map_smul, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs, inner_precision, inner_precision, real_inner_self_eq_norm_sq,
      real_inner_comm (A.symm (U i))]
    ring
  have hVG : ∑ i, ⟪G i, precision A (G i)⟫ = vnorm A Gf := by
    unfold vnorm
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [inner_precision, real_inner_self_eq_norm_sq]
  have hGG : beta A θ Gf Gf ≤ c₀ * vnorm A Gf := by
    have := beta_self_le A θ hlo hl Gf
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have hγ : stepSize p = p.components / (2 * c₀) := by
    unfold stepSize
    simp only [c₀]
    field_simp
  have hs0 : 0 < (p.components : ℝ) / (2 * c₀) := by positivity
  have hamgm := beta_amgm A θ hlo hl Gf U hs0
  have hdesc : vnorm A (fun i => (θ - stepSize p • G) i - t) ≤
      vnorm A U - beta A θ U U / c₀ :=
    descent_algebra (bGG := beta A θ Gf Gf) hn hc0 hγ hV1 (hG U) (hG Gf)
      (by rw [hVG]; exact hGG) hamgm
  have hlow := beta_lower A θ hlo hl hhi hh t
  have hfin : p.lower ^ 2 / ((1 + 8 * Real.log p.components) * p.upper ^ 2) *
      min (vnorm A U / 2) (vnorm A U ^ 2 /
        (4 * (p.components * (min p.components (Module.finrank ℝ (Space p)) : ℕ)))) ≤
      beta A θ U U / c₀ := by
    have e : p.lower ^ 2 / ((1 + 8 * Real.log p.components) * p.upper ^ 2) =
        1 / (c₀ * p.upper ^ 2) := by
      simp only [c₀]; field_simp
    rw [e, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hc0]
    nlinarith [hlow]
  linarith

end LongTails.Proofs.GeneralCovarianceReverseFisherStep
