import LongTails.Algorithms.PLMinimaxCubic
import LongTails.Proofs.PLMinimaxGeometry
import LongTails.Proofs.PLMinimaxOracleGeometry
import LongTails.Proofs.TwoSidedPLEnvelope

open Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.PLMinimax

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma residualModel_continuous (v : E) (A : E →L[ℝ] E) (ρ : ℝ) :
    Continuous (residualModel v A ρ) := by
  unfold residualModel
  fun_prop

lemma residualModel_exists_min [ProperSpace E] (v : E) (A : E →L[ℝ] E)
    {ρ : ℝ} (hρ : 0 < ρ) : ∃ d, ∀ s, residualModel v A ρ d ≤ residualModel v A ρ s := by
  apply TwoSidedPL.exists_min_of_growth (residualModel v A ρ)
    (residualModel_continuous v A ρ).lowerSemicontinuous 0 (1 + 2 * ‖v‖ / ρ)
  intro d hd
  simp only [sub_zero] at hd
  have hdiv : 0 ≤ 2 * ‖v‖ / ρ := by positivity
  have hn : 1 < ‖d‖ := by linarith
  have hmul : 2 * ‖v‖ < ρ * ‖d‖ := by
    have hh : 2 * ‖v‖ / ρ < ‖d‖ := by linarith
    have := (div_lt_iff₀ hρ).mp hh
    nlinarith
  simp only [residualModel, map_zero, add_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero]
  nlinarith [norm_nonneg (v + A d), mul_nonneg hρ.le (show 0 ≤ ‖d‖ ^ 2 - ‖d‖ by nlinarith)]

lemma residualNewtonStep_min [ProperSpace E] (v : E) (A : E →L[ℝ] E)
    {ρ : ℝ} (hρ : 0 < ρ) (s : E) :
    residualModel v A ρ (residualNewtonStep v A ρ) ≤ residualModel v A ρ s :=
  Classical.epsilon_spec (residualModel_exists_min v A hρ) s

lemma residualModel_step {F : E → E} {A : E →L[ℝ] E} {ρ : ℝ} {w p d : E}
    (hρ : 0 < ρ) (hp : F p = 0)
    (htaylor : ∀ s, ‖F (w + s) - (F w + A s)‖ ≤ ρ / 2 * ‖s‖ ^ 2)
    (hmin : ∀ s, residualModel (F w) A ρ d ≤ residualModel (F w) A ρ s) :
    ‖F (w + d)‖ ≤ ρ * ‖p - w‖ ^ 2 ∧ ‖d‖ ^ 2 ≤ 2 * ‖p - w‖ ^ 2 := by
  have ht := htaylor (p - w)
  rw [add_sub_cancel, hp, zero_sub, norm_neg] at ht
  have hm := hmin (p - w)
  unfold residualModel at hm
  have hb : ‖F w + A d‖ + ρ / 2 * ‖d‖ ^ 2 ≤ ρ * ‖p - w‖ ^ 2 := by linarith
  constructor
  · have htri := norm_add_le (F (w + d) - (F w + A d)) (F w + A d)
    rw [sub_add_cancel] at htri
    linarith [htaylor d]
  · have := norm_nonneg (F w + A d)
    nlinarith

lemma residualNewtonStep_bound [ProperSpace E] {F : E → E} {A : E →L[ℝ] E}
    {ρ : ℝ} {w p : E} (hρ : 0 < ρ) (hp : F p = 0)
    (htaylor : ∀ s, ‖F (w + s) - (F w + A s)‖ ≤ ρ / 2 * ‖s‖ ^ 2) :
    ‖F (w + residualNewtonStep (F w) A ρ)‖ ≤ ρ * ‖p - w‖ ^ 2 ∧
      ‖residualNewtonStep (F w) A ρ‖ ^ 2 ≤ 2 * ‖p - w‖ ^ 2 :=
  residualModel_step hρ hp htaylor (residualNewtonStep_min (F w) A hρ)

lemma residualNewtonStep_local [ProperSpace E] {F : E → E} {A : E →L[ℝ] E}
    {ρ c r : ℝ} {w p : E} (hρ : 0 < ρ) (hc : 0 < c) (hr : 0 ≤ r)
    (hsmall : ρ * r ≤ c / 2) (hp : F p = 0) (hd : ‖p - w‖ ≤ r)
    (heb : ∀ x, ∃ q, F q = 0 ∧ c * ‖q - x‖ ≤ ‖F x‖)
    (htaylor : ∀ s, ‖F (w + s) - (F w + A s)‖ ≤ ρ / 2 * ‖s‖ ^ 2) :
    ‖F (w + residualNewtonStep (F w) A ρ)‖ ≤ ρ * r ^ 2 ∧
      ∃ q, F q = 0 ∧ ‖q - (w + residualNewtonStep (F w) A ρ)‖ ≤ r / 2 := by
  have hh := (residualNewtonStep_bound hρ hp htaylor).1
  have hd2 : ‖p - w‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg (p - w)]
  have hn : ‖F (w + residualNewtonStep (F w) A ρ)‖ ≤ ρ * r ^ 2 :=
    hh.trans (mul_le_mul_of_nonneg_left hd2 hρ.le)
  obtain ⟨q, hq, hqe⟩ := heb (w + residualNewtonStep (F w) A ρ)
  refine ⟨hn, q, hq, ?_⟩
  have hs := mul_le_mul_of_nonneg_right hsmall hr
  nlinarith

lemma residualNewtonSequence_error [ProperSpace E] {F : E → E} {J : E → E →L[ℝ] E}
    {ρ c r : ℝ} (hρ : 0 < ρ) (hc : 0 < c) (hr : 0 ≤ r) (hsmall : ρ * r ≤ c / 2)
    (u : ℕ → E) (hu : ∀ n, u (n + 1) = u n + residualNewtonStep (F (u n)) (J (u n)) ρ)
    (hstart : ∃ p, F p = 0 ∧ ‖p - u 0‖ ≤ r)
    (heb : ∀ x, ∃ q, F q = 0 ∧ c * ‖q - x‖ ≤ ‖F x‖)
    (htaylor : ∀ n s, ‖F (u n + s) - (F (u n) + J (u n) s)‖ ≤ ρ / 2 * ‖s‖ ^ 2) :
    (∀ n, ∃ q, F q = 0 ∧ ‖q - u n‖ ≤ r * (1 / 2 : ℝ) ^ n) ∧
      ∀ n, ‖F (u (n + 1))‖ ≤ ρ * (r * (1 / 2 : ℝ) ^ n) ^ 2 := by
  have hsmall' : ∀ n, ρ * (r * (1 / 2 : ℝ) ^ n) ≤ c / 2 := by
    intro n
    have hp : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg hρ.le hr)
    nlinarith
  have hall : ∀ n, ∃ q, F q = 0 ∧ ‖q - u n‖ ≤ r * (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => simpa using hstart
    | succ n ih =>
      obtain ⟨p, hp, hd⟩ := ih
      obtain ⟨_, q, hq, hdist⟩ := residualNewtonStep_local hρ hc
        (mul_nonneg hr (pow_nonneg (by norm_num) n)) (hsmall' n) hp hd heb (htaylor n)
      refine ⟨q, hq, ?_⟩
      rw [hu n, pow_succ]
      convert hdist using 1
      ring
  refine ⟨hall, fun n => ?_⟩
  obtain ⟨p, hp, hd⟩ := hall n
  rw [hu n]
  exact (residualNewtonStep_local hρ hc (mul_nonneg hr (pow_nonneg (by norm_num) n))
    (hsmall' n) hp hd heb (htaylor n)).1

lemma setup_refinement
    {p : LongTails.Setups.NonconvexPLSecondOrder.Params}
    {f : LongTails.Setups.NonconvexPLSecondOrder.Space p → ℝ} {oracle}
    (hv : LongTails.Setups.NonconvexPLSecondOrder.spec.valid p)
    (hf : LongTails.Setups.NonconvexPLSecondOrder.spec.admissible p f oracle)
    (z : p.E) (u : ℕ → LongTails.Setups.NonconvexPLSecondOrder.Space p)
    (hu : ∀ n, u (n + 1) = u n + residualNewtonStep
      (regularizedGradient (gradient f) p.L z (u n))
      (regularizedHessian (fderiv ℝ (gradient f) (u n)) p.L) p.ρ)
    {r : ℝ} (hr : 0 ≤ r) (hsmall : p.ρ * r ≤ p.μ / 16)
    (hstart : ∃ q, regularizedGradient (gradient f) p.L z q = 0 ∧ ‖q - u 0‖ ≤ r) :
    (∀ n, ∃ q, regularizedGradient (gradient f) p.L z q = 0 ∧
      ‖q - u n‖ ≤ r * (1 / 2 : ℝ) ^ n) ∧
      ∀ n, ‖regularizedGradient (gradient f) p.L z (u (n + 1))‖ ≤
        p.ρ * (r * (1 / 2 : ℝ) ^ n) ^ 2 := by
  have H := setup_hyp hv hf
  have hc : 0 < p.μ / 8 := div_pos hv.1 (by norm_num)
  have hsmall' : p.ρ * r ≤ (p.μ / 8) / 2 := by convert hsmall using 1; ring
  refine residualNewtonSequence_error
    (F := regularizedGradient (gradient f) p.L z)
    (J := fun w => regularizedHessian (fderiv ℝ (gradient f) w) p.L)
    hv.2.2.1 hc hr hsmall' u hu hstart (fun w => regularized_root_error H z w) ?_
  intro n s
  exact regularizedGradient_residual_taylor (fun w => (hf.2.1 w).hasFDerivAt)
    hf.2.2.2.1 p.L z (u n) s

end OracleTemplate.PLMinimax
