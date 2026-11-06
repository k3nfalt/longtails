import LongTails.Algorithms.SpikedSoftCut
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpikedSoftCutCoordinates

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCut

lemma join_head_tail (q : Params) (x : Space q) : join q (head q x) (tail q x) = x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [join, head, tail]

lemma join_sub (q : Params) (a b : ℝ) (x y : InnerSpace q) :
    join q a x - join q b y = join q (a - b) (x - y) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [join]

lemma inner_join (q : Params) (x : Space q) (a : ℝ) (y : InnerSpace q) :
    ⟪x, join q a y⟫ = head q x * a + ⟪tail q x, y⟫ := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, join, head, tail, mul_comm]

lemma norm_join_sq (q : Params) (a : ℝ) (y : InnerSpace q) :
    ‖join q a y‖ ^ 2 = a ^ 2 + ‖y‖ ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, join]

lemma norm_join_zero (q : Params) (y : InnerSpace q) : ‖join q 0 y‖ = ‖y‖ := by
  have h := norm_join_sq q 0 y
  nlinarith [norm_nonneg (join q 0 y), norm_nonneg y]

lemma norm_join_scalar (q : Params) (a : ℝ) : ‖join q a 0‖ = |a| := by
  have h := norm_join_sq q a 0
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  nlinarith [norm_nonneg (join q a 0), abs_nonneg a, sq_abs a]

lemma norm_tail_le (q : Params) (x : Space q) : ‖tail q x‖ ≤ ‖x‖ := by
  have h := norm_join_sq q (head q x) (tail q x)
  rw [join_head_tail] at h
  nlinarith [sq_nonneg (head q x), norm_nonneg x, norm_nonneg (tail q x)]

lemma abs_head_le (q : Params) (x : Space q) : |head q x| ≤ ‖x‖ := by
  exact (Real.norm_eq_abs _).symm ▸ PiLp.norm_apply_le x 0

lemma proxy_tail (q : Params) (u : InnerSpace q) :
    varianceProxy q (join q 0 u) = q.vRest * ‖u‖ ^ 2 := by
  rw [varianceProxy, norm_join_zero]
  simp [join]

lemma proxy_head (q : Params) (a : ℝ) :
    varianceProxy q (join q a 0) = q.vTop * a ^ 2 := by
  rw [varianceProxy, norm_join_scalar, sq_abs]
  change q.vRest * a ^ 2 + (q.vTop - q.vRest) * a ^ 2 = q.vTop * a ^ 2
  ring

lemma continuous_join (q : Params) : Continuous (fun z : ℝ × InnerSpace q => join q z.1 z.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Continuous (fun z : ℝ × InnerSpace q => z.1)
    exact continuous_fst
  · change Continuous (fun z : ℝ × InnerSpace q => z.2 j)
    fun_prop

lemma continuous_tail (q : Params) : Continuous (tail q) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  exact PiLp.continuous_apply 2 _ i.succ

lemma continuous_head (q : Params) : Continuous (head q) := PiLp.continuous_apply 2 _ 0

lemma tail_sub (q : Params) (x y : Space q) : tail q (x-y) = tail q x - tail q y := by
  ext i
  rfl

lemma tail_direction_exp (q : Params) (p : MeasureTheory.Measure q.Ω)
    [MeasureTheory.IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsSubGaussianSubgradient q p f v g)
    (x : Space q) (u : InnerSpace q) (t : ℝ) :
    MeasureTheory.Integrable (fun ω => Real.exp (t * ⟪tail q (g x ω - v x), u⟫)) p ∧
    (∫ ω, Real.exp (t * ⟪tail q (g x ω - v x), u⟫) ∂p) ≤
      Real.exp (t ^ 2 * (q.vRest * ‖u‖ ^ 2) / 2) := by
  have he (ω : q.Ω) : ⟪g x ω - v x, join q 0 u⟫ = ⟪tail q (g x ω - v x), u⟫ := by
    rw [inner_join]; simp
  constructor
  · simpa only [he] using hg.exponential_integrable x (join q 0 u) t
  · simpa only [he, proxy_tail] using hg.exponential_bound x (join q 0 u) t

lemma head_direction_exp (q : Params) (p : Measure q.Ω)
    [IsProbabilityMeasure p] (f : Space q → ℝ) (v : Space q → Space q)
    (g : Space q → q.Ω → Space q) (hg : IsSubGaussianSubgradient q p f v g)
    (x : Space q) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * head q (g x ω - v x))) p ∧
    (∫ ω, Real.exp (t * head q (g x ω - v x)) ∂p) ≤
      Real.exp (t ^ 2 * q.vTop / 2) := by
  have he (ω : q.Ω) : ⟪g x ω - v x, join q 1 0⟫ = head q (g x ω - v x) := by
    rw [inner_join]; simp
  constructor
  · simpa only [he] using hg.exponential_integrable x (join q 1 0) t
  · simpa only [he, proxy_head, one_pow, mul_one] using hg.exponential_bound x (join q 1 0) t

lemma measurable_mean (q : Params) (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsSubGaussianSubgradient q p f v g) : Measurable v := by
  have hm : Measurable (fun x => ∫ ω, g x ω ∂p) :=
    hg.measurable.stronglyMeasurable.integral_prod_right.measurable
  simpa only [hg.unbiased] using hm

lemma measurable_tail_error (q : Params) (p : Measure q.Ω) [IsProbabilityMeasure p]
    (f : Space q → ℝ) (v : Space q → Space q) (g : Space q → q.Ω → Space q)
    (hg : IsSubGaussianSubgradient q p f v g) :
    Measurable (fun z : Space q × q.Ω => tail q (g z.1 z.2 - v z.1)) := by
  exact (continuous_tail q).measurable.comp
    (hg.measurable.sub ((measurable_mean q p f v g hg).comp measurable_fst))

lemma subgradient_norm_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (G : ℝ) (hG : 0 ≤ G)
    (hlip : ∀ x y, |f x - f y| ≤ G * ‖x - y‖)
    (x v : E) (hsupport : ∀ y, ⟪v, y - x⟫ ≤ f y - f x) : ‖v‖ ≤ G := by
  have hs := hsupport (x + v)
  have hl := hlip (x + v) x
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq] at hs
  simp only [add_sub_cancel_left] at hl
  have hb := hs.trans ((le_abs_self _).trans hl)
  nlinarith [norm_nonneg v]

end LongTails.Proofs.SpikedSoftCutCoordinates
