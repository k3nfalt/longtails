import LongTails.Setups.StochasticSmoothNonconvex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

open MeasureTheory Set InnerProductSpace
open scoped RealInnerProductSpace NNReal

namespace OracleTemplate.StochasticNonconvex

open LongTails.Setups.StochasticSmoothNonconvex

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma smooth_bound {f : E → ℝ} {L : ℝ}
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  let d := y - x
  let F := fun t : ℝ => f (x + t • d)
  let B := fun t : ℝ => f x + t * ⟪gradient f x, d⟫ + t ^ 2 * (L / 2 * ‖d‖ ^ 2)
  have hF (t : ℝ) : HasDerivAt F ⟪gradient f (x + t • d), d⟫ t := by
    have h := (hg _).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const d |>.const_add x)
    simp only [id_eq, one_smul, toDual_apply_apply] at h
    exact h
  have hB (t : ℝ) : HasDerivAt B (⟪gradient f x, d⟫ + L * ‖d‖ ^ 2 * t) t := by
    convert ((hasDerivAt_id t).mul_const ⟪gradient f x, d⟫ |>.const_add (f x)).add
      (((hasDerivAt_id t).pow 2).mul_const (L / 2 * ‖d‖ ^ 2)) using 1
    · funext s
      dsimp [B]
    · dsimp [B]
      ring
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1,
      ⟪gradient f (x + t • d), d⟫ ≤ ⟪gradient f x, d⟫ + L * ‖d‖ ^ 2 * t := by
    intro t ht
    have h := (real_inner_le_norm (gradient f (x + t • d) - gradient f x) d).trans
      (mul_le_mul_of_nonneg_right (hlip (x + t • d) x) (norm_nonneg d))
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht.1, inner_sub_left] at h
    nlinarith
  have h := image_le_of_deriv_right_le_deriv_boundary
    (fun t _ => (hF t).continuousAt.continuousWithinAt) (fun t _ => (hF t).hasDerivWithinAt)
    (show F 0 ≤ B 0 by simp [F, B])
    (fun t _ => (hB t).continuousAt.continuousWithinAt) (fun t _ => (hB t).hasDerivWithinAt)
    hderiv (show (1 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
  simpa [F, B, d] using h

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]

omit [SecondCountableTopology E] in
lemma gradient_measurable {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    Measurable (gradient f) :=
  (lipschitzWith_iff_norm_sub_le.mpr (show ∀ x y,
    ‖gradient f x - gradient f y‖ ≤ (⟨L, hL⟩ : ℝ≥0) * ‖x - y‖ from hlip)).continuous.measurable

lemma expected_step {f : E → ℝ} {g : E → Ω → E} {p : Measure Ω}
    [IsProbabilityMeasure p] {L σ η lower : ℝ}
    (hL : 0 < L) (hη : 0 ≤ η) (hηL : η * L ≤ 1)
    (hg : ∀ x, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hb : ∀ x, lower ≤ f x) (ho : StochasticGradient E Ω p f g σ) (x : E) :
    Integrable (fun ω => f (x - η • g x ω) - lower) p ∧
    (∫ ω, f (x - η • g x ω) - lower ∂p) + η / 2 * ‖gradient f x‖ ^ 2 ≤
      f x - lower + L * η ^ 2 / 2 * σ ^ 2 := by
  let v := gradient f x
  let noise := fun ω => g x ω - v
  have hn : Integrable noise p := (ho.integrable x).sub (integrable_const _)
  have hz : (∫ ω, noise ω ∂p) = 0 := by
    simp [noise, v, integral_sub (ho.integrable x) (integrable_const _), ho.unbiased]
  have hnorm : (fun ω => ‖g x ω‖ ^ 2) =
      fun ω => ‖v‖ ^ 2 + 2 * ⟪v, noise ω⟫ + ‖noise ω‖ ^ 2 := by
    funext ω
    rw [← norm_add_sq_real]
    simp [noise]
  have hgi : Integrable (fun ω => ‖g x ω‖ ^ 2) p := by
    rw [hnorm]
    exact ((integrable_const _).add ((hn.const_inner v).const_mul 2)).add (ho.variance_integrable x)
  have hg2 : (∫ ω, ‖g x ω‖ ^ 2 ∂p) ≤ ‖v‖ ^ 2 + σ ^ 2 := by
    have hn2 : Integrable (fun ω => ‖noise ω‖ ^ 2) p := ho.variance_integrable x
    have hn1 : Integrable (fun ω => ‖v‖ ^ 2 + 2 * ⟪v, noise ω⟫) p :=
      (integrable_const _).add ((hn.const_inner v).const_mul 2)
    rw [hnorm, integral_add hn1 hn2, integral_add (integrable_const (‖v‖ ^ 2)) ((hn.const_inner v).const_mul 2),
      integral_const_mul, integral_inner hn, hz]
    simpa [noise, v] using add_le_add_left (ho.variance x) (‖v‖ ^ 2)
  let B := fun ω => f x - lower - η * ⟪v, g x ω⟫ + L * η ^ 2 / 2 * ‖g x ω‖ ^ 2
  have hBi : Integrable B p :=
    ((integrable_const _).sub (((ho.integrable x).const_inner v).const_mul η)).add
      (hgi.const_mul _)
  have hupper (ω) : f (x - η • g x ω) - lower ≤ B ω := by
    have h := smooth_bound hg hlip x (x - η • g x ω)
    simp only [sub_sub_cancel_left, inner_neg_right, inner_smul_right,
      norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
    dsimp [B, v]
    nlinarith
  have hf : Measurable f := (continuous_iff_continuousAt.mpr (fun x => (hg x).continuousAt)).measurable
  have hFi : Integrable (fun ω => f (x - η • g x ω) - lower) p :=
    hBi.mono_nonneg
      (((hf.comp (measurable_const.sub (ho.measurable.of_uncurry_left.const_smul η))).sub_const lower).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun ω => sub_nonneg.mpr (hb _)))
      (Filter.Eventually.of_forall hupper)
  refine ⟨hFi, ?_⟩
  have hi := integral_mono hFi hBi hupper
  have hBvalue : (∫ ω, B ω ∂p) =
      f x - lower - η * ‖v‖ ^ 2 + L * η ^ 2 / 2 * (∫ ω, ‖g x ω‖ ^ 2 ∂p) := by
    dsimp [B]
    have hB1 : Integrable (fun ω => f x - lower - η * ⟪v, g x ω⟫) p :=
      (integrable_const _).sub (((ho.integrable x).const_inner v).const_mul η)
    rw [integral_add hB1
      (hgi.const_mul (L * η ^ 2 / 2)), integral_sub (integrable_const (f x - lower))
      (((ho.integrable x).const_inner v).const_mul η), integral_const_mul,
      integral_const_mul, integral_inner (ho.integrable x), ho.unbiased]
    simp [v]
  rw [hBvalue] at hi
  have hn := mul_le_mul_of_nonneg_left hg2 (show 0 ≤ L * η ^ 2 / 2 by positivity)
  have hc : L * η ^ 2 ≤ η := by nlinarith
  have hc' := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖v‖)
  dsimp [v] at *
  nlinarith

end OracleTemplate.StochasticNonconvex
