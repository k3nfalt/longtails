import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.CurvatureAligned

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {Ω : Type} [MeasurableSpace Ω]

structure Hyp (p : Measure Ω) (f : E → ℝ) (g : E → Ω → E) (Q : E → E →L[ℝ] E)
    (lower Lg Lξ σ : ℝ) : Prop where
  grad : ∀ x, HasGradientAt f (gradient f x) x
  upper : ∀ x u, f (x + u) ≤ f x + ⟪gradient f x, u⟫ + ⟪Q x u, u⟫ / 2
  align : ∀ x, ⟪Q x (gradient f x), gradient f x⟫ ≤ Lg * ‖gradient f x‖ ^ 2
  lower_le : ∀ x, lower ≤ f x
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = gradient f x
  vint : ∀ x, Integrable (fun ω => ‖g x ω - gradient f x‖ ^ 2) p
  var : ∀ x, ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p ≤ σ ^ 2
  qint : ∀ x, Integrable (fun ω => ⟪Q x (g x ω - gradient f x), g x ω - gradient f x⟫) p
  qvar : ∀ x, ∫ ω, ⟪Q x (g x ω - gradient f x), g x ω - gradient f x⟫ ∂p ≤
    Lξ * ∫ ω, ‖g x ω - gradient f x‖ ^ 2 ∂p
  Lg_pos : 0 < Lg
  Lξ_nn : 0 ≤ Lξ

variable {p : Measure Ω} {f : E → ℝ} {g : E → Ω → E} {Q : E → E →L[ℝ] E}
  {lower Lg Lξ σ : ℝ}

lemma Hyp.continuous (H : Hyp p f g Q lower Lg Lξ σ) : Continuous f :=
  continuous_iff_continuousAt.mpr fun x => (H.grad x).hasFDerivAt.continuousAt

lemma Hyp.grad_sq_le (H : Hyp p f g Q lower Lg Lξ σ) (x : E) :
    ‖gradient f x‖ ^ 2 ≤ 2 * Lg * (f x - lower) := by
  have hL := H.Lg_pos
  set v := gradient f x
  have h := H.upper x (-(1 / Lg) • v)
  have hQ : ⟪Q x (-(1 / Lg) • v), -(1 / Lg) • v⟫ = (1 / Lg) ^ 2 * ⟪Q x v, v⟫ := by
    rw [map_smul, inner_smul_left, inner_smul_right]
    simp only [conj_trivial]
    ring
  have hlin : ⟪v, -(1 / Lg) • v⟫ = -(1 / Lg) * ‖v‖ ^ 2 := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hQ, hlin] at h
  have ha := H.align x
  have hlow := H.lower_le (x + -(1 / Lg) • v)
  have h2 : (1 / Lg) ^ 2 * ⟪Q x v, v⟫ ≤ (1 / Lg) ^ 2 * (Lg * ‖v‖ ^ 2) :=
    mul_le_mul_of_nonneg_left ha (by positivity)
  have e : (1 / Lg) ^ 2 * (Lg * ‖v‖ ^ 2) = (1 / Lg) * ‖v‖ ^ 2 := by
    field_simp
  have hfin : (1 / Lg) * ‖v‖ ^ 2 / 2 ≤ f x - lower := by linarith
  have e2 : ‖v‖ ^ 2 = 2 * Lg * ((1 / Lg) * ‖v‖ ^ 2 / 2) := by field_simp
  rw [e2]
  exact mul_le_mul_of_nonneg_left hfin (by positivity)

lemma Hyp.noise_int [IsFiniteMeasure p] (H : Hyp p f g Q lower Lg Lξ σ) (x : E) :
    Integrable (fun ω => g x ω - gradient f x) p :=
  (H.int x).sub (integrable_const _)

lemma Hyp.noise_mean [IsProbabilityMeasure p] (H : Hyp p f g Q lower Lg Lξ σ) (x : E) :
    ∫ ω, (g x ω - gradient f x) ∂p = 0 := by
  rw [integral_sub (H.int x) (integrable_const _), H.mean x, integral_const]
  simp

lemma Hyp.step [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure p]
    (H : Hyp p f g Q lower Lg Lξ σ) (η : ℝ) (x : E) (hmeas : Measurable fun ω => g x ω) :
    Integrable (fun ω => f (x - η • g x ω)) p ∧
      ∫ ω, f (x - η • g x ω) ∂p ≤
        f x - η * (1 - η * Lg / 2) * ‖gradient f x‖ ^ 2 + η ^ 2 * Lξ * σ ^ 2 / 2 := by
  set v := gradient f x with hv
  set ξ := fun ω => g x ω - v
  have hξi : Integrable ξ p := H.noise_int x
  have hξ0 : ∫ ω, ξ ω ∂p = 0 := H.noise_mean x
  have hg : ∀ ω, g x ω = v + ξ ω := fun ω => by simp [ξ]
  set r : Ω → ℝ := fun ω => f x - η * (‖v‖ ^ 2 + ⟪v, ξ ω⟫) +
    η ^ 2 / 2 * (⟪Q x v, v⟫ + ⟪Q x v, ξ ω⟫ + ⟪v, Q x (ξ ω)⟫ + ⟪Q x (ξ ω), ξ ω⟫)
  have hpt : ∀ ω, f (x - η • g x ω) ≤ r ω := by
    intro ω
    have h := H.upper x (-(η • g x ω))
    rw [← sub_eq_add_neg, ← hv] at h
    refine h.trans (le_of_eq ?_)
    rw [hg ω]
    simp only [r, map_neg, map_smul, map_add, inner_neg_right, inner_neg_left, inner_smul_left,
      inner_smul_right, inner_add_left, inner_add_right, real_inner_self_eq_norm_sq, conj_trivial]
    rw [real_inner_comm (Q x (ξ ω)) v]
    ring
  have i1 : Integrable (fun ω => ⟪v, ξ ω⟫) p := hξi.const_inner v
  have i2 : Integrable (fun ω => ⟪Q x v, ξ ω⟫) p := hξi.const_inner (Q x v)
  have i3 : Integrable (fun ω => ⟪v, Q x (ξ ω)⟫) p :=
    ((Q x).integrable_comp hξi).const_inner v
  have i4 : Integrable (fun ω => ⟪Q x (ξ ω), ξ ω⟫) p := H.qint x
  have ir : Integrable r p := by
    refine (integrable_const _).sub (((integrable_const _).add i1).const_mul η) |>.add ?_
    exact ((((integrable_const _).add i2).add i3).add i4).const_mul _
  have hfm : AEStronglyMeasurable (fun ω => f (x - η • g x ω)) p :=
    (H.continuous.measurable.comp ((continuous_sub_left x).measurable.comp
      (hmeas.const_smul η))).aestronglyMeasurable
  have ifx : Integrable (fun ω => f (x - η • g x ω)) p := by
    refine Integrable.mono' ((integrable_const |lower|).add (ir.norm)) hfm
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := H.lower_le (x - η • g x ω)
    have h2 := hpt ω
    simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_le]
    constructor
    · have := neg_abs_le lower; have := abs_nonneg (r ω); linarith
    · have := le_abs_self lower; have := le_abs_self (r ω); have := abs_nonneg lower; linarith
  refine ⟨ifx, ?_⟩
  have hr1 : ∫ ω, ⟪v, ξ ω⟫ ∂p = 0 := by rw [integral_inner hξi, hξ0, inner_zero_right]
  have hr2 : ∫ ω, ⟪Q x v, ξ ω⟫ ∂p = 0 := by rw [integral_inner hξi, hξ0, inner_zero_right]
  have hr3 : ∫ ω, ⟪v, Q x (ξ ω)⟫ ∂p = 0 := by
    rw [integral_inner ((Q x).integrable_comp hξi), (Q x).integral_comp_comm hξi, hξ0, map_zero,
      inner_zero_right]
  have hrint : ∫ ω, r ω ∂p = f x - η * ‖v‖ ^ 2 +
      η ^ 2 / 2 * (⟪Q x v, v⟫ + ∫ ω, ⟪Q x (ξ ω), ξ ω⟫ ∂p) := by
    simp only [r]
    rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_add,
      integral_add, integral_add, integral_add]
    · simp only [integral_const, probReal_univ, one_smul, hr1, hr2, hr3]; ring
    all_goals first
      | exact integrable_const _ | exact i1 | exact i2 | exact i3 | exact i4
      | exact (integrable_const _).add i1 | exact (integrable_const _).add i2
      | exact ((integrable_const _).add i2).add i3
      | exact (((integrable_const _).add i1).const_mul η)
      | exact ((((integrable_const _).add i2).add i3).add i4).const_mul _
      | exact (integrable_const _).sub (((integrable_const _).add i1).const_mul η)
  have hle := integral_mono ifx ir hpt
  have ha := H.align x
  have hq := H.qvar x
  have hv := H.var x
  have hq' : ∫ ω, ⟪Q x (ξ ω), ξ ω⟫ ∂p ≤ Lξ * σ ^ 2 :=
    hq.trans (mul_le_mul_of_nonneg_left hv H.Lξ_nn)
  have hη2 : 0 ≤ η ^ 2 / 2 := by positivity
  have := mul_le_mul_of_nonneg_left (add_le_add ha hq') hη2
  rw [hrint] at hle
  nlinarith

end OracleTemplate.CurvatureAligned
