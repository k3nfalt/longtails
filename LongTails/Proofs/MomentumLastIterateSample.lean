import LongTails.Setups.MomentumLipschitzConvex
import LongTails.Proofs.MomentumLastIterateRecursion
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic

open MeasureTheory Set InnerProductSpace
open scoped RealInnerProductSpace

namespace OracleTemplate.MomentumConvex

open LongTails.Setups.MomentumLipschitzConvex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]

structure Hyp (p : Measure Ξ) (f : E → ℝ) (Gr : Ξ → E → E) (G : ℝ) (xstar : E) : Prop where
  meas : Measurable (Function.uncurry Gr)
  conv : ConvexOn ℝ univ f
  sq_int : ∀ x, Integrable (fun ξ => ‖Gr ξ x‖ ^ 2) p
  sq_le : ∀ x, ∫ ξ, ‖Gr ξ x‖ ^ 2 ∂p ≤ G ^ 2
  sub : ∀ x y, f x + inner ℝ (∫ ξ, Gr ξ x ∂p) (y - x) ≤ f y
  min : IsMinOn f univ xstar
  pos : 0 ≤ G

noncomputable def mean (p : Measure Ξ) (Gr : Ξ → E → E) (x : E) : E := ∫ ξ, Gr ξ x ∂p

namespace Hyp

variable {p : Measure Ξ} [IsProbabilityMeasure p] {f : E → ℝ} {Gr : Ξ → E → E} {G : ℝ} {xstar : E}

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma grad_meas (h : Hyp p f Gr G xstar) (x : E) : Measurable (fun ξ => Gr ξ x) :=
  h.meas.comp (measurable_id.prodMk measurable_const)

omit [CompleteSpace E] in
lemma int_grad (h : Hyp p f Gr G xstar) (x : E) : Integrable (fun ξ => Gr ξ x) p := by
  have hb : Integrable (fun ξ => 1 + ‖Gr ξ x‖ ^ 2) p := (integrable_const (1 : ℝ)).add (h.sq_int x)
  refine Integrable.mono' hb (h.grad_meas x).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => ?_))
  nlinarith [sq_nonneg (‖Gr ξ x‖ - 1), norm_nonneg (Gr ξ x)]

omit [CompleteSpace E] in
lemma norm_mean_le (h : Hyp p f Gr G xstar) (x : E) : ‖mean p Gr x‖ ≤ G := by
  have hi : Integrable (fun ξ => ‖Gr ξ x‖) p := (h.int_grad x).norm
  set c := ∫ ξ, ‖Gr ξ x‖ ∂p with hc
  have h1 : ‖mean p Gr x‖ ≤ c := norm_integral_le_integral_norm _
  have hc0 : 0 ≤ c := integral_nonneg (fun ξ => norm_nonneg _)
  have hsq : Integrable (fun ξ => (‖Gr ξ x‖ - c) ^ 2) p := by
    have : (fun ξ => (‖Gr ξ x‖ - c) ^ 2) =
        fun ξ => ‖Gr ξ x‖ ^ 2 - 2 * c * ‖Gr ξ x‖ + c ^ 2 := by funext ξ; ring
    rw [this]
    exact ((h.sq_int x).sub (hi.const_mul _)).add (integrable_const _)
  have h2 : 0 ≤ ∫ ξ, (‖Gr ξ x‖ - c) ^ 2 ∂p := integral_nonneg (fun ξ => sq_nonneg _)
  have h3 : ∫ ξ, (‖Gr ξ x‖ - c) ^ 2 ∂p = ∫ ξ, ‖Gr ξ x‖ ^ 2 ∂p - c ^ 2 := by
    have hfun : (fun ξ => (‖Gr ξ x‖ - c) ^ 2) =
        fun ξ => (‖Gr ξ x‖ ^ 2 - 2 * c * ‖Gr ξ x‖) + c ^ 2 := by funext ξ; ring
    have ea : ∫ ξ, ((‖Gr ξ x‖ ^ 2 - 2 * c * ‖Gr ξ x‖) + c ^ 2) ∂p =
        ∫ ξ, (‖Gr ξ x‖ ^ 2 - 2 * c * ‖Gr ξ x‖) ∂p + ∫ _ξ : Ξ, c ^ 2 ∂p :=
      integral_add ((h.sq_int x).sub (hi.const_mul _)) (integrable_const _)
    have eb : ∫ ξ, (‖Gr ξ x‖ ^ 2 - 2 * c * ‖Gr ξ x‖) ∂p =
        ∫ ξ, ‖Gr ξ x‖ ^ 2 ∂p - ∫ ξ, 2 * c * ‖Gr ξ x‖ ∂p :=
      integral_sub (h.sq_int x) (hi.const_mul _)
    have ec : ∫ ξ, 2 * c * ‖Gr ξ x‖ ∂p = 2 * c * c := by
      rw [integral_const_mul, ← hc]
    have ed : ∫ _ξ : Ξ, c ^ 2 ∂p = c ^ 2 := by simp
    rw [hfun, ea, eb, ec, ed]; ring
  have h4 : c ^ 2 ≤ G ^ 2 := by linarith [h.sq_le x]
  have h5 : c ≤ G := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [h.pos]
  linarith

omit [CompleteSpace E] in
lemma lip (h : Hyp p f Gr G xstar) (x y : E) : f x - f y ≤ G * ‖x - y‖ := by
  have h1 := h.sub x y
  have h2 : ⟪mean p Gr x, x - y⟫ ≤ G * ‖x - y‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (h.norm_mean_le x) (norm_nonneg _))
  have h3 : ⟪mean p Gr x, y - x⟫ = -⟪mean p Gr x, x - y⟫ := by
    rw [← inner_neg_right]; congr 1; abel
  change f x + ⟪mean p Gr x, y - x⟫ ≤ f y at h1
  rw [h3] at h1
  linarith

omit [CompleteSpace E] in
lemma continuous (h : Hyp p f Gr G xstar) : Continuous f := by
  have hL : LipschitzWith ⟨G, h.pos⟩ f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, dist_eq_norm, abs_le]
    change -(G * ‖x - y‖) ≤ f x - f y ∧ f x - f y ≤ G * ‖x - y‖
    have h1 := h.lip x y
    have h2 := h.lip y x
    rw [norm_sub_rev] at h2
    constructor <;> linarith
  exact hL.continuous

omit [CompleteSpace E] in
lemma gap_bounds (h : Hyp p f Gr G xstar) (y : E) :
    0 ≤ f y - f xstar ∧ f y - f xstar ≤ G * ‖y - xstar‖ :=
  ⟨sub_nonneg.mpr (h.min (mem_univ y)), h.lip y xstar⟩

lemma one_sample (h : Hyp p f Gr G xstar) (x m w : E) {s c e : ℝ} (hs : 0 ≤ s) (hc : 0 ≤ c)
    (he : 0 < e) :
    Integrable (fun ω => ‖x - c • m - s • Gr ω x - w‖ ^ 2) p ∧
    ∫ ω, ‖x - c • m - s • Gr ω x - w‖ ^ 2 ∂p ≤
      ‖x - c • m - w‖ ^ 2 - 2 * s * ((1 + c / e) * f x - c / e * f (x + e • m) - f w) +
        s ^ 2 * G ^ 2 := by
  set v := x - c • m - w with hv
  have hexp : ∀ ω, ‖x - c • m - s • Gr ω x - w‖ ^ 2 =
      ‖v‖ ^ 2 - 2 * s * ⟪v, Gr ω x⟫ + s ^ 2 * ‖Gr ω x‖ ^ 2 := by
    intro ω
    have e1 : x - c • m - s • Gr ω x - w = v - s • Gr ω x := by rw [hv]; abel
    rw [e1, norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hii : Integrable (fun ω => ⟪v, Gr ω x⟫) p := (h.int_grad x).const_inner v
  have hie : ∫ ω, ⟪v, Gr ω x⟫ ∂p = ⟪v, mean p Gr x⟫ := integral_inner (h.int_grad x) v
  have hi1 : Integrable (fun ω => ‖v‖ ^ 2 - 2 * s * ⟪v, Gr ω x⟫) p :=
    (integrable_const _).sub (hii.const_mul _)
  have hi2 : Integrable (fun ω => s ^ 2 * ‖Gr ω x‖ ^ 2) p := (h.sq_int x).const_mul _
  have hfun : (fun ω => ‖x - c • m - s • Gr ω x - w‖ ^ 2) =
      fun ω => ‖v‖ ^ 2 - 2 * s * ⟪v, Gr ω x⟫ + s ^ 2 * ‖Gr ω x‖ ^ 2 := funext hexp
  rw [hfun]
  refine ⟨hi1.add hi2, ?_⟩
  have ei1 : ∫ _ω : Ξ, ‖v‖ ^ 2 ∂p = ‖v‖ ^ 2 := by simp
  have ei2 : ∫ ω, 2 * s * ⟪v, Gr ω x⟫ ∂p = 2 * s * ⟪v, mean p Gr x⟫ := by
    rw [integral_const_mul, hie]
  have ei3 : ∫ ω, s ^ 2 * ‖Gr ω x‖ ^ 2 ∂p = s ^ 2 * ∫ ω, ‖Gr ω x‖ ^ 2 ∂p := integral_const_mul _ _
  rw [integral_add hi1 hi2, integral_sub (integrable_const _) (hii.const_mul _), ei1, ei2, ei3]
  have hsub1 := h.sub x w
  have hsub2 := h.sub x (x + e • m)
  change f x + ⟪mean p Gr x, w - x⟫ ≤ f w at hsub1
  change f x + ⟪mean p Gr x, x + e • m - x⟫ ≤ f (x + e • m) at hsub2
  have e2 : x + e • m - x = e • m := by abel
  rw [e2, inner_smul_right] at hsub2
  have e3 : ⟪v, mean p Gr x⟫ = -⟪mean p Gr x, w - x⟫ - c * ⟪mean p Gr x, m⟫ := by
    rw [real_inner_comm, hv]
    have : x - c • m - w = -(w - x) - c • m := by abel
    rw [this, inner_sub_right, inner_neg_right, inner_smul_right]
  have hq : c / e * (f x - f (x + e • m)) ≤ -(c * ⟪mean p Gr x, m⟫) := by
    have h1 : e * ⟪mean p Gr x, m⟫ ≤ f (x + e • m) - f x := by linarith
    have h2 : ⟪mean p Gr x, m⟫ ≤ (f (x + e • m) - f x) / e := by
      rw [le_div_iff₀ he]; linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hc
    have h4 : c * ((f (x + e • m) - f x) / e) = -(c / e * (f x - f (x + e • m))) := by
      field_simp; ring
    linarith
  have h5 : s ^ 2 * ∫ ω, ‖Gr ω x‖ ^ 2 ∂p ≤ s ^ 2 * G ^ 2 :=
    mul_le_mul_of_nonneg_left (h.sq_le x) (sq_nonneg s)
  have h6 : (1 + c / e) * f x - c / e * f (x + e • m) - f w ≤ ⟪v, mean p Gr x⟫ := by
    rw [e3]; linarith
  nlinarith [mul_le_mul_of_nonneg_left h6 hs]

omit [CompleteSpace E] in
lemma moment_sample (h : Hyp p f Gr G xstar) (x m : E) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    Integrable (fun ω => ‖β • m + (1 - β) • Gr ω x‖ ^ 2) p ∧
    ∫ ω, ‖β • m + (1 - β) • Gr ω x‖ ^ 2 ∂p ≤ β * ‖m‖ ^ 2 + (1 - β) * G ^ 2 := by
  have hpt : ∀ ω, ‖β • m + (1 - β) • Gr ω x‖ ^ 2 ≤ β * ‖m‖ ^ 2 + (1 - β) * ‖Gr ω x‖ ^ 2 := by
    intro ω
    have h1 : ‖β • m + (1 - β) • Gr ω x‖ ≤ β * ‖m‖ + (1 - β) * ‖Gr ω x‖ := by
      calc ‖β • m + (1 - β) • Gr ω x‖ ≤ ‖β • m‖ + ‖(1 - β) • Gr ω x‖ := norm_add_le _ _
        _ = β * ‖m‖ + (1 - β) * ‖Gr ω x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hβ0,
            abs_of_nonneg (by linarith)]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖m‖ - ‖Gr ω x‖), mul_nonneg hβ0 (by linarith : (0 : ℝ) ≤ 1 - β)]
  have hb : Integrable (fun ω => β * ‖m‖ ^ 2 + (1 - β) * ‖Gr ω x‖ ^ 2) p :=
    (integrable_const _).add ((h.sq_int x).const_mul _)
  have hm : Measurable (fun ω => ‖β • m + (1 - β) • Gr ω x‖ ^ 2) :=
    (measurable_const.add ((h.grad_meas x).const_smul _)).norm.pow_const 2
  have hint : Integrable (fun ω => ‖β • m + (1 - β) • Gr ω x‖ ^ 2) p :=
    Integrable.mono' hb hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt ω))
  refine ⟨hint, ?_⟩
  calc ∫ ω, ‖β • m + (1 - β) • Gr ω x‖ ^ 2 ∂p
      ≤ ∫ ω, (β * ‖m‖ ^ 2 + (1 - β) * ‖Gr ω x‖ ^ 2) ∂p := integral_mono hint hb hpt
    _ = β * ‖m‖ ^ 2 + (1 - β) * ∫ ω, ‖Gr ω x‖ ^ 2 ∂p := by
        have e1 : ∫ _ω : Ξ, β * ‖m‖ ^ 2 ∂p = β * ‖m‖ ^ 2 := by simp
        have e2 : ∫ ω, (1 - β) * ‖Gr ω x‖ ^ 2 ∂p = (1 - β) * ∫ ω, ‖Gr ω x‖ ^ 2 ∂p :=
          integral_const_mul _ _
        rw [integral_add (integrable_const _) ((h.sq_int x).const_mul _), e1, e2]
    _ ≤ β * ‖m‖ ^ 2 + (1 - β) * G ^ 2 := by
        have := mul_le_mul_of_nonneg_left (h.sq_le x) (by linarith : (0 : ℝ) ≤ 1 - β)
        linarith

end Hyp

end OracleTemplate.MomentumConvex
