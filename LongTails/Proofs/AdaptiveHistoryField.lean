import LongTails.Proofs.AdaptiveHistoryAlgebra
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Group.Integral

namespace LongTails.Proofs.AdaptiveHistoryField

noncomputable def scalarField (δ b c x : ℝ) : ℝ :=
  x / (δ + Real.sqrt (b * x ^ 2 + c))

lemma scalarField_hasDerivAt {δ b c : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b)
    (hc : 0 < c) (x : ℝ) :
    HasDerivAt (scalarField δ b c)
      ((δ + c / Real.sqrt (b * x ^ 2 + c)) / (δ + Real.sqrt (b * x ^ 2 + c)) ^ 2) x := by
  have hz : 0 < b * x ^ 2 + c := by positivity
  have hs : 0 < Real.sqrt (b * x ^ 2 + c) := Real.sqrt_pos.mpr hz
  have hd : δ + Real.sqrt (b * x ^ 2 + c) ≠ 0 := by positivity
  have hi : HasDerivAt (fun y : ℝ => b * y ^ 2 + c) (b * (2 * x)) x := by
    simpa using (((hasDerivAt_id x).pow 2).const_mul b).add_const c
  have hr := (Real.hasDerivAt_sqrt hz.ne').comp x hi
  have h := (hasDerivAt_id x).div (hr.const_add δ) hd
  convert h using 1
  · rfl
  · have hsq := Real.sq_sqrt hz.le
    dsimp only [Function.comp_def, id]
    field_simp
    nlinarith

lemma scalarField_derivative_lower {δ t c : ℝ} (hδ : 0 < δ) (ht : 0 < t)
    (hc : 0 ≤ c) :
    (δ ^ 2 + c) / (δ + t) ^ 3 ≤ (δ + c / t) / (δ + t) ^ 2 := by
  have hd : 0 < t * (δ + t) ^ 3 := by positivity
  apply (mul_le_mul_iff_of_pos_right hd).mp
  field_simp
  nlinarith [mul_nonneg hδ.le hc, mul_nonneg hδ.le (sq_nonneg t)]

lemma scalarField_increment {δ b c u v U : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b)
    (hc : 0 < c) (huv : u ≤ v) (_hU : 0 < U)
    (hbound : ∀ x ∈ Set.Icc u v, δ + Real.sqrt (b * x ^ 2 + c) ≤ U) :
    (δ ^ 2 + c) / U ^ 3 * (v - u) ≤ scalarField δ b c v - scalarField δ b c u := by
  have hd (x : ℝ) := scalarField_hasDerivAt hδ hb hc x
  apply (convex_Icc u v).mul_sub_le_image_sub_of_le_deriv
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
    u (by simp [huv]) v (by simp [huv]) huv
  intro x hx
  rw [(hd x).deriv]
  have hx' : x ∈ Set.Icc u v := interior_subset hx
  have hs : 0 < Real.sqrt (b * x ^ 2 + c) := Real.sqrt_pos.mpr (by positivity)
  have hden : 0 < δ + Real.sqrt (b * x ^ 2 + c) := by positivity
  have hp := pow_le_pow_left₀ hden.le (hbound x hx') 3
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
    (scalarField_derivative_lower hδ hs hc.le)

lemma scalarField_continuousAt_residual {δ b c x : ℝ} (hδ : 0 < δ) :
    ContinuousAt (fun r => scalarField δ b r x) c := by
  unfold scalarField
  apply continuousAt_const.div
    (continuousAt_const.add (Real.continuous_sqrt.continuousAt.comp
      (continuousAt_const.add continuousAt_id)))
  change δ + Real.sqrt (b * x ^ 2 + c) ≠ 0
  positivity

lemma scalarField_increment_nonneg {δ b c u v U : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (huv : u ≤ v) (hU : 0 < U)
    (hbound : ∀ x ∈ Set.Icc u v, δ + Real.sqrt (b * x ^ 2 + c) ≤ U) :
    (δ ^ 2 + c) / U ^ 3 * (v - u) ≤ scalarField δ b c v - scalarField δ b c u := by
  have hl : ContinuousAt
      (fun e : ℝ => (δ ^ 2 + (c + e)) / (U + Real.sqrt e) ^ 3 * (v - u)) 0 := by
    apply ContinuousAt.mul _ continuousAt_const
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using pow_ne_zero 3 hU.ne'
  have hr : ContinuousAt
      (fun e : ℝ => scalarField δ b (c + e) v - scalarField δ b (c + e) u) 0 := by
    exact ((scalarField_continuousAt_residual hδ).comp
      (continuousAt_const.add continuousAt_id)).sub
      ((scalarField_continuousAt_residual hδ).comp
        (continuousAt_const.add continuousAt_id))
  have he : ∀ᶠ e : ℝ in nhdsWithin 0 (Set.Ioi 0),
      (δ ^ 2 + (c + e)) / (U + Real.sqrt e) ^ 3 * (v - u) ≤
        scalarField δ b (c + e) v - scalarField δ b (c + e) u := by
    filter_upwards [self_mem_nhdsWithin] with e he
    change 0 < e at he
    apply scalarField_increment hδ hb (by exact add_pos_of_nonneg_of_pos hc he)
      huv (by positivity)
    intro x hx
    have hz : 0 ≤ b * x ^ 2 + c := by positivity
    have hs := Real.sq_sqrt hz
    have ht := Real.sq_sqrt (show 0 ≤ e from le_of_lt he)
    have hv := Real.sq_sqrt (show 0 ≤ b * x ^ 2 + (c + e) by positivity)
    have hsum : Real.sqrt (b * x ^ 2 + (c + e)) ≤
        Real.sqrt (b * x ^ 2 + c) + Real.sqrt e := by
      nlinarith [Real.sqrt_nonneg (b * x ^ 2 + (c + e)),
        Real.sqrt_nonneg (b * x ^ 2 + c), Real.sqrt_nonneg e,
        mul_nonneg (Real.sqrt_nonneg (b * x ^ 2 + c)) (Real.sqrt_nonneg e)]
    linarith [hbound x hx]
  simpa using le_of_tendsto_of_tendsto
    (hl.tendsto.mono_left nhdsWithin_le_nhds)
    (hr.tendsto.mono_left nhdsWithin_le_nhds) he

lemma scalarField_neg (δ b c x : ℝ) :
    scalarField δ b c (-x) = -scalarField δ b c x := by
  simp only [scalarField, neg_sq, neg_div]

lemma scalarField_sign_pair {δ b c g r : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hg : 0 ≤ g) (hr : 0 ≤ r) :
    g * (δ ^ 2 + c) / (δ + Real.sqrt (b * (g + r) ^ 2 + c)) ^ 3 ≤
      (scalarField δ b c (g + r) + scalarField δ b c (g - r)) / 2 := by
  have hi := scalarField_increment_nonneg hδ hb hc
    (show r - g ≤ r + g by linarith)
    (show 0 < δ + Real.sqrt (b * (g + r) ^ 2 + c) by positivity)
    (U := δ + Real.sqrt (b * (g + r) ^ 2 + c))
  have hbound : ∀ x ∈ Set.Icc (r - g) (r + g),
      δ + Real.sqrt (b * x ^ 2 + c) ≤
        δ + Real.sqrt (b * (g + r) ^ 2 + c) := by
    intro x hx
    have hsq : x ^ 2 ≤ (g + r) ^ 2 := by
      have hleft : 0 ≤ x + (g + r) := by linarith [hx.1]
      have hright : 0 ≤ g + r - x := by linarith [hx.2]
      nlinarith [mul_nonneg hleft hright]
    have harg : b * x ^ 2 + c ≤ b * (g + r) ^ 2 + c :=
      add_le_add (mul_le_mul_of_nonneg_left hsq hb) le_rfl
    exact add_le_add le_rfl (Real.sqrt_le_sqrt harg)
  specialize hi hbound
  have hn : scalarField δ b c (r - g) = -scalarField δ b c (g - r) := by
    rw [show r - g = -(g - r) by ring, scalarField_neg]
  rw [hn, show r + g = g + r by ring] at hi
  have heq : (δ ^ 2 + c) / (δ + Real.sqrt (b * (g + r) ^ 2 + c)) ^ 3 *
      (g + r - (r - g)) =
      2 * (g * (δ ^ 2 + c) / (δ + Real.sqrt (b * (g + r) ^ 2 + c)) ^ 3) := by ring
  rw [heq] at hi
  linarith

lemma scalarField_sign_pair_common_denominator {δ b c g r U : ℝ}
    (hδ : 0 < δ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hg : 0 ≤ g) (hr : 0 ≤ r)
    (hU : δ + Real.sqrt (b * (g + r) ^ 2 + c) ≤ U) :
    g * (δ ^ 2 + c) / U ^ 3 ≤
      (scalarField δ b c (g + r) + scalarField δ b c (g - r)) / 2 := by
  have hd : 0 < δ + Real.sqrt (b * (g + r) ^ 2 + c) := by positivity
  apply le_trans _ (scalarField_sign_pair hδ hb hc hg hr)
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_left₀ hd.le hU 3)

lemma paired_numerator_bound {δ b β S g r s : ℝ}
    (hb : 0 ≤ b) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hS : 0 ≤ S) :
    β / 8 * (δ + Real.sqrt (S + b * ((g + r) ^ 2 + (g + s) ^ 2))) ^ 2 ≤
      δ ^ 2 + S + β * b * (g ^ 2 + (r ^ 2 + s ^ 2) / 2) := by
  have hz : 0 ≤ S + b * ((g + r) ^ 2 + (g + s) ^ 2) := by positivity
  have hsqrt := Real.sq_sqrt hz
  have hcross : (g + r) ^ 2 + (g + s) ^ 2 ≤ 4 * g ^ 2 + 2 * (r ^ 2 + s ^ 2) := by
    nlinarith [sq_nonneg (g - r), sq_nonneg (g - s)]
  have hupper : (δ + Real.sqrt (S + b * ((g + r) ^ 2 + (g + s) ^ 2))) ^ 2 ≤
      2 * δ ^ 2 + 2 * S + 8 * b * g ^ 2 + 4 * b * (r ^ 2 + s ^ 2) := by
    nlinarith [sq_nonneg (δ - Real.sqrt (S + b * ((g + r) ^ 2 + (g + s) ^ 2))),
      mul_le_mul_of_nonneg_left hcross hb]
  have hscaled := mul_le_mul_of_nonneg_left hupper hβ
  have hcoef : 0 ≤ 8 - 2 * β := by linarith
  have hn1 := mul_nonneg hcoef (sq_nonneg δ)
  have hn2 := mul_nonneg hcoef hS
  nlinarith

noncomputable def twoSampleField (δ b β S g r s : ℝ) : ℝ :=
  (scalarField δ b (S + β * b * (g + s) ^ 2) (g + r) +
    scalarField δ b (S + β * b * (g + s) ^ 2) (g - r) +
    scalarField δ b (S + β * b * (g - s) ^ 2) (g + r) +
    scalarField δ b (S + β * b * (g - s) ^ 2) (g - r)) / 4

lemma twoSampleField_lower {δ b β S g r s : ℝ}
    (hδ : 0 < δ) (hb : 0 ≤ b) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hS : 0 ≤ S) (hg : 0 ≤ g) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    g * (δ ^ 2 + S + β * b * (g ^ 2 + s ^ 2)) /
        (δ + Real.sqrt (S + b * ((g + r) ^ 2 + (g + s) ^ 2))) ^ 3 ≤
      twoSampleField δ b β S g r s := by
  let U := δ + Real.sqrt (S + b * ((g + r) ^ 2 + (g + s) ^ 2))
  have hplus : b * (g + r) ^ 2 + (S + β * b * (g + s) ^ 2) ≤
      S + b * ((g + r) ^ 2 + (g + s) ^ 2) := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - β by linarith)
      (mul_nonneg hb (sq_nonneg (g + s)))]
  have hminus : b * (g + r) ^ 2 + (S + β * b * (g - s) ^ 2) ≤
      S + b * ((g + r) ^ 2 + (g + s) ^ 2) := by
    have hsq : (g - s) ^ 2 ≤ (g + s) ^ 2 := by nlinarith [mul_nonneg hg hs]
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hβ hb)]
  have hp := scalarField_sign_pair_common_denominator hδ hb
    (show 0 ≤ S + β * b * (g + s) ^ 2 by positivity) hg hr
    (show δ + Real.sqrt (b * (g + r) ^ 2 + (S + β * b * (g + s) ^ 2)) ≤ U from
      add_le_add le_rfl (Real.sqrt_le_sqrt hplus))
  have hm := scalarField_sign_pair_common_denominator hδ hb
    (show 0 ≤ S + β * b * (g - s) ^ 2 by positivity) hg hr
    (show δ + Real.sqrt (b * (g + r) ^ 2 + (S + β * b * (g - s) ^ 2)) ≤ U from
      add_le_add le_rfl (Real.sqrt_le_sqrt hminus))
  change g * (δ ^ 2 + S + β * b * (g ^ 2 + s ^ 2)) / U ^ 3 ≤ _
  calc
    _ = (g * (δ ^ 2 + (S + β * b * (g + s) ^ 2)) / U ^ 3 +
        g * (δ ^ 2 + (S + β * b * (g - s) ^ 2)) / U ^ 3) / 2 := by ring
    _ ≤ twoSampleField δ b β S g r s := by
      unfold twoSampleField
      linarith only [hp, hm]

lemma twoSampleField_swap_lower {δ b β S g r s : ℝ}
    (hδ : 0 < δ) (hb : 0 ≤ b) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hS : 0 ≤ S) (hg : 0 ≤ g) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    β * g / (8 * (δ + Real.sqrt (S + b * ((g + r) ^ 2 + (g + s) ^ 2)))) ≤
      (twoSampleField δ b β S g r s + twoSampleField δ b β S g s r) / 2 := by
  let U := δ + Real.sqrt (S + b * ((g + r) ^ 2 + (g + s) ^ 2))
  have hU : 0 < U := by dsimp [U]; positivity
  have hnum := paired_numerator_bound (δ := δ) (g := g) (r := r) (s := s) hb hβ hβ1 hS
  change β / 8 * U ^ 2 ≤ _ at hnum
  have hp := twoSampleField_lower hδ hb hβ hβ1 hS hg hr hs
  have hm := twoSampleField_lower hδ hb hβ hβ1 hS hg hs hr
  rw [show (g + s) ^ 2 + (g + r) ^ 2 = (g + r) ^ 2 + (g + s) ^ 2 by ring] at hm
  change g * (δ ^ 2 + S + β * b * (g ^ 2 + s ^ 2)) / U ^ 3 ≤ _ at hp
  change g * (δ ^ 2 + S + β * b * (g ^ 2 + r ^ 2)) / U ^ 3 ≤ _ at hm
  change β * g / (8 * U) ≤ _
  calc
    _ = g * (β / 8 * U ^ 2) / U ^ 3 := by field_simp
    _ ≤ g * (δ ^ 2 + S + β * b * (g ^ 2 + (r ^ 2 + s ^ 2) / 2)) / U ^ 3 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hg) (by positivity)
    _ = (g * (δ ^ 2 + S + β * b * (g ^ 2 + s ^ 2)) / U ^ 3 +
        g * (δ ^ 2 + S + β * b * (g ^ 2 + r ^ 2)) / U ^ 3) / 2 := by ring
    _ ≤ _ := by linarith only [hp, hm]

lemma twoSampleField_neg_left (δ b β S g r s : ℝ) :
    twoSampleField δ b β S g (-r) s = twoSampleField δ b β S g r s := by
  unfold twoSampleField
  rw [show g + -r = g - r by ring, show g - -r = g + r by ring]
  ring

lemma twoSampleField_neg_right (δ b β S g r s : ℝ) :
    twoSampleField δ b β S g r (-s) = twoSampleField δ b β S g r s := by
  unfold twoSampleField
  rw [show g + -s = g - s by ring, show g - -s = g + s by ring]
  ring

lemma twoSampleField_abs (δ b β S g r s : ℝ) :
    twoSampleField δ b β S g |r| |s| = twoSampleField δ b β S g r s := by
  rcases le_total 0 r with hr | hr <;> rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hr, abs_of_nonneg hs]
  · rw [abs_of_nonneg hr, abs_of_nonpos hs, twoSampleField_neg_right]
  · rw [abs_of_nonpos hr, abs_of_nonneg hs, twoSampleField_neg_left]
  · rw [abs_of_nonpos hr, abs_of_nonpos hs, twoSampleField_neg_left, twoSampleField_neg_right]

lemma integral_sign_pair {μ : MeasureTheory.Measure ℝ} {f : ℝ → ℝ}
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hf : MeasureTheory.Integrable f μ) :
    (∫ x, f x ∂μ) = ∫ x, (f x + f (-x)) / 2 ∂μ := by
  have hpres : MeasureTheory.MeasurePreserving (fun x : ℝ => -x) μ μ :=
    ⟨measurable_neg, hsym⟩
  have hneg : MeasureTheory.Integrable (fun x => f (-x)) μ :=
    (hpres.integrable_comp hf.aestronglyMeasurable).mpr hf
  have hi := hpres.integral_comp (MeasurableEquiv.neg ℝ).measurableEmbedding f
  rw [MeasureTheory.integral_div, MeasureTheory.integral_add hf hneg, hi]
  ring

end LongTails.Proofs.AdaptiveHistoryField
