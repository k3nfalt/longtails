import LongTails.Proofs.AdamHeavyTailedAlgebra
import LongTails.Proofs.AdamHeavyTailedNormalizer
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.AdamHeavyTailedCancellation

noncomputable def tailIndicator (r z : ℝ) : ℝ := if r < |z| then 1 else 0

lemma tailIndicator_nonneg (r z : ℝ) : 0 ≤ tailIndicator r z := by
  unfold tailIndicator
  split_ifs <;> norm_num

lemma tailIndicator_le_one (r z : ℝ) : tailIndicator r z ≤ 1 := by
  unfold tailIndicator
  split_ifs <;> norm_num

lemma measurable_tailIndicator (r : ℝ) : Measurable (tailIndicator r) := by
  unfold tailIndicator
  exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
    measurable_const measurable_const

lemma tailIndicator_le_moment {r p z : ℝ} (hr : 0 < r) (hp : 0 ≤ p) :
    tailIndicator r z ≤ |z| ^ p / r ^ p := by
  unfold tailIndicator
  split_ifs with h
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hr p)).2
    simpa using Real.rpow_le_rpow hr.le h.le hp
  · positivity

lemma integrable_tailIndicator {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Measurable X) (r : ℝ) :
    Integrable (fun ω => tailIndicator r (X ω)) P := by
  apply Integrable.of_bound ((measurable_tailIndicator r).comp hX).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun ω => by
    change ‖tailIndicator r (X ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (tailIndicator_nonneg _ _)]
    exact tailIndicator_le_one _ _

lemma integral_tailIndicator_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Measurable X) {r p : ℝ}
    (hr : 0 < r) (hp : 0 ≤ p) (hi : Integrable (fun ω => |X ω| ^ p) P) :
    (∫ ω, tailIndicator r (X ω) ∂P) ≤ (∫ ω, |X ω| ^ p ∂P) / r ^ p := by
  rw [← integral_div]
  exact integral_mono (integrable_tailIndicator hX r) (hi.div_const _)
    (fun _ => tailIndicator_le_moment hr hp)

lemma two_tail_integral_le {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : Ω → ℝ} {Y : Ω → Ξ → ℝ} (hX : Measurable X)
    (hY : Measurable (Function.uncurry Y)) {r p M : ℝ}
    (hr : 0 < r) (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hXi : Integrable (fun ω => |X ω| ^ p) P)
    (hYi : ∀ ω, Integrable (fun z => |Y ω z| ^ p) Q)
    (hYm : ∀ ω, (∫ z, |Y ω z| ^ p ∂Q) ≤ M) :
    (∫ ω, tailIndicator r (X ω) * (∫ z, tailIndicator r (Y ω z) ∂Q) ∂P) ≤
      M * (∫ ω, |X ω| ^ p ∂P) / (r ^ p) ^ 2 := by
  let C : Ω → ℝ := fun ω => ∫ z, tailIndicator r (Y ω z) ∂Q
  have hC : Measurable C :=
    ((measurable_tailIndicator r).comp hY).stronglyMeasurable.integral_prod_right'.measurable
  have hCy (ω : Ω) : Measurable (Y ω) := hY.comp (measurable_const.prodMk measurable_id)
  have hC0 (ω : Ω) : 0 ≤ C ω := integral_nonneg fun _ => tailIndicator_nonneg _ _
  have hC1 (ω : Ω) : C ω ≤ 1 := by
    calc
      C ω ≤ ∫ _z, (1 : ℝ) ∂Q := integral_mono
        (integrable_tailIndicator (hCy ω) r) (integrable_const _) (fun _ => tailIndicator_le_one _ _)
      _ = 1 := by simp
  have hCb (ω : Ω) : C ω ≤ M / r ^ p := by
    exact (integral_tailIndicator_le (hCy ω) hr hp (hYi ω)).trans
      (div_le_div_of_nonneg_right (hYm ω) (Real.rpow_nonneg hr.le _))
  have hprod : Integrable (fun ω => tailIndicator r (X ω) * C ω) P := by
    apply Integrable.of_bound (((measurable_tailIndicator r).comp hX).mul hC).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by
      change ‖tailIndicator r (X ω) * C ω‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (tailIndicator_nonneg _ _) (hC0 ω))]
      calc
        tailIndicator r (X ω) * C ω ≤ tailIndicator r (X ω) * 1 :=
          mul_le_mul_of_nonneg_left (hC1 ω) (tailIndicator_nonneg _ _)
        _ ≤ 1 := by simpa using tailIndicator_le_one r (X ω)
  calc
    _ ≤ ∫ ω, tailIndicator r (X ω) * (M / r ^ p) ∂P :=
      integral_mono hprod ((integrable_tailIndicator hX r).mul_const _)
        (fun ω => mul_le_mul_of_nonneg_left (hCb ω) (tailIndicator_nonneg _ _))
    _ = (∫ ω, tailIndicator r (X ω) ∂P) * (M / r ^ p) := integral_mul_const _ _
    _ ≤ ((∫ ω, |X ω| ^ p ∂P) / r ^ p) * (M / r ^ p) :=
      mul_le_mul_of_nonneg_right (integral_tailIndicator_le hX hr hp hXi) (by positivity)
    _ = _ := by ring

lemma integrable_ratio_square {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {D : Ω → ℝ} (hD : Measurable D) {μ τ : ℝ}
    (hτ : 0 < τ) (hbound : ∀ ω, τ ≤ D ω) :
    Integrable (fun ω => μ ^ 2 / (D ω) ^ 2) P := by
  apply Integrable.of_bound ((measurable_const.div (hD.pow_const 2)).aestronglyMeasurable) (μ ^ 2 / τ ^ 2)
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    apply div_le_div_of_nonneg_left (sq_nonneg μ) (sq_pos_of_pos hτ)
    exact pow_le_pow_left₀ hτ.le (hbound ω) 2

lemma two_observation_integral {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : Ω → ℝ} {Y D : Ω → Ξ → ℝ} (hX : Measurable X)
    (hY : Measurable (Function.uncurry Y)) (hD : Measurable (Function.uncurry D))
    {μ A τ r p M : ℝ} (hμ : μ ≠ 0) (hτ : 0 < τ) (hτA : τ ≤ A)
    (hr : 0 ≤ r) (hp : 0 ≤ p) (hM : 0 ≤ M)
    (hAd : ∀ ω z, A ≤ D ω z)
    (h₀ : ∀ ω z, r * |μ + X ω| ≤ D ω z)
    (h₁ : ∀ ω z, r * |μ + Y ω z| ≤ D ω z)
    (hXi : Integrable (fun ω => |X ω| ^ p) P)
    (hYi : ∀ ω, Integrable (fun z => |Y ω z| ^ p) Q)
    (hYm : ∀ ω, (∫ z, |Y ω z| ^ p ∂Q) ≤ M) :
    (∫ ω, ∫ z, μ ^ 2 / (D ω z) ^ 2 ∂Q ∂P) ≤
      3 * μ ^ 2 / (τ * (A + r * |μ|)) +
        (μ ^ 2 / A ^ 2) * (M * (∫ ω, |X ω| ^ p ∂P) / ((|μ| / 2) ^ p) ^ 2) := by
  let B := 3 * μ ^ 2 / (τ * (A + r * |μ|))
  let C := μ ^ 2 / A ^ 2
  let I : Ω → ℝ := fun ω => ∫ z, tailIndicator (|μ| / 2) (Y ω z) ∂Q
  have hA : 0 < A := hτ.trans_le hτA
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hIy (ω : Ω) := integrable_tailIndicator (P := Q)
    (hY.comp (measurable_const.prodMk measurable_id) : Measurable (Y ω)) (|μ| / 2)
  have hI : Measurable I :=
    ((measurable_tailIndicator (|μ| / 2)).comp hY).stronglyMeasurable.integral_prod_right'.measurable
  have hI0 (ω : Ω) : 0 ≤ I ω := integral_nonneg fun _ => tailIndicator_nonneg _ _
  have hI1 (ω : Ω) : I ω ≤ 1 := by
    calc
      I ω ≤ ∫ _z, (1 : ℝ) ∂Q := integral_mono (hIy ω) (integrable_const _)
        (fun _ => tailIndicator_le_one _ _)
      _ = 1 := by simp
  have hprod : Integrable (fun ω => tailIndicator (|μ| / 2) (X ω) * I ω) P := by
    apply Integrable.of_bound (((measurable_tailIndicator (|μ| / 2)).comp hX).mul hI).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun ω => by
      change ‖tailIndicator (|μ| / 2) (X ω) * I ω‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (tailIndicator_nonneg _ _) (hI0 ω))]
      exact (mul_le_mul (tailIndicator_le_one _ _) (hI1 ω) (hI0 ω) (by norm_num)).trans_eq (by ring)
  have hpoint (ω : Ω) (z : Ξ) : μ ^ 2 / (D ω z) ^ 2 ≤
      B + C * (tailIndicator (|μ| / 2) (X ω) * tailIndicator (|μ| / 2) (Y ω z)) := by
    have hb := AdamHeavyTailedAlgebra.two_observation_ratio hτ hτA (hAd ω z) hr (h₀ ω z) (h₁ ω z)
    apply hb.trans
    dsimp [B, C, tailIndicator]
    split_ifs <;> simp_all
    positivity
  have hinner (ω : Ω) : (∫ z, μ ^ 2 / (D ω z) ^ 2 ∂Q) ≤
      B + C * (tailIndicator (|μ| / 2) (X ω) * I ω) := by
    have hd := integrable_ratio_square (P := Q) (μ := μ)
      (hD.comp (measurable_const.prodMk measurable_id) : Measurable (D ω)) hτ
      (fun z => hτA.trans (hAd ω z))
    have hi : Integrable (fun z => C * (tailIndicator (|μ| / 2) (X ω) *
        tailIndicator (|μ| / 2) (Y ω z))) Q :=
      ((hIy ω).const_mul (tailIndicator (|μ| / 2) (X ω))).const_mul C
    have hb := integral_mono hd ((integrable_const B).add hi) (hpoint ω)
    change (∫ z, μ ^ 2 / (D ω z) ^ 2 ∂Q) ≤
      ∫ z, B + C * (tailIndicator (|μ| / 2) (X ω) * tailIndicator (|μ| / 2) (Y ω z)) ∂Q at hb
    simpa only [integral_add (integrable_const B) hi, integral_const, probReal_univ,
      one_smul, integral_const_mul, I] using hb
  have hdint : Integrable (fun ω => ∫ z, μ ^ 2 / (D ω z) ^ 2 ∂Q) P := by
    apply Integrable.of_bound ((measurable_const.div (hD.pow_const 2)).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable) (μ ^ 2 / τ ^ 2)
    exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => div_nonneg (sq_nonneg _) (sq_nonneg _)))]
      calc
        _ ≤ ∫ _z, μ ^ 2 / τ ^ 2 ∂Q := integral_mono
          (integrable_ratio_square (hD.comp (measurable_const.prodMk measurable_id)) hτ
            (fun z => hτA.trans (hAd ω z))) (integrable_const _) (fun z => by
              apply div_le_div_of_nonneg_left (sq_nonneg μ) (sq_pos_of_pos hτ)
              exact pow_le_pow_left₀ hτ.le (hτA.trans (hAd ω z)) 2)
        _ = μ ^ 2 / τ ^ 2 := by simp
  have hb := integral_mono hdint ((integrable_const B).add (hprod.const_mul C)) hinner
  change _ ≤ ∫ ω, B + C * (tailIndicator (|μ| / 2) (X ω) * I ω) ∂P at hb
  rw [integral_add (integrable_const B) (hprod.const_mul C), integral_const,
    probReal_univ, one_smul, integral_const_mul] at hb
  exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (two_tail_integral_le hX hY (by positivity : 0 < |μ| / 2) hp hM hXi hYi hYm) hC))

lemma centered_remainder_bias {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} {φ : ℝ → ℝ} {a C p : ℝ}
    (hX : Integrable X P) (hmean : ∫ ω, X ω ∂P = 0)
    (hφ : Integrable (fun ω => φ (X ω)) P)
    (hm : Integrable (fun ω => |X ω| ^ p) P)
    (hrem : ∀ z, |φ z - φ 0 - a * z| ≤ C * |z| ^ p) :
    |(∫ ω, φ (X ω) ∂P) - φ 0| ≤ C * ∫ ω, |X ω| ^ p ∂P := by
  have hb := norm_integral_le_of_norm_le (hm.const_mul C)
    (f := fun ω => φ (X ω) - φ 0 - a * X ω)
    (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using hrem (X ω))
  have hconst : Integrable (fun _ : Ω => φ 0) P := integrable_const _
  have hsub : Integrable (fun ω => φ (X ω) - φ 0) P := hφ.sub hconst
  rw [integral_sub hsub (hX.const_mul a),
    integral_sub hφ hconst, integral_const, integral_const_mul,
    hmean, mul_zero, sub_zero, integral_const_mul] at hb
  simpa only [probReal_univ, one_smul, Real.norm_eq_abs] using hb

lemma integrable_normalized_line {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) (x v : E)
    {τ : ℝ} (hτ : 0 < τ) {X : Ω → ℝ} (hX : AEStronglyMeasurable X P) :
    Integrable (fun ω => ℓ (x + X ω • v) / (‖x + X ω • v‖ + τ)) P := by
  have hc : Continuous (fun z : ℝ => ℓ (x + z • v) / (‖x + z • v‖ + τ)) := by
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro z
    exact ne_of_gt (by positivity)
  apply Integrable.of_bound (hc.comp_aestronglyMeasurable hX) 1
  exact Filter.Eventually.of_forall fun ω => by
    change ‖ℓ (x + X ω • v) / (‖x + X ω • v‖ + τ)‖ ≤ 1
    rw [norm_div, Real.norm_eq_abs (‖x + X ω • v‖ + τ), abs_of_pos (by positivity)]
    apply (div_le_one (by positivity : 0 < ‖x + X ω • v‖ + τ)).2
    calc
      ‖ℓ (x + X ω • v)‖ ≤ ‖ℓ‖ * ‖x + X ω • v‖ := ℓ.le_opNorm _
      _ ≤ 1 * ‖x + X ω • v‖ := mul_le_mul_of_nonneg_right hℓ (norm_nonneg _)
      _ ≤ ‖x + X ω • v‖ + τ := by linarith

lemma normalized_line_bias {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) (x v : E)
    {τ A p : ℝ} (hτ : 0 < τ) (hA : 0 < A)
    (hAx : A ≤ ‖x‖ + τ) (hAv : ∀ z : ℝ, A ≤ ‖x + z • v‖ + τ)
    (hp : 1 ≤ p) (hp2 : p ≤ 2) {X : Ω → ℝ}
    (hX : Integrable X P) (hmean : ∫ ω, X ω ∂P = 0)
    (hm : Integrable (fun ω => |X ω| ^ p) P) :
    |(∫ ω, ℓ (x + X ω • v) / (‖x + X ω • v‖ + τ) ∂P) -
      ℓ x / (‖x‖ + τ)| ≤ (4 * (‖v‖ / A) ^ p) * ∫ ω, |X ω| ^ p ∂P := by
  have hφ := integrable_normalized_line ℓ hℓ x v hτ hX.aestronglyMeasurable
  let a := ℓ v / (‖x‖ + τ) - ℓ x * ⟪x, v⟫ / (‖x‖ * (‖x‖ + τ) ^ 2)
  have hb := centered_remainder_bias (φ := fun z => ℓ (x + z • v) / (‖x + z • v‖ + τ))
    (a := a) hX hmean hφ hm (fun z => by
      simpa only [zero_smul, add_zero] using
        AdamHeavyTailedNormalizer.normalized_line_taylor ℓ hℓ x v hτ hA hAx hAv hp hp2 z)
  simpa only [zero_smul, add_zero] using hb

lemma two_observation_integral_uniform {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {X : Ω → ℝ} {Y D : Ω → Ξ → ℝ} (hX : Measurable X)
    (hY : Measurable (Function.uncurry Y)) (hD : Measurable (Function.uncurry D))
    {μ A τ r r0 p M : ℝ} (hτ : 0 < τ) (hτA : τ ≤ A)
    (hr : 0 ≤ r) (hr0 : 0 < r0) (hp : 1 ≤ p) (hp2 : p ≤ 2) (hM : 0 ≤ M)
    (hscale : M * r0 ^ p ≤ A ^ 2 * r0 ^ 2) (hrr0 : r ≤ A * r0)
    (hAd : ∀ ω z, A ≤ D ω z)
    (h₀ : ∀ ω z, r * |μ + X ω| ≤ D ω z)
    (h₁ : ∀ ω z, r * |μ + Y ω z| ≤ D ω z)
    (hXi : Integrable (fun ω => |X ω| ^ p) P)
    (hYi : ∀ ω, Integrable (fun z => |Y ω z| ^ p) Q)
    (hYm : ∀ ω, (∫ z, |Y ω z| ^ p ∂Q) ≤ M) :
    (∫ ω, ∫ z, μ ^ 2 / (D ω z) ^ 2 ∂Q ∂P) ≤
      3 * μ ^ 2 / (τ * (A + r * |μ|)) + 16 * (∫ ω, |X ω| ^ p ∂P) * r0 ^ p := by
  have hA : 0 < A := hτ.trans_le hτA
  have hH : 0 < A + r * |μ| := by positivity
  have hm0 : 0 ≤ ∫ ω, |X ω| ^ p ∂P := integral_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _
  by_cases hsmall : r * |μ| ≤ A
  · have hi := integrable_ratio_square (P := P.prod Q) (μ := μ) hD hτ
      (fun z => hτA.trans (hAd z.1 z.2))
    have hpw (z : Ω × Ξ) : μ ^ 2 / (D z.1 z.2) ^ 2 ≤ 3 * μ ^ 2 / (τ * (A + r * |μ|)) := by
      apply AdamHeavyTailedAlgebra.inverse_square_le hτ hH (hA.trans_le (hAd z.1 z.2))
        (hτA.trans (hAd z.1 z.2))
      linarith [hAd z.1 z.2]
    have hh := integral_mono hi (integrable_const _) hpw
    rw [integral_prod _ hi, integral_const, probReal_univ, one_smul] at hh
    exact hh.trans (le_add_of_nonneg_right (by positivity))
  · have hx : 0 < |μ| := by
      by_contra hn
      have he : |μ| = 0 := le_antisymm (le_of_not_gt hn) (abs_nonneg _)
      simp [he] at hsmall
      linarith
    have hlarge : 1 ≤ r0 * |μ| := by
      have hh := mul_le_mul_of_nonneg_right hrr0 (abs_nonneg μ)
      nlinarith
    have htail := AdamHeavyTailedAlgebra.two_tail_scaling hx hA hr0 hm0 hp hp2 hlarge hscale
    rw [sq_abs] at htail
    exact (two_observation_integral hX hY hD (abs_pos.mp hx) hτ hτA hr (by linarith) hM
      hAd h₀ h₁ hXi hYi hYm).trans (add_le_add le_rfl htail)

end LongTails.Proofs.AdamHeavyTailedCancellation
