import LongTails.Proofs.KernelPerceptronBridge
import LongTails.Proofs.ClusteredConvolutionalPerceptronInstances

open scoped RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace LongTails.Proofs.KernelPerceptronInstances

open LongTails.Setups.KernelConvolutionalPerceptron
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift)
open ManySampleConvolutionalPerceptronGeometry (minusFeature)
open KernelPerceptronGeometry

variable {d n : ℕ} {D : Data d n} {g R μ κ : ℝ}

lemma highPass_two (u : Features d) : highPass 2 u = minusFeature u := by
  unfold highPass minusFeature
  have h2 : (1 - ((2 : ℕ) : ℝ)⁻¹) = 1 / 2 := by norm_num
  have h1 : shifted 1 u = shift u := shifted_succ 0 u
  rw [h2, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, shifted_zero, h1, Nat.cast_ofNat]
  have hs : (Real.sqrt (1 / 2))⁻¹ = Real.sqrt 2 := by
    rw [one_div, Real.sqrt_inv, inv_inv]
  rw [hs]
  have h3 : Real.sqrt 2 = 2 * (Real.sqrt 2)⁻¹ := by
    have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    field_simp
    linarith
  conv_lhs => rw [h3]
  module

lemma two_thirds_le : (2 / 3 : ℝ) ≤ (Real.sqrt ((2 : ℕ) : ℝ))⁻¹ := by
  rw [Nat.cast_ofNat, le_inv_comm₀ (by norm_num) (by positivity), Real.sqrt_le_left (by norm_num)]
  norm_num

noncomputable def ofClustered
    (G : LongTails.Setups.ClusteredConvolutionalPerceptron.Geometry D g R μ κ)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1 / 4) : Geometry 2 D g R μ κ where
  background := G.background
  defect := G.defect
  separator := ‖minusFeature G.center‖⁻¹ • minusFeature G.center
  sample_eq := G.sample_eq
  background_lower := G.background_lower
  background_upper := G.background_upper
  centered := G.centered
  defect_norm := fun i =>
    (ClusteredConvolutionalPerceptronGeometry.defect_norm G hκ1 i).trans two_thirds_le
  separator_unit := by
    have hpos : 0 < ‖minusFeature G.center‖ := by
      have := G.derivative_lower
      change 2 * κ ≤ ‖minusFeature G.center‖ at this
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']
  derivative_margin := by
    intro i
    rw [highPass_two]
    have hpos : 0 < ‖minusFeature G.center‖ := by
      have := G.derivative_lower
      change 2 * κ ≤ ‖minusFeature G.center‖ at this
      linarith
    have hlow : 2 * κ ≤ ‖minusFeature G.center‖ := G.derivative_lower
    have hclose := ClusteredConvolutionalPerceptronGeometry.minus_close G hκ i
    have hunit : ⟪‖minusFeature G.center‖⁻¹ • minusFeature G.center, minusFeature G.center⟫ =
        ‖minusFeature G.center‖ := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    have hdiff : |⟪‖minusFeature G.center‖⁻¹ • minusFeature G.center,
        minusFeature (G.defect i) - minusFeature G.center⟫| ≤ κ / 32 := by
      calc _ ≤ ‖‖minusFeature G.center‖⁻¹ • minusFeature G.center‖ *
            ‖minusFeature (G.defect i) - minusFeature G.center‖ := abs_real_inner_le_norm _ _
        _ = ‖minusFeature (G.defect i) - minusFeature G.center‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
              inv_mul_cancel₀ hpos.ne', one_mul]
        _ ≤ κ / 32 := hclose
    have hsplit : ⟪‖minusFeature G.center‖⁻¹ • minusFeature G.center, minusFeature (G.defect i)⟫ =
        ‖minusFeature G.center‖ + ⟪‖minusFeature G.center‖⁻¹ • minusFeature G.center,
          minusFeature (G.defect i) - minusFeature G.center⟫ := by
      rw [inner_sub_right, hunit]; ring
    change κ ≤ ⟪‖minusFeature G.center‖⁻¹ • minusFeature G.center, minusFeature (G.defect i)⟫
    rw [hsplit]
    linarith [neg_abs_le ⟪‖minusFeature G.center‖⁻¹ • minusFeature G.center,
      minusFeature (G.defect i) - minusFeature G.center⟫]

open ClusteredConvolutionalPerceptronInstances

noncomputable def familyGeometry (n : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    Geometry 2 (dataset n μ) (Real.sqrt 2) (2 * Real.sqrt 2) μ (1 / 8) :=
  ofClustered (ClusteredConvolutionalPerceptronInstances.familyGeometry n hμ hμ1)
    (by norm_num) (by norm_num)

noncomputable def parameters (n : ℕ) (μ : ℝ) : Params :=
  ⟨2 * n + 4, 2, 2 * n + 1, Real.sqrt 2, 2 * Real.sqrt 2, μ, 1 / 8⟩

lemma log_le_four_sqrt_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ 4 * Real.sqrt (Real.sqrt x) := by
  have h1 : Real.log x = 4 * Real.log (Real.sqrt (Real.sqrt x)) := by
    rw [Real.log_sqrt (Real.sqrt_nonneg x), Real.log_sqrt hx.le]; ring
  rw [h1]
  have h2 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx))
  linarith

lemma parameters_valid (n : ℕ) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 10 ^ 24) :
    spec.valid (parameters n μ) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hμ1' : μ ≤ 1 := by
    have : (1 : ℝ) / 10 ^ 24 ≤ 1 := by norm_num
    linarith
  refine ⟨by show 0 < 2 * n + 4; omega, le_refl _, hs,
    by show Real.sqrt 2 ≤ 2 * Real.sqrt 2; linarith, hμ,
    by show μ ≤ 2 * Real.sqrt 2; nlinarith, by show (0 : ℝ) < 1 / 8; norm_num,
    by show (1 / 8 : ℝ) ≤ 1; norm_num, ?_⟩
  change μ ^ 2 * (2 * Real.sqrt 2 / Real.sqrt 2) ^ 4 *
    Real.log (128 * ((2 : ℕ) : ℝ) * (2 * Real.sqrt 2) ^ 2 / ((1 / 8) * μ) ^ 2) ^ 2 ≤
    ((2 : ℕ) : ℝ) * (1 / 8) ^ 6 * (2 * Real.sqrt 2) ^ 2 / 10 ^ 13
  have h4 : (2 * Real.sqrt 2 / Real.sqrt 2) ^ 4 = 16 := by
    rw [mul_div_assoc, div_self hs.ne']; norm_num
  have h8 : (2 * Real.sqrt 2) ^ 2 = 8 := by rw [mul_pow, hs2]; norm_num
  rw [h4, h8]
  push_cast
  have hx : (128 * 2 * 8 / ((1 / 8) * μ) ^ 2 : ℝ) = 131072 / μ ^ 2 := by
    field_simp; ring
  rw [hx]
  have hpos : (0 : ℝ) < 131072 / μ ^ 2 := by positivity
  have hlog := log_le_four_sqrt_sqrt hpos
  have hlog0 : 0 ≤ Real.log (131072 / μ ^ 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hsq1 : Real.sqrt (131072 / μ ^ 2) ≤ 363 / μ := by
    rw [Real.sqrt_le_left (by positivity), div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg μ]
  have hsq2 : Real.sqrt (Real.sqrt (131072 / μ ^ 2)) ≤ 20 / Real.sqrt μ := by
    calc Real.sqrt (Real.sqrt (131072 / μ ^ 2)) ≤ Real.sqrt (363 / μ) := Real.sqrt_le_sqrt hsq1
      _ ≤ 20 / Real.sqrt μ := by
          rw [Real.sqrt_le_left (by positivity), div_pow, Real.sq_sqrt hμ.le]
          apply div_le_div_of_nonneg_right _ hμ.le
          norm_num
  have hL : Real.log (131072 / μ ^ 2) ≤ 4 * (20 / Real.sqrt μ) := by linarith
  have hL2 : Real.log (131072 / μ ^ 2) ^ 2 ≤ (4 * (20 / Real.sqrt μ)) ^ 2 :=
    pow_le_pow_left₀ hlog0 hL 2
  have hL3 : (4 * (20 / Real.sqrt μ)) ^ 2 = 6400 / μ := by
    rw [mul_pow, div_pow, Real.sq_sqrt hμ.le]; ring
  rw [hL3] at hL2
  have hmain : μ ^ 2 * 16 * (6400 / μ) ≤ 2 * (1 / 8) ^ 6 * 8 / 10 ^ 13 := by
    have : μ ^ 2 * 16 * (6400 / μ) = 102400 * μ := by field_simp; ring
    rw [this]
    nlinarith
  calc μ ^ 2 * 16 * Real.log (131072 / μ ^ 2) ^ 2 ≤ μ ^ 2 * 16 * (6400 / μ) := by
        apply mul_le_mul_of_nonneg_left hL2 (by positivity)
    _ ≤ _ := hmain

lemma parameters_admissible (n : ℕ) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≤ 1 / 10 ^ 24) :
    Nonempty (Geometry (parameters n μ).kernel (dataset n μ) (parameters n μ).lower
      (parameters n μ).upper (parameters n μ).contrast (parameters n μ).derivativeMargin) :=
  ⟨familyGeometry n hμ.le (by
    have : (1 : ℝ) / 10 ^ 24 ≤ 1 := by norm_num
    linarith)⟩


section Unaligned

open LongTails.Setups.TwoSampleQuadraticPerceptron (shift)
open TwoSampleQuadraticPerceptronEmbedding
open ClusteredConvolutionalPerceptronInstances (unitVector unit_norm unit_axis_inner)

noncomputable def alt (d : ℕ) : Features d := WithLp.toLp 2 fun i => (-1 : ℝ) ^ (i : ℕ)

lemma alt_apply {d : ℕ} (i : Fin d) : alt d i = (-1 : ℝ) ^ (i : ℕ) := rfl

lemma features_inner_eq_sum {d : ℕ} (x y : Features d) : ⟪x, y⟫ = ∑ i, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

lemma sum_neg_one_pow (m : ℕ) :
    ∑ j ∈ Finset.range m, (-1 : ℝ) ^ j = if Even m then 0 else 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hm : Even m
    · have h1 : ¬ Even (m + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hm
      simp [hm, h1, hm.neg_one_pow]
    · have h1 : Even (m + 1) := by rw [Nat.even_add_one]; exact hm
      simp [hm, h1, (Nat.not_even_iff_odd.mp hm).neg_one_pow]

lemma sum_fin_neg_one_pow (m : ℕ) :
    ∑ j : Fin m, (-1 : ℝ) ^ (j : ℕ) = if Even m then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (-1 : ℝ) ^ j) m]
  exact sum_neg_one_pow m

lemma alt_norm_sq (d : ℕ) : ‖alt d‖ ^ 2 = d := by
  rw [← real_inner_self_eq_norm_sq, features_inner_eq_sum]
  have h : ∀ i : ℕ, (-1 : ℝ) ^ i * (-1) ^ i = 1 := fun i => by
    rw [← pow_add, ← two_mul]; exact Even.neg_one_pow (even_two_mul i)
  simp only [alt_apply, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]

lemma alt_norm (d : ℕ) : ‖alt d‖ = Real.sqrt d := by
  rw [← Real.sqrt_sq (norm_nonneg _), alt_norm_sq]

lemma alt_axis_inner (n : ℕ) : ⟪axis (2 * n + 4), alt (2 * n + 4)⟫ = 0 := by
  rw [features_inner_eq_sum]
  have h : ∀ i : Fin (2 * n + 4), axis (2 * n + 4) i * alt (2 * n + 4) i =
      (Real.sqrt ((2 * n + 4 : ℕ) : ℝ))⁻¹ * (-1 : ℝ) ^ (i : ℕ) := by
    intro i
    simp [axis, LongTails.Setups.ManySampleConvolutionalPerceptron.axis,
      LongTails.Setups.TwoSampleQuadraticPerceptron.ones, alt]
  have he : Even (2 * n + 4) := ⟨n + 2, by ring⟩
  simp only [h, ← Finset.mul_sum, sum_fin_neg_one_pow]
  simp [he]

lemma alt_shift (n : ℕ) : shift (alt (2 * n + 4)) = -alt (2 * n + 4) := by
  ext j
  rw [shift_apply]
  obtain ⟨i, rfl⟩ : ∃ i, j = finRotate (2 * n + 4) i :=
    ⟨(finRotate _).symm j, (Equiv.apply_symm_apply _ _).symm⟩
  rw [Equiv.symm_apply_apply]
  simp only [PiLp.neg_apply, alt_apply]
  by_cases hi : i = Fin.last (2 * n + 3)
  · rw [hi, finRotate_last, Fin.val_zero, Fin.val_last, pow_zero,
      Odd.neg_one_pow (⟨n + 1, by ring⟩ : Odd (2 * n + 3))]
  · rw [coe_finRotate_of_ne_last hi, pow_succ]
    ring

lemma alt_inner_shift (n : ℕ) (y : Features (2 * n + 4)) :
    ⟪alt (2 * n + 4), shift y⟫ = -⟪alt (2 * n + 4), y⟫ := by
  have h : ∀ i, alt (2 * n + 4) (finRotate (2 * n + 4) i) = -alt (2 * n + 4) i := by
    intro i
    have := congrArg (fun v : Features (2 * n + 4) => v (finRotate (2 * n + 4) i)) (alt_shift n)
    simp only [shift_apply, Equiv.symm_apply_apply, PiLp.neg_apply] at this
    linarith
  rw [features_inner_eq_sum, features_inner_eq_sum, ← Equiv.sum_comp (finRotate (2 * n + 4))]
  simp only [shift_apply, Equiv.symm_apply_apply, h, neg_mul, Finset.sum_neg_distrib]

lemma alt_inner_shifted (n : ℕ) (j : ℕ) (y : Features (2 * n + 4)) :
    ⟪alt (2 * n + 4), shifted j y⟫ = (-1) ^ j * ⟪alt (2 * n + 4), y⟫ := by
  induction j with
  | zero => simp [shifted_zero]
  | succ j ih => rw [shifted_succ, alt_inner_shift, ih, pow_succ]; ring

lemma alt_inner_highPass (n k : ℕ) (u : Features (2 * n + 4)) :
    ⟪alt (2 * n + 4), highPass k u⟫ =
      (Real.sqrt (1 - (k : ℝ)⁻¹))⁻¹ * (1 - (if Even k then 0 else 1) / k) *
        ⟪alt (2 * n + 4), u⟫ := by
  unfold highPass
  rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right, inner_sum]
  simp only [alt_inner_shifted]
  rw [← Finset.sum_mul, sum_fin_neg_one_pow]
  ring

lemma highPass_factor_ge (k : ℕ) (hk : 2 ≤ k) :
    (1 / 2 : ℝ) ≤ (Real.sqrt (1 - (k : ℝ)⁻¹))⁻¹ * (1 - (if Even k then 0 else 1) / k) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hinv : (k : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (by positivity) (by norm_num)]; simpa using hk2
  have hpos : 0 < 1 - (k : ℝ)⁻¹ := by linarith
  have hs1 : Real.sqrt (1 - (k : ℝ)⁻¹) ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith [inv_pos.mpr (show (0:ℝ) < k by linarith)]
  have hs0 : 0 < Real.sqrt (1 - (k : ℝ)⁻¹) := Real.sqrt_pos.mpr hpos
  have h1 : 1 ≤ (Real.sqrt (1 - (k : ℝ)⁻¹))⁻¹ := (one_le_inv₀ hs0).mpr hs1
  have h2 : (1 / 2 : ℝ) ≤ 1 - (if Even k then 0 else 1) / k := by
    split_ifs
    · norm_num
    · have e : (1 : ℝ) / k = (k : ℝ)⁻¹ := one_div _
      rw [e]; linarith
  calc (1 / 2 : ℝ) = 1 * (1 / 2) := by ring
    _ ≤ _ := mul_le_mul h1 h2 (by norm_num) (by linarith)

variable (n k : ℕ) (μ : ℝ)

noncomputable def unalignedSeparator : Features (2 * n + 4) :=
  (Real.sqrt ((2 * n + 4 : ℕ) : ℝ))⁻¹ • alt (2 * n + 4)

noncomputable def bump (i : Fin (n + 1)) : Features (2 * n + 4) :=
  (1 / 2 : ℝ) • (unitVector ⟨2 * i.val, by have := i.isLt; omega⟩ -
    unitVector ⟨2 * i.val + 2, by have := i.isLt; omega⟩)

noncomputable def unalignedResidual (i : Fin (n + 1)) : Features (2 * n + 4) :=
  (Real.sqrt k)⁻¹ • ((1 / 4 : ℝ) • unalignedSeparator n + (3 / 4 : ℝ) • bump n i)

noncomputable def unalignedBackground (i : Fin (n + 1)) : ℝ := (-1) ^ (i : ℕ) * Real.sqrt 2

noncomputable def unalignedDataset : Data (2 * n + 4) n := fun i =>
  (unalignedBackground n i / Real.sqrt 2) • axis (2 * n + 4) + μ • unalignedResidual n k i

lemma unalignedSeparator_unit : ‖unalignedSeparator n‖ = 1 := by
  have hd : (0 : ℝ) < ((2 * n + 4 : ℕ) : ℝ) := by positivity
  have hsd : 0 < Real.sqrt ((2 * n + 4 : ℕ) : ℝ) := Real.sqrt_pos.mpr hd
  rw [unalignedSeparator, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsd), alt_norm,
    inv_mul_cancel₀ hsd.ne']

lemma bump_norm (i : Fin (n + 1)) : ‖bump n i‖ ≤ 1 := by
  have h := norm_sub_le (unitVector (⟨2 * i.val, by have := i.isLt; omega⟩ : Fin (2 * n + 4)))
    (unitVector ⟨2 * i.val + 2, by have := i.isLt; omega⟩)
  rw [unit_norm, unit_norm] at h
  rw [bump, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  linarith

lemma bump_axis_inner (i : Fin (n + 1)) : ⟪axis (2 * n + 4), bump n i⟫ = 0 := by
  simp only [bump, real_inner_smul_right, inner_sub_right, unit_axis_inner, sub_self, mul_zero]

lemma bump_alt_inner (i : Fin (n + 1)) : ⟪alt (2 * n + 4), bump n i⟫ = 0 := by
  have h1 : ((-1 : ℝ)) ^ (2 * i.val) = 1 := Even.neg_one_pow (even_two_mul _)
  have h2 : ((-1 : ℝ)) ^ (2 * i.val + 2) = 1 := Even.neg_one_pow ⟨i.val + 1, by ring⟩
  simp only [bump, unitVector, real_inner_smul_right, inner_sub_right,
    EuclideanSpace.inner_single_right, conj_trivial, alt_apply, h1, h2]
  norm_num

lemma unalignedBackground_abs (i : Fin (n + 1)) : |unalignedBackground n i| = Real.sqrt 2 := by
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  rw [unalignedBackground, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hs]

lemma unalignedResidual_centered (i : Fin (n + 1)) :
    ⟪axis (2 * n + 4), unalignedResidual n k i⟫ = 0 := by
  simp only [unalignedResidual, unalignedSeparator, inner_add_right, real_inner_smul_right,
    alt_axis_inner, bump_axis_inner, mul_zero, add_zero]

lemma unalignedResidual_norm (hk : 2 ≤ k) (i : Fin (n + 1)) :
    ‖unalignedResidual n k i‖ ≤ (Real.sqrt k)⁻¹ := by
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
  have h1 := unalignedSeparator_unit n
  have h2 := bump_norm n i
  have h3 : ‖(1 / 4 : ℝ) • unalignedSeparator n + (3 / 4 : ℝ) • bump n i‖ ≤ 1 := by
    calc _ ≤ ‖(1 / 4 : ℝ) • unalignedSeparator n‖ + ‖(3 / 4 : ℝ) • bump n i‖ := norm_add_le _ _
      _ ≤ 1 := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4), abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4),
            h1]
          linarith
  rw [unalignedResidual, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsk)]
  calc (Real.sqrt k)⁻¹ * ‖(1 / 4 : ℝ) • unalignedSeparator n + (3 / 4 : ℝ) • bump n i‖
      ≤ (Real.sqrt k)⁻¹ * 1 := mul_le_mul_of_nonneg_left h3 (inv_pos.mpr hsk).le
    _ = (Real.sqrt k)⁻¹ := mul_one _

lemma unaligned_margin (hk : 2 ≤ k) (i : Fin (n + 1)) :
    (8 * Real.sqrt k)⁻¹ ≤ ⟪unalignedSeparator n, highPass k (unalignedResidual n k i)⟫ := by
  have hd : (0 : ℝ) < ((2 * n + 4 : ℕ) : ℝ) := by positivity
  have hsd : 0 < Real.sqrt ((2 * n + 4 : ℕ) : ℝ) := Real.sqrt_pos.mpr hd
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
  have hfac := highPass_factor_ge k hk
  have hdd : (Real.sqrt ((2 * n + 4 : ℕ) : ℝ))⁻¹ * ((2 * n + 4 : ℕ) : ℝ) =
      Real.sqrt ((2 * n + 4 : ℕ) : ℝ) := by
    have := Real.mul_self_sqrt hd.le
    field_simp
    linarith
  have halt : ⟪alt (2 * n + 4), unalignedResidual n k i⟫ =
      (Real.sqrt k)⁻¹ * (1 / 4) * Real.sqrt ((2 * n + 4 : ℕ) : ℝ) := by
    simp only [unalignedResidual, unalignedSeparator, inner_add_right, real_inner_smul_right,
      bump_alt_inner, mul_zero, add_zero, real_inner_self_eq_norm_sq, alt_norm_sq]
    rw [hdd]
    ring
  rw [unalignedSeparator, real_inner_smul_left, alt_inner_highPass, halt]
  set F := (Real.sqrt (1 - (k : ℝ)⁻¹))⁻¹ * (1 - (if Even k then 0 else 1) / k) with hF
  have hd' : (Real.sqrt ((2 * n + 4 : ℕ) : ℝ))⁻¹ * Real.sqrt ((2 * n + 4 : ℕ) : ℝ) = 1 :=
    inv_mul_cancel₀ hsd.ne'
  have hik : 0 < (Real.sqrt (k : ℝ))⁻¹ := inv_pos.mpr hsk
  have e : (Real.sqrt ((2 * n + 4 : ℕ) : ℝ))⁻¹ *
      (F * ((Real.sqrt k)⁻¹ * (1 / 4) * Real.sqrt ((2 * n + 4 : ℕ) : ℝ))) =
      F * (Real.sqrt k)⁻¹ * (1 / 4) := by
    rw [show (Real.sqrt ((2 * n + 4 : ℕ) : ℝ))⁻¹ *
        (F * ((Real.sqrt k)⁻¹ * (1 / 4) * Real.sqrt ((2 * n + 4 : ℕ) : ℝ))) =
        F * (Real.sqrt k)⁻¹ * (1 / 4) *
          ((Real.sqrt ((2 * n + 4 : ℕ) : ℝ))⁻¹ * Real.sqrt ((2 * n + 4 : ℕ) : ℝ)) by ring, hd',
      mul_one]
  rw [e, mul_inv]
  nlinarith [mul_le_mul_of_nonneg_right hfac hik.le]

noncomputable def unalignedGeometry (hk : 2 ≤ k) :
    Geometry k (unalignedDataset n k μ) (Real.sqrt 2) (Real.sqrt 2) μ (8 * Real.sqrt k)⁻¹ where
  background := unalignedBackground n
  defect := unalignedResidual n k
  separator := unalignedSeparator n
  sample_eq _ := rfl
  background_lower i := le_of_eq (unalignedBackground_abs n i).symm
  background_upper i := le_of_eq (unalignedBackground_abs n i)
  centered := unalignedResidual_centered n k
  defect_norm := unalignedResidual_norm n k hk
  separator_unit := unalignedSeparator_unit n
  derivative_margin := unaligned_margin n k hk

noncomputable def unalignedParameters : Params :=
  ⟨2 * n + 4, k, n, Real.sqrt 2, Real.sqrt 2, μ, (8 * Real.sqrt k)⁻¹⟩

lemma unalignedParameters_valid (hk : 2 ≤ k) (hμ : 0 < μ) (hμ1 : μ ≤ 1 / (10 ^ 22 * k ^ 3)) :
    spec.valid (unalignedParameters n k μ) := by
  have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk0
  have hkk : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt hk0.le
  have hk0' : (k : ℝ) ≠ 0 := hk0.ne'
  have hμ' : μ ≠ 0 := hμ.ne'
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hk3 : (1 : ℝ) ≤ k ^ 3 := one_le_pow₀ (by linarith)
  have hμk : μ * (10 ^ 22 * k ^ 3) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hμ1; exact hμ1
  have hμ1' : μ ≤ 1 := by nlinarith
  have hκ : (8 * Real.sqrt k)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    have : 1 ≤ Real.sqrt (k : ℝ) := Real.one_le_sqrt.mpr (by linarith)
    linarith
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  refine ⟨by show 0 < 2 * n + 4; omega, hk, hs, le_refl _, hμ,
    by show μ ≤ Real.sqrt 2; linarith,
    by show (0 : ℝ) < (8 * Real.sqrt (k : ℝ))⁻¹; positivity, hκ, ?_⟩
  change μ ^ 2 * (Real.sqrt 2 / Real.sqrt 2) ^ 4 *
    Real.log (128 * (k : ℝ) * Real.sqrt 2 ^ 2 / ((8 * Real.sqrt k)⁻¹ * μ) ^ 2) ^ 2 ≤
    (k : ℝ) * ((8 * Real.sqrt k)⁻¹) ^ 6 * Real.sqrt 2 ^ 2 / 10 ^ 13
  have h6 : Real.sqrt (k : ℝ) ^ 6 = k ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hkk]
  rw [div_self hs.ne', one_pow, mul_one, hs2]
  simp only [inv_pow, mul_pow, hkk, h6]
  have hx : (128 * (k : ℝ) * 2 / (((8 : ℝ) ^ 2 * (k : ℝ))⁻¹ * μ ^ 2)) = 16384 * k ^ 2 / μ ^ 2 := by
    field_simp
    ring
  rw [hx]
  have hpos : (0 : ℝ) < 16384 * k ^ 2 / μ ^ 2 := by positivity
  have hlog := log_le_four_sqrt_sqrt hpos
  have hlog0 : 0 ≤ Real.log (16384 * k ^ 2 / μ ^ 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hsq1 : Real.sqrt (16384 * k ^ 2 / μ ^ 2) ≤ 128 * k / μ := by
    rw [Real.sqrt_le_left (by positivity), div_pow, mul_pow]
    norm_num
  have hsq2 : Real.sqrt (Real.sqrt (16384 * k ^ 2 / μ ^ 2)) ≤ 12 * Real.sqrt k / Real.sqrt μ := by
    calc Real.sqrt (Real.sqrt (16384 * k ^ 2 / μ ^ 2)) ≤ Real.sqrt (128 * k / μ) :=
          Real.sqrt_le_sqrt hsq1
      _ ≤ 12 * Real.sqrt k / Real.sqrt μ := by
          rw [Real.sqrt_le_left (by positivity), div_pow, mul_pow, hkk, Real.sq_sqrt hμ.le,
            div_le_div_iff₀ hμ hμ]
          have : 0 ≤ (k : ℝ) * μ := by positivity
          nlinarith
  have hL : Real.log (16384 * k ^ 2 / μ ^ 2) ≤ 4 * (12 * Real.sqrt k / Real.sqrt μ) := by linarith
  have hL2 : Real.log (16384 * k ^ 2 / μ ^ 2) ^ 2 ≤ (4 * (12 * Real.sqrt k / Real.sqrt μ)) ^ 2 :=
    pow_le_pow_left₀ hlog0 hL 2
  have hL3 : (4 * (12 * Real.sqrt (k : ℝ) / Real.sqrt μ)) ^ 2 = 2304 * k / μ := by
    rw [mul_pow, div_pow, mul_pow, hkk, Real.sq_sqrt hμ.le]; ring
  rw [hL3] at hL2
  have e1 : μ ^ 2 * (2304 * k / μ) = 2304 * k * μ := by
    field_simp
  have e2 : (k : ℝ) * ((8 : ℝ) ^ 6 * (k : ℝ) ^ 3)⁻¹ * 2 / 10 ^ 13 =
      2 * k / ((8 : ℝ) ^ 6 * (k : ℝ) ^ 3 * 10 ^ 13) := by
    ring
  have hmain : μ ^ 2 * (2304 * k / μ) ≤ (k : ℝ) * ((8 : ℝ) ^ 6 * (k : ℝ) ^ 3)⁻¹ * 2 / 10 ^ 13 := by
    rw [e1, e2, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hμk hk0.le, hk0]
  calc μ ^ 2 * Real.log (16384 * k ^ 2 / μ ^ 2) ^ 2 ≤ μ ^ 2 * (2304 * k / μ) :=
        mul_le_mul_of_nonneg_left hL2 (by positivity)
    _ ≤ _ := hmain

lemma unalignedParameters_admissible (hk : 2 ≤ k) :
    Nonempty (Geometry (unalignedParameters n k μ).kernel (unalignedDataset n k μ)
      (unalignedParameters n k μ).lower (unalignedParameters n k μ).upper
      (unalignedParameters n k μ).contrast (unalignedParameters n k μ).derivativeMargin) :=
  ⟨unalignedGeometry n k μ hk⟩

end Unaligned

end LongTails.Proofs.KernelPerceptronInstances
