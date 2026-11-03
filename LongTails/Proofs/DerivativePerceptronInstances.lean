import LongTails.Proofs.DerivativeConvolutionalPerceptronConvergence
import LongTails.Proofs.DerivativePerceptronLowerBound
import LongTails.Proofs.ClusteredConvolutionalPerceptronInstances

open scoped RealInnerProductSpace

namespace LongTails.Proofs.DerivativePerceptronInstances

open LongTails.Setups.DerivativeConvolutionalPerceptron
open LongTails.Setups.TwoSampleQuadraticPerceptron (shift)
open ClusteredConvolutionalPerceptronInstances (unitVector unit_norm unit_axis_inner)
open TwoSampleQuadraticPerceptronEmbedding

noncomputable def base (n : ℕ) : Features (2 * n + 10) :=
  (1 / 16 : ℝ) • (unitVector ⟨0, by omega⟩ - unitVector ⟨2 * n + 9, by omega⟩)

noncomputable def perturbation (n : ℕ) (j : Fin (n + 1)) : Features (2 * n + 10) :=
  (1 / 16 : ℝ) • (unitVector ⟨0, by omega⟩ + unitVector ⟨2 * n + 9, by omega⟩ -
    (2 : ℝ) • unitVector ⟨1, by omega⟩) +
  (1 / 4 : ℝ) • (unitVector ⟨3, by omega⟩ - unitVector ⟨4, by omega⟩) +
  (1 / 32 : ℝ) • (unitVector ⟨6 + 2 * j.val, by have := j.isLt; omega⟩ -
    unitVector ⟨7 + 2 * j.val, by have := j.isLt; omega⟩)

noncomputable def defect (n : ℕ) (j : Fin (n + 1)) (σ : ℝ) : Features (2 * n + 10) :=
  base n + σ • perturbation n j

lemma centered (n : ℕ) (j : Fin (n + 1)) (σ : ℝ) :
    ⟪axis (2 * n + 10), defect n j σ⟫ = 0 := by
  simp only [defect, base, perturbation, inner_add_right, inner_sub_right,
    real_inner_smul_right, unit_axis_inner]
  ring

set_option maxRecDepth 4096 in
lemma defect_zero (n : ℕ) (j : Fin (n + 1)) (σ : ℝ) :
    defect n j σ ⟨0, by omega⟩ = (1 + σ) / 16 := by
  have hj := j.isLt
  simp only [defect, base, perturbation, unitVector, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, PiLp.single_apply, Fin.mk.injEq]
  simp (disch := omega) only [ite_eq_right]
  norm_num
  ring

lemma defect_last (n : ℕ) (j : Fin (n + 1)) (σ : ℝ) :
    defect n j σ ⟨2 * n + 9, by omega⟩ = (-1 + σ) / 16 := by
  have hj := j.isLt
  norm_num [defect, base, perturbation, unitVector, Fin.ext_iff,
    show 0 ≠ 2 * n + 9 by omega, show 1 ≠ 2 * n + 9 by omega,
    show 3 ≠ 2 * n + 9 by omega, show 4 ≠ 2 * n + 9 by omega,
    show 6 + 2 * j.val ≠ 2 * n + 9 by omega, show 7 + 2 * j.val ≠ 2 * n + 9 by omega]
  ring

lemma derivative_projection (n : ℕ) (j : Fin (n + 1)) (σ : ℝ) :
    ⟪ManySampleConvolutionalPerceptronGeometry.minusFeature (defect n j σ),
      unitVector ⟨0, by omega⟩⟫ = Real.sqrt 2 / 16 := by
  have hprev : (finRotate (2 * n + 10)).symm (⟨0, by omega⟩ : Fin (2 * n + 10)) =
      ⟨2 * n + 9, by omega⟩ := by
    apply Fin.ext
    simp
  simp only [ManySampleConvolutionalPerceptronGeometry.minusFeature, unitVector,
    EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, shift_apply, hprev]
  rw [defect_zero, defect_last]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp
  nlinarith only [hs]

set_option maxRecDepth 4096 in
lemma defect_norm_sq (n : ℕ) (j : Fin (n + 1)) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    ‖defect n j σ‖ ^ 2 = 81 / 512 := by
  rw [← real_inner_self_eq_norm_sq]
  have hj := j.isLt
  simp only [defect, base, perturbation, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    unitVector, EuclideanSpace.inner_single_left, PiLp.single_apply, Fin.mk.injEq]
  simp (disch := omega) only [ite_eq_right]
  norm_num
  nlinarith only [hσ]

lemma defect_norm (n : ℕ) (j : Fin (n + 1)) (σ : ℝ) (hσ : σ ^ 2 = 1) :
    ‖defect n j σ‖ ≤ 1 / 2 := by
  have hs := defect_norm_sq n j σ hσ
  nlinarith only [hs, norm_nonneg (defect n j σ)]

def pairIndex {n : ℕ} (i : Fin (2 * n + 2)) : Fin (n + 1) :=
  ⟨i.val / 2, by have := i.isLt; omega⟩

noncomputable def sampleDefect (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (i : Fin (2 * n + 2)) : Features (2 * n + 10) :=
  if i.val % 2 = 0 then defect n (pairIndex i) 1 else defect n (π (pairIndex i)) (-1)

noncomputable def background {n : ℕ} (μ : ℝ) (i : Fin (2 * n + 2)) : ℝ :=
  if i.val % 2 = 0 then Real.sqrt 2 else -(Real.sqrt 2 * (1 + μ))

noncomputable def data (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (μ : ℝ) : Data (2 * n + 10) (2 * n + 1) :=
  fun i => (background μ i / Real.sqrt 2) • axis (2 * n + 10) + μ • sampleDefect n π i

noncomputable def geometry (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (μ : ℝ)
    (hμ : 0 ≤ μ) (hμ₁ : μ ≤ 1) :
    Geometry (data n π μ) (Real.sqrt 2) (2 * Real.sqrt 2) μ (Real.sqrt 2 / 16) where
  background := background μ
  defect := sampleDefect n π
  separator := unitVector ⟨0, by omega⟩
  sample_eq _ := rfl
  background_lower := by
    intro i
    have hs := Real.sqrt_nonneg (2 : ℝ)
    have hm := mul_nonneg hs hμ
    unfold background
    split_ifs
    · rw [abs_of_nonneg hs]
    · rw [abs_neg, abs_of_nonneg (mul_nonneg hs (by linarith))]
      nlinarith only [hm]
  background_upper := by
    intro i
    have hs := Real.sqrt_nonneg (2 : ℝ)
    have hm := mul_le_mul_of_nonneg_left hμ₁ hs
    unfold background
    split_ifs
    · rw [abs_of_nonneg hs]
      linarith only [hs]
    · rw [abs_neg, abs_of_nonneg (mul_nonneg hs (by linarith))]
      nlinarith only [hm]
  centered := by
    intro i
    unfold sampleDefect
    split_ifs <;> exact centered _ _ _
  defect_norm := by
    intro i
    unfold sampleDefect
    split_ifs <;> exact defect_norm _ _ _ (by norm_num)
  separator_norm := unit_norm _
  derivative_margin := by
    intro i
    change Real.sqrt 2 / 16 ≤
      ⟪ManySampleConvolutionalPerceptronGeometry.minusFeature (sampleDefect n π i), unitVector _⟫
    unfold sampleDefect
    split_ifs <;> exact le_of_eq (derivative_projection _ _ _).symm

noncomputable def contrast (n : ℕ) : ℝ := 1 / (2 ^ 500 * ((n : ℝ) + 2) ^ 2)

noncomputable def parameters (n : ℕ) : Params where
  dimension := 2 * n + 10
  samples := 2 * n + 1
  lower := Real.sqrt 2
  upper := 2 * Real.sqrt 2
  contrast := contrast n
  derivativeMargin := Real.sqrt 2 / 16

lemma contrast_pos (n : ℕ) : 0 < contrast n := by
  unfold contrast
  positivity

set_option exponentiation.threshold 1024 in
lemma contrast_le (n : ℕ) : contrast n ≤ 1 / 2 ^ 500 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hsq : (1 : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith only [hn]
  unfold contrast
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith only [mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ 2 ^ 500 by positivity)]

set_option exponentiation.threshold 1024 in
lemma parameters_valid (n : ℕ) : spec.valid (parameters n) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs₂ := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs₁ : 1 ≤ Real.sqrt (2 : ℝ) := by nlinarith only [hs, hs₂]
  have hsle : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith only [hs, hs₂]
  change 0 < 2 * n + 10 ∧ 0 < Real.sqrt 2 ∧ Real.sqrt 2 ≤ 2 * Real.sqrt 2 ∧
    0 < contrast n ∧ 0 < Real.sqrt 2 / 16 ∧ Real.sqrt 2 / 16 ≤ 1 ∧
    contrast n / (2 * Real.sqrt 2) ≤ (Real.sqrt 2 / 16) ^ 20 *
      (Real.sqrt 2 / (2 * Real.sqrt 2)) ^ 24 / 2 ^ 400
  refine ⟨by omega, hs, by linarith only [hs], contrast_pos n, by positivity,
    by linarith only [hsle], ?_⟩
  have hr : Real.sqrt (2 : ℝ) / (2 * Real.sqrt 2) = 1 / 2 := by field_simp
  have hk : (Real.sqrt (2 : ℝ) / 16) ^ 20 = 1 / 2 ^ 70 := by
    rw [div_pow, show (20 : ℕ) = 2 * 10 by omega, pow_mul, hs₂]
    norm_num
  rw [hr, hk]
  have hc := contrast_le n
  have hd : contrast n / (2 * Real.sqrt 2) ≤ contrast n := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_left hs₁ (contrast_pos n).le
    nlinarith only [hm, (contrast_pos n).le]
  apply hd.trans
  apply hc.trans
  norm_num

set_option maxRecDepth 4096 in
lemma opposite_distance_sq (n : ℕ) (j : Fin (n + 1)) :
    ‖defect n j 1 - defect n j (-1)‖ ^ 2 = 77 / 128 := by
  rw [← real_inner_self_eq_norm_sq]
  have hj := j.isLt
  simp only [defect, base, perturbation, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    unitVector, EuclideanSpace.inner_single_left, PiLp.single_apply, Fin.mk.injEq]
  simp (disch := omega) only [ite_eq_right]
  norm_num

lemma no_common_cap (n : ℕ) (j : Fin (n + 1)) :
    ¬∃ c : Features (2 * n + 10),
      ‖defect n j 1 - c‖ ≤ (Real.sqrt 2 / 16) / 64 ∧
      ‖defect n j (-1) - c‖ ≤ (Real.sqrt 2 / 16) / 64 := by
  rintro ⟨c, hp, hm⟩
  have ht := norm_sub_le (defect n j 1 - c) (defect n j (-1) - c)
  rw [sub_sub_sub_cancel_right] at ht
  have hs := opposite_distance_sq n j
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := norm_nonneg (defect n j 1 - defect n j (-1))
  have hu : ‖defect n j 1 - defect n j (-1)‖ ≤ Real.sqrt 2 / 512 := by
    linarith only [ht, hp, hm]
  have hsle : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith only [hsq, Real.sqrt_nonneg (2 : ℝ)]
  nlinarith only [hu, hsle, hn, hs]

lemma defect_far_coordinate (n : ℕ) (j : Fin (n + 1)) (σ : ℝ)
    (i : Fin (2 * n + 10)) (hi : 6 ≤ i.val) (hilast : i.val < 2 * n + 9) :
    defect n j σ i = σ / 32 *
      ((if i.val = 6 + 2 * j.val then 1 else 0) - (if i.val = 7 + 2 * j.val then 1 else 0)) := by
  have hj := j.isLt
  simp only [defect, base, perturbation, unitVector, PiLp.add_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul, PiLp.single_apply]
  simp (disch := omega) only [Fin.ext_iff, ite_eq_right]
  ring

lemma derivative_tail (n : ℕ) (j l : Fin (n + 1)) (σ : ℝ) :
    ManySampleConvolutionalPerceptronGeometry.minusFeature (defect n j σ)
      ⟨7 + 2 * l.val, by have := l.isLt; omega⟩ =
      if j = l then -σ / (16 * Real.sqrt 2) else 0 := by
  have hj := j.isLt
  have hl := l.isLt
  let i : Fin (2 * n + 10) := ⟨7 + 2 * l.val, by omega⟩
  have hi : i ≠ 0 := by intro he; have hv := congrArg Fin.val he; simp [i] at hv
  have hprev : (finRotate (2 * n + 10)).symm i = ⟨6 + 2 * l.val, by omega⟩ := by
    apply Fin.ext
    rw [coe_finRotate_symm_of_ne_zero hi]
    simp [i]
  change ((Real.sqrt 2)⁻¹ • (defect n j σ - shift (defect n j σ))) i = _
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, shift_apply, hprev]
  rw [defect_far_coordinate n j σ i (by dsimp [i]; omega) (by dsimp [i]; omega),
    defect_far_coordinate n j σ ⟨6 + 2 * l.val, by omega⟩
      (by change 6 ≤ 6 + 2 * l.val; omega)
      (by change 6 + 2 * l.val < 2 * n + 9; omega)]
  dsimp only [i]
  by_cases he : j = l
  · subst j
    simp (disch := omega) only [ite_eq_right, ite_true]
    ring
  · have hne : j.val ≠ l.val := fun hv => he (Fin.ext hv)
    simp (disch := omega) only [ite_eq_right]
    ring

lemma derivative_independent (n : ℕ) :
    LinearIndependent ℝ (fun j : Fin (n + 1) =>
      ManySampleConvolutionalPerceptronGeometry.minusFeature (defect n j 1)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  have hv := congrArg (fun v : Features (2 * n + 10) =>
    v ⟨7 + 2 * i.val, by have := i.isLt; omega⟩) ha
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul, derivative_tail, PiLp.zero_apply] at hv
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hv
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hn : (-1 : ℝ) / (16 * Real.sqrt 2) ≠ 0 := div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) hs)
  exact (mul_eq_zero.mp hv).resolve_right hn

def evenIndex {n : ℕ} (j : Fin (n + 1)) : Fin (2 * n + 2) :=
  ⟨2 * j.val, by have := j.isLt; omega⟩

def oddIndex {n : ℕ} (j : Fin (n + 1)) : Fin (2 * n + 2) :=
  ⟨2 * j.val + 1, by have := j.isLt; omega⟩

lemma data_even (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (μ : ℝ) (j : Fin (n + 1)) :
    data n π μ (evenIndex j) = axis (2 * n + 10) + μ • defect n j 1 := by
  have hi : pairIndex (evenIndex j) = j := by apply Fin.ext; dsimp [pairIndex, evenIndex]; omega
  have he : (evenIndex j).val % 2 = 0 := by dsimp [evenIndex]; omega
  simp only [data, background, sampleDefect, he, ite_true, hi]
  rw [div_self (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))), one_smul]

lemma data_odd (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (μ : ℝ) (j : Fin (n + 1)) :
    data n π μ (oddIndex j) = -((1 + μ) • axis (2 * n + 10) - μ • defect n (π j) (-1)) := by
  have hi : pairIndex (oddIndex j) = j := by apply Fin.ext; dsimp [pairIndex, oddIndex]; omega
  have he : ¬(oddIndex j).val % 2 = 0 := by dsimp [oddIndex]; omega
  simp only [data, background, sampleDefect, he, ite_false, hi]
  have hs : -(Real.sqrt 2 * (1 + μ)) / Real.sqrt 2 = -(1 + μ) := by
    field_simp
  rw [hs]
  module

lemma family_frozen_mistakes (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (μ η : ℝ) (hμ : 0 < μ) (hμ₁ : μ ≤ 1 / 4) (hη : 0 < η)
    (k : ℕ) (hk : (k : ℝ) * μ ≤ 1 / 4) :
    let pos := fun j => LongTails.Algorithms.DerivativeConvolutionalPerceptron.frozenFeature
      (data n π μ (evenIndex j))
    let neg := fun j => -LongTails.Algorithms.DerivativeConvolutionalPerceptron.frozenFeature
      (data n π μ (oddIndex j))
    let j : Fin (n + 1) := ⟨k % (n + 1), Nat.mod_lt _ (by omega)⟩
    ⟪pos j, LongTails.Algorithms.DerivativeConvolutionalPerceptron.frozenPairedIterate η pos neg k⟫ ≤ 0 ∧
      ⟪-neg j, LongTails.Algorithms.DerivativeConvolutionalPerceptron.frozenPairedMiddle η pos neg k⟫ < 0 := by
  have hm := DerivativePerceptronLowerBound.frozen_mistakes
    (d := 2 * n + 10) (u := fun j => defect n j 1) (v := fun j => defect n (π j) (-1))
    (by omega) hμ hμ₁ hη (fun j => centered n j 1) (fun j => centered n (π j) (-1))
    (fun j => defect_norm n j 1 (by norm_num)) (fun j => defect_norm n (π j) (-1) (by norm_num)) k hk
  simpa only [data_even, data_odd, LongTails.Algorithms.DerivativeConvolutionalPerceptron.frozenFeature,
    smul_neg, neg_neg] using hm

end LongTails.Proofs.DerivativePerceptronInstances
