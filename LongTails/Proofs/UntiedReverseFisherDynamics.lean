import LongTails.Proofs.UntiedReverseFisherGradient
import LongTails.Proofs.UntiedReverseFisherRidge
import LongTails.Proofs.SymmetricReverseFisherTrajectory
import LongTails.Proofs.SymmetricReverseFisherContraction
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.UntiedReverseFisherDynamics

open LongTails.Setups.UntiedGaussianReverseFisher (Means loss)
open LongTails.Proofs.UntiedReverseFisherLoss
open LongTails.Proofs.UntiedReverseFisherGradient
open LongTails.Proofs.UntiedReverseFisherRidge
open LongTails.Proofs.SymmetricReverseFisherScalar
open LongTails.Proofs.SymmetricReverseFisherRidge
open LongTails.Proofs.SymmetricReverseFisherCoefficients
open LongTails.Proofs.SymmetricReverseFisherDynamics
open LongTails.Proofs.SymmetricReverseFisherTrajectory

abbrev SParams := LongTails.Setups.SymmetricGaussianReverseFisher.Params
abbrev SSpace (q : SParams) := LongTails.Setups.SymmetricGaussianReverseFisher.Space q

noncomputable def stepSize : ℝ := 1 / 32

noncomputable def pairStep {q : SParams} (b : SSpace q) (x : SSpace q × SSpace q) : SSpace q × SSpace q :=
  ((1 - stepSize) • x.1 + (stepSize / 4 * (ridgeForce ‖b‖ ⟪x.1 + x.2, b⟫ +
      ridgeForce ‖b‖ ⟪x.1 - x.2, b⟫)) • b,
    (1 - stepSize / 2 * alpha ‖x.2‖) • x.2 + (stepSize / 4 * (ridgeForce ‖b‖ ⟪x.1 + x.2, b⟫ -
      ridgeForce ‖b‖ ⟪x.1 - x.2, b⟫)) • b)

lemma orthogonal_split {q : SParams} (w b : SSpace q) (hb : b ≠ 0) :
    ‖w‖ ^ 2 = ‖w - (⟪w, b⟫ / ‖b‖ ^ 2) • b‖ ^ 2 + ⟪w, b⟫ ^ 2 / ‖b‖ ^ 2 := by
  have hb2 : 0 < ‖b‖ ^ 2 := by positivity
  have hq : ⟪w - (⟪w, b⟫ / ‖b‖ ^ 2) • b, (⟪w, b⟫ / ‖b‖ ^ 2) • b⟫ = 0 := by
    rw [inner_sub_left, inner_smul_left, inner_smul_right, inner_smul_right,
      real_inner_self_eq_norm_sq]
    simp only [conj_trivial]
    field_simp
    ring
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real hq
  rw [sub_add_cancel, ← sq, ← sq, ← sq] at h
  rw [h, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

lemma orthogonal_contract {q : SParams} (w b : SSpace q) (hb : b ≠ 0) {c l φ : ℝ}
    (hc : 0 ≤ c) (hl : l ^ 2 ≤ c ^ 2) (hφ : |φ| ≤ c * |⟪w, b⟫|) :
    ‖l • (w - (⟪w, b⟫ / ‖b‖ ^ 2) • b) + (φ / ‖b‖ ^ 2) • b‖ ≤ c * ‖w‖ := by
  have hb2 : 0 < ‖b‖ ^ 2 := by positivity
  set P := w - (⟪w, b⟫ / ‖b‖ ^ 2) • b with hP
  have hPb : ⟪P, b⟫ = 0 := by
    rw [hP, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [conj_trivial]
    field_simp
    ring
  have hq : ⟪l • P, (φ / ‖b‖ ^ 2) • b⟫ = 0 := by
    rw [inner_smul_left, inner_smul_right, hPb]; simp
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_real hq
  rw [← sq, ← sq, ← sq] at h
  have hs0 := orthogonal_split w b hb
  rw [← hP] at hs0
  have hsq : ‖l • P + (φ / ‖b‖ ^ 2) • b‖ ^ 2 ≤ (c * ‖w‖) ^ 2 := by
    rw [h, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs,
      abs_div, abs_of_pos hb2, div_pow, mul_pow, hs0]
    have hφ2 : φ ^ 2 ≤ c ^ 2 * ⟪w, b⟫ ^ 2 := by
      rw [← sq_abs φ, ← sq_abs ⟪w, b⟫, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hφ 2
    have hn : ‖b‖ ^ 2 ≠ 0 := hb2.ne'
    have e1 : φ ^ 2 / (‖b‖ ^ 2) ^ 2 * ‖b‖ ^ 2 = φ ^ 2 / ‖b‖ ^ 2 := by field_simp
    rw [sq_abs, e1]
    have e2 : φ ^ 2 / ‖b‖ ^ 2 ≤ c ^ 2 * (⟪w, b⟫ ^ 2 / ‖b‖ ^ 2) := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right hφ2 hb2.le
    nlinarith [mul_le_mul_of_nonneg_right hl (sq_nonneg ‖P‖)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq

lemma pairStep_fst_eq {q : SParams} (b : SSpace q) (hb : b ≠ 0) (x : SSpace q × SSpace q) :
    (pairStep b x).1 = (1 - stepSize) • (x.1 - (⟪x.1, b⟫ / ‖b‖ ^ 2) • b) +
      (((1 - stepSize) * ⟪x.1, b⟫ + stepSize / 4 * ‖b‖ ^ 2 *
        (ridgeForce ‖b‖ (⟪x.1, b⟫ + ⟪x.2, b⟫) + ridgeForce ‖b‖ (⟪x.1, b⟫ - ⟪x.2, b⟫))) /
          ‖b‖ ^ 2) • b := by
  have hb2 : ‖b‖ ^ 2 ≠ 0 := by positivity
  simp only [pairStep, inner_add_left, inner_sub_left]
  rw [show ((1 - stepSize) * ⟪x.1, b⟫ + stepSize / 4 * ‖b‖ ^ 2 *
        (ridgeForce ‖b‖ (⟪x.1, b⟫ + ⟪x.2, b⟫) + ridgeForce ‖b‖ (⟪x.1, b⟫ - ⟪x.2, b⟫))) /
          ‖b‖ ^ 2 = (1 - stepSize) * (⟪x.1, b⟫ / ‖b‖ ^ 2) + stepSize / 4 *
        (ridgeForce ‖b‖ (⟪x.1, b⟫ + ⟪x.2, b⟫) + ridgeForce ‖b‖ (⟪x.1, b⟫ - ⟪x.2, b⟫)) by
      field_simp]
  module

lemma centre_norm_step {q : SParams} (b : SSpace q) (hb1 : ‖b‖ ≤ 1 / 2) (x : SSpace q × SSpace q) :
    ‖(pairStep b x).1‖ ≤ (1 - 7 * stepSize / 16) * ‖x.1‖ := by
  have hγ : stepSize = 1 / 32 := rfl
  by_cases hb : b = 0
  · subst hb
    simp only [pairStep, smul_zero, add_zero, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (by rw [hγ]; norm_num)]
    exact mul_le_mul_of_nonneg_right (by rw [hγ]; norm_num) (norm_nonneg _)
  rw [pairStep_fst_eq b hb]
  apply orthogonal_contract x.1 b hb (by rw [hγ]; norm_num) (by rw [hγ]; norm_num)
  exact centre_contraction (norm_nonneg b) hb1 (by rw [hγ]; norm_num) (by rw [hγ]; norm_num) _ _

noncomputable def shiftDefect (a σ κ : ℝ) : ℝ :=
  ridgeForce a (σ + κ) - ridgeForce a (σ - κ) - 2 * ridgeForce a κ

lemma snd_eq_gdStep {q : SParams} (b : SSpace q) (x : SSpace q × SSpace q) :
    (pairStep b x).2 = gdStep b (stepSize / 2) x.2 +
      (stepSize / 4 * shiftDefect ‖b‖ ⟪x.1, b⟫ ⟪x.2, b⟫) • b := by
  rw [gdStep_eq]
  simp only [pairStep, shiftDefect, inner_add_left, inner_sub_left]
  module

lemma inner_axis {q : SParams} (e x : SSpace q) (a : ℝ) : ⟪x, a • e⟫ = a * ⟪x, e⟫ := by
  rw [inner_smul_right]

lemma norm_axis {q : SParams} (e : SSpace q) {a : ℝ} (he : ‖e‖ = 1) (ha : 0 ≤ a) :
    ‖a • e‖ = a := by
  rw [norm_smul, he, Real.norm_eq_abs, abs_of_nonneg ha, mul_one]

lemma snd_inner {q : SParams} (e : SSpace q) {a : ℝ} (he : ‖e‖ = 1) (ha : 0 ≤ a)
    (x : SSpace q × SSpace q) :
    ⟪(pairStep (a • e) x).2, e⟫ =
      (1 - stepSize / 2 * alpha ‖x.2‖ + stepSize / 2 * beta a (a * ⟪x.2, e⟫) * a ^ 2) *
          ⟪x.2, e⟫ +
        stepSize / 4 * shiftDefect a (a * ⟪x.1, e⟫) (a * ⟪x.2, e⟫) * a := by
  rw [snd_eq_gdStep, inner_add_left, inner_step e x.2 he ha, norm_axis e he ha,
    inner_axis, inner_axis, inner_smul_left, inner_smul_left]
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  simp only [conj_trivial, hee]
  ring

lemma snd_transverse {q : SParams} (e : SSpace q) {a : ℝ} (he : ‖e‖ = 1) (ha : 0 ≤ a)
    (x : SSpace q × SSpace q) :
    transverse e (pairStep (a • e) x).2 = (1 - stepSize / 2 * alpha ‖x.2‖) • transverse e x.2 := by
  rw [snd_eq_gdStep, ← transverse_step e x.2 (η := stepSize / 2) he ha]
  unfold transverse
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  rw [inner_add_left, inner_smul_left, inner_smul_left, hee]
  simp only [conj_trivial]
  module

lemma snd_inner_direct {q : SParams} (e : SSpace q) {a : ℝ} (he : ‖e‖ = 1) (ha : 0 ≤ a)
    (x : SSpace q × SSpace q) :
    ⟪(pairStep (a • e) x).2, e⟫ =
      (1 - stepSize / 2 * alpha ‖x.2‖) * ⟪x.2, e⟫ +
        stepSize / 4 * (ridgeForce a (a * ⟪x.1, e⟫ + a * ⟪x.2, e⟫) -
          ridgeForce a (a * ⟪x.1, e⟫ - a * ⟪x.2, e⟫)) * a := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  simp only [pairStep, norm_axis e he ha, inner_add_left, inner_sub_left, inner_axis,
    inner_smul_left, conj_trivial, hee]
  ring

lemma defect_bound {q : SParams} (e : SSpace q) {a : ℝ} (he : ‖e‖ = 1) (ha : 0 ≤ a)
    (ha1 : a ≤ 1 / 2) (x : SSpace q × SSpace q) :
    |stepSize / 4 * shiftDefect a (a * ⟪x.1, e⟫) (a * ⟪x.2, e⟫) * a| ≤
      stepSize / 2 * (32 * a ^ 3 * ‖x.1‖) * |⟪x.2, e⟫| := by
  have h := ridge_difference_shift ha ha1 (a * ⟪x.1, e⟫) (a * ⟪x.2, e⟫)
  have hc : |⟪x.1, e⟫| ≤ ‖x.1‖ := by
    simpa [he] using abs_real_inner_le_norm x.1 e
  have hγ : stepSize = 1 / 32 := rfl
  unfold shiftDefect
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_pos (by rw [hγ]; norm_num : (0:ℝ) < stepSize / 4)]
  rw [abs_mul, abs_mul, abs_of_nonneg ha] at h
  have h2 : 64 * (a * |⟪x.2, e⟫|) * (a * |⟪x.1, e⟫|) ≤ 64 * (a * |⟪x.2, e⟫|) * (a * ‖x.1‖) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc ha) (by positivity)
  have h3 := mul_le_mul_of_nonneg_left (h.trans h2) (show 0 ≤ stepSize / 4 * a by rw [hγ]; positivity)
  nlinarith [h3]

lemma snd_inner_crude {q : SParams} (e : SSpace q) {a : ℝ} (he : ‖e‖ = 1) (ha : 0 ≤ a)
    (ha1 : a ≤ 1 / 2) (x : SSpace q × SSpace q) (hu : 0 ≤ ⟪x.2, e⟫) :
    (1 - stepSize / 2 * alpha ‖x.2‖ - stepSize / 2 * (13 / 2 * a ^ 2)) * ⟪x.2, e⟫ ≤
      ⟪(pairStep (a • e) x).2, e⟫ := by
  rw [snd_inner_direct e he ha]
  have h := ridge_difference_crude ha ha1 (a * ⟪x.1, e⟫) (a * ⟪x.2, e⟫)
  rw [abs_mul, abs_of_nonneg ha, abs_of_nonneg hu] at h
  have hγ : stepSize = 1 / 32 := rfl
  have h1 := neg_abs_le (ridgeForce a (a * ⟪x.1, e⟫ + a * ⟪x.2, e⟫) -
    ridgeForce a (a * ⟪x.1, e⟫ - a * ⟪x.2, e⟫))
  have h2 := mul_le_mul_of_nonneg_left (neg_le_neg h) (show 0 ≤ stepSize / 4 * a by rw [hγ]; positivity)
  nlinarith [h1, h2, mul_le_mul_of_nonneg_left h1 (show 0 ≤ stepSize / 4 * a by rw [hγ]; positivity)]

lemma snd_norm_bound {q : SParams} (e : SSpace q) {a : ℝ} (he : ‖e‖ = 1) (ha : 0 ≤ a)
    (x : SSpace q × SSpace q) :
    ‖(pairStep (a • e) x).2‖ ≤ (1 - stepSize / 2 * alpha ‖x.2‖) * ‖x.2‖ + 4 * (stepSize / 2) * a := by
  have hγ : stepSize = 1 / 32 := rfl
  have hl := (lambda_bounds (r := ‖x.2‖) (η := stepSize / 2) (by rw [hγ]; norm_num)
    (by rw [hγ]; norm_num)).1
  have h1 := ridgeForce_abs_le_four a (⟪x.1 + x.2, a • e⟫)
  have h2 := ridgeForce_abs_le_four a (⟪x.1 - x.2, a • e⟫)
  simp only [pairStep, norm_axis e he ha]
  calc
    _ ≤ ‖(1 - stepSize / 2 * alpha ‖x.2‖) • x.2‖ + ‖(stepSize / 4 * (ridgeForce a ⟪x.1 + x.2, a • e⟫ -
        ridgeForce a ⟪x.1 - x.2, a • e⟫)) • (a • e)‖ := norm_add_le _ _
    _ = (1 - stepSize / 2 * alpha ‖x.2‖) * ‖x.2‖ + stepSize / 4 * |ridgeForce a ⟪x.1 + x.2, a • e⟫ -
        ridgeForce a ⟪x.1 - x.2, a • e⟫| * a := by
      rw [norm_smul, norm_smul, norm_axis e he ha, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by linarith), abs_mul, abs_of_pos (by rw [hγ]; norm_num : (0:ℝ) < stepSize / 4)]
    _ ≤ _ := by
      have h3 := abs_sub (ridgeForce a ⟪x.1 + x.2, a • e⟫) (ridgeForce a ⟪x.1 - x.2, a • e⟫)
      have h4 : stepSize / 4 * |ridgeForce a ⟪x.1 + x.2, a • e⟫ - ridgeForce a ⟪x.1 - x.2, a • e⟫| * a ≤
          stepSize / 4 * 8 * a :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith)
          (by rw [hγ]; norm_num)) ha
      linarith

section Scalar

variable {η m P : ℝ} {U T R A B : ℕ → ℝ}

lemma post_positive (hη : 0 ≤ η) (hη1 : η ≤ 1 / 64) (hm : 0 ≤ m)
    (hA : ∀ k, 0 ≤ A k ∧ A k ≤ 4) (hB : ∀ k, 0 < U k → m ≤ B k)
    (hU : ∀ k, 0 < U k → (1 - η * A k + η * (B k - m / 4)) * U k ≤ U (k + 1))
    (h0 : 0 < U 0) (k : ℕ) : 0 < U k := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    have h1 := hU k ih
    have h2 := hB k ih
    have h3 := (hA k).2
    have hpos : 0 < 1 - η * A k + η * (B k - m / 4) := by nlinarith
    exact lt_of_lt_of_le (mul_pos hpos ih) h1

lemma post_ratio (hη : 0 ≤ η) (hη1 : η ≤ 1 / 64) (hm : 0 ≤ m)
    (hA : ∀ k, 0 ≤ A k ∧ A k ≤ 4) (hB : ∀ k, 0 < U k → m ≤ B k)
    (hU : ∀ k, 0 < U k → (1 - η * A k + η * (B k - m / 4)) * U k ≤ U (k + 1))
    (hT : ∀ k, T (k + 1) = (1 - η * A k) * T k) (hT0 : ∀ k, 0 ≤ T k)
    (h0 : 0 < U 0) (hP : T 0 ≤ P * U 0) (k : ℕ) :
    T k ≤ P * (1 / (1 + 3 * η * m / 4)) ^ k * U k := by
  have hpos := post_positive hη hη1 hm hA hB hU h0
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    have hτ1 : 1 - η * A k ≤ 1 := by nlinarith [(hA k).1]
    have hτ0 : 0 ≤ 1 - η * A k := by nlinarith [(hA k).2]
    have hb := hB k (hpos k)
    have hg : 0 < 1 + 3 * η * m / 4 := by positivity
    have hgrow : (1 - η * A k) * (1 + 3 * η * m / 4) * U k ≤ U (k + 1) := by
      have h1 := hU k (hpos k)
      have h2 : (1 - η * A k) * (1 + 3 * η * m / 4) ≤ 1 - η * A k + η * (B k - m / 4) := by
        nlinarith [mul_nonneg hτ0 (show 0 ≤ 3 * η * m / 4 by positivity), mul_nonneg hη hm]
      nlinarith [mul_le_mul_of_nonneg_right h2 (hpos k).le]
    rw [hT k, pow_succ]
    have hPk : 0 ≤ P * (1 / (1 + 3 * η * m / 4)) ^ k := by
      have := hT0 k
      by_contra hneg
      push Not at hneg
      have hU := hpos k
      have : P * (1 / (1 + 3 * η * m / 4)) ^ k * U k < 0 := mul_neg_of_neg_of_pos hneg hU
      linarith
    calc
      (1 - η * A k) * T k ≤ (1 - η * A k) * (P * (1 / (1 + 3 * η * m / 4)) ^ k * U k) :=
        mul_le_mul_of_nonneg_left ih hτ0
      _ = P * (1 / (1 + 3 * η * m / 4)) ^ k * (1 / (1 + 3 * η * m / 4)) *
          ((1 - η * A k) * (1 + 3 * η * m / 4) * U k) := by
        field_simp
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hgrow
          (mul_nonneg hPk (show 0 ≤ 1 / (1 + 3 * η * m / 4) by positivity))
        linarith

lemma post_floor (hη : 0 ≤ η) (hη1 : η ≤ 1 / 64) (hm : 0 ≤ m) (hP0 : 0 ≤ P)
    (hA : ∀ k, 0 ≤ A k ∧ A k ≤ 4 * R k ^ 2) (hA4 : ∀ k, A k ≤ 4)
    (hB : ∀ k, 0 < U k → m ≤ B k)
    (hU : ∀ k, 0 < U k → (1 - η * A k + η * (B k - m / 4)) * U k ≤ U (k + 1))
    (hR : ∀ k, R k ≤ U k + T k) (hR0 : ∀ k, 0 ≤ R k) (hcone : ∀ k, T k ≤ P * U k)
    (h0 : 0 < U 0) {ϱ : ℝ} (_hϱ : 0 ≤ ϱ) (hϱm : 4 * ϱ ^ 2 ≤ m / 2) (k : ℕ) :
    min (U 0) (ϱ / (2 * (1 + P))) ≤ U k := by
  have hpos := post_positive hη hη1 hm (fun k => ⟨(hA k).1, hA4 k⟩) hB hU h0
  induction k with
  | zero => exact min_le_left _ _
  | succ k ih =>
    have hb := hB k (hpos k)
    have h1 := hU k (hpos k)
    by_cases hr : R k ≤ ϱ
    · have hAk : A k ≤ m / 2 := by
        have := (hA k).2
        have hr2 : R k ^ 2 ≤ ϱ ^ 2 := by
          exact pow_le_pow_left₀ (hR0 k) hr 2
        nlinarith
      have hg : 1 ≤ 1 - η * A k + η * (B k - m / 4) := by nlinarith [mul_nonneg hη hm]
      nlinarith [mul_le_mul_of_nonneg_right hg (hpos k).le]
    · push Not at hr
      have hu : ϱ / (1 + P) ≤ U k := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hR k, hcone k]
      have hhalf : U k / 2 ≤ U (k + 1) := by
        have hl : 1 / 2 ≤ 1 - η * A k + η * (B k - m / 4) := by nlinarith [hA4 k]
        nlinarith [mul_le_mul_of_nonneg_right hl (hpos k).le]
      have : ϱ / (2 * (1 + P)) = ϱ / (1 + P) / 2 := by field_simp
      rw [this] at *
      exact (min_le_right _ _).trans (by linarith)

lemma post_escape_step (hη : 0 ≤ η) (hη1 : η ≤ 1 / 64) (hm : 0 ≤ m) {q : ℝ} (hq : 0 ≤ q)
    (hqm : q ^ 2 = m) (k : ℕ)
    (hA : 0 ≤ A k ∧ A k ≤ 4 * R k ^ 2) (hA4 : A k ≤ 4) (hb : m ≤ B k)
    (hUk : 0 < U k) (hU : (1 - η * A k + η * (B k - m / 4)) * U k ≤ U (k + 1))
    (hR2 : R k ^ 2 ≤ 2 * U k ^ 2) :
    min ((1 + η * m / 4) * U k) (q / 8) ≤ U (k + 1) := by
  by_cases hr : R k ^ 2 ≤ m / 8
  · have hg : 1 + η * m / 4 ≤ 1 - η * A k + η * (B k - m / 4) := by nlinarith [hA.2]
    exact (min_le_left _ _).trans (by nlinarith [mul_le_mul_of_nonneg_right hg hUk.le])
  · push Not at hr
    have hu2 : (q / 4) ^ 2 ≤ U k ^ 2 := by nlinarith
    have hu : q / 4 ≤ U k :=
      (pow_le_pow_iff_left₀ (by positivity) hUk.le two_ne_zero).mp hu2
    have hl : 1 / 2 ≤ 1 - η * A k + η * (B k - m / 4) := by nlinarith
    exact (min_le_right _ _).trans (by nlinarith [mul_le_mul_of_nonneg_right hl hUk.le])

lemma warm_lower (hη : 0 ≤ η) (hη1 : η ≤ 1 / 64) {c0 : ℝ} (_hc0 : 0 ≤ c0) (hc2 : c0 ≤ 2)
    (hA : ∀ k, 0 ≤ A k ∧ A k ≤ 4)
    (hU : ∀ k, 0 ≤ U k → (1 - η * A k - η * c0) * U k ≤ U (k + 1))
    (h0 : 0 ≤ U 0) (k : ℕ) : (1 - 6 * η) ^ k * U 0 ≤ U k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hU0 : 0 ≤ U k := le_trans (mul_nonneg (pow_nonneg (by linarith) _) h0) ih
    have h1 := hU k hU0
    have h2 : 1 - 6 * η ≤ 1 - η * A k - η * c0 := by nlinarith [(hA k).2]
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left ih (show 0 ≤ 1 - 6 * η by linarith),
      mul_le_mul_of_nonneg_right h2 hU0]

lemma warm_ratio (hη : 0 ≤ η) (hη1 : η ≤ 1 / 64) {c0 : ℝ} (hc0 : 0 ≤ c0) (hc2 : c0 ≤ 2)
    (hA : ∀ k, 0 ≤ A k ∧ A k ≤ 4)
    (hU : ∀ k, 0 ≤ U k → (1 - η * A k - η * c0) * U k ≤ U (k + 1))
    (hT : ∀ k, T (k + 1) = (1 - η * A k) * T k) (_hT0 : ∀ k, 0 ≤ T k)
    (h0 : 0 < U 0) (hP : T 0 ≤ P * U 0) (hP0 : 0 ≤ P) (k : ℕ) :
    T k ≤ P * (1 / (1 - 4 * η)) ^ k * U k := by
  have hlow := warm_lower hη hη1 hc0 hc2 hA hU h0.le
  have hpos (k : ℕ) : 0 < U k :=
    lt_of_lt_of_le (mul_pos (pow_pos (by linarith) _) h0) (hlow k)
  induction k with
  | zero => simpa using hP
  | succ k ih =>
    have hτ0 : 1 / 2 ≤ 1 - η * A k := by nlinarith [(hA k).2]
    have hgrow : (1 - η * A k) * (1 - 4 * η) * U k ≤ U (k + 1) := by
      have h1 := hU k (hpos k).le
      have h2 : (1 - η * A k) * (1 - 4 * η) ≤ 1 - η * A k - η * c0 := by nlinarith [(hA k).2]
      nlinarith [mul_le_mul_of_nonneg_right h2 (hpos k).le]
    have hg : 0 < 1 - 4 * η := by linarith
    rw [hT k, pow_succ]
    have hQ : 0 ≤ P * (1 / (1 - 4 * η)) ^ k := mul_nonneg hP0 (by positivity)
    calc
      (1 - η * A k) * T k ≤ (1 - η * A k) * (P * (1 / (1 - 4 * η)) ^ k * U k) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      _ = P * (1 / (1 - 4 * η)) ^ k * (1 / (1 - 4 * η)) *
          ((1 - η * A k) * (1 - 4 * η) * U k) := by
        rw [show P * (1 / (1 - 4 * η)) ^ k * (1 / (1 - 4 * η)) * ((1 - η * A k) * (1 - 4 * η) * U k) =
          P * (1 / (1 - 4 * η)) ^ k * ((1 - η * A k) * U k) * ((1 / (1 - 4 * η)) * (1 - 4 * η)) by ring,
          one_div_mul_cancel hg.ne']
        ring
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hgrow
          (mul_nonneg hQ (show 0 ≤ 1 / (1 - 4 * η) by positivity))
        linarith

end Scalar

section Trajectory

variable {q : SParams} (e : SSpace q) {a : ℝ} (y : ℕ → SSpace q × SSpace q)

lemma radius_step {r : ℝ} (hr0 : 0 ≤ r) (ha : 0 ≤ a) (hr : r ≤ 1 + 600 * a) :
    (1 - stepSize / 2 * alpha r) * r + 4 * (stepSize / 2) * a ≤ 1 + 600 * a := by
  have hγ : stepSize = 1 / 32 := rfl
  have hl := lambda_bounds (r := r) (η := stepSize / 2) (by rw [hγ]; norm_num) (by rw [hγ]; norm_num)
  by_cases hr1 : r ≤ 1
  · have ht : (1 - stepSize / 2 * alpha r) * r ≤ 1 :=
      (mul_le_mul_of_nonneg_right hl.2 hr0).trans (by simpa using hr1)
    rw [hγ] at ht ⊢
    nlinarith
  · have hr1' : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
    have hα := alpha_lower hr0
    have hsq : 1 ≤ r ^ 2 := by nlinarith
    rw [min_eq_right hsq] at hα
    have hR := mul_le_mul_of_nonneg_left hr (show 0 ≤ 1 - stepSize / 2 * alpha r by linarith)
    have hαR := mul_le_mul_of_nonneg_left hα
      (mul_nonneg (show (0:ℝ) ≤ stepSize / 2 by rw [hγ]; norm_num) (show 0 ≤ 1 + 600 * a by positivity))
    rw [hγ] at hR hαR ⊢
    nlinarith

variable {e y}

lemma traj_ball (he : ‖e‖ = 1) (ha : 0 ≤ a) (hy : ∀ k, y (k + 1) = pairStep (a • e) (y k))
    (h0 : ‖(y 0).2‖ ≤ 1 + 600 * a) (k : ℕ) : ‖(y k).2‖ ≤ 1 + 600 * a := by
  induction k with
  | zero => exact h0
  | succ k ih =>
    rw [hy k]
    exact (snd_norm_bound e he ha (y k)).trans (radius_step (norm_nonneg _) ha ih)

lemma traj_centre (ha1 : a ≤ 1 / 2) (he : ‖e‖ = 1) (ha : 0 ≤ a)
    (hy : ∀ k, y (k + 1) = pairStep (a • e) (y k)) (k : ℕ) :
    ‖(y k).1‖ ≤ (1 - 7 * stepSize / 16) ^ k * ‖(y 0).1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hy k, pow_succ]
    have h := centre_norm_step (a • e) (by rw [norm_axis e he ha]; exact ha1) (y k)
    have hc : 0 ≤ 1 - 7 * stepSize / 16 := by rw [show stepSize = 1/32 from rfl]; norm_num
    nlinarith [mul_le_mul_of_nonneg_left ih hc]

lemma traj_transverse (he : ‖e‖ = 1) (ha : 0 ≤ a)
    (hy : ∀ k, y (k + 1) = pairStep (a • e) (y k)) (k : ℕ) :
    ‖transverse e (y (k + 1)).2‖ = (1 - stepSize / 2 * alpha ‖(y k).2‖) * ‖transverse e (y k).2‖ := by
  rw [hy k, snd_transverse e he ha, norm_smul, Real.norm_eq_abs, abs_of_nonneg]
  have hγ : stepSize = 1 / 32 := rfl
  have hl := lambda_bounds (r := ‖(y k).2‖) (η := stepSize / 2) (by rw [hγ]; norm_num)
    (by rw [hγ]; norm_num)
  linarith [hl.1]

lemma traj_crude (he : ‖e‖ = 1) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hy : ∀ k, y (k + 1) = pairStep (a • e) (y k)) (k : ℕ) (hu : 0 ≤ ⟪(y k).2, e⟫) :
    (1 - stepSize / 2 * alpha ‖(y k).2‖ - stepSize / 2 * (13 / 2 * a ^ 2)) * ⟪(y k).2, e⟫ ≤
      ⟪(y (k + 1)).2, e⟫ := by
  rw [hy k]
  exact snd_inner_crude e he ha ha1 (y k) hu

lemma traj_perturbed (he : ‖e‖ = 1) (ha : 0 ≤ a) (ha1 : a ≤ 1 / 2)
    (hy : ∀ k, y (k + 1) = pairStep (a • e) (y k)) (k : ℕ) (hu : 0 ≤ ⟪(y k).2, e⟫) :
    (1 - stepSize / 2 * alpha ‖(y k).2‖ + stepSize / 2 *
        (beta a (a * ⟪(y k).2, e⟫) * a ^ 2 - 32 * a ^ 3 * ‖(y k).1‖)) * ⟪(y k).2, e⟫ ≤
      ⟪(y (k + 1)).2, e⟫ := by
  rw [hy k, snd_inner e he ha]
  have h := defect_bound e he ha ha1 (y k)
  rw [abs_of_nonneg hu] at h
  have h2 := neg_abs_le (stepSize / 4 * shiftDefect a (a * ⟪(y k).1, e⟫) (a * ⟪(y k).2, e⟫) * a)
  nlinarith

lemma traj_alpha (k : ℕ) :
    0 ≤ alpha ‖(y k).2‖ ∧ alpha ‖(y k).2‖ ≤ 4 * ‖(y k).2‖ ^ 2 ∧ alpha ‖(y k).2‖ ≤ 4 := by
  have h := alpha_le_four_min ‖(y k).2‖
  refine ⟨alpha_nonneg _, h.trans ?_, h.trans ?_⟩
  · exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  · nlinarith [min_le_right (‖(y k).2‖ ^ 2) 1]

end Trajectory

noncomputable def coordinates {p : LongTails.Setups.UntiedGaussianReverseFisher.Params} (μ θ : Means p) :
    SSpace (tiedParams p) × SSpace (tiedParams p) :=
  (centre θ - centre μ, half θ)

lemma coordinates_step {p : LongTails.Setups.UntiedGaussianReverseFisher.Params} (μ θ : Means p) :
    coordinates μ (θ - stepSize • gradient (loss μ) θ) =
      pairStep (q := tiedParams p) (half μ) (coordinates μ θ) := by
  unfold coordinates pairStep
  rw [gradient_loss, step_centre, step_half, input_zero, input_one]
  rfl


end LongTails.Proofs.UntiedReverseFisherDynamics
