import LongTails.Proofs.AdamMoments
import LongTails.Proofs.AdamSymmetricGeometry
import LongTails.Setups.SpectralSmoothAdamComparison

namespace LongTails.Proofs.AdamHistory

open LongTails.Setups.SpectralSmoothAdamComparison
open LongTails.Setups.BatchedSpectralSmooth
open LongTails.Algorithms.MatrixPolar

noncomputable def ema (β : ℝ) (g : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => β * ema β g t + (1 - β) * g t

lemma ema_congr (β : ℝ) (g k : ℕ → ℝ) (t : ℕ)
    (h : ∀ j < t, g j = k j) : ema β g t = ema β k t := by
  induction t with
  | zero => rfl
  | succ t ih => rw [ema, ema, ih (fun j hj => h j (by omega)), h t (by omega)]

lemma ema_sum (β : ℝ) (g : ℕ → ℝ) (t : ℕ) :
    ema β g t = (1 - β) * ∑ j ∈ Finset.range t, β ^ (t - 1 - j) * g j := by
  induction t with
  | zero => simp [ema]
  | succ t ih =>
    rw [ema, ih, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    have heq : ∑ j ∈ Finset.range t, β ^ (t - j) * g j =
        β * ∑ j ∈ Finset.range t, β ^ (t - 1 - j) * g j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [show t - j = (t - 1 - j) + 1 by have := Finset.mem_range.mp hj; omega, pow_succ]
      ring
    rw [heq]
    ring

lemma firstMoment_coordinate {r : ℕ} (β : ℝ) (B : ℕ) (reply : ℕ → Space r r)
    (i : Fin r × Fin r) (t : ℕ) :
    firstMoment β B reply t i = ema β (fun k => batchMean B reply k i) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [firstMoment, ema, PiLp.add_apply, PiLp.smul_apply, ih]

lemma secondMoment_coordinate {r : ℕ} (β : ℝ) (B : ℕ) (reply : ℕ → Space r r)
    (i : Fin r × Fin r) (t : ℕ) :
    secondMoment β B reply t i = ema β (fun k => (batchMean B reply k i) ^ 2) t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [secondMoment, ema, PiLp.add_apply, PiLp.smul_apply, ih]

lemma corrected_ema_sum {β : ℝ} (hβ : β < 1) (g : ℕ → ℝ) (t : ℕ) :
    ema β g t / (1 - β ^ t) =
      (∑ j ∈ Finset.range t, β ^ (t - 1 - j) * g j) /
        (∑ j ∈ Finset.range t, β ^ j) := by
  rw [ema_sum, ← geom_sum_mul_neg]
  have hβ' : 1 - β ≠ 0 := by linarith
  field_simp

lemma reversed_geometric_sum (β : ℝ) (t : ℕ) :
    (∑ j ∈ Finset.range t, β ^ (t - 1 - j)) = ∑ j ∈ Finset.range t, β ^ j :=
  Finset.sum_range_reflect (fun j => β ^ j) t

noncomputable def weight (β : ℝ) (t : ℕ) (j : Fin t) : ℝ :=
  β ^ (t - 1 - (j : ℕ)) / (∑ k ∈ Finset.range t, β ^ k)

lemma weight_nonneg {β : ℝ} (hβ : 0 ≤ β) (t : ℕ) (j : Fin t) :
    0 ≤ weight β t j := by
  unfold weight
  positivity

lemma weight_sum {β : ℝ} (hβ : 0 ≤ β) {t : ℕ} (ht : 0 < t) :
    ∑ j : Fin t, weight β t j = 1 := by
  simp only [weight, ← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun j => β ^ (t - 1 - j)) t, reversed_geometric_sum]
  exact div_self (geom_sum_pos hβ ht.ne').ne'

lemma weight_square {β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hβ₁₁ : β₁ ≤ 1) (hβ₂₁ : β₂ ≤ 1) (hβ : β₁ ^ 2 ≤ β₂)
    (t : ℕ) (j : Fin t) : weight β₁ t j ^ 2 ≤ t * weight β₂ t j := by
  cases t with
  | zero => exact Fin.elim0 j
  | succ n =>
    have h := LongTails.Proofs.AdamMoments.normalized_weight_square hβ₁ hβ₂ hβ₁₁ hβ₂₁ hβ n
      (⟨n - j, by omega⟩ : Fin (n + 1))
    simpa only [weight, Nat.succ_eq_add_one, Nat.add_sub_cancel, Fin.sum_univ_eq_sum_range,
      Nat.cast_add, Nat.cast_one] using h

lemma corrected_ema_weighted {β : ℝ} (hβ : β < 1) (g : ℕ → ℝ) (t : ℕ) :
    ema β g t / (1 - β ^ t) = ∑ j : Fin t, weight β t j * g j := by
  rw [corrected_ema_sum hβ]
  simp only [weight, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun j => β ^ (t - 1 - j) * g j) t]

lemma corrected_mean_rms {β₁ β₂ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂)
    (hβ₁₁ : β₁ < 1) (hβ₂₁ : β₂ < 1) (hβ : β₁ ^ 2 ≤ β₂) (g : ℕ → ℝ) (t : ℕ) :
    |ema β₁ g t / (1 - β₁ ^ t)| ≤
      t * Real.sqrt (ema β₂ (fun j => g j ^ 2) t / (1 - β₂ ^ t)) := by
  rw [corrected_ema_weighted hβ₁₁, corrected_ema_weighted hβ₂₁]
  exact LongTails.Proofs.AdamMoments.weighted_mean_le_rms
    (weight β₁ t) (weight β₂ t) (fun j : Fin t => g j) t (Nat.cast_nonneg _) (by simp)
    (weight_nonneg hβ₂ t) (weight_square hβ₁ hβ₂ hβ₁₁.le hβ₂₁.le hβ t)

lemma corrected_mean_difference {β : ℝ} (hβ : 0 ≤ β) (hβ₁ : β < 1)
    (g k : ℕ → ℝ) (h : ℝ) {t : ℕ} (ht : 0 < t)
    (hg : ∀ j < t, |g j - k j| ≤ h) :
    |ema β g t / (1 - β ^ t) - ema β k t / (1 - β ^ t)| ≤ h := by
  rw [corrected_ema_weighted hβ₁, corrected_ema_weighted hβ₁]
  exact LongTails.Proofs.AdamMoments.weighted_mean_difference (weight β t)
    (fun j : Fin t => g j) (fun j : Fin t => k j) h (weight_nonneg hβ t)
    (weight_sum hβ ht) (fun j => hg j j.isLt)

lemma corrected_rms_difference {β : ℝ} (hβ : 0 ≤ β) (hβ₁ : β < 1)
    (g k : ℕ → ℝ) (h : ℝ) (hh : 0 ≤ h) {t : ℕ} (ht : 0 < t)
    (hg : ∀ j < t, |g j - k j| ≤ h) :
    |Real.sqrt (ema β (fun j => g j ^ 2) t / (1 - β ^ t)) -
      Real.sqrt (ema β (fun j => k j ^ 2) t / (1 - β ^ t))| ≤ h := by
  rw [corrected_ema_weighted hβ₁, corrected_ema_weighted hβ₁]
  exact LongTails.Proofs.AdamMoments.weighted_rms_difference (weight β t)
    (fun j : Fin t => g j) (fun j : Fin t => k j) h (weight_nonneg hβ t)
    (weight_sum hβ ht) hh (fun j => hg j j.isLt)

lemma ema_nonneg {β : ℝ} (hβ : 0 ≤ β) (hβ₁ : β ≤ 1) (g : ℕ → ℝ)
    (hg : ∀ j, 0 ≤ g j) (t : ℕ) : 0 ≤ ema β g t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [ema]
    exact add_nonneg (mul_nonneg hβ ih) (mul_nonneg (sub_nonneg.mpr hβ₁) (hg t))

lemma latest_weight_bounds {β : ℝ} (hβ : 0 ≤ β) (hβ₁ : β < 1) (t : ℕ) :
    0 < (1 - β) / (1 - β ^ (t + 1)) ∧
      (1 - β) / (1 - β ^ (t + 1)) ≤ 1 ∧
      1 ≤ ((1 - β) / (1 - β ^ (t + 1))) * (t + 1) := by
  obtain ⟨hS₁, hSn⟩ := LongTails.Proofs.AdamMoments.geometric_sum_bounds hβ hβ₁.le t
  rw [Fin.sum_univ_eq_sum_range (fun j => β ^ j) (t + 1)] at hS₁ hSn
  have hS : 0 < ∑ j ∈ Finset.range (t + 1), β ^ j := by linarith
  have hβ' : 1 - β ≠ 0 := by linarith
  have heq : (1 - β) / (1 - β ^ (t + 1)) =
      1 / (∑ j ∈ Finset.range (t + 1), β ^ j) := by
    rw [← geom_sum_mul_neg]
    field_simp
  rw [heq]
  refine ⟨by positivity, (div_le_one hS).mpr hS₁, ?_⟩
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hS]
  simpa using hSn

lemma corrected_ema_step (β : ℝ) (g : ℕ → ℝ) (t : ℕ) :
    ema β g (t + 1) / (1 - β ^ (t + 1)) =
      β * ema β g t / (1 - β ^ (t + 1)) +
        ((1 - β) / (1 - β ^ (t + 1))) * g t := by
  rw [ema]
  ring

noncomputable def direction (a : AdamTuning) (g : ℕ → ℝ) (t : ℕ) : ℝ :=
  (ema a.β₁ g t / (1 - a.β₁ ^ t)) /
    (Real.sqrt (ema a.β₂ (fun j => g j ^ 2) t / (1 - a.β₂ ^ t)) + a.τ)

lemma direction_pair_envelope (a : AdamTuning) (ha : a.Valid)
    (g k : ℕ → ℝ) (h : ℝ) (hh : 0 ≤ h) {t : ℕ} (ht : 0 < t)
    (hg : ∀ j < t, |g j - k j| ≤ h) :
    |direction a g t - direction a k t| ≤ 2 * t ∧
      (Real.sqrt (ema a.β₂ (fun j => k j ^ 2) t / (1 - a.β₂ ^ t)) + a.τ) *
        |direction a g t - direction a k t| ≤ h * (1 + t) := by
  obtain ⟨_, hb₁, hb₁', hb₂, hb₂', hb, hτ⟩ := ha
  exact AdamSymmetricGeometry.normalized_pair_envelope
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hτ (Nat.cast_nonneg t)
    (corrected_mean_rms hb₁ hb₂ hb₁' hb₂' hb g t)
    (corrected_mean_rms hb₁ hb₂ hb₁' hb₂' hb k t)
    (corrected_mean_difference hb₁ hb₁' g k h ht hg)
    (corrected_rms_difference hb₂ hb₂' g k h hh ht hg)

end LongTails.Proofs.AdamHistory
