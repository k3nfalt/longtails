import LongTails.Proofs.SamCycleInterpolation

open InnerProductSpace
open scoped RealInnerProductSpace

namespace LongTails.Proofs.SamCycle

lemma cycle_norm {μ t : ℝ} (hm : 0 < μ) (ht : 0 < t) (i : Fin 5)
    (hi : i = 1 ∨ i = 2) : ‖grad μ t i‖ = μ*t/20 := by
  have h : ‖grad μ t i‖ ^ 2 = (μ*t/20)^2 := by
    rcases hi with rfl | rfl <;> norm_num [grad, pair_norm_sq] <;> ring
  nlinarith [norm_nonneg (grad μ t i), mul_pos hm ht]

lemma perturbation_plus {μ t : ℝ} (hm : 0 < μ) (ht : 0 < t) :
    point μ t 1 + (1 / ‖grad μ t 1‖) • grad μ t 1 = point μ t 3 := by
  rw [cycle_norm hm ht 1 (Or.inl rfl)]
  norm_num [point, grad, pair_smul, pair_add]
  congr 1 <;> field_simp [hm.ne', ht.ne'] <;> ring

lemma perturbation_minus {μ t : ℝ} (hm : 0 < μ) (ht : 0 < t) :
    point μ t 2 + (1 / ‖grad μ t 2‖) • grad μ t 2 = point μ t 4 := by
  rw [cycle_norm hm ht 2 (Or.inr rfl)]
  norm_num [point, grad, pair_smul, pair_add]
  congr 1 <;> field_simp [hm.ne', ht.ne'] <;> ring

lemma step_plus {μ t : ℝ} (hm : 0 < μ) (ht : 0 < t) {f : Space → ℝ}
    (hg : ∀ i, gradient f (point μ t i) = grad μ t i) :
    LongTails.Algorithms.NormalizedSam.step (gradient f) (μ*t) 1 (point μ t 1) = point μ t 2 := by
  unfold LongTails.Algorithms.NormalizedSam.step
  rw [hg, perturbation_plus hm ht, hg]
  norm_num [point, grad, pair_smul, pair_sub]
  congr 1
  ring

lemma step_minus {μ t : ℝ} (hm : 0 < μ) (ht : 0 < t) {f : Space → ℝ}
    (hg : ∀ i, gradient f (point μ t i) = grad μ t i) :
    LongTails.Algorithms.NormalizedSam.step (gradient f) (μ*t) 1 (point μ t 2) = point μ t 1 := by
  unfold LongTails.Algorithms.NormalizedSam.step
  rw [hg, perturbation_minus hm ht, hg]
  norm_num [point, grad, pair_smul, pair_sub]
  congr 1
  ring

lemma output_in_cycle {μ t : ℝ} (hm : 0 < μ) (ht : 0 < t) {f : Space → ℝ}
    (hg : ∀ i, gradient f (point μ t i) = grad μ t i) (T : ℕ) :
    LongTails.Algorithms.NormalizedSam.output (gradient f) (μ*t) 1 (point μ t 1) T = point μ t 1 ∨
    LongTails.Algorithms.NormalizedSam.output (gradient f) (μ*t) 1 (point μ t 1) T = point μ t 2 := by
  unfold LongTails.Algorithms.NormalizedSam.output
  induction T with
  | zero => exact Or.inl rfl
  | succ T ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h
    · rw [h, step_plus hm ht hg]
      exact Or.inr rfl
    · rw [h, step_minus hm ht hg]
      exact Or.inl rfl

lemma output_gap {μ t : ℝ} (hm : 0 < μ) (ht : 0 < t) {f : Space → ℝ}
    (hi : ∀ i, f (point μ t i) = value μ t i ∧ gradient f (point μ t i) = grad μ t i)
    (h0 : f 0 = 0) (T : ℕ) :
    f (LongTails.Algorithms.NormalizedSam.output (gradient f) (μ*t) 1 (point μ t 1) T) - f 0 =
      μ*t^2/5000 := by
  rcases output_in_cycle hm ht (fun i => (hi i).2) T with h | h
  · rw [h, (hi 1).1, h0]
    norm_num [value]
  · rw [h, (hi 2).1, h0]
    norm_num [value]

lemma norm_sq_coordinate (z : Space) : (z 0)^2 ≤ ‖z‖^2 := by
  have he : ‖z‖^2 = (z 0)^2 + (z 1)^2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp [Fin.sum_univ_two, pow_two]
  nlinarith [sq_nonneg (z 1)]

lemma common_coordinate_gap {μ t : ℝ} (hm : 0 ≤ μ) {f : Space → ℝ}
    (hc : ∀ a b, f a + ⟪gradient f a, b-a⟫ + μ/2*‖b-a‖^2 ≤ f b)
    (hg0 : gradient f 0 = 0) (z : Space) (hz : z 0 = 3*t/200) :
    9*μ*t^2/80000 ≤ f z - f 0 := by
  have h := hc 0 z
  rw [hg0, inner_zero_left, sub_zero] at h
  have hn := mul_le_mul_of_nonneg_left (norm_sq_coordinate z) (by positivity : 0 ≤ μ/2)
  rw [hz] at hn
  nlinarith

lemma cycle_average_gap {μ t a b : ℝ} (hm : 0 ≤ μ) (hab : a+b=1) {f : Space → ℝ}
    (hc : ∀ x y, f x + ⟪gradient f x, y-x⟫ + μ/2*‖y-x‖^2 ≤ f y)
    (hg0 : gradient f 0 = 0) :
    9*μ*t^2/80000 ≤ f (a • point μ t 1 + b • point μ t 2) - f 0 := by
  apply common_coordinate_gap hm hc hg0
  change a*(3*t/200)+b*(3*t/200)=3*t/200
  calc
    _ = (a+b)*(3*t/200) := by ring
    _ = _ := by rw [hab, one_mul]

lemma exists_cycle {μ t : ℝ} (hm : 0 < μ) (hmb : μ ≤ 1/100)
    (ht : 0 < t) (htb : t ≤ 1/10) :
    ∃ f : Space → ℝ,
      (∀ a, HasGradientAt f (gradient f a) a) ∧
      (∀ a b, f a + ⟪gradient f a, b-a⟫ + μ/2*‖b-a‖^2 ≤ f b) ∧
      (∀ a b, ‖gradient f a-gradient f b‖ ≤ ‖a-b‖) ∧
      IsMinOn f Set.univ 0 ∧
      (∀ T, f (LongTails.Algorithms.NormalizedSam.output (gradient f) (μ*t) 1
        (point μ t 1) T) - f 0 = μ*t^2/5000) ∧
      (∀ a b : ℝ, a+b=1 →
        9*μ*t^2/80000 ≤ f (a • point μ t 1 + b • point μ t 2) - f 0) := by
  obtain ⟨f, hf, hc, hl, hi, h0, hmin⟩ := exists_model hm hmb ht htb
  refine ⟨f, hf, hc, hl, hmin, output_gap hm ht hi h0, ?_⟩
  have hg0 := (hi 0).2
  norm_num [point, grad] at hg0
  intro a b hab
  exact cycle_average_gap hm.le hab hc hg0

end LongTails.Proofs.SamCycle
