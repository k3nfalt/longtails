import LongTails.Proofs.LogFreeGeometry

namespace LongTails.Proofs.LogFreeSteps

open scoped RealInnerProductSpace
open LongTails.Proofs.LogFreeGeometry LongTails.Proofs.LogFreeLineSearch
  LongTails.Proofs.LogFreeLinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma residual_inner {f : E → ℝ} {γ : ℝ} {c y d : E}
    (hd : fderiv ℝ (gradient f) y d + γ • d = -(gradient f y + γ • (y - c))) :
    ⟪gradient f y + γ • (y - c), d⟫ = -(⟪fderiv ℝ (gradient f) y d, d⟫ + γ * ‖d‖ ^ 2) := by
  have h := congrArg (fun w => ⟪w, d⟫) hd
  simp only [inner_add_left, real_inner_smul_left, inner_neg_left, real_inner_self_eq_norm_sq] at h
  simp only [inner_add_left, real_inner_smul_left]
  linarith

section Steps

variable {f : E → ℝ} (hf : ContDiff ℝ 3 f) {L : ℝ} (hL : 0 ≤ L)
  (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
    fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖)
include hf hL hT

lemma newton_grid {γ r : ℝ} (hγ : 256 * L * r ^ 2 ≤ γ) (hr : 0 < r) (c y d : E)
    (hcoer : ∀ v, (3 * γ / 4) * ‖v‖ ^ 2 ≤ ⟪fderiv ℝ (gradient f) y v, v⟫ + γ * ‖v‖ ^ 2)
    (hd : fderiv ℝ (gradient f) y d + γ • d = -(gradient f y + γ • (y - c)))
    (hd0 : d ≠ 0) :
    ∃ t ∈ ({1, 1 / 2, 1 / 4, 1 / 8, -1} : Set ℝ),
      regF f γ c (y + (t * min 1 (r / ‖d‖)) • d) ≤ regF f γ c y -
        min ((⟪fderiv ℝ (gradient f) y d, d⟫ + γ * ‖d‖ ^ 2) / 64)
          (γ * r ^ 2 / 64 - L * r ^ 4) := by
  set Λ := ⟪fderiv ℝ (gradient f) y d, d⟫ + γ * ‖d‖ ^ 2 with hΛ
  set τm := min 1 (r / ‖d‖) with hτm
  have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  have hτ0 : 0 ≤ τm := le_min zero_le_one (div_nonneg hr.le hdn.le)
  have hτ1 : τm ≤ 1 := min_le_left _ _
  have hγ0 : 0 ≤ γ := le_trans (by positivity) hγ
  have hΛlow : (3 * γ / 4) * ‖d‖ ^ 2 ≤ Λ := hcoer d
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) hΛlow
  set e := τm • d with he
  have hge : ⟪gradient f y + γ • (y - c), e⟫ = -(τm * Λ) := by
    rw [he, real_inner_smul_right, residual_inner hd]; ring
  have hhe : ⟪fderiv ℝ (gradient f) y e, e⟫ + γ * ‖e‖ ^ 2 = τm ^ 2 * Λ := by
    rw [he, map_smul, real_inner_smul_left, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hτ0]
    rw [hΛ]; ring
  have happrox : ∀ t ∈ ({1, 1 / 2, 1 / 4, 1 / 8, -1} : Set ℝ),
      regF f γ c (y + t • e) ≤
        cubicModel (regF f γ c y) (τm * Λ) (τm ^ 2 * Λ)
          ⟪fderiv ℝ (fderiv ℝ (gradient f)) y e e, e⟫ t + L * ‖e‖ ^ 4 := by
    intro t ht
    have ht1 : |t| ≤ 1 := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with h | h | h | h | h <;> rw [h] <;> norm_num [abs_of_nonneg, abs_of_neg]
    have hle := (abs_le.mp (line_expansion hf hL hT γ c y e t)).2
    rw [hge, hhe] at hle
    have h4 : |t| ^ 4 ≤ 1 := pow_le_one₀ (abs_nonneg t) ht1
    have hE : L * ‖e‖ ^ 4 * |t| ^ 4 ≤ L * ‖e‖ ^ 4 :=
      mul_le_of_le_one_right (by positivity) h4
    unfold cubicModel
    linarith
  have hhle : τm ^ 2 * Λ ≤ τm * Λ := by
    have : τm ^ 2 ≤ τm := by nlinarith
    exact mul_le_mul_of_nonneg_right this hΛ0
  obtain ⟨t, ht, hφ⟩ := grid_descent (φ := fun t => regF f γ c (y + t • e))
    (mul_nonneg hτ0 hΛ0) hhle happrox
  refine ⟨t, ht, ?_⟩
  have hsm : (t * τm) • d = t • e := by rw [he, smul_smul]
  rw [hsm]
  refine hφ.trans ?_
  by_cases hcap : ‖d‖ ≤ r
  · have hτ1' : τm = 1 := by
      rw [hτm]; apply min_eq_left
      rw [le_div_iff₀ hdn]; linarith
    have heq : e = d := by rw [he, hτ1', one_smul]
    rw [heq, hτ1', one_mul]
    have h1 : L * ‖d‖ ^ 4 ≤ L * r ^ 2 * ‖d‖ ^ 2 := by
      have hd2 : ‖d‖ ^ 2 ≤ r ^ 2 := by nlinarith
      have e1 : L * ‖d‖ ^ 4 = (L * ‖d‖ ^ 2) * ‖d‖ ^ 2 := by ring
      rw [e1]
      calc (L * ‖d‖ ^ 2) * ‖d‖ ^ 2 ≤ (L * ‖d‖ ^ 2) * r ^ 2 :=
            mul_le_mul_of_nonneg_left hd2 (by positivity)
        _ = L * r ^ 2 * ‖d‖ ^ 2 := by ring
    have h2 : 192 * (L * r ^ 2 * ‖d‖ ^ 2) ≤ Λ := by nlinarith [sq_nonneg ‖d‖]
    have hmin := min_le_left (Λ / 64) (γ * r ^ 2 / 64 - L * r ^ 4)
    linarith
  · have hgt : r < ‖d‖ := lt_of_not_ge hcap
    have hτv : τm = r / ‖d‖ := by
      rw [hτm]; apply min_eq_right
      rw [div_le_one hdn]; exact hgt.le
    have hne : ‖e‖ = r := by
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ0, hτv]; field_simp
    rw [hne]
    have ha : 3 * γ / 4 * r ^ 2 ≤ τm * Λ := by
      rw [hτv]
      have h3 : 3 * γ / 4 * r ^ 2 ≤ r / ‖d‖ * (3 * γ / 4 * ‖d‖ ^ 2) := by
        have : r / ‖d‖ * (3 * γ / 4 * ‖d‖ ^ 2) = 3 * γ / 4 * r * ‖d‖ := by
          field_simp
        rw [this]
        have : r * r ≤ r * ‖d‖ := mul_le_mul_of_nonneg_left hgt.le hr.le
        nlinarith
      exact h3.trans (mul_le_mul_of_nonneg_left hΛlow (div_nonneg hr.le hdn.le))
    have hmin := min_le_right (Λ / 64) (γ * r ^ 2 / 64 - L * r ^ 4)
    linarith

end Steps

end LongTails.Proofs.LogFreeSteps
