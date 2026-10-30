import Mathlib.Tactic

namespace LongTails.Proofs.DerivativePerceptronCounting

lemma energy_contradiction (E K K₀ κ r δ Λ : ℝ)
    (hK : 0 < K) (hK₀ : 0 ≤ K₀) (hκ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hr : 0 < r) (hr₁ : r ≤ 1)
    (hinit : 16777216 * K₀ ≤ κ ^ 2 * r ^ 2 * K)
    (hlinear : 65536 ≤ κ ^ 2 * K) (hΛ : 1024 * Λ ≤ κ ^ 2)
    (hcubic : 16384 * δ * K ≤ κ ^ 2)
    (hupper : E ≤ 4112 * K₀ ^ 2 + 9 * K + 8192 * K * K₀ / r ^ 2 +
      Λ * K ^ 2 + 16 * δ * K ^ 3)
    (hlower : κ ^ 2 * K ^ 2 / 64 ≤ E) : False := by
  have hr₂ : r ^ 2 ≤ 1 := by nlinarith [hr.le]
  have hκ₂ : κ ^ 2 ≤ κ := by nlinarith [hκ.le]
  have hprod := mul_le_mul_of_nonneg_left hr₂ (sq_nonneg κ)
  have hκr : κ ^ 2 * r ^ 2 ≤ κ := by nlinarith
  have hmulK := mul_le_mul_of_nonneg_right hκr hK.le
  have hsmall : 16777216 * K₀ ≤ κ * K := hinit.trans hmulK
  have hsq := mul_nonneg (sub_nonneg.mpr hsmall)
    (show 0 ≤ κ * K + 16777216 * K₀ by positivity)
  have hinitial : 4112 * K₀ ^ 2 ≤ κ ^ 2 * K ^ 2 / 65536 := by nlinarith [sq_nonneg K₀]
  have hlinmul := mul_le_mul_of_nonneg_right hlinear hK.le
  have hlin : 9 * K ≤ 9 * κ ^ 2 * K ^ 2 / 65536 := by nlinarith
  have hnoisemul := mul_le_mul_of_nonneg_right hinit hK.le
  have hnoise : 8192 * K * K₀ / r ^ 2 ≤ κ ^ 2 * K ^ 2 / 2048 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith
  have hΛmul := mul_le_mul_of_nonneg_right hΛ (sq_nonneg K)
  have hΛbound : Λ * K ^ 2 ≤ κ ^ 2 * K ^ 2 / 1024 := by nlinarith
  have hcubmul := mul_le_mul_of_nonneg_right hcubic (sq_nonneg K)
  have hcub : 16 * δ * K ^ 3 ≤ κ ^ 2 * K ^ 2 / 1024 := by nlinarith
  have hpos : 0 < κ ^ 2 * K ^ 2 := mul_pos (sq_pos_of_pos hκ) (sq_pos_of_pos hK)
  nlinarith

noncomputable def leakage (h A ρ : ℝ) : ℝ :=
  4096 * h ^ 4 / ρ ^ 2 + 12 * h ^ 2 / ρ + 16 * A * h ^ 2 / ρ ^ 2 +
    24 * h ^ 2 + 16 * h ^ 4 * A + 16 * A

lemma scaled_increment_identity (δ h A r K K₀ : ℝ) (hh : 0 < h) (hr : 0 < r) :
    let ρ := r * h
    let J := 4096 * δ * K₀ / ρ ^ 2 + 16 * δ * K * A / ρ ^ 2
    let D := 4096 * δ * K₀ / ρ ^ 2 + 12 * δ * K / ρ + J + 24 * δ * K +
      16 * h ^ 2 * δ * K * A
    9 * δ + 4 * δ * A * (4 * K) + δ ^ 2 * (4 * K) ^ 2 +
      h ^ 4 * (4096 * δ * K / ρ ^ 2) + h ^ 2 * D =
      δ * (9 + 8192 * K₀ / r ^ 2 + leakage h A ρ * K + 16 * δ * K ^ 2) := by
  dsimp [leakage]
  field_simp
  ring

lemma leakage_substitution (h r : ℝ) (hh : 0 < h) (hr : 0 < r) :
    leakage h h (r * h) = 4096 * h ^ 2 / r ^ 2 + 12 * h / r + 16 * h / r ^ 2 +
      24 * h ^ 2 + 16 * h ^ 5 + 16 * h := by
  unfold leakage
  field_simp

lemma leakage_bound (h r : ℝ) (hh : 0 < h) (hr : 0 < r)
    (hhsmall : h ≤ 1 / 4096) (hr₁ : r ≤ 1) : leakage h h (r * h) ≤ 128 * h / r ^ 2 := by
  have hh₁ : h ≤ 1 := by linarith
  have hr₂ : r ^ 2 ≤ 1 := by nlinarith [hr.le]
  have hrr : r ^ 2 ≤ r := by nlinarith [hr.le]
  have hh₂ : h ^ 2 ≤ h := by nlinarith [hh.le]
  have hh₄ : h ^ 4 ≤ 1 := by
    have ht := pow_le_pow_left₀ hh.le hh₁ 4
    simpa using ht
  have hh₅ : h ^ 5 ≤ h := by
    have ht := mul_le_mul_of_nonneg_left hh₄ hh.le
    nlinarith
  have hdiv : h ≤ h / r ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hr₂ hh.le]
  have ht₁ : 4096 * h ^ 2 / r ^ 2 ≤ h / r ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg r)
    nlinarith [mul_le_mul_of_nonneg_left hhsmall hh.le]
  have ht₂ : 12 * h / r ≤ 12 * h / r ^ 2 := by
    apply (div_le_div_iff₀ hr (sq_pos_of_pos hr)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hrr hh.le]
  have hn : 0 ≤ h / r ^ 2 := by positivity
  rw [leakage_substitution h r hh hr]
  simp only [div_eq_mul_inv] at hdiv ht₁ ht₂ hn ⊢
  nlinarith

lemma restart_energy_bound (z a δ ρ K₀ : ℝ)
    (hz : 0 ≤ z) (hδ : 0 ≤ δ) (hρ : 0 < ρ) (hK₀ : 0 ≤ K₀)
    (hzbound : z ≤ 4 * K₀) (habound : a ^ 2 ≤ 4096 * δ * K₀ / ρ ^ 2)
    (hsize : 1 ≤ ρ ^ 2 * K₀) : δ * z ^ 2 + a ^ 2 ≤ 4112 * δ * K₀ ^ 2 := by
  have hzsq : z ^ 2 ≤ 16 * K₀ ^ 2 := by nlinarith
  have hzδ := mul_le_mul_of_nonneg_left hzsq hδ
  have ha : 4096 * δ * K₀ / ρ ^ 2 ≤ 4096 * δ * K₀ ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hρ)).mpr
    have hm := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 4096 * δ * K₀ by positivity)
    nlinarith
  linarith

lemma barrier_parameters (δ A h ρ K K₀ : ℝ)
    (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hρ : 0 < ρ) (hK : 0 ≤ K) (hK₀ : 0 ≤ K₀) :
    let Q := 4096 * δ * K₀ / ρ ^ 2
    let J := Q + 16 * δ * K * A / ρ ^ 2
    let D := Q + 12 * δ * K / ρ + J + 24 * δ * K + 16 * h ^ 2 * δ * K * A
    0 ≤ J ∧ J ≤ D ∧ Q ≤ J ∧ Q ≤ D ∧
      4 * (δ * (4 * K)) * A ≤ ρ ^ 2 * J ∧
      (3 * δ * (4 * K)) / ρ + J + 2 * (3 * δ * (4 * K)) +
        4 * h ^ 2 * (δ * (4 * K)) * A ≤ D := by
  have hQ : 0 ≤ 4096 * δ * K₀ / ρ ^ 2 := by positivity
  have he : 0 ≤ 16 * δ * K * A / ρ ^ 2 := by positivity
  have hS : 0 ≤ 12 * δ * K / ρ := by positivity
  have hlin : 0 ≤ 24 * δ * K := by positivity
  have hquad : 0 ≤ 16 * h ^ 2 * δ * K * A := by positivity
  have hid : ρ ^ 2 * (4096 * δ * K₀ / ρ ^ 2 + 16 * δ * K * A / ρ ^ 2) =
      4096 * δ * K₀ + 16 * δ * K * A := by field_simp
  dsimp only
  refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · nlinarith [mul_nonneg hδ hK₀]
  · simp only [div_eq_mul_inv] at hQ hS he ⊢
    nlinarith

lemma mass_sharp (D C K x L ρ : ℝ) (hD : 0 < D) (hC : 0 ≤ C) (hx : 0 ≤ x)
    (hmass : D * K ≤ C * L) (hlog : x * L ≤ 1)
    (hcontrast : 16384 * C * x ≤ ρ ^ 2 * D) : 16384 * x ^ 2 * K ≤ ρ ^ 2 := by
  have hm := mul_le_mul_of_nonneg_right hmass (sq_nonneg x)
  have hl := mul_le_mul_of_nonneg_left hlog (mul_nonneg hC hx)
  have hh : D * (16384 * x ^ 2 * K) ≤ D * ρ ^ 2 := by
    nlinarith only [hm, hl, hcontrast]
  exact (mul_le_mul_iff_right₀ hD).mp hh

lemma mass_quadratic (D C K x L : ℝ) (hD : 0 < D) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hx : 0 ≤ x) (hL : 0 ≤ L)
    (hmass : D * K ≤ C * L) (hlog : x * L ^ 2 ≤ 4)
    (hcontrast : 64 * C ^ 2 * x ≤ D ^ 2) : x ^ 2 * K ^ 2 ≤ 1 / 16 := by
  have hs := mul_nonneg (sub_nonneg.mpr hmass)
    (add_nonneg (mul_nonneg hC hL) (mul_nonneg hD.le hK))
  have hsq : D ^ 2 * K ^ 2 ≤ C ^ 2 * L ^ 2 := by nlinarith only [hs]
  have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg x)
  have hl := mul_le_mul_of_nonneg_left hlog (mul_nonneg (sq_nonneg C) hx)
  have hh : D ^ 2 * (16 * x ^ 2 * K ^ 2) ≤ D ^ 2 * 1 := by
    nlinarith only [hm, hl, hcontrast]
  have hc := (mul_le_mul_iff_right₀ (sq_pos_of_pos hD)).mp hh
  linarith only [hc]

end LongTails.Proofs.DerivativePerceptronCounting
