import LongTails.Algorithms.AffineMomentAccelerated
import LongTails.Proofs.AcceleratedCoordinateEnergy

open scoped RealInnerProductSpace
open LongTails.Algorithms.AffineMomentAccelerated

namespace LongTails.Proofs.AffineMomentPrimal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma relative_pilot_geometry (q h : E) (hh : ‖h - q‖ ≤ ‖q‖ / 8) :
    ‖h‖ ≤ 9 / 8 * ‖q‖ ∧ 7 / 8 * ‖q‖ ≤ ‖h‖ ∧
      7 / 8 * ‖q‖ ^ 2 ≤ inner ℝ q h := by
  have ht := norm_add_le (h - q) q
  rw [sub_add_cancel] at ht
  have ht' := norm_add_le (q - h) h
  rw [sub_add_cancel, norm_sub_rev] at ht'
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm q (h - q))
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at hi
  have hm := mul_le_mul_of_nonneg_left hh (norm_nonneg q)
  exact ⟨by linarith, by linarith, by nlinarith⟩

lemma norm_primalVertex (h : E) : ‖primalVertex h‖ ≤ 4 := by
  by_cases hh : h = 0
  · simp [primalVertex, hh]
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  unfold primalVertex
  rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hn]
  norm_num
  rw [div_mul_cancel₀ _ hn.ne']

omit [InnerProductSpace ℝ E] in
lemma primalFraction_bounds (h : E) : 0 ≤ primalFraction h ∧ primalFraction h ≤ 1 := by
  exact ⟨le_min (by norm_num) (by positivity), min_le_left _ _⟩

lemma primal_radius (y h : E) (hy : ‖y‖ ≤ 4) : ‖primalStep y h‖ ≤ 4 := by
  have hg := primalFraction_bounds h
  have ht := norm_add_le ((1 - primalFraction h) • y) (primalFraction h • primalVertex h)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hg.2), abs_of_nonneg hg.1] at ht
  have h1 := mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr hg.2)
  have h2 := mul_le_mul_of_nonneg_left (norm_primalVertex h) hg.1
  unfold primalStep
  nlinarith only [ht, h1, h2]

lemma primal_direction {f : E → ℝ} (y u q h : E) (hu : ‖u‖ ≤ 1)
    (hh : ‖h - q‖ ≤ ‖q‖ / 8) (hq : 0 < ‖q‖)
    (hs : f y + inner ℝ q (u - y) ≤ f u) (hm : f u ≤ f y) :
    2 * ‖q‖ ≤ inner ℝ q (y - primalVertex h) := by
  have hg := relative_pilot_geometry q h hh
  have hh0 : 0 < ‖h‖ := by linarith [hg.2.1]
  have huq := neg_le_of_abs_le (abs_real_inner_le_norm q u)
  have hum := mul_le_mul_of_nonneg_left hu (norm_nonneg q)
  have hys : 0 ≤ inner ℝ q (y - u) := by
    rw [inner_sub_right] at hs ⊢
    linarith
  have hy : -‖q‖ ≤ inner ℝ q y := by
    rw [inner_sub_right] at hys
    linarith
  have hhq : (3 / 4) * ‖q‖ * ‖h‖ ≤ inner ℝ q h := by
    have ht := mul_le_mul_of_nonneg_left hg.1 (show 0 ≤ (3 / 4) * ‖q‖ by positivity)
    nlinarith [hg.2.2, sq_nonneg ‖q‖]
  have hd : (3 / 4) * ‖q‖ ≤ inner ℝ q h / ‖h‖ := (le_div_iff₀ hh0).mpr hhq
  unfold primalVertex
  rw [inner_sub_right, inner_smul_right]
  have he : (-4 / ‖h‖) * inner ℝ q h = -4 * (inner ℝ q h / ‖h‖) := by ring
  rw [he]
  linarith

lemma primal_descent {f : E → ℝ} (y u q h : E) (hy : ‖y‖ ≤ 4) (hu : ‖u‖ ≤ 1)
    (hq : ‖q‖ ≤ 5) (hh : ‖h - q‖ ≤ ‖q‖ / 8)
    (hs : f y + inner ℝ q (u - y) ≤ f u) (hm : f u ≤ f y)
    (hsm : f (primalStep y h) ≤ f y + inner ℝ q (primalStep y h - y) +
      (1 / 2) * ‖primalStep y h - y‖ ^ 2) :
    f (primalStep y h) ≤ f y - ‖q‖ ^ 2 / 1024 := by
  by_cases hq0 : q = 0
  · have hh0 : h = 0 := by simpa [hq0] using hh
    simp [hq0, hh0, primalStep, primalFraction]
  have hqpos := norm_pos_iff.mpr hq0
  have hg := relative_pilot_geometry q h hh
  have hγ : primalFraction h = ‖h‖ / 128 := min_eq_right (by linarith [hg.1])
  have hdir := primal_direction y u q h hu hh hqpos hs hm
  have hn : ‖primalVertex h - y‖ ≤ 8 :=
    (norm_sub_le _ _).trans (by linarith [norm_primalVertex h])
  have he : primalStep y h - y = primalFraction h • (primalVertex h - y) := by
    unfold primalStep
    module
  rw [he, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (primalFraction_bounds h).1, hγ, mul_pow] at hsm
  have hi : inner ℝ q (primalVertex h - y) = -inner ℝ q (y - primalVertex h) := by
    simp only [inner_sub_right]; ring
  rw [hi] at hsm
  have h1 := mul_le_mul_of_nonneg_left hdir (show 0 ≤ ‖h‖ / 128 by positivity)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (1 / 2 : ℝ) * (‖h‖ / 128) ^ 2 by positivity)
  have h4 := mul_le_mul_of_nonneg_left hg.1 (norm_nonneg h)
  have h5 := mul_le_mul_of_nonneg_right hg.2.1 (norm_nonneg q)
  nlinarith only [hsm, h1, h3, h4, h5]


omit [InnerProductSpace ℝ E] in
lemma mixed_pilot_norm (q h : E) {ν : ℝ} (hh : ‖h - q‖ ≤ ‖q‖ / 8 + ν) :
    ‖h‖ ≤ 9 / 8 * ‖q‖ + ν ∧ 7 / 8 * ‖q‖ - ν ≤ ‖h‖ := by
  have ht := norm_add_le (h - q) q
  rw [sub_add_cancel] at ht
  have ht' := norm_add_le (q - h) h
  rw [sub_add_cancel, norm_sub_rev] at ht'
  constructor <;> linarith

lemma mixed_primal_direction {f : E → ℝ} (y u q h : E) (hu : ‖u‖ ≤ 1)
    {ν : ℝ} (hh : ‖h - q‖ ≤ ‖q‖ / 8 + ν) (hh0 : 0 < ‖h‖)
    (hs : f y + inner ℝ q (u - y) ≤ f u) (hm : f u ≤ f y) :
    2 * ‖q‖ - 8 * ν ≤ inner ℝ q (y - primalVertex h) := by
  have huq := neg_le_of_abs_le (abs_real_inner_le_norm q u)
  have hum := mul_le_mul_of_nonneg_left hu (norm_nonneg q)
  have hy : -‖q‖ ≤ inner ℝ q y := by
    rw [inner_sub_right] at hs
    linarith
  have hi := neg_le_of_abs_le (abs_real_inner_le_norm (q - h) h)
  rw [inner_sub_left, real_inner_self_eq_norm_sq, norm_sub_rev q] at hi
  have ht := norm_le_norm_sub_add q h
  rw [norm_sub_rev q] at ht
  have ht' := mul_le_mul_of_nonneg_right ht (norm_nonneg h)
  have hd : ‖q‖ - 2 * ‖h - q‖ ≤ inner ℝ q h / ‖h‖ := by
    apply (le_div_iff₀ hh0).mpr
    nlinarith only [hi, ht']
  unfold primalVertex
  rw [inner_sub_right, inner_smul_right]
  have he : (-4 / ‖h‖) * inner ℝ q h = -4 * (inner ℝ q h / ‖h‖) := by ring
  rw [he]
  linarith

lemma mixed_primal_descent {f : E → ℝ} (y u q h : E) (hy : ‖y‖ ≤ 4) (hu : ‖u‖ ≤ 1)
    (hq : ‖q‖ ≤ 5) {ν : ℝ} (hν : 0 ≤ ν) (hν1 : ν ≤ 1)
    (hh : ‖h - q‖ ≤ ‖q‖ / 8 + ν)
    (hs : f y + inner ℝ q (u - y) ≤ f u) (hm : f u ≤ f y)
    (hsm : f (primalStep y h) ≤ f y + inner ℝ q (primalStep y h - y) +
      (1 / 2) * ‖primalStep y h - y‖ ^ 2) :
    f (primalStep y h) ≤ f y - ‖q‖ ^ 2 / 1024 + ν ^ 2 := by
  have hg := mixed_pilot_norm q h hh
  by_cases hh0 : h = 0
  · have hqn : ‖q‖ ≤ 8 / 7 * ν := by
      have hz := hg.2
      simp only [hh0, norm_zero] at hz
      linarith
    have hsq := mul_self_le_mul_self (norm_nonneg q) hqn
    simp only [hh0, primalStep, primalFraction, norm_zero, zero_div, min_eq_right
      (show (0 : ℝ) ≤ 1 by norm_num), sub_zero, one_smul, zero_smul, add_zero]
    nlinarith [sq_nonneg ν]
  have hγ : primalFraction h = ‖h‖ / 128 := min_eq_right (by linarith [hg.1])
  have hdir := mixed_primal_direction y u q h hu hh (norm_pos_iff.mpr hh0) hs hm
  have hn : ‖primalVertex h - y‖ ≤ 8 :=
    (norm_sub_le _ _).trans (by linarith [norm_primalVertex h])
  have he : primalStep y h - y = primalFraction h • (primalVertex h - y) := by
    unfold primalStep
    module
  rw [he, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (primalFraction_bounds h).1, hγ, mul_pow] at hsm
  have hi : inner ℝ q (primalVertex h - y) = -inner ℝ q (y - primalVertex h) := by
    simp only [inner_sub_right]; ring
  rw [hi] at hsm
  have h1 := mul_le_mul_of_nonneg_left hdir (show 0 ≤ ‖h‖ / 128 by positivity)
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ (1 / 2 : ℝ) * (‖h‖ / 128) ^ 2 by positivity)
  have h4 := mul_le_mul_of_nonneg_left hg.1 (norm_nonneg h)
  have h5 := mul_le_mul_of_nonneg_right hg.2 (norm_nonneg q)
  have h6 := mul_le_mul_of_nonneg_right hg.1 hν
  nlinarith only [hsm, h1, h3, h4, h5, h6, sq_nonneg (‖q‖ - 11 * ν),
    sq_nonneg ‖q‖, sq_nonneg ν]

end LongTails.Proofs.AffineMomentPrimal
