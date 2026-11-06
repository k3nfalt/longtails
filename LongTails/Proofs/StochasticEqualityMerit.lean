import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import LongTails.Proofs.GdConvex
import Mathlib.Tactic

namespace LongTails.Proofs.StochasticEqualityMerit

open scoped RealInnerProductSpace

lemma quadratic_remainder {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {D : E → E →L[ℝ] F}
    {L : ℝ} (hL : 0 ≤ L) (hf : ∀ x, HasFDerivAt f (D x) x)
    (hD : ∀ x y, ‖D y - D x‖ ≤ L * ‖y - x‖) (x y : E) :
    ‖f y - f x - D x (y - x)‖ ≤ L * ‖y - x‖ ^ 2 := by
  have hd : ∀ z ∈ segment ℝ x y,
      HasFDerivWithinAt (fun z => f z - D x z) (D z - D x) (segment ℝ x y) z := by
    intro z _
    exact ((hf z).sub (D x).hasFDerivAt).hasFDerivWithinAt
  have hb : ∀ z ∈ segment ℝ x y, ‖D z - D x‖ ≤ L * ‖y - x‖ := by
    intro z hz
    exact (hD x z).trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hL)
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hd hb
    (convex_segment x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have he : (f y - D x y) - (f x - D x x) = f y - f x - D x (y - x) := by
    rw [map_sub]
    abel
  rw [he] at h
  convert h using 1; ring

lemma objective_upper {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {g : E → E} {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x, HasGradientAt f (g x) x)
    (hg : ∀ x y, ‖g y - g x‖ ≤ L * ‖y - x‖) (x y : E) :
    f y - f x ≤ ⟪g x, y - x⟫ + L * ‖y - x‖ ^ 2 := by
  have h := OracleTemplate.Gradient.smooth_upper_bound hf (fun x y => hg y x) x y
  have hp := mul_nonneg hL (sq_nonneg ‖y - x‖)
  linarith only [h, hp]

lemma multiplier_pairing_increment {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {u v c c' q : F} {B K Lc LJ t : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hu : ‖u‖ ≤ B) (hv : ‖v - u‖ ≤ K * t)
    (hc : ‖c' - c‖ ≤ Lc * t) (hr : ‖c' - c - q‖ ≤ LJ * t ^ 2) :
    ⟪v, c'⟫ - ⟪u, c⟫ ≤ ⟪u, q⟫ + K * t * ‖c‖ + (B * LJ + K * Lc) * t ^ 2 := by
  have he : ⟪v, c'⟫ - ⟪u, c⟫ = ⟪u, q⟫ + ⟪u, c' - c - q⟫ +
      ⟪v - u, c⟫ + ⟪v - u, c' - c⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have h₁ : ⟪u, c' - c - q⟫ ≤ B * (LJ * t ^ 2) := by
    apply (real_inner_le_norm _ _).trans
    gcongr
  have h₂ : ⟪v - u, c⟫ ≤ K * t * ‖c‖ := by
    apply (real_inner_le_norm _ _).trans
    gcongr
  have h₃ : ⟪v - u, c' - c⟫ ≤ (K * t) * (Lc * t) := by
    apply (real_inner_le_norm _ _).trans
    gcongr
  rw [he]
  nlinarith only [h₁, h₂, h₃]

lemma constraint_square_increment {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {c c' q : F} {Lc LJ t : ℝ}
    (hLc : 0 ≤ Lc) (ht : 0 ≤ t)
    (hc : ‖c' - c‖ ≤ Lc * t) (hr : ‖c' - c - q‖ ≤ LJ * t ^ 2) :
    ‖c'‖ ^ 2 - ‖c‖ ^ 2 ≤ 2 * ⟪c, q⟫ + (2 * ‖c‖ * LJ + Lc ^ 2) * t ^ 2 := by
  have he := norm_add_sq_real c (c' - c)
  rw [add_sub_cancel] at he
  have hi : ⟪c, c' - c - q⟫ ≤ ‖c‖ * (LJ * t ^ 2) := by
    apply (real_inner_le_norm _ _).trans
    gcongr
  rw [inner_sub_right] at hi
  have hs : ‖c' - c‖ ^ 2 ≤ (Lc * t) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hLc ht)).mpr hc
  nlinarith only [he, hi, hs]

lemma combined_merit_increment {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {u v c c' q : F} {f f' linear B K Lf Lc LJ t β : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hLc : 0 ≤ Lc) (ht : 0 ≤ t) (hβ : 0 ≤ β)
    (hf : f' - f ≤ linear + Lf * t ^ 2)
    (hu : ‖u‖ ≤ B) (hv : ‖v - u‖ ≤ K * t)
    (hc : ‖c' - c‖ ≤ Lc * t) (hr : ‖c' - c - q‖ ≤ LJ * t ^ 2) :
    (f' + ⟪v, c'⟫ + β * ‖c'‖ ^ 2 / 2) -
      (f + ⟪u, c⟫ + β * ‖c‖ ^ 2 / 2) ≤
      linear + ⟪u, q⟫ + β * ⟪c, q⟫ + K * t * ‖c‖ +
      (Lf + B * LJ + K * Lc + β * (‖c‖ * LJ + Lc ^ 2 / 2)) * t ^ 2 := by
  have hp := multiplier_pairing_increment hB hK ht hu hv hc hr
  have hs := mul_le_mul_of_nonneg_left (constraint_square_increment hLc ht hc hr) hβ
  nlinarith only [hf, hp, hs]

lemma orthogonal_direction_linear {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a b e : E} {β : ℝ} (hβ : 0 ≤ β) (hab : ⟪a, b⟫ = 0) :
    ⟪a + β • b, -a - b + e⟫ ≤
      -‖a‖ ^ 2 - β * ‖b‖ ^ 2 + ‖a‖ * ‖e‖ + β * ‖b‖ * ‖e‖ := by
  have hba : ⟪b, a⟫ = 0 := by rw [real_inner_comm]; exact hab
  simp only [inner_add_left, inner_add_right, inner_sub_right, inner_neg_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq, hab, hba]
  have h₁ := real_inner_le_norm a e
  have h₂ := mul_le_mul_of_nonneg_left (real_inner_le_norm b e) hβ
  nlinarith only [h₁, h₂]

lemma orthogonal_direction_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a b e : E} (hab : ⟪a, b⟫ = 0) :
    ‖-a - b + e‖ ≤ ‖a‖ + ‖b‖ + ‖e‖ ∧
    ‖-a - b + e‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖e‖ ^ 2) := by
  have he : -a - b + e = -(a + b) + e := by abel
  rw [he]
  have ht : ‖-(a + b) + e‖ ≤ ‖a + b‖ + ‖e‖ := by
    simpa only [norm_neg] using norm_add_le (-(a + b)) e
  constructor
  · exact ht.trans (add_le_add (norm_add_le a b) le_rfl)
  · have hs := norm_add_sq_real a b
    rw [hab, mul_zero, add_zero] at hs
    have hsq : ‖-(a + b) + e‖ ^ 2 ≤ (‖a + b‖ + ‖e‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ht
    nlinarith only [hs, hsq, sq_nonneg (‖a + b‖ - ‖e‖)]

lemma quadratic_absorption {a b e k β : ℝ} (hk : 0 ≤ k)
    (hβ : 8 * (k ^ 2 + k + 1) ≤ β) :
    -a ^ 2 - β * b ^ 2 + a * e + β * b * e + k * (a + b + e) * b +
        (a ^ 2 + b ^ 2 + e ^ 2) / 8 ≤
      -a ^ 2 / 2 - β * b ^ 2 / 4 + (β + 3) * e ^ 2 := by
  have hβ0 : 0 ≤ β := by nlinarith [sq_nonneg k]
  have h₁ : k * a * b ≤ a ^ 2 / 8 + 2 * k ^ 2 * b ^ 2 := by
    nlinarith only [sq_nonneg (a - 4 * k * b)]
  have h₂ : k * e * b ≤ e ^ 2 / 2 + k ^ 2 * b ^ 2 / 2 := by
    nlinarith only [sq_nonneg (e - k * b)]
  have h₃ : a * e ≤ a ^ 2 / 8 + 2 * e ^ 2 := by
    nlinarith only [sq_nonneg (a - 4 * e)]
  have h₄ : β * b * e ≤ β * b ^ 2 / 4 + β * e ^ 2 := by
    nlinarith only [mul_nonneg hβ0 (sq_nonneg (b - 2 * e))]
  have h₅ := mul_le_mul_of_nonneg_right hβ (sq_nonneg b)
  have h₆ := mul_nonneg hk (sq_nonneg b)
  nlinarith only [h₁, h₂, h₃, h₄, h₅, h₆, sq_nonneg a, sq_nonneg b,
    sq_nonneg e, sq_nonneg (k * b)]

lemma merit_lower_bound {f f₀ β c B cross : ℝ} (hf : f₀ ≤ f)
    (hβ : 0 < β) (hcross : -B * c ≤ cross) :
    f₀ + β * c ^ 2 / 4 - B ^ 2 / β ≤ f + cross + β * c ^ 2 / 2 := by
  have hsq : 0 ≤ (β * c - 2 * B) ^ 2 / (4 * β) := by positivity
  field_simp at hsq ⊢
  nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr hf),
    mul_nonneg hβ.le (sub_nonneg.mpr hcross)]

lemma merit_step {φ φ' a b e d k β D η : ℝ} (hb : 0 ≤ b)
    (hk : 0 ≤ k) (hη : 0 ≤ η) (hβ : 8 * (k ^ 2 + k + 1) ≤ β)
    (hd : d ≤ a + b + e) (hd₂ : d ^ 2 ≤ 2 * (a ^ 2 + b ^ 2 + e ^ 2))
    (hηD : D * η ≤ 1 / 16)
    (hstep : φ' - φ ≤
      η * (-a ^ 2 - β * b ^ 2 + a * e + β * b * e + k * d * b) +
        D * η ^ 2 * d ^ 2) :
    φ' ≤ φ - η * a ^ 2 / 2 - η * β * b ^ 2 / 4 + η * (β + 3) * e ^ 2 := by
  have hlinear : k * d * b ≤ k * (a + b + e) * b := by
    nlinarith only [mul_le_mul_of_nonneg_right hd (mul_nonneg hk hb)]
  have hcurv : D * η ^ 2 * d ^ 2 ≤ η * (a ^ 2 + b ^ 2 + e ^ 2) / 8 := by
    have h₁ : D * η * d ^ 2 ≤ (a ^ 2 + b ^ 2 + e ^ 2) / 8 := by
      nlinarith only [mul_le_mul_of_nonneg_right hηD (sq_nonneg d), hd₂]
    nlinarith only [mul_le_mul_of_nonneg_left h₁ hη]
  have hquad := mul_le_mul_of_nonneg_left
    (quadratic_absorption (a := a) (b := b) (e := e) hk hβ) hη
  have hlin := mul_le_mul_of_nonneg_left hlinear hη
  nlinarith only [hstep, hcurv, hquad, hlin]

lemma inexact_merit_step {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a b e : E} {φ φ' k β D η : ℝ}
    (hab : ⟪a, b⟫ = 0) (hk : 0 ≤ k) (hη : 0 ≤ η)
    (hβ : 8 * (k ^ 2 + k + 1) ≤ β) (hηD : D * η ≤ 1 / 16)
    (hstep : φ' - φ ≤ ⟪a + β • b, η • (-a - b + e)⟫ +
      k * ‖η • (-a - b + e)‖ * ‖b‖ + D * ‖η • (-a - b + e)‖ ^ 2) :
    φ' ≤ φ - η * ‖a‖ ^ 2 / 2 - η * β * ‖b‖ ^ 2 / 4 +
      η * (β + 3) * ‖e‖ ^ 2 := by
  have hβ0 : 0 ≤ β := by nlinarith [sq_nonneg k]
  have hnorm := orthogonal_direction_norm (e := e) hab
  apply merit_step (norm_nonneg b) hk hη hβ hnorm.1 hnorm.2 hηD
  simp only [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη, mul_pow] at hstep
  have hl := mul_le_mul_of_nonneg_left (orthogonal_direction_linear (e := e) hβ0 hab) hη
  nlinarith only [hstep, hl]

lemma relative_merit_lower {F β c u g ν L cross : ℝ} (hF : 0 ≤ F)
    (hβ : 0 < β) (hν : 0 < ν) (hu : 0 ≤ u) (hg : 0 ≤ g)
    (huG : ν * u ≤ g) (hgF : g ^ 2 ≤ 2 * L * F)
    (hβL : 4 * L ≤ β * ν ^ 2) (hcross : -u * c ≤ cross) :
    F / 2 + β * c ^ 2 / 4 ≤ F + cross + β * c ^ 2 / 2 := by
  have hs : (ν * u) ^ 2 ≤ g ^ 2 := (sq_le_sq₀ (by positivity) hg).mpr huG
  have hb := mul_le_mul_of_nonneg_right hβL hF
  have hu2 : u ^ 2 ≤ β * F / 2 := by
    nlinarith [sq_pos_of_pos hν]
  have hd : u ^ 2 / β ≤ F / 2 := by
    apply (div_le_iff₀ hβ).mpr
    nlinarith only [hu2]
  have hm := merit_lower_bound (f := F) (f₀ := F) (le_refl F) hβ hcross
  linarith only [hm, hd]

lemma constraint_bound_of_merit {f f₀ β c B cross U : ℝ} (hf : f₀ ≤ f)
    (hβ : 0 < β) (hcross : -B * c ≤ cross)
    (hupper : f + cross + β * c ^ 2 / 2 ≤ f₀ + U) :
    c ^ 2 ≤ 4 * (U + B ^ 2 / β) / β := by
  have h := merit_lower_bound hf hβ hcross
  apply (le_div_iff₀ hβ).mpr
  nlinarith only [h, hupper]

end LongTails.Proofs.StochasticEqualityMerit
