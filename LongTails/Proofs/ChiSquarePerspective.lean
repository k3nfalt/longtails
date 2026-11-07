import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped RealInnerProductSpace

namespace OracleTemplate.ChiSquareDro

noncomputable def phi (c u η s : ℝ) : ℝ := η + c * u ^ 2 / (2 * s) + c * s / 2

lemma quad_over_lin {u u' s s' : ℝ} (hs : 0 < s) (hs' : 0 < s') :
    u ^ 2 / s + 2 * u / s * (u' - u) - u ^ 2 / s ^ 2 * (s' - s) ≤ u' ^ 2 / s' := by
  have key : u' ^ 2 / s' - (u ^ 2 / s + 2 * u / s * (u' - u) - u ^ 2 / s ^ 2 * (s' - s)) =
      (u' - u * s' / s) ^ 2 / s' := by
    field_simp
    ring
  have : 0 ≤ (u' - u * s' / s) ^ 2 / s' := div_nonneg (sq_nonneg _) hs'.le
  linarith

lemma tail_step {l l' η η' a : ℝ} (hsub : l + a ≤ l') :
    max (l - η) 0 * (max (l' - η') 0 - max (l - η) 0) ≥ max (l - η) 0 * (a - (η' - η)) := by
  rcases le_total (l - η) 0 with h | h
  · rw [max_eq_right h]; simp
  · rw [max_eq_left h]
    have h1 : l' - η' ≤ max (l' - η') 0 := le_max_left _ _
    have : (a - (η' - η)) ≤ max (l' - η') 0 - (l - η) := by linarith
    exact mul_le_mul_of_nonneg_left this h

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma sample_ineq {c : ℝ} (hc : 0 ≤ c) {l l' η η' s s' : ℝ} {g dx : E}
    (hs : 0 < s) (hs' : 0 < s') (hsub : l + ⟪g, dx⟫ ≤ l') :
    phi c (max (l - η) 0) η s + c * max (l - η) 0 / s * ⟪g, dx⟫ +
        (1 - c * max (l - η) 0 / s) * (η' - η) +
        (c / 2 - c * max (l - η) 0 ^ 2 / (2 * s ^ 2)) * (s' - s) ≤
      phi c (max (l' - η') 0) η' s' := by
  set u := max (l - η) 0
  set u' := max (l' - η') 0
  have hq := quad_over_lin (u := u) (u' := u') hs hs'
  have ht := tail_step (η := η) (η' := η') hsub
  have h2 : 2 * u / s * (u' - u) ≥ 2 / s * (u * (⟪g, dx⟫ - (η' - η))) := by
    have : 2 * u / s * (u' - u) = 2 / s * (u * (u' - u)) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  have hmain : u ^ 2 / s + 2 / s * (u * (⟪g, dx⟫ - (η' - η))) - u ^ 2 / s ^ 2 * (s' - s) ≤
      u' ^ 2 / s' := by linarith
  have hc2 : 0 ≤ c / 2 := by positivity
  have := mul_le_mul_of_nonneg_left hmain hc2
  unfold phi
  have e1 : c * u ^ 2 / (2 * s) = c / 2 * (u ^ 2 / s) := by ring
  have e2 : c * u' ^ 2 / (2 * s') = c / 2 * (u' ^ 2 / s') := by ring
  rw [e1, e2]
  have e3 : c / 2 * (u ^ 2 / s + 2 / s * (u * (⟪g, dx⟫ - (η' - η))) - u ^ 2 / s ^ 2 * (s' - s)) =
      c / 2 * (u ^ 2 / s) + c * u / s * ⟪g, dx⟫ - c * u / s * (η' - η) -
        c * u ^ 2 / (2 * s ^ 2) * (s' - s) := by
    field_simp; ring
  rw [e3] at this
  nlinarith [this]

lemma noise_x {c G u s : ℝ} {g : E} (hg : ‖g‖ ≤ G) :
    ‖(c * u / s) • g‖ ^ 2 ≤ c ^ 2 * G ^ 2 * u ^ 2 / s ^ 2 := by
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h1 : ‖g‖ ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  have h2 : (c * u / s) ^ 2 = c ^ 2 * u ^ 2 / s ^ 2 := by ring
  rw [h2]
  have : 0 ≤ c ^ 2 * u ^ 2 / s ^ 2 := by positivity
  calc c ^ 2 * u ^ 2 / s ^ 2 * ‖g‖ ^ 2 ≤ c ^ 2 * u ^ 2 / s ^ 2 * G ^ 2 :=
        mul_le_mul_of_nonneg_left h1 this
    _ = _ := by ring

lemma noise_eta {c u s : ℝ} : (1 - c * u / s) ^ 2 ≤ 2 + 2 * c ^ 2 * u ^ 2 / s ^ 2 := by
  rw [show 2 * c ^ 2 * u ^ 2 / s ^ 2 = 2 * (c * u / s) ^ 2 by ring]
  nlinarith [sq_nonneg (1 + c * u / s)]

lemma noise_s {c u s B : ℝ} (hs : 0 < s) (hu : 0 ≤ u) (huB : u ≤ B) :
    (c / 2 - c * u ^ 2 / (2 * s ^ 2)) ^ 2 ≤ c ^ 2 / 2 + c ^ 2 * B ^ 2 * u ^ 2 / (2 * s ^ 4) := by
  have h1 : (c / 2 - c * u ^ 2 / (2 * s ^ 2)) ^ 2 ≤
      2 * (c / 2) ^ 2 + 2 * (c * u ^ 2 / (2 * s ^ 2)) ^ 2 := by
    nlinarith [sq_nonneg (c / 2 + c * u ^ 2 / (2 * s ^ 2))]
  have h2 : (c * u ^ 2 / (2 * s ^ 2)) ^ 2 = c ^ 2 * u ^ 2 * u ^ 2 / (4 * s ^ 4) := by ring
  have h3 : u ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hu huB 2
  have h4 : c ^ 2 * u ^ 2 * u ^ 2 / (4 * s ^ 4) ≤ c ^ 2 * u ^ 2 * B ^ 2 / (4 * s ^ 4) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  rw [h2] at h1
  have : 2 * (c / 2) ^ 2 + 2 * (c ^ 2 * u ^ 2 * B ^ 2 / (4 * s ^ 4)) =
      c ^ 2 / 2 + c ^ 2 * B ^ 2 * u ^ 2 / (2 * s ^ 4) := by ring
  linarith

lemma self_bound {c Q s η L : ℝ} (hc : 0 < c) (hs : 0 < s) (hQ : 0 ≤ Q)
    (hF : L ≤ η + c * Real.sqrt Q) :
    Q ≤ 2 * s ^ 2 + 4 * s / c * (η + c * Q / (2 * s) + c * s / 2 - L) := by
  have hsq : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ
  set r := Real.sqrt Q
  have hdiff : η + c * Q / (2 * s) + c * s / 2 - (η + c * r) = c / (2 * s) * (r - s) ^ 2 := by
    rw [← hsq]; field_simp; ring
  have hgap : c / (2 * s) * (r - s) ^ 2 ≤ η + c * Q / (2 * s) + c * s / 2 - L := by linarith
  have hr : (r - s) ^ 2 ≤ 2 * s / c * (η + c * Q / (2 * s) + c * s / 2 - L) := by
    have h := mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * s / c by positivity)
    have e : 2 * s / c * (c / (2 * s) * (r - s) ^ 2) = (r - s) ^ 2 := by field_simp
    linarith
  have : Q ≤ 2 * s ^ 2 + 2 * (r - s) ^ 2 := by rw [← hsq]; nlinarith [sq_nonneg (r - 2 * s)]
  have e : 4 * s / c = 2 * (2 * s / c) := by ring
  rw [e]
  have e2 : 2 * (2 * s / c) * (η + c * Q / (2 * s) + c * s / 2 - L) =
      2 * (2 * s / c * (η + c * Q / (2 * s) + c * s / 2 - L)) := by ring
  rw [e2]
  linarith

end OracleTemplate.ChiSquareDro
