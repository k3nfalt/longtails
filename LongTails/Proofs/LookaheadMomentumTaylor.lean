import LongTails.Proofs.ThirdOrderTaylorBounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LongTails.Proofs.LookaheadMomentumTaylor

open LongTails.Proofs.ThirdOrderTaylorBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {grad : E → E} {hess : E → E →L[ℝ] E} {third : E → E →L[ℝ] E →L[ℝ] E} {L₁ L₂ L₃ : ℝ}

lemma line_hasDerivAt (x d : E) (t : ℝ) : HasDerivAt (fun s : ℝ => x + s • d) d t := by
  have h := ((hasDerivAt_id t).smul_const d).const_add x
  simpa using h

omit [NormedSpace ℝ E] in
lemma first_remainder (hl : ∀ x y, ‖grad x - grad y‖ ≤ L₁ * ‖x - y‖) (x d : E) :
    ‖grad (x + d) - grad x‖ ≤ L₁ * ‖d‖ := by
  have h := hl (x + d) x
  rwa [add_sub_cancel_left] at h

lemma smul_hasDerivAt (v : E) (t : ℝ) : HasDerivAt (fun s : ℝ => s • v) v t := by
  simpa using (hasDerivAt_id t).smul_const v

lemma half_sq_hasDerivAt (v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (s ^ 2 / 2) • v) (t • v) t := by
  have h := (hasDerivAt_pow 2 t).div_const 2
  have e : ((2 : ℕ) : ℝ) * t ^ (2 - 1) / 2 = t := by norm_num
  rw [e] at h
  exact h.smul_const v

lemma second_remainder (hL : 0 ≤ L₂) (hd : ∀ x, HasFDerivAt grad (hess x) x)
    (hl : ∀ x y, ‖hess x - hess y‖ ≤ L₂ * ‖x - y‖) (x d : E) :
    ‖grad (x + d) - grad x - hess x d‖ ≤ L₂ * ‖d‖ ^ 2 := by
  have hφ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => grad (x + s • d) - s • hess x d)
      (hess (x + t • d) d - hess x d) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => grad (x + s • d)) (hess (x + t • d) d) t :=
      (hd (x + t • d)).comp_hasDerivAt t (line_hasDerivAt x d t)
    exact h1.sub (smul_hasDerivAt (hess x d) t)
  have hb : ∀ t : ℝ, ‖hess (x + t • d) d - hess x d‖ ≤ (L₂ * ‖d‖ ^ 2) * |t| ^ 1 := by
    intro t
    have h1 : ‖hess (x + t • d) d - hess x d‖ ≤ ‖hess (x + t • d) - hess x‖ * ‖d‖ :=
      (hess (x + t • d) - hess x).le_opNorm d
    have h2 := hl (x + t • d) x
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h2
    calc _ ≤ ‖hess (x + t • d) - hess x‖ * ‖d‖ := h1
      _ ≤ (L₂ * (|t| * ‖d‖)) * ‖d‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg d)
      _ = _ := by ring
  have hm := power_derivative_bound (by positivity : 0 ≤ L₂ * ‖d‖ ^ 2) 1 hφ hb 1
  have he : grad (x + (1 : ℝ) • d) - (1 : ℝ) • hess x d -
      (grad (x + (0 : ℝ) • d) - (0 : ℝ) • hess x d) = grad (x + d) - grad x - hess x d := by
    rw [one_smul, one_smul, zero_smul, zero_smul, add_zero, sub_zero]
    abel
  rw [he] at hm
  simpa using hm

lemma third_remainder (hL : 0 ≤ L₃) (hd : ∀ x, HasFDerivAt grad (hess x) x)
    (hd₂ : ∀ x, HasFDerivAt hess (third x) x)
    (hl : ∀ x y, ‖third x - third y‖ ≤ L₃ * ‖x - y‖) (x d : E) :
    ‖grad (x + d) - grad x - hess x d - (1 / 2 : ℝ) • third x d d‖ ≤ L₃ * ‖d‖ ^ 3 := by
  have hM : 0 ≤ L₃ * ‖d‖ ^ 3 := by positivity
  have hφ₁ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => hess (x + s • d) d) (third (x + t • d) d d) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => hess (x + s • d)) (third (x + t • d) d) t :=
      (hd₂ (x + t • d)).comp_hasDerivAt t (line_hasDerivAt x d t)
    have h2 := h1.clm_apply (hasDerivAt_const t d)
    simpa using h2
  have hr₁ : ∀ t : ℝ, HasDerivAt (fun s : ℝ => hess (x + s • d) d - hess x d - s • third x d d)
      (third (x + t • d) d d - third x d d) t := by
    intro t
    exact ((hφ₁ t).sub_const (hess x d)).sub (smul_hasDerivAt (third x d d) t)
  have hb₂ : ∀ t : ℝ, ‖third (x + t • d) d d - third x d d‖ ≤ (L₃ * ‖d‖ ^ 3) * |t| ^ 1 := by
    intro t
    have h1 : ‖third (x + t • d) d d - third x d d‖ ≤ ‖third (x + t • d) - third x‖ * ‖d‖ * ‖d‖ :=
      (((third (x + t • d) - third x) d).le_opNorm d).trans
        (mul_le_mul_of_nonneg_right ((third (x + t • d) - third x).le_opNorm d) (norm_nonneg d))
    have h2 := hl (x + t • d) x
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h2
    calc _ ≤ ‖third (x + t • d) - third x‖ * ‖d‖ * ‖d‖ := h1
      _ ≤ (L₃ * (|t| * ‖d‖)) * ‖d‖ * ‖d‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (norm_nonneg d)) (norm_nonneg d)
      _ = _ := by ring
  have hb₁ : ∀ t : ℝ, ‖hess (x + t • d) d - hess x d - t • third x d d‖ ≤
      (L₃ * ‖d‖ ^ 3) * |t| ^ 2 := by
    intro t
    have hm := power_derivative_bound hM 1 hr₁ hb₂ t
    simpa using hm
  have hr₀ : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => grad (x + s • d) - s • hess x d - (s ^ 2 / 2) • third x d d)
      (hess (x + t • d) d - hess x d - t • third x d d) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => grad (x + s • d)) (hess (x + t • d) d) t :=
      (hd (x + t • d)).comp_hasDerivAt t (line_hasDerivAt x d t)
    exact (h1.sub (smul_hasDerivAt (hess x d) t)).sub (half_sq_hasDerivAt (third x d d) t)
  have hm := power_derivative_bound hM 2 hr₀ hb₁ 1
  have he : grad (x + (1 : ℝ) • d) - (1 : ℝ) • hess x d - ((1 : ℝ) ^ 2 / 2) • third x d d -
      (grad (x + (0 : ℝ) • d) - (0 : ℝ) • hess x d - ((0 : ℝ) ^ 2 / 2) • third x d d) =
      grad (x + d) - grad x - hess x d - (1 / 2 : ℝ) • third x d d := by
    have e0 : ((0 : ℝ) ^ 2 / 2) = 0 := by norm_num
    rw [one_smul, one_smul, zero_smul, e0, zero_smul, zero_smul, add_zero, sub_zero, sub_zero,
      one_pow]
    abel
  rw [he] at hm
  simpa using hm

lemma three_point_first (hl : ∀ x y, ‖grad x - grad y‖ ≤ L₁ * ‖x - y‖)
    (x d : E) (w₁ w₂ w₃ s₁ s₂ s₃ : ℝ) :
    ‖w₁ • (grad (x + s₁ • d) - grad x) + w₂ • (grad (x + s₂ • d) - grad x) +
        w₃ • (grad (x + s₃ • d) - grad x)‖ ≤
      L₁ * ‖d‖ * (|w₁| * |s₁| + |w₂| * |s₂| + |w₃| * |s₃|) := by
  have h : ∀ w s : ℝ, ‖w • (grad (x + s • d) - grad x)‖ ≤ L₁ * ‖d‖ * (|w| * |s|) := by
    intro w s
    have h1 := first_remainder hl x (s • d)
    rw [norm_smul, Real.norm_eq_abs] at h1
    rw [norm_smul, Real.norm_eq_abs]
    calc |w| * ‖grad (x + s • d) - grad x‖ ≤ |w| * (L₁ * (|s| * ‖d‖)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg w)
      _ = _ := by ring
  calc _ ≤ ‖w₁ • (grad (x + s₁ • d) - grad x)‖ + ‖w₂ • (grad (x + s₂ • d) - grad x)‖ +
        ‖w₃ • (grad (x + s₃ • d) - grad x)‖ := norm_add₃_le
    _ ≤ L₁ * ‖d‖ * (|w₁| * |s₁|) + L₁ * ‖d‖ * (|w₂| * |s₂|) + L₁ * ‖d‖ * (|w₃| * |s₃|) :=
        add_le_add (add_le_add (h w₁ s₁) (h w₂ s₂)) (h w₃ s₃)
    _ = _ := by ring

lemma three_point_second (hL : 0 ≤ L₂) (hd : ∀ x, HasFDerivAt grad (hess x) x)
    (hl : ∀ x y, ‖hess x - hess y‖ ≤ L₂ * ‖x - y‖)
    (x d : E) (w₁ w₂ w₃ s₁ s₂ s₃ : ℝ) (h₁ : w₁ * s₁ + w₂ * s₂ + w₃ * s₃ = 0) :
    ‖w₁ • (grad (x + s₁ • d) - grad x) + w₂ • (grad (x + s₂ • d) - grad x) +
        w₃ • (grad (x + s₃ • d) - grad x)‖ ≤
      L₂ * ‖d‖ ^ 2 * (|w₁| * s₁ ^ 2 + |w₂| * s₂ ^ 2 + |w₃| * s₃ ^ 2) := by
  have h : ∀ w s : ℝ, ‖w • (grad (x + s • d) - grad x - hess x (s • d))‖ ≤
      L₂ * ‖d‖ ^ 2 * (|w| * s ^ 2) := by
    intro w s
    have h1 := second_remainder hL hd hl x (s • d)
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h1
    rw [norm_smul, Real.norm_eq_abs]
    calc |w| * ‖grad (x + s • d) - grad x - hess x (s • d)‖ ≤ |w| * (L₂ * (s ^ 2 * ‖d‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg w)
      _ = _ := by ring
  have he : w₁ • (grad (x + s₁ • d) - grad x) + w₂ • (grad (x + s₂ • d) - grad x) +
        w₃ • (grad (x + s₃ • d) - grad x) =
      w₁ • (grad (x + s₁ • d) - grad x - hess x (s₁ • d)) +
        w₂ • (grad (x + s₂ • d) - grad x - hess x (s₂ • d)) +
        w₃ • (grad (x + s₃ • d) - grad x - hess x (s₃ • d)) := by
    have hz : (w₁ * s₁ + w₂ * s₂ + w₃ * s₃) • hess x d = 0 := by rw [h₁, zero_smul]
    simp only [map_smul, smul_sub, smul_smul]
    rw [← sub_eq_zero]
    rw [← hz]
    module
  rw [he]
  calc _ ≤ ‖w₁ • (grad (x + s₁ • d) - grad x - hess x (s₁ • d))‖ +
        ‖w₂ • (grad (x + s₂ • d) - grad x - hess x (s₂ • d))‖ +
        ‖w₃ • (grad (x + s₃ • d) - grad x - hess x (s₃ • d))‖ := norm_add₃_le
    _ ≤ L₂ * ‖d‖ ^ 2 * (|w₁| * s₁ ^ 2) + L₂ * ‖d‖ ^ 2 * (|w₂| * s₂ ^ 2) +
        L₂ * ‖d‖ ^ 2 * (|w₃| * s₃ ^ 2) := add_le_add (add_le_add (h w₁ s₁) (h w₂ s₂)) (h w₃ s₃)
    _ = _ := by ring

lemma three_point_third (hL : 0 ≤ L₃) (hd : ∀ x, HasFDerivAt grad (hess x) x)
    (hd₂ : ∀ x, HasFDerivAt hess (third x) x)
    (hl : ∀ x y, ‖third x - third y‖ ≤ L₃ * ‖x - y‖)
    (x d : E) (w₁ w₂ w₃ s₁ s₂ s₃ : ℝ) (h₁ : w₁ * s₁ + w₂ * s₂ + w₃ * s₃ = 0)
    (h₂ : w₁ * s₁ ^ 2 + w₂ * s₂ ^ 2 + w₃ * s₃ ^ 2 = 0) :
    ‖w₁ • (grad (x + s₁ • d) - grad x) + w₂ • (grad (x + s₂ • d) - grad x) +
        w₃ • (grad (x + s₃ • d) - grad x)‖ ≤
      L₃ * ‖d‖ ^ 3 * (|w₁| * |s₁| ^ 3 + |w₂| * |s₂| ^ 3 + |w₃| * |s₃| ^ 3) := by
  have h : ∀ w s : ℝ, ‖w • (grad (x + s • d) - grad x - hess x (s • d) -
      (1 / 2 : ℝ) • third x (s • d) (s • d))‖ ≤ L₃ * ‖d‖ ^ 3 * (|w| * |s| ^ 3) := by
    intro w s
    have h1 := third_remainder hL hd hd₂ hl x (s • d)
    rw [norm_smul, Real.norm_eq_abs, mul_pow] at h1
    rw [norm_smul, Real.norm_eq_abs]
    calc _ ≤ |w| * (L₃ * (|s| ^ 3 * ‖d‖ ^ 3)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg w)
      _ = _ := by ring
  have he : w₁ • (grad (x + s₁ • d) - grad x) + w₂ • (grad (x + s₂ • d) - grad x) +
        w₃ • (grad (x + s₃ • d) - grad x) =
      w₁ • (grad (x + s₁ • d) - grad x - hess x (s₁ • d) -
          (1 / 2 : ℝ) • third x (s₁ • d) (s₁ • d)) +
        w₂ • (grad (x + s₂ • d) - grad x - hess x (s₂ • d) -
          (1 / 2 : ℝ) • third x (s₂ • d) (s₂ • d)) +
        w₃ • (grad (x + s₃ • d) - grad x - hess x (s₃ • d) -
          (1 / 2 : ℝ) • third x (s₃ • d) (s₃ • d)) := by
    have hz : (w₁ * s₁ + w₂ * s₂ + w₃ * s₃) • hess x d = 0 := by rw [h₁, zero_smul]
    have hz₂ : (w₁ * s₁ ^ 2 + w₂ * s₂ ^ 2 + w₃ * s₃ ^ 2) • third x d d = 0 := by
      rw [h₂, zero_smul]
    simp only [map_smul, smul_apply, smul_sub, smul_smul]
    rw [← sub_eq_zero]
    have hcomb : (0 : E) = (w₁ * s₁ + w₂ * s₂ + w₃ * s₃) • hess x d +
        (1 / 2 : ℝ) • ((w₁ * s₁ ^ 2 + w₂ * s₂ ^ 2 + w₃ * s₃ ^ 2) • third x d d) := by
      rw [hz, hz₂, smul_zero, add_zero]
    rw [hcomb]
    module
  rw [he]
  calc _ ≤ ‖w₁ • (grad (x + s₁ • d) - grad x - hess x (s₁ • d) -
          (1 / 2 : ℝ) • third x (s₁ • d) (s₁ • d))‖ +
        ‖w₂ • (grad (x + s₂ • d) - grad x - hess x (s₂ • d) -
          (1 / 2 : ℝ) • third x (s₂ • d) (s₂ • d))‖ +
        ‖w₃ • (grad (x + s₃ • d) - grad x - hess x (s₃ • d) -
          (1 / 2 : ℝ) • third x (s₃ • d) (s₃ • d))‖ := norm_add₃_le
    _ ≤ L₃ * ‖d‖ ^ 3 * (|w₁| * |s₁| ^ 3) + L₃ * ‖d‖ ^ 3 * (|w₂| * |s₂| ^ 3) +
        L₃ * ‖d‖ ^ 3 * (|w₃| * |s₃| ^ 3) := add_le_add (add_le_add (h w₁ s₁) (h w₂ s₂)) (h w₃ s₃)
    _ = _ := by ring

end LongTails.Proofs.LookaheadMomentumTaylor
