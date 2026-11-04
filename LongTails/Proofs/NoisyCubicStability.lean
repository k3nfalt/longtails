import LongTails.Proofs.CubicRegularization

namespace LongTails.Proofs.NoisyCubicStability

open scoped RealInnerProductSpace
open LongTails.Proofs.CubicRegularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma response_energy (H : E →L[ℝ] E) (hH : ∀ v, 0 ≤ ⟪H v, v⟫)
    (η M : ℝ) (hM : 0 ≤ M) (g e s t : E)
    (hs : H s + η • s + (M / 2) • cubicGradient s + g + e = 0)
    (ht : H t + η • t + (M / 2) • cubicGradient t + g = 0) :
    η * ‖s - t‖ ^ 2 + M / 4 * ‖s - t‖ ^ 3 ≤ -⟪e, s - t⟫ := by
  have he : H (s - t) + η • (s - t) +
      (M / 2) • (cubicGradient s - cubicGradient t) = -e := by
    rw [map_sub, smul_sub, smul_sub]
    calc
      _ = (H s + η • s + (M / 2) • cubicGradient s + g + e) -
          (H t + η • t + (M / 2) • cubicGradient t + g) - e := by module
      _ = -e := by rw [hs, ht]; simp
  have hi := congrArg (fun v => ⟪v, s - t⟫) he
  simp only [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    inner_neg_left] at hi
  have hc := mul_le_mul_of_nonneg_left (cubicGradient_strong_monotone s t)
    (show 0 ≤ M / 2 by positivity)
  have hp := hH (s - t)
  nlinarith

lemma response_lipschitz (H : E →L[ℝ] E) (hH : ∀ v, 0 ≤ ⟪H v, v⟫)
    (η M : ℝ) (hη : 0 < η) (hM : 0 ≤ M) (g e s t : E)
    (hs : H s + η • s + (M / 2) • cubicGradient s + g + e = 0)
    (ht : H t + η • t + (M / 2) • cubicGradient t + g = 0) :
    ‖s - t‖ ≤ ‖e‖ / η := by
  have he := response_energy H hH η M hM g e s t hs ht
  have hc := (abs_le.mp (abs_real_inner_le_norm e (s - t))).1
  have hp : 0 ≤ M / 4 * ‖s - t‖ ^ 3 := by positivity
  apply (le_div_iff₀ hη).mpr
  by_cases hz : ‖s - t‖ = 0
  · simp [hz]
  · have hn : 0 < ‖s - t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

lemma reverse_remainder_absorption (q e t c : ℝ)
    (hq : 0 ≤ q) (he : 0 ≤ e) (ht : 0 ≤ t)
    (hc : c ≤ 1 / 16)
    (hrem : (1 - c) * q ≤ t / 8 + c * t + c * e) :
    q ≤ t / 5 + e / 15 := by
  have h₁ := mul_nonneg (show 0 ≤ 1 / 16 - c by linarith) hq
  have h₂ := mul_nonneg (show 0 ≤ 1 / 16 - c by linarith) ht
  have h₃ := mul_nonneg (show 0 ≤ 1 / 16 - c by linarith) he
  nlinarith

lemma noisy_residual_square (r q e t : ℝ)
    (hr : 0 ≤ r) (he : 0 ≤ e) (ht : 0 ≤ t)
    (hrq : r ≤ q + e) (hq : q ≤ t / 5 + e / 15) :
    r ^ 2 ≤ t ^ 2 / 4 + 3 * e ^ 2 := by
  have hb : r ≤ t / 5 + 16 * e / 15 := by linarith
  have hsq := sq_nonneg (t / 5 - 16 * e / 15)
  have hm := mul_nonneg (show 0 ≤ t / 5 + 16 * e / 15 - r by linarith)
    (show 0 ≤ t / 5 + 16 * e / 15 + r by positivity)
  nlinarith [sq_nonneg t, sq_nonneg e]

lemma local_gradient_taylor {g : E → E} {A : E → E →L[ℝ] E} {H : ℝ}
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (x d : E)
    (hLip : ∀ z, ‖z - x‖ ≤ ‖d‖ → ‖A z - A x‖ ≤ H * ‖z - x‖) :
    ‖g (x + d) - g x - A x d‖ ≤ H * ‖d‖ ^ 2 / 2 := by
  let R : ℝ → E := fun t => g (x + t • d) - g x - t • A x d
  let D : ℝ → E := fun t => (A (x + t • d) - A x) d
  have hd (t : ℝ) : HasDerivAt R (D t) t := by
    have hline : HasDerivAt (fun t : ℝ => x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have ht := ((hg (x + t • d)).comp_hasDerivAt t hline).sub_const (g x)
    convert ht.sub ((hasDerivAt_id t).smul_const (A x d)) using 1
    · ext t
      rfl
    · simp [D]
  have hB (t : ℝ) : HasDerivAt (fun t : ℝ => H * ‖d‖ ^ 2 / 2 * t ^ 2)
      (H * ‖d‖ ^ 2 * t) t := by
    convert ((hasDerivAt_id t).pow 2).const_mul (H * ‖d‖ ^ 2 / 2) using 1
    · ext t
      rfl
    · simp
      ring
  have hb (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) : ‖D t‖ ≤ H * ‖d‖ ^ 2 * t := by
    have h₁ := (A (x + t • d) - A x).le_opNorm d
    have hdist : ‖x + t • d - x‖ ≤ ‖d‖ := by
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg d) ht.2.le
    have h₂ := hLip (x + t • d) hdist
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at h₂
    have h₃ := mul_le_mul_of_nonneg_right h₂ (norm_nonneg d)
    dsimp [D]
    nlinarith only [h₁, h₃]
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (a := 0) (b := 1) (f := R) (f' := D)
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).hasDerivWithinAt)
    (B := fun t => H * ‖d‖ ^ 2 / 2 * t ^ 2)
    (by simp [R]) hB hb (x := 1) (by norm_num)
  simpa [R] using h

lemma reverse_gradient_remainder {g : E → E} {A : E → E →L[ℝ] E}
    (hg : ∀ x, HasFDerivAt g (A x) x) (x y : E) (H : E →L[ℝ] E) (C δ : ℝ)
    (hLip : ∀ z, ‖z - y‖ ≤ ‖x - y‖ → ‖A z - A y‖ ≤ C * ‖z - y‖)
    (hH : ‖A x - H‖ ≤ δ) :
    ‖g y - g x - H (y - x)‖ ≤ δ * ‖y - x‖ + 3 / 2 * C * ‖y - x‖ ^ 2 := by
  have ht := local_gradient_taylor hg y (x - y) hLip
  rw [add_sub_cancel] at ht
  have hl := hLip x (le_refl _)
  rw [norm_sub_rev (A x) (A y), norm_sub_rev x y] at hl
  have hb : ‖A y - H‖ ≤ C * ‖y - x‖ + δ := by
    calc
      _ = ‖(A y - A x) + (A x - H)‖ := by congr 1; abel
      _ ≤ ‖A y - A x‖ + ‖A x - H‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hl hH
  have he : g y - g x - H (y - x) =
      -(g x - g y - A y (x - y)) + (A y - H) (y - x) := by
    simp only [sub_apply, map_sub]
    abel
  calc
    _ ≤ ‖g x - g y - A y (x - y)‖ + ‖(A y - H) (y - x)‖ := by
      rw [he]
      exact (norm_add_le _ _).trans_eq (by rw [norm_neg])
    _ ≤ C * ‖x - y‖ ^ 2 / 2 + ‖A y - H‖ * ‖y - x‖ :=
      add_le_add ht ((A y - H).le_opNorm _)
    _ ≤ C * ‖x - y‖ ^ 2 / 2 + (C * ‖y - x‖ + δ) * ‖y - x‖ :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
    _ = _ := by rw [norm_sub_rev x y]; ring

lemma scaled_remainder_absorption (q e t c : ℝ)
    (hq : 0 ≤ q) (he : 0 ≤ e) (hc : c ≤ 1 / 4)
    (hrem : (1 - c) * q ≤ 3 / 4 * t + c * e) : q ≤ t + e := by
  have h₁ := mul_nonneg (show 0 ≤ 1 / 4 - c by linarith) hq
  have h₂ := mul_nonneg (show 0 ≤ 1 / 4 - c by linarith) he
  nlinarith

lemma local_model_residual {g : E → E} {A : E → E →L[ℝ] E}
    (hg : ∀ x, HasFDerivAt g (A x) x) (x y e : E) (H : E →L[ℝ] E)
    (M₀ M₁ ρ δ τ α : ℝ) (hM₁ : 0 ≤ M₁)
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) (hα : α ≤ 1 / 2)
    (hLip : ∀ u v, ‖v - u‖ ≤ ρ →
      ‖A v - A u‖ ≤ (M₀ + M₁ * ‖g u‖) * ‖v - u‖)
    (hH : ‖A x - H‖ ≤ δ) (hr : ‖y - x‖ ≤ ρ)
    (hs : H (y - x) + τ • (y - x) + g x + e = 0)
    (hshort : M₁ * ‖y - x‖ ^ 2 ≤ α / 4)
    (hreg : 4 * (δ + M₀ * ‖y - x‖) ≤ α * τ) :
    ‖g y + τ • (y - x)‖ ≤ α * τ * ‖y - x‖ + 2 * ‖e‖ := by
  let q := g y - g x - H (y - x)
  let r := ‖y - x‖
  let c := 3 / 2 * M₁ * r ^ 2
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc : c ≤ 1 / 4 := by dsimp [c, r]; nlinarith only [hshort, hα]
  have hrem := reverse_gradient_remainder hg x y H (M₀ + M₁ * ‖g y‖) δ
    (fun z hz => hLip y z (hz.trans (by simpa only [norm_sub_rev x y] using hr))) hH
  have heq : g y + τ • (y - x) = q - e := by
    calc
      _ = q - e + (H (y - x) + τ • (y - x) + g x + e) := by dsimp [q]; module
      _ = q - e := by rw [hs]; simp
  have hgn : ‖g y‖ ≤ τ * r + ‖q‖ + ‖e‖ := by
    have hv : g y = q - e - τ • (y - x) := by rw [← heq]; abel
    rw [hv]
    calc
      _ ≤ ‖q - e‖ + ‖τ • (y - x)‖ := norm_sub_le _ _
      _ ≤ ‖q‖ + ‖e‖ + ‖τ • (y - x)‖ := add_le_add (norm_sub_le _ _) (le_refl _)
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]; dsimp [r]; ring
  have hgn' := mul_le_mul_of_nonneg_left hgn hc0
  have hreg' := mul_le_mul_of_nonneg_right hreg (norm_nonneg (y - x))
  have hshort' := mul_le_mul_of_nonneg_right hshort (mul_nonneg hτ (norm_nonneg (y - x)))
  have hb : (1 - c) * ‖q‖ ≤ 3 / 4 * (α * τ * r) + c * ‖e‖ := by
    dsimp [c, r, q] at *
    have hn := mul_nonneg hδ (norm_nonneg (y - x))
    nlinarith only [hrem, hgn', hreg', hshort', hn]
  have hq := scaled_remainder_absorption ‖q‖ ‖e‖ (α * τ * r) c
    (norm_nonneg _) (norm_nonneg _) hc hb
  rw [heq]
  have hh := norm_sub_le q e
  dsimp [r] at hq
  linarith

end LongTails.Proofs.NoisyCubicStability
