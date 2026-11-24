import LongTails.Proofs.EllSmoothGd

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.StochasticEllSmoothStep

open LongTails.Setups.EllSmoothNonconvex

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma inexact_descent (f : E → ℝ) (ℓ : ℝ → ℝ) (x v : E)
    (hmono : ∀ u w, 0 ≤ u → u ≤ w → ℓ u ≤ ℓ w)
    (hg : ∀ y, HasGradientAt f (gradient f y) y)
    (hd : Differentiable ℝ (gradient f))
    (hH : ∀ y, ‖fderiv ℝ (gradient f) y‖ ≤ ℓ ‖gradient f y‖)
    (hv : 0 < ‖v‖) (herr : ‖v - gradient f x‖ ≤ ‖v‖ / 4) (hℓ : 0 < ℓ (3 * ‖v‖)) :
    f (x - (1 / (2 * ℓ (3 * ‖v‖))) • v) ≤ f x - ‖v‖ ^ 2 / (8 * ℓ (3 * ‖v‖)) := by
  set g := gradient f x with hgdef
  set a := ‖v‖ with ha
  set γ := 1 / (2 * ℓ (3 * a)) with hγ
  have hγpos : 0 < γ := by positivity
  have hga : ‖g‖ ≤ 5 * a / 4 := by
    have h1 : ‖g‖ ≤ ‖g - v‖ + ‖v‖ := by
      have := norm_add_le (g - v) v
      simpa using this
    rw [norm_sub_rev] at h1
    linarith
  have hinner : 3 * a ^ 2 / 4 ≤ ⟪g, v⟫ := by
    have e : ⟪g, v⟫ = a ^ 2 - ⟪v - g, v⟫ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]
      ring
    have hcs : ⟪v - g, v⟫ ≤ ‖v - g‖ * ‖v‖ := real_inner_le_norm _ _
    have h2 : ‖v - g‖ * ‖v‖ ≤ a / 4 * a := mul_le_mul_of_nonneg_right herr (norm_nonneg _)
    rw [e]
    nlinarith
  let c : ℝ → E := fun t => x - (t * γ) • v
  have hc (t : ℝ) : HasDerivAt c (-(γ • v)) t := by
    have h1 : HasDerivAt (fun t : ℝ => (t * γ) • v) (γ • v) t := by
      simpa using ((hasDerivAt_id t).mul_const γ).smul_const v
    simpa [c] using h1.const_sub x
  let G : ℝ → E := fun t => gradient f (c t)
  have hG (t : ℝ) : HasDerivAt G (fderiv ℝ (gradient f) (c t) (-(γ • v))) t :=
    (hd (c t)).hasFDerivAt.comp_hasDerivAt t (hc t)
  have hfc (t : ℝ) : HasDerivAt (fun t => f (c t)) ⟪G t, -(γ • v)⟫ t := by
    have h := (hg (c t)).hasFDerivAt.comp_hasDerivAt t (hc t)
    refine h.congr_deriv ?_
    rfl
  have hfence : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖G t - g‖ ≤ t * a := by
    have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t * a) a t := by
      intro t
      simpa using (hasDerivAt_id t).mul_const a
    refine image_norm_le_of_norm_deriv_right_lt_deriv_boundary
      (f := fun t => G t - g) (f' := fun t => fderiv ℝ (gradient f) (c t) (-(γ • v)))
      (B := fun t => t * a) (B' := fun _ => a) ?_ ?_ ?_ hB ?_
    · exact (continuous_iff_continuousAt.mpr fun t => ((hG t).sub_const g).continuousAt).continuousOn
    · intro t _
      exact ((hG t).sub_const g).hasDerivWithinAt
    · simp [G, c, hgdef]
    · intro t ht heq
      have hGle : ‖G t‖ ≤ 3 * a := by
        have h1 : ‖G t‖ ≤ ‖G t - g‖ + ‖g‖ := by
          have := norm_add_le (G t - g) g
          simpa using this
        have h2 : t * a ≤ a := by nlinarith [ht.2, norm_nonneg v]
        linarith
      have h3 : ‖fderiv ℝ (gradient f) (c t)‖ ≤ ℓ (3 * a) :=
        (hH (c t)).trans (hmono _ _ (norm_nonneg _) hGle)
      have h4 : ‖fderiv ℝ (gradient f) (c t) (-(γ • v))‖ ≤ ℓ (3 * a) * (γ * a) := by
        have h5 := ContinuousLinearMap.le_opNorm (fderiv ℝ (gradient f) (c t)) (-(γ • v))
        rw [norm_neg, norm_smul, Real.norm_of_nonneg hγpos.le] at h5
        exact h5.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
      have h6 : ℓ (3 * a) * (γ * a) = a / 2 := by
        rw [hγ]; field_simp
      linarith
  let φ : ℝ → ℝ := fun t => f (c t) + γ * (3 * a ^ 2 / 4) * t - γ * a ^ 2 * t ^ 2 / 2
  have hφ (t : ℝ) :
      HasDerivAt φ (⟪G t, -(γ • v)⟫ + γ * (3 * a ^ 2 / 4) - γ * a ^ 2 * t) t := by
    have h1 : HasDerivAt (fun t : ℝ => γ * (3 * a ^ 2 / 4) * t) (γ * (3 * a ^ 2 / 4)) t := by
      simpa using (hasDerivAt_id t).const_mul (γ * (3 * a ^ 2 / 4))
    have h2 : HasDerivAt (fun t : ℝ => γ * a ^ 2 * t ^ 2 / 2) (γ * a ^ 2 * t) t := by
      have h := ((hasDerivAt_pow 2 t).const_mul (γ * a ^ 2)).div_const 2
      refine h.congr_deriv ?_
      simp only [Nat.cast_ofNat, show (2 - 1 : ℕ) = 1 from rfl, pow_one]
      ring
    exact ((hfc t).add h1).sub h2
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact (continuous_iff_continuousAt.mpr fun t => (hφ t).continuousAt).continuousOn
    · exact fun t _ => (hφ t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hφ t).deriv]
      have hf := hfence t ⟨ht.1.le, ht.2.le⟩
      have e : ⟪G t, -(γ • v)⟫ = -γ * ⟪G t - g, v⟫ - γ * ⟪g, v⟫ := by
        rw [inner_neg_right, real_inner_smul_right, inner_sub_left]
        ring
      have hcs : -⟪G t - g, v⟫ ≤ ‖G t - g‖ * a := by
        have := abs_real_inner_le_norm (G t - g) v
        linarith [neg_abs_le ⟪G t - g, v⟫]
      rw [e]
      have h7 : -γ * ⟪G t - g, v⟫ ≤ γ * (t * a * a) := by
        have := mul_le_mul_of_nonneg_left
          (hcs.trans (mul_le_mul_of_nonneg_right hf (norm_nonneg v))) hγpos.le
        linarith
      have h8 : γ * (3 * a ^ 2 / 4) ≤ γ * ⟪g, v⟫ := mul_le_mul_of_nonneg_left hinner hγpos.le
      nlinarith
  have h01 := hanti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  have e0 : φ 0 = f x := by simp [φ, c]
  have e1 : φ 1 = f (x - γ • v) + γ * a ^ 2 / 4 := by
    simp only [φ, c, one_mul]
    ring
  rw [e0, e1] at h01
  have e2 : a ^ 2 / (8 * ℓ (3 * a)) = γ * a ^ 2 / 4 := by
    rw [hγ]; field_simp; ring
  rw [e2]
  linarith

lemma inexact_decrease_lower (ℓ : ℝ → ℝ) (ρ ε a : ℝ) (hρ2 : ρ ≤ 2) (hreg : Regular ℓ ρ)
    (hε : 0 < ε) (ha : ε / 2 < a) :
    ε ^ 2 / (72 * ℓ ε) ≤ a ^ 2 / (8 * ℓ (3 * a)) := by
  obtain ⟨-, hr, hpos⟩ := hreg
  have ha0 : 0 < a := by linarith
  have h1 := hr ε (3 * a) hε (by linarith)
  have hl1 := hpos ε hε
  have hl2 := hpos (3 * a) (by linarith)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hq : 1 ≤ 3 * a / ε := by rw [le_div_iff₀ hε]; linarith
  have hεp : 0 < ε ^ ρ := Real.rpow_pos_of_pos hε _
  have e : (3 * a) ^ ρ = (3 * a / ε) ^ ρ * ε ^ ρ := by
    rw [← Real.mul_rpow (by positivity) hε.le]
    congr 1
    field_simp
  rw [e] at h1
  have h2 : ℓ (3 * a) ≤ ℓ ε * (3 * a / ε) ^ ρ := by
    have : ℓ (3 * a) * ε ^ ρ ≤ ℓ ε * (3 * a / ε) ^ ρ * ε ^ ρ := by linarith
    exact le_of_mul_le_mul_right this hεp
  have h3 : (3 * a / ε) ^ ρ ≤ (3 * a / ε) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hq hρ2
  rw [Real.rpow_two] at h3
  have h4 : ℓ (3 * a) ≤ ℓ ε * (3 * a / ε) ^ 2 := h2.trans (mul_le_mul_of_nonneg_left h3 hl1.le)
  have h5 : ε ^ 2 * (ℓ ε * (3 * a / ε) ^ 2) = 9 * ℓ ε * a ^ 2 := by
    field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg ε)]

lemma initial_gradient_sq (f : E → ℝ) (ℓ : ℝ → ℝ) (x0 : E) (Δ : ℝ)
    (hmono : ∀ u w, 0 ≤ u → u ≤ w → ℓ u ≤ ℓ w) (hpos : ∀ u, 0 < u → 0 < ℓ u)
    (hg : ∀ y, HasGradientAt f (gradient f y) y)
    (hd : Differentiable ℝ (gradient f))
    (hH : ∀ y, ‖fderiv ℝ (gradient f) y‖ ≤ ℓ ‖gradient f y‖)
    (hΔ : ∀ y, f x0 - f y ≤ Δ) (hx : 0 < ‖gradient f x0‖) :
    ‖gradient f x0‖ ^ 2 ≤ 4 * Δ * ℓ (2 * ‖gradient f x0‖) := by
  have hl := hpos (2 * ‖gradient f x0‖) (by positivity)
  have h := LongTails.Proofs.EllSmoothGd.descent f ℓ x0 hmono hg hd hH hx hl
  have h2 := hΔ (x0 - (1 / (2 * ℓ (2 * ‖gradient f x0‖))) • gradient f x0)
  have h3 : ‖gradient f x0‖ ^ 2 / (4 * ℓ (2 * ‖gradient f x0‖)) ≤ Δ := by linarith
  rw [div_le_iff₀ (by positivity)] at h3
  linarith

lemma initial_gradient_bound (f : E → ℝ) (ℓ : ℝ → ℝ) (ρ : ℝ) (x0 : E) (Δ ε : ℝ)
    (hρ2 : ρ < 2) (hreg : Regular ℓ ρ) (hε : 0 < ε)
    (hg : ∀ y, HasGradientAt f (gradient f y) y)
    (hd : Differentiable ℝ (gradient f))
    (hH : ∀ y, ‖fderiv ℝ (gradient f) y‖ ≤ ℓ ‖gradient f y‖)
    (hΔ : ∀ y, f x0 - f y ≤ Δ) :
    ‖gradient f x0‖ ≤ ε * (1 + (16 * (Δ * ℓ ε / ε ^ 2)) ^ (1 / (2 - ρ))) := by
  obtain ⟨hmono, hr, hpos⟩ := hreg
  set u := ‖gradient f x0‖ with hu
  have hΔ0 : 0 ≤ Δ := by
    have := hΔ x0
    linarith
  have hl0 : 0 < ℓ ε := hpos ε hε
  have hT0 : 0 ≤ (16 * (Δ * ℓ ε / ε ^ 2)) ^ (1 / (2 - ρ)) := Real.rpow_nonneg (by positivity) _
  by_cases hue : u ≤ ε
  · nlinarith
  push Not at hue
  have hu0 : 0 < u := hε.trans hue
  have hsq := initial_gradient_sq f ℓ x0 Δ hmono hpos hg hd hH hΔ hu0
  have hl1 := hpos ε hε
  have h1 := hr ε (2 * u) hε (by linarith)
  have hεp : 0 < ε ^ ρ := Real.rpow_pos_of_pos hε _
  set s := u / ε with hs
  have hs1 : 1 < s := by rw [hs, lt_div_iff₀ hε]; linarith
  have e : (2 * u) ^ ρ = 2 ^ ρ * s ^ ρ * ε ^ ρ := by
    rw [← Real.mul_rpow (by norm_num) (by positivity), ← Real.mul_rpow (by positivity) hε.le]
    congr 1
    rw [hs]
    field_simp
  rw [e] at h1
  have h2 : ℓ (2 * u) ≤ ℓ ε * (2 ^ ρ * s ^ ρ) := by
    have : ℓ (2 * u) * ε ^ ρ ≤ ℓ ε * (2 ^ ρ * s ^ ρ) * ε ^ ρ := by linarith
    exact le_of_mul_le_mul_right this hεp
  have h2ρ : (2 : ℝ) ^ ρ ≤ 4 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hρ2.le
    rw [Real.rpow_two] at this
    linarith
  have hsρ : 0 < s ^ ρ := Real.rpow_pos_of_pos (by linarith) _
  have h3 : u ^ 2 ≤ 16 * Δ * ℓ ε * s ^ ρ := by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * Δ)
    nlinarith [mul_le_mul_of_nonneg_right h2ρ (by positivity : (0 : ℝ) ≤ ℓ ε * s ^ ρ * (4 * Δ))]
  have hus : u = s * ε := by rw [hs]; field_simp
  have h4 : s ^ (2 : ℝ) ≤ 16 * (Δ * ℓ ε / ε ^ 2) * s ^ ρ := by
    rw [Real.rpow_two]
    rw [hus] at h3
    have he2 : (0 : ℝ) < ε ^ 2 := by positivity
    have : (s * ε) ^ 2 = s ^ 2 * ε ^ 2 := by ring
    rw [this] at h3
    have h5 : 16 * (Δ * ℓ ε / ε ^ 2) * s ^ ρ * ε ^ 2 = 16 * Δ * ℓ ε * s ^ ρ := by
      field_simp
    nlinarith
  have h5 : s ^ (2 - ρ) ≤ 16 * (Δ * ℓ ε / ε ^ 2) := by
    have hs0 : 0 < s := by linarith
    rw [Real.rpow_sub hs0]
    rw [div_le_iff₀ hsρ]
    exact h4
  have h6 : s ≤ (16 * (Δ * ℓ ε / ε ^ 2)) ^ (1 / (2 - ρ)) := by
    have hs0 : 0 ≤ s := by linarith
    have h2ρ' : 0 < 2 - ρ := by linarith
    have := Real.rpow_le_rpow (by positivity) h5 (by positivity : (0 : ℝ) ≤ 1 / (2 - ρ))
    rw [← Real.rpow_mul hs0, mul_one_div_cancel h2ρ'.ne', Real.rpow_one] at this
    exact this
  rw [hus]
  nlinarith

end LongTails.Proofs.StochasticEllSmoothStep
