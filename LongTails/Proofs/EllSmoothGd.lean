import LongTails.Setups.EllSmoothNonconvex
import LongTails.Algorithms.EllSmoothGd
import LongTails.Proofs.Execution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

open OracleTemplate MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.EllSmoothGd

open LongTails.Setups.EllSmoothNonconvex LongTails.Algorithms.EllSmoothGd

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma descent (f : E → ℝ) (ℓ : ℝ → ℝ) (x : E)
    (hmono : ∀ u v, 0 ≤ u → u ≤ v → ℓ u ≤ ℓ v)
    (hg : ∀ y, HasGradientAt f (gradient f y) y)
    (hd : Differentiable ℝ (gradient f))
    (hH : ∀ y, ‖fderiv ℝ (gradient f) y‖ ≤ ℓ ‖gradient f y‖)
    (hx : 0 < ‖gradient f x‖) (hℓ : 0 < ℓ (2 * ‖gradient f x‖)) :
    f (x - (1 / (2 * ℓ (2 * ‖gradient f x‖))) • gradient f x) ≤
      f x - ‖gradient f x‖ ^ 2 / (4 * ℓ (2 * ‖gradient f x‖)) := by
  set g := gradient f x with hgdef
  set γ := 1 / (2 * ℓ (2 * ‖g‖)) with hγ
  have hγpos : 0 < γ := by positivity
  let c : ℝ → E := fun t => x - (t * γ) • g
  have hc (t : ℝ) : HasDerivAt c (-(γ • g)) t := by
    have h1 : HasDerivAt (fun t : ℝ => (t * γ) • g) (γ • g) t := by
      simpa using ((hasDerivAt_id t).mul_const γ).smul_const g
    simpa [c] using h1.const_sub x
  let G : ℝ → E := fun t => gradient f (c t)
  have hG (t : ℝ) : HasDerivAt G (fderiv ℝ (gradient f) (c t) (-(γ • g))) t :=
    (hd (c t)).hasFDerivAt.comp_hasDerivAt t (hc t)
  have hfc (t : ℝ) : HasDerivAt (fun t => f (c t)) ⟪G t, -(γ • g)⟫ t := by
    have h := (hg (c t)).hasFDerivAt.comp_hasDerivAt t (hc t)
    refine h.congr_deriv ?_
    rfl
  have hfence : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖G t - g‖ ≤ t * ‖g‖ := by
    have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t * ‖g‖) ‖g‖ t := by
      intro t
      simpa using (hasDerivAt_id t).mul_const ‖g‖
    refine image_norm_le_of_norm_deriv_right_lt_deriv_boundary
      (f := fun t => G t - g) (f' := fun t => fderiv ℝ (gradient f) (c t) (-(γ • g)))
      (B := fun t => t * ‖g‖) (B' := fun _ => ‖g‖) ?_ ?_ ?_ hB ?_
    · exact (continuous_iff_continuousAt.mpr fun t => ((hG t).sub_const g).continuousAt).continuousOn
    · intro t _
      exact ((hG t).sub_const g).hasDerivWithinAt
    · simp [G, c, hgdef]
    · intro t ht heq
      have hGle : ‖G t‖ ≤ 2 * ‖g‖ := by
        have h1 : ‖G t‖ ≤ ‖G t - g‖ + ‖g‖ := by
          have := norm_add_le (G t - g) g
          simpa using this
        have h2 : t * ‖g‖ ≤ ‖g‖ := by nlinarith [ht.2, norm_nonneg g]
        linarith
      have h3 : ‖fderiv ℝ (gradient f) (c t)‖ ≤ ℓ (2 * ‖g‖) :=
        (hH (c t)).trans (hmono _ _ (norm_nonneg _) hGle)
      have h4 : ‖fderiv ℝ (gradient f) (c t) (-(γ • g))‖ ≤ ℓ (2 * ‖g‖) * (γ * ‖g‖) := by
        have h5 := ContinuousLinearMap.le_opNorm (fderiv ℝ (gradient f) (c t)) (-(γ • g))
        rw [norm_neg, norm_smul, Real.norm_of_nonneg hγpos.le] at h5
        exact h5.trans (mul_le_mul_of_nonneg_right h3 (by positivity))
      have h6 : ℓ (2 * ‖g‖) * (γ * ‖g‖) = ‖g‖ / 2 := by
        rw [hγ]; field_simp
      linarith
  let φ : ℝ → ℝ := fun t => f (c t) + γ * ‖g‖ ^ 2 * t - γ * ‖g‖ ^ 2 * t ^ 2 / 2
  have hφ (t : ℝ) : HasDerivAt φ (⟪G t, -(γ • g)⟫ + γ * ‖g‖ ^ 2 - γ * ‖g‖ ^ 2 * t) t := by
    have h1 : HasDerivAt (fun t : ℝ => γ * ‖g‖ ^ 2 * t) (γ * ‖g‖ ^ 2) t := by
      simpa using (hasDerivAt_id t).const_mul (γ * ‖g‖ ^ 2)
    have h2 : HasDerivAt (fun t : ℝ => γ * ‖g‖ ^ 2 * t ^ 2 / 2) (γ * ‖g‖ ^ 2 * t) t := by
      have h := ((hasDerivAt_pow 2 t).const_mul (γ * ‖g‖ ^ 2)).div_const 2
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
      have e : ⟪G t, -(γ • g)⟫ = -γ * ⟪G t - g, g⟫ - γ * ‖g‖ ^ 2 := by
        rw [inner_neg_right, real_inner_smul_right, inner_sub_left, real_inner_self_eq_norm_sq]
        ring
      have hcs : -⟪G t - g, g⟫ ≤ ‖G t - g‖ * ‖g‖ := by
        have := abs_real_inner_le_norm (G t - g) g
        linarith [neg_abs_le ⟪G t - g, g⟫]
      rw [e]
      have h7 : -γ * ⟪G t - g, g⟫ ≤ γ * (t * ‖g‖ * ‖g‖) := by
        have := mul_le_mul_of_nonneg_left
          (hcs.trans (mul_le_mul_of_nonneg_right hf (norm_nonneg g))) hγpos.le
        linarith
      nlinarith
  have h01 := hanti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  have e0 : φ 0 = f x := by simp [φ, c]
  have e1 : φ 1 = f (x - γ • g) + γ * ‖g‖ ^ 2 / 2 := by
    simp only [φ, c, one_mul]
    ring
  rw [e0, e1] at h01
  have e2 : ‖g‖ ^ 2 / (4 * ℓ (2 * ‖g‖)) = γ * ‖g‖ ^ 2 / 2 := by
    rw [hγ]; field_simp; ring
  rw [e2]
  linarith

lemma decrease_lower (ℓ : ℝ → ℝ) (ρ ε t : ℝ) (hρ2 : ρ ≤ 2) (hreg : Regular ℓ ρ)
    (hε : 0 < ε) (ht : ε < t) :
    ε ^ 2 / (16 * ℓ ε) ≤ t ^ 2 / (4 * ℓ (2 * t)) := by
  obtain ⟨-, hr, hpos⟩ := hreg
  have ht0 : 0 < t := hε.trans ht
  have h1 := hr ε (2 * t) hε (by linarith)
  have hl1 := hpos ε hε
  have hl2 := hpos (2 * t) (by linarith)
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hq : 1 ≤ t / ε := (one_le_div hε).mpr ht.le
  have hεp : 0 < ε ^ ρ := Real.rpow_pos_of_pos hε _
  have e : (2 * t) ^ ρ = (2 * (t / ε)) ^ ρ * ε ^ ρ := by
    rw [← Real.mul_rpow (by positivity) hε.le]
    congr 1
    field_simp
  rw [e] at h1
  have h2 : ℓ (2 * t) ≤ ℓ ε * (2 * (t / ε)) ^ ρ := by
    have : ℓ (2 * t) * ε ^ ρ ≤ ℓ ε * (2 * (t / ε)) ^ ρ * ε ^ ρ := by linarith
    exact le_of_mul_le_mul_right this hεp
  have h3 : (2 * (t / ε)) ^ ρ ≤ (2 * (t / ε)) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hρ2
  rw [Real.rpow_two] at h3
  have h4 : ℓ (2 * t) ≤ ℓ ε * (2 * (t / ε)) ^ 2 := h2.trans (mul_le_mul_of_nonneg_left h3 hl1.le)
  have h5 : ε ^ 2 * (ℓ ε * (2 * (t / ε)) ^ 2) = 4 * ℓ ε * t ^ 2 := by
    field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg ε)]

lemma step_frozen (ℓ : ℝ → ℝ) (ε : ℝ) (f : E → ℝ) (x : E) (hx : ‖gradient f x‖ ≤ ε) (k : ℕ) :
    (fun y => gdStep ℓ ε y (gradient f y))^[k] x = x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [gdStep, hx]

lemma iterate_accuracy (f : E → ℝ) (ℓ : ℝ → ℝ) (ρ Δ ε : ℝ) (x0 : E)
    (hρ2 : ρ ≤ 2) (hreg : Regular ℓ ρ) (hε : 0 < ε)
    (hg : ∀ y, HasGradientAt f (gradient f y) y)
    (hd : Differentiable ℝ (gradient f))
    (hH : ∀ y, ‖fderiv ℝ (gradient f) y‖ ≤ ℓ ‖gradient f y‖)
    (hΔ : ∀ y, f x0 - f y ≤ Δ) (K : ℕ) (hK : 16 * Δ * ℓ ε / ε ^ 2 < K) :
    ‖gradient f ((fun y => gdStep ℓ ε y (gradient f y))^[K] x0)‖ ≤ ε := by
  set T := fun y => gdStep ℓ ε y (gradient f y) with hT
  have hl := hreg.2.2 ε hε
  by_contra hcon
  push Not at hcon
  have hall : ∀ k ≤ K, ε < ‖gradient f (T^[k] x0)‖ := by
    intro k hk
    by_contra hk'
    push Not at hk'
    have := step_frozen ℓ ε f (T^[k] x0) hk' (K - k)
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hk] at this
    rw [this] at hcon
    linarith
  have hdec : ∀ k ≤ K, f (T^[k] x0) ≤ f x0 - k * (ε ^ 2 / (16 * ℓ ε)) := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hgk := hall k (by omega)
      have ihk := ih (by omega)
      have hstep : T^[k + 1] x0 = T^[k] x0 -
          (1 / (2 * ℓ (2 * ‖gradient f (T^[k] x0)‖))) • gradient f (T^[k] x0) := by
        rw [Function.iterate_succ_apply']
        change gdStep ℓ ε (T^[k] x0) (gradient f (T^[k] x0)) = _
        unfold gdStep
        rw [ite_eq_right (not_le.mpr hgk)]
      rw [hstep]
      have h1 := descent f ℓ (T^[k] x0) hreg.1 hg hd hH (hε.trans hgk)
        (hreg.2.2 _ (by linarith [hε.trans hgk]))
      have h2 := decrease_lower ℓ ρ ε _ hρ2 hreg hε hgk
      push_cast
      linarith
  have h1 := hdec K le_rfl
  have h2 := hΔ (T^[K] x0)
  rw [div_lt_iff₀ (by positivity)] at hK
  have h3 : (K : ℝ) * (ε ^ 2 / (16 * ℓ ε)) ≤ Δ := by linarith
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)] at h3
  nlinarith

end LongTails.Proofs.EllSmoothGd
