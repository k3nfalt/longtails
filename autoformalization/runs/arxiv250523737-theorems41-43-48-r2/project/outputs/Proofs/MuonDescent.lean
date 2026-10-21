import outputs.Proofs.MuonMatrix
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace OracleTemplate.Muon

variable {m n : ℕ}

theorem hasDerivAt_line (f : Mat m n → ℝ) (hg : ∀ W, HasGradientAt f (gradient f W) W)
    (W D : Mat m n) (τ : ℝ) :
    HasDerivAt (fun τ : ℝ => f (W + τ • D)) (inner ℝ (gradient f (W + τ • D)) D) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => W + τ • D) D τ := by
    simpa using ((hasDerivAt_id τ).smul_const D).const_add W
  have h2 := (hg (W + τ • D)).hasFDerivAt.comp_hasDerivAt τ h1
  rw [InnerProductSpace.toDual_apply_apply] at h2
  exact h2

theorem descent_of_inner_bound (f : Mat m n → ℝ) (hg : ∀ W, HasGradientAt f (gradient f W) W)
    (W D : Mat m n) (K : ℝ)
    (h : ∀ τ ∈ Set.Icc (0 : ℝ) 1, inner ℝ (gradient f (W + τ • D) - gradient f W) D ≤ K * τ) :
    f (W + D) ≤ f W + inner ℝ (gradient f W) D + K / 2 := by
  let φ : ℝ → ℝ := fun τ => f (W + τ • D) - τ * inner ℝ (gradient f W) D - K * τ ^ 2 / 2
  have hφ : ∀ τ, HasDerivAt φ
      (inner ℝ (gradient f (W + τ • D)) D - 1 * inner ℝ (gradient f W) D - K * (2 * τ) / 2) τ := by
    intro τ
    have h1 := hasDerivAt_line f hg W D τ
    have h2 := (hasDerivAt_id τ).mul_const (inner ℝ (gradient f W) D)
    have h3 := ((hasDerivAt_pow 2 τ).const_mul K).div_const 2
    simp only [id] at h2
    convert (h1.sub h2).sub h3 using 1
    simp
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun τ _ => (hφ τ).continuousAt.continuousWithinAt) (fun τ _ => (hφ τ).hasDerivWithinAt)
      (fun τ hτ => ?_)
    rw [interior_Icc] at hτ
    have := h τ (Set.Ioo_subset_Icc_self hτ)
    rw [inner_sub_left] at this
    linarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
  have e0 : φ 0 = f W := by simp only [φ, zero_smul, add_zero, zero_mul, sub_zero]; ring
  have e1 : φ 1 = f (W + D) - inner ℝ (gradient f W) D - K / 2 := by
    simp only [φ, one_smul, one_mul, one_pow, mul_one]
  rw [e0, e1] at this
  linarith

theorem frobenius_descent (f : Mat m n → ℝ) (L : ℝ) (hg : ∀ W, HasGradientAt f (gradient f W) W)
    (hL : ∀ W W', ‖gradient f W - gradient f W'‖ ≤ L * ‖W - W'‖) (W D : Mat m n) :
    f (W + D) ≤ f W + inner ℝ (gradient f W) D + L * ‖D‖ ^ 2 / 2 := by
  have := descent_of_inner_bound f hg W D (L * ‖D‖ ^ 2) (fun τ hτ => ?_)
  · linarith
  · refine (real_inner_le_norm _ _).trans ?_
    have h1 := hL (W + τ • D) W
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ.1] at h1
    calc ‖gradient f (W + τ • D) - gradient f W‖ * ‖D‖ ≤ L * (τ * ‖D‖) * ‖D‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = L * ‖D‖ ^ 2 * τ := by ring

theorem spectral_descent (f : Mat m n → ℝ) (Ls : ℝ) (hg : ∀ W, HasGradientAt f (gradient f W) W)
    (hL : ∀ W W', nuclearNorm (gradient f W - gradient f W') ≤ Ls * spectralNorm (W - W'))
    (W D : Mat m n) :
    f (W + D) ≤ f W + inner ℝ (gradient f W) D + Ls * spectralNorm D ^ 2 / 2 := by
  have := descent_of_inner_bound f hg W D (Ls * spectralNorm D ^ 2) (fun τ hτ => ?_)
  · linarith
  · refine (inner_le_nuclearNorm_mul_spectralNorm _ _).trans ?_
    have h1 := hL (W + τ • D) W
    rw [add_sub_cancel_left, spectralNorm_smul, abs_of_nonneg hτ.1] at h1
    calc nuclearNorm (gradient f (W + τ • D) - gradient f W) * spectralNorm D ≤
          Ls * (τ * spectralNorm D) * spectralNorm D :=
          mul_le_mul_of_nonneg_right h1 (spectralNorm_nonneg _)
      _ = Ls * spectralNorm D ^ 2 * τ := by ring

theorem step_frobenius (f : Mat m n → ℝ) (L η : ℝ) (hη : 0 < η) (hL0 : 0 ≤ L)
    (hg : ∀ W, HasGradientAt f (gradient f W) W)
    (hL : ∀ W W', ‖gradient f W - gradient f W'‖ ≤ L * ‖W - W'‖) (W M : Mat m n) :
    η * nuclearNorm (gradient f W) ≤ f W - f (W - η • orthogonalize M) +
      ((min m n : ℕ) : ℝ) * L * η ^ 2 / 2 + 2 * η * Real.sqrt ((min m n : ℕ) : ℝ) * ‖gradient f W - M‖ := by
  set r : ℝ := ((min m n : ℕ) : ℝ)
  set P := orthogonalize M
  have hd := frobenius_descent f L hg hL W (-(η • P))
  rw [← sub_eq_add_neg, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hη, inner_neg_right,
    inner_smul_right] at hd
  have hP2 : ‖P‖ ^ 2 ≤ r := norm_orthogonalize_sq_le M
  have hPn : ‖P‖ ≤ Real.sqrt r := by
    rw [Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)]; exact hP2
  have hMP : inner ℝ M P = nuclearNorm M := inner_orthogonalize M
  have hsplit : inner ℝ (gradient f W) P = nuclearNorm M + inner ℝ (gradient f W - M) P := by
    rw [inner_sub_left, hMP]; ring
  have hcs : inner ℝ (gradient f W - M) P ≥ -(‖gradient f W - M‖ * Real.sqrt r) := by
    have := abs_real_inner_le_norm (gradient f W - M) P
    have h2 := mul_le_mul_of_nonneg_left hPn (norm_nonneg (gradient f W - M))
    linarith [neg_abs_le (inner ℝ (gradient f W - M) P)]
  have htri : nuclearNorm (gradient f W) ≤ nuclearNorm M + Real.sqrt r * ‖gradient f W - M‖ := by
    have h1 := nuclearNorm_le_add_inner M (gradient f W - M)
    rw [add_sub_cancel] at h1
    have h2 := nuclearNorm_le_sqrt_mul_norm (gradient f W - M)
    linarith
  have hsq : η ^ 2 * ‖P‖ ^ 2 ≤ η ^ 2 * r := mul_le_mul_of_nonneg_left hP2 (sq_nonneg η)
  have hmul : (η * ‖P‖) ^ 2 = η ^ 2 * ‖P‖ ^ 2 := by ring
  rw [hmul] at hd
  nlinarith [mul_le_mul_of_nonneg_left hsq hL0]

theorem step_spectral (f : Mat m n → ℝ) (Ls η : ℝ) (hη : 0 < η) (hL0 : 0 ≤ Ls)
    (hg : ∀ W, HasGradientAt f (gradient f W) W)
    (hL : ∀ W W', nuclearNorm (gradient f W - gradient f W') ≤ Ls * spectralNorm (W - W'))
    (W M : Mat m n) :
    η * nuclearNorm (gradient f W) ≤ f W - f (W - η • orthogonalize M) +
      Ls * η ^ 2 / 2 + 2 * η * nuclearNorm (gradient f W - M) := by
  set P := orthogonalize M
  have hd := spectral_descent f Ls hg hL W (-(η • P))
  have hneg : spectralNorm (-(η • P)) = η * spectralNorm P := by
    rw [show -(η • P) = (-η) • P by rw [neg_smul], spectralNorm_smul, abs_neg, abs_of_pos hη]
  rw [← sub_eq_add_neg, hneg, inner_neg_right, inner_smul_right] at hd
  have hP1 : spectralNorm P ≤ 1 := spectralNorm_orthogonalize_le M
  have hP0 : 0 ≤ spectralNorm P := spectralNorm_nonneg P
  have hMP : inner ℝ M P = nuclearNorm M := inner_orthogonalize M
  have hsplit : inner ℝ (gradient f W) P = nuclearNorm M + inner ℝ (gradient f W - M) P := by
    rw [inner_sub_left, hMP]; ring
  have hcs : inner ℝ (gradient f W - M) P ≥ -nuclearNorm (gradient f W - M) := by
    have := abs_inner_le_nuclearNorm_mul_spectralNorm (gradient f W - M) P
    have h2 := mul_le_mul_of_nonneg_left hP1 (nuclearNorm_nonneg (gradient f W - M))
    linarith [neg_abs_le (inner ℝ (gradient f W - M) P)]
  have htri : nuclearNorm (gradient f W) ≤ nuclearNorm M + nuclearNorm (gradient f W - M) := by
    have h1 := nuclearNorm_le_add_inner M (gradient f W - M)
    rw [add_sub_cancel] at h1
    exact h1
  have hsq : (η * spectralNorm P) ^ 2 ≤ η ^ 2 := by
    rw [mul_pow]
    nlinarith [sq_nonneg η, mul_le_mul hP1 hP1 hP0 zero_le_one]
  nlinarith [mul_le_mul_of_nonneg_left hsq hL0]

theorem momentum_tracking_frobenius (f : Mat m n → ℝ) (L η β : ℝ) (hL0 : 0 ≤ L) (hη : 0 ≤ η)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hL : ∀ W W', ‖gradient f W - gradient f W'‖ ≤ L * ‖W - W'‖)
    (W M G D : ℕ → Mat m n) (hW : ∀ t, W (t + 1) = W t - η • orthogonalize (M t))
    (hM0 : M 0 = G 0) (hM : ∀ t, M (t + 1) = β • M t + (1 - β) • G (t + 1))
    (hD0 : D 0 = G 0 - gradient f (W 0))
    (hD : ∀ t, D (t + 1) = β • D t + (1 - β) • (G (t + 1) - gradient f (W (t + 1)))) (t : ℕ) :
    ‖gradient f (W t) - M t‖ ≤
      ‖D t‖ + Real.sqrt ((min m n : ℕ) : ℝ) * β * L * η / (1 - β) := by
  set r : ℝ := ((min m n : ℕ) : ℝ)
  set e : ℕ → Mat m n := fun t => gradient f (W t) - M t + D t
  have he0 : e 0 = 0 := by simp only [e, hM0, hD0]; module
  have he : ∀ t, e (t + 1) = β • (e t + (gradient f (W (t + 1)) - gradient f (W t))) := by
    intro t
    simp only [e, hM, hD]
    module
  have hstep : ∀ t, ‖gradient f (W (t + 1)) - gradient f (W t)‖ ≤ L * η * Real.sqrt r := by
    intro t
    refine (hL _ _).trans ?_
    rw [hW, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
    have hP : ‖orthogonalize (M t)‖ ≤ Real.sqrt r := by
      rw [Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg _)]; exact norm_orthogonalize_sq_le _
    have := mul_le_mul_of_nonneg_left hP hη
    nlinarith
  have hbound : ∀ t, ‖e t‖ ≤ β * (L * η * Real.sqrt r) / (1 - β) := by
    intro t
    have h1b : 0 < 1 - β := by linarith
    have hK : 0 ≤ L * η * Real.sqrt r := by positivity
    induction t with
    | zero => rw [he0, norm_zero]; positivity
    | succ t ih =>
      rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ0]
      have h2 := (norm_add_le _ _).trans (add_le_add ih (hstep t))
      calc β * ‖e t + (gradient f (W (t + 1)) - gradient f (W t))‖ ≤
            β * (β * (L * η * Real.sqrt r) / (1 - β) + L * η * Real.sqrt r) :=
            mul_le_mul_of_nonneg_left h2 hβ0
        _ = β * (L * η * Real.sqrt r) / (1 - β) := by field_simp; ring
  have hdec : gradient f (W t) - M t = e t - D t := by simp only [e]; module
  rw [hdec]
  refine (norm_sub_le _ _).trans ?_
  have := hbound t
  have e2 : β * (L * η * Real.sqrt r) / (1 - β) = Real.sqrt r * β * L * η / (1 - β) := by ring
  linarith

theorem momentum_tracking_spectral (f : Mat m n → ℝ) (Ls η β : ℝ) (hL0 : 0 ≤ Ls) (hη : 0 ≤ η)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hL : ∀ W W', nuclearNorm (gradient f W - gradient f W') ≤ Ls * spectralNorm (W - W'))
    (W M G D : ℕ → Mat m n) (hW : ∀ t, W (t + 1) = W t - η • orthogonalize (M t))
    (hM0 : M 0 = G 0) (hM : ∀ t, M (t + 1) = β • M t + (1 - β) • G (t + 1))
    (hD0 : D 0 = G 0 - gradient f (W 0))
    (hD : ∀ t, D (t + 1) = β • D t + (1 - β) • (G (t + 1) - gradient f (W (t + 1)))) (t : ℕ) :
    nuclearNorm (gradient f (W t) - M t) ≤
      Real.sqrt ((min m n : ℕ) : ℝ) * ‖D t‖ + β * Ls * η / (1 - β) := by
  set e : ℕ → Mat m n := fun t => gradient f (W t) - M t + D t
  have he0 : e 0 = 0 := by simp only [e, hM0, hD0]; module
  have he : ∀ t, e (t + 1) = β • (e t + (gradient f (W (t + 1)) - gradient f (W t))) := by
    intro t
    simp only [e, hM, hD]
    module
  have hstep : ∀ t, nuclearNorm (gradient f (W (t + 1)) - gradient f (W t)) ≤ Ls * η := by
    intro t
    refine (hL _ _).trans ?_
    rw [hW, sub_sub_cancel_left, show -(η • orthogonalize (M t)) = (-η) • orthogonalize (M t) by
      rw [neg_smul], spectralNorm_smul, abs_neg, abs_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hη (spectralNorm_orthogonalize_le (M t))) hL0
  have hbound : ∀ t, nuclearNorm (e t) ≤ β * (Ls * η) / (1 - β) := by
    intro t
    have h1b : 0 < 1 - β := by linarith
    have hK : 0 ≤ Ls * η := by positivity
    induction t with
    | zero =>
      rw [he0]
      have := nuclearNorm_le_sqrt_mul_norm (0 : Mat m n)
      rw [norm_zero, mul_zero] at this
      exact this.trans (by positivity)
    | succ t ih =>
      rw [he]
      refine (nuclearNorm_smul_le _ _).trans ?_
      rw [abs_of_nonneg hβ0]
      have h2 := (nuclearNorm_le_add_inner _ _).trans (add_le_add ih (hstep t))
      calc β * nuclearNorm (e t + (gradient f (W (t + 1)) - gradient f (W t))) ≤
            β * (β * (Ls * η) / (1 - β) + Ls * η) := mul_le_mul_of_nonneg_left h2 hβ0
        _ = β * (Ls * η) / (1 - β) := by field_simp; ring
  have hdec : gradient f (W t) - M t = e t - D t := by simp only [e]; module
  rw [hdec]
  refine (nuclearNorm_sub_le _ _).trans ?_
  have h1 := hbound t
  have h2 := nuclearNorm_le_sqrt_mul_norm (D t)
  have e2 : β * (Ls * η) / (1 - β) = β * Ls * η / (1 - β) := by ring
  linarith

end OracleTemplate.Muon
