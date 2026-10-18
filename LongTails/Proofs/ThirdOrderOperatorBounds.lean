import LongTails.Proofs.ThirdOrderObjectiveGeometry

namespace LongTails.Proofs.ThirdOrderOperatorBounds

open scoped RealInnerProductSpace

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma symmetric_norm_bound (A : E →L[ℝ] E) {C : ℝ} (hC : 0 ≤ C)
    (hsym : ∀ u v, ⟪A u, v⟫ = ⟪A v, u⟫)
    (hq : ∀ v, |⟪A v, v⟫| ≤ C * ‖v‖ ^ 2) : ‖A‖ ≤ 2 * C := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  by_cases hz : A v = 0
  · simp [hz, hC]
  have hn : 0 < ‖A v‖ := norm_pos_iff.mpr hz
  let w := ‖A v‖⁻¹ • A v
  have hw : ‖w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hi : ⟪A v, w⟫ = ‖A v‖ := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hid : ⟪A (v + w), v + w⟫ - ⟪A (v - w), v - w⟫ = 4 * ⟪A v, w⟫ := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
    rw [hsym w v]
    ring
  have hplus : ‖v + w‖ ≤ 2 := by simpa only [hv, hw, one_add_one_eq_two] using norm_add_le v w
  have hminus : ‖v - w‖ ≤ 2 := by simpa only [hv, hw, one_add_one_eq_two] using norm_sub_le v w
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hplus 2) hC
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hminus 2) hC
  have h₁ := (abs_le.mp (hq (v + w))).2
  have h₂ := (abs_le.mp (hq (v - w))).1
  rw [hi] at hid
  nlinarith

lemma third_norm_from_diagonal {f : E → ℝ} (hf : ContDiff ℝ 3 f) (x : E)
    {C : ℝ} (hC : 0 ≤ C)
    (hq : ∀ v, |⟪fderiv ℝ (fderiv ℝ (_root_.gradient f)) x v v, v⟫| ≤ C * ‖v‖ ^ 3) :
    ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x‖ ≤ 6 * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro a
  have hm (v : E) : |⟪fderiv ℝ (fderiv ℝ (_root_.gradient f)) x a v, v⟫| ≤
      (3 * C * ‖a‖) * ‖v‖ ^ 2 := by
    simpa only [ContinuousLinearEquiv.refl_apply] using
      ThirdOrderObjectiveGeometry.third_mixed_bound hf x (ContinuousLinearEquiv.refl ℝ E) hC hq a v
  have hs (u v : E) : ⟪fderiv ℝ (fderiv ℝ (_root_.gradient f)) x a u, v⟫ =
      ⟪fderiv ℝ (fderiv ℝ (_root_.gradient f)) x a v, u⟫ :=
    ThirdOrderObjectiveGeometry.third_swap_last hf x a u v
  have hh := symmetric_norm_bound (fderiv ℝ (fderiv ℝ (_root_.gradient f)) x a) (by positivity) hs hm
  nlinarith only [hh]

lemma third_norm_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ σ H : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hH : 0 ≤ H) (hΔ : Δ = L * σ ^ 2)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
      fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ L * ‖x - y‖)
    (x : E) (hgap : ∀ y, f x - f y ≤ Δ) (hessian : ‖fderiv ℝ (_root_.gradient f) x‖ ≤ H) :
    ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x‖ ≤ 54 * Real.sqrt (L * (H + 4 * L * σ)) := by
  have hc : 0 ≤ L * (H + 4 * L * σ) := by positivity
  have hs := Real.sq_sqrt hc
  have hd (v : E) : |⟪fderiv ℝ (fderiv ℝ (_root_.gradient f)) x v v, v⟫| ≤
      (9 * Real.sqrt (L * (H + 4 * L * σ))) * ‖v‖ ^ 3 := by
    have hh : ⟪fderiv ℝ (_root_.gradient f) x v, v⟫ ≤ H * ‖v‖ ^ 2 := by
      calc
        _ ≤ ‖fderiv ℝ (_root_.gradient f) x v‖ * ‖v‖ := real_inner_le_norm _ _
        _ ≤ (H * ‖v‖) * ‖v‖ := by
          gcongr
          exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hessian (norm_nonneg _))
        _ = _ := by ring
    have hp := ThirdOrderObjectiveGeometry.third_diagonal_bound hf hL hσ hΔ hT x v hgap
    have hm := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 72 * L * ‖v‖ ^ 4)
    have hpow : 0 ≤ L * (H + 4 * L * σ) * ‖v‖ ^ 6 := mul_nonneg hc (by positivity)
    have he : ((9 * Real.sqrt (L * (H + 4 * L * σ))) * ‖v‖ ^ 3) ^ 2 =
        81 * (L * (H + 4 * L * σ)) * ‖v‖ ^ 6 := by
      rw [mul_pow, mul_pow, hs]
      ring
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    rw [sq_abs, he]
    nlinarith only [hp, hm, hpow]
  have hh := third_norm_from_diagonal hf x (by positivity) hd
  nlinarith only [hh]

lemma hessian_growth {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {L Δ σ H : ℝ} (hL : 0 < L) (hσ : 0 < σ) (hH : 0 ≤ H) (hΔ : Δ = L * σ ^ 2)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (_root_.gradient f)) x -
      fderiv ℝ (fderiv ℝ (_root_.gradient f)) y‖ ≤ L * ‖x - y‖)
    (x y : E) (hgap : ∀ z, f x - f z ≤ Δ) (hessian : ‖fderiv ℝ (_root_.gradient f) x‖ ≤ H) :
    ‖fderiv ℝ (_root_.gradient f) y‖ ≤ 28 * H + 108 * L * σ + 28 * L * ‖y - x‖ ^ 2 := by
  let Hx := fderiv ℝ (_root_.gradient f) x
  let Hy := fderiv ℝ (_root_.gradient f) y
  let Tx := fderiv ℝ (fderiv ℝ (_root_.gradient f)) x
  have ht := third_norm_bound hf hL hσ hH hΔ hT x hgap hessian
  have hr := ThirdOrderObjectiveGeometry.hessian_taylor_remainder hf hL.le hT x y
  have he : Hy = (Hy - Hx - Tx (y - x)) + Tx (y - x) + Hx := by abel
  have hn : ‖Hy‖ ≤ L * ‖y - x‖ ^ 2 + 54 * Real.sqrt (L * (H + 4 * L * σ)) * ‖y - x‖ + H := by
    calc
      _ = ‖(Hy - Hx - Tx (y - x)) + Tx (y - x) + Hx‖ := congrArg norm he
      _ ≤ ‖Hy - Hx - Tx (y - x)‖ + ‖Tx (y - x)‖ + ‖Hx‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
      _ ≤ _ := add_le_add (add_le_add hr
        ((ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _)))) hessian
  have hC : 0 ≤ H + 4 * L * σ := by positivity
  have hs₁ := Real.sq_sqrt hC
  have hs₂ := Real.sq_sqrt hL.le
  have hyoung := sq_nonneg (Real.sqrt (H + 4 * L * σ) - Real.sqrt L * ‖y - x‖)
  rw [Real.sqrt_mul hL.le] at hn
  nlinarith

end LongTails.Proofs.ThirdOrderOperatorBounds
