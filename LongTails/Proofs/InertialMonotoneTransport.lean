import LongTails.Proofs.GeneralizedMonotoneRegularization

open scoped RealInnerProductSpace

namespace OracleTemplate.InertialMonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma transport_energy {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2)
    (s g d : E)
    (hm : 0 ≤ 3 * r * ⟪s, d⟫ - r * (1 + r) * ⟪g, d⟫ -
      4 * (1 + r) * ‖d‖ ^ 2) :
    ‖(1 / (1 + r)) • s + d‖ ^ 2 + ‖g + d‖ ^ 2 ≤ ‖s‖ ^ 2 + ‖g‖ ^ 2 := by
  have hq : 0 < 1 + r := by linarith
  have hf : 0 < 4 - r := by linarith
  have hsq := sq_nonneg ‖(2 * r) • s - ((4 - r) * (1 + r)) • d‖
  rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs] at hsq
  have hp := mul_nonneg hm (show 0 ≤ 2 * (1 + r) * (4 - r) by positivity)
  have ht := mul_nonneg (sq_nonneg ‖s‖)
    (show 0 ≤ r ^ 3 * (2 - r) by positivity)
  rw [norm_add_sq_real, norm_add_sq_real, norm_smul, real_inner_smul_left,
    Real.norm_eq_abs, mul_pow, sq_abs]
  apply (mul_le_mul_iff_of_pos_left (show 0 < r * (4 - r) * (1 + r) ^ 2 by
    positivity)).mp
  field_simp
  by_contra h
  have hh := mul_pos (sub_pos.mpr (lt_of_not_ge h)) (mul_pos hr hf)
  nlinarith only [hh, hp, hsq, ht]

lemma transport_from_root_balance {r μ : ℝ} (hr : 0 < r) (hr2 : r ≤ 2)
    (hμ : 0 ≤ μ) (s g d p q : E)
    (hm : 0 ≤ ⟪d, q - p⟫)
    (hb : (4 * (1 + r) * μ) • (q - p) =
      (3 * r) • s - (r * (1 + r)) • g - (4 * (1 + r)) • d) :
    ‖(1 / (1 + r)) • s + d‖ ^ 2 + ‖g + d‖ ^ 2 ≤ ‖s‖ ^ 2 + ‖g‖ ^ 2 := by
  apply transport_energy hr hr2
  have hh := mul_nonneg (show 0 ≤ 4 * (1 + r) * μ by positivity) hm
  have hi := congrArg (fun v : E => ⟪v, d⟫) hb
  simp only [real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq] at hi
  have hc : ⟪d, q - p⟫ = ⟪q - p, d⟫ := real_inner_comm _ _
  rw [hc, inner_sub_left] at hh
  linarith

lemma regularized_transport {F : E → E} {r μ : ℝ}
    (hr : 0 < r) (hr2 : r ≤ 2) (hμ : 0 ≤ μ)
    (hmono : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫)
    (x w p q : E) (hp : F p = μ • (x - p))
    (hq : F q = (μ * (1 + r / 2)) •
      (x + (3 * r / (2 * (2 + r))) • (w - x) - q)) :
    ‖(μ * (1 + r / 2)) •
      (x + ((4 + 3 * r) / (2 * (2 + r))) • (w - x) - q)‖ ^ 2 +
      ‖F q‖ ^ 2 ≤ ‖(μ * (1 + r)) • (w - p)‖ ^ 2 + ‖F p‖ ^ 2 := by
  have hd : 2 + r ≠ 0 := by linarith
  have he : 1 + r ≠ 0 := by linarith
  have hb : (4 * (1 + r) * (μ * (1 + r / 2))) • (q - p) =
      (3 * r) • ((μ * (1 + r)) • (w - p)) -
        (r * (1 + r)) • F p - (4 * (1 + r)) • (F q - F p) := by
    rw [hp, hq]
    match_scalars <;> field_simp <;> ring
  have hi : (μ * (1 + r / 2)) •
      (x + ((4 + 3 * r) / (2 * (2 + r))) • (w - x) - q) =
      (1 / (1 + r)) • ((μ * (1 + r)) • (w - p)) + (F q - F p) := by
    rw [hp, hq]
    match_scalars <;> field_simp <;> ring
  have hh := transport_from_root_balance hr hr2
    (show 0 ≤ μ * (1 + r / 2) by positivity)
    ((μ * (1 + r)) • (w - p)) (F p) (F q - F p) p q (hmono q p) hb
  rw [hi]
  have hv : F p + (F q - F p) = F q := by abel
  rw [hv] at hh
  exact hh

lemma initial_energy {F : E → E} {μ R : ℝ} (hμ : 0 < μ)
    (hmono : ∀ a b, 0 ≤ ⟪F a - F b, a - b⟫) (x p xs : E)
    (hp : HolderMonotone.reg F μ x p = 0) (hxs : F xs = 0) (hx : ‖x - xs‖ ≤ R) :
    μ ^ 2 * ‖x - p‖ ^ 2 + ‖F p‖ ^ 2 ≤ 2 * μ ^ 2 * R ^ 2 := by
  have hd := (HolderMonotone.anchor_dist hmono hμ hp hxs).trans hx
  rw [norm_sub_rev p x] at hd
  have hv := ClippedExtragradient.regularized_root_value hp
  rw [hv, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_rev p x]
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hd 2) (sq_nonneg μ)
  linarith

omit [InnerProductSpace ℝ E] in
lemma residual_energy {F : E → E} {L μ : ℝ} (hL : 0 ≤ L) (hμ : L ≤ μ)
    (hlip : ∀ a b, ‖F a - F b‖ ≤ L * ‖a - b‖) (z p : E) :
    ‖F z‖ ^ 2 ≤ 2 * (μ ^ 2 * ‖z - p‖ ^ 2 + ‖F p‖ ^ 2) := by
  have ht := norm_le_insert' (F z) (F p)
  have hl := hlip z p
  have hs : ‖F z‖ ≤ L * ‖z - p‖ + ‖F p‖ := by linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hs 2
  have hb := sq_nonneg (L * ‖z - p‖ - ‖F p‖)
  have hc := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hL hμ 2) (sq_nonneg ‖z - p‖)
  nlinarith

end OracleTemplate.InertialMonotone
