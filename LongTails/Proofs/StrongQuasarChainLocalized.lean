import LongTails.Proofs.SmoothConvexFiniteWall

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped RealInnerProductSpace

namespace LongTails.Proofs.StrongQuasarChainLocalized

open LongTails.Proofs.SmoothConvexFiniteWall LongTails.Proofs.SmoothConvexFiniteGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma smoothMax_eq_blend (w a b : ℝ) (hw : 0 < w) :
    smoothMax w a b = weight w a b * a + (1 - weight w a b) * b +
      w / 2 * weight w a b * (1 - weight w a b) := by
  unfold smoothMax weight
  set z := (a - b) / w + 1 / 2 with hz
  have ha : a = b + w * (z - 1 / 2) := by rw [hz]; field_simp; ring
  rw [ha]
  simp only [ramp, rampSlope_cases]
  split_ifs <;> ring

lemma weight_lt_one {w a b : ℝ} (hw : 0 < w) (h : weight w a b < 1) : a - b < w / 2 := by
  unfold weight rampSlope at h
  have h2 : max 0 ((a - b) / w + 1 / 2) < 1 := by
    by_contra hc
    push Not at hc
    rw [min_eq_left hc] at h
    exact lt_irrefl _ h
  have h3 : (a - b) / w + 1 / 2 < 1 := lt_of_le_of_lt (le_max_right _ _) h2
  have h4 : (a - b) / w < 1 / 2 := by linarith
  rw [div_lt_iff₀ hw] at h4
  linarith

lemma localized_strongQuasar (R : ℝ) (hR : 0 < R) (f : E → ℝ) (df : E → E) (xs : E)
    (γ μ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 1 / 8) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1)
    (hf0 : ∀ x, 0 ≤ f x) (hfs : f xs = 0) (hxs : ‖xs‖ ≤ R / 2)
    (hsq : ∀ x, γ * f x + ⟪df x, xs - x⟫ + γ * μ / 2 * ‖xs - x‖ ^ 2 ≤ 0) (x : E) :
    γ * localized R f x + ⟪localizedField R f df x, xs - x⟫ +
        γ * μ / 2 * ‖xs - x‖ ^ 2 ≤ γ * localized R f xs := by
  have hloc0 : localized R f xs = 0 := localized_zero R hR f xs hfs (by linarith)
  rw [hloc0, mul_zero]
  have hR2 : 0 < R ^ 2 := by positivity
  set s := weight (R ^ 2) (f x) (wall R x) with hsdef
  have hs0 : 0 ≤ s := weight_nonneg _ _ _
  have hs1 : s ≤ 1 := weight_le_one _ _ _
  have hM : localized R f x = s * f x + (1 - s) * wall R x + R ^ 2 / 2 * s * (1 - s) :=
    smoothMax_eq_blend (R ^ 2) (f x) (wall R x) hR2
  have hF : ⟪localizedField R f df x, xs - x⟫ =
      s * ⟪df x, xs - x⟫ + (1 - s) * (4 * ⟪x, xs - x⟫) := by
    unfold localizedField
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
  rw [hM, hF]
  have h1 := mul_le_mul_of_nonneg_left (hsq x) hs0
  rw [mul_zero] at h1
  have key : (1 - s) * (γ * wall R x + 4 * ⟪x, xs - x⟫ + γ * μ / 2 * ‖xs - x‖ ^ 2 +
      γ * (R ^ 2 / 2) * s) ≤ 0 := by
    rcases eq_or_lt_of_le hs1 with he | hlt
    · rw [he, sub_self, zero_mul]
    · apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
      have hw := weight_lt_one hR2 hlt
      have hfx := hf0 x
      set r := ‖x‖ with hr
      have hr0 : 0 ≤ r := norm_nonneg _
      have hwall : wall R x = 2 * r ^ 2 - 4 * R ^ 2 := rfl
      have hbig : 7 * R ^ 2 < 4 * r ^ 2 := by rw [hwall] at hw; nlinarith
      have hRr : R ≤ 4 / 5 * r := by nlinarith
      have hcs : ⟪x, xs⟫ ≤ r * (R / 2) := by
        have := real_inner_le_norm x xs
        nlinarith [norm_nonneg xs]
      have hin : ⟪x, xs - x⟫ = ⟪x, xs⟫ - r ^ 2 := by
        rw [inner_sub_right, real_inner_self_eq_norm_sq]
      have hd : ‖xs - x‖ ≤ R / 2 + r := by
        have := norm_sub_le xs x
        linarith
      have hd2 : ‖xs - x‖ ^ 2 ≤ (R / 2 + r) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hd 2
      rw [hwall, hin]
      have hγμ : γ * μ / 2 ≤ γ / 2 := by nlinarith
      have hγμ0 : 0 ≤ γ * μ / 2 := by positivity
      have e1 : γ * μ / 2 * ‖xs - x‖ ^ 2 ≤ γ / 2 * (R / 2 + r) ^ 2 := by
        calc γ * μ / 2 * ‖xs - x‖ ^ 2 ≤ γ * μ / 2 * (R / 2 + r) ^ 2 :=
              mul_le_mul_of_nonneg_left hd2 hγμ0
          _ ≤ γ / 2 * (R / 2 + r) ^ 2 := mul_le_mul_of_nonneg_right hγμ (by positivity)
      have e2 : γ * (R ^ 2 / 2) * s ≤ γ * (R ^ 2 / 2) := by
        have : 0 ≤ γ * (R ^ 2 / 2) := by positivity
        nlinarith
      have hR0 := hR.le
      nlinarith [mul_nonneg hγ0 (sq_nonneg r), mul_nonneg hγ0 (sq_nonneg R),
        mul_nonneg hR0 hr0]
  nlinarith [key, h1]

end LongTails.Proofs.StrongQuasarChainLocalized
