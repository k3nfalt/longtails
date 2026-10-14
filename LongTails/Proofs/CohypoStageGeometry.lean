import LongTails.Proofs.CohypoRegularizedOperator

open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticCohypomonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ : ℝ}

lemma OpHyp.stage_dist (H : OpHyp F G J L ρ) {Λ' l : ℝ} (cp c a zp z : E) (hΛ' : 0 ≤ Λ')
    (hl : 0 < l) (h4 : 4 * ρ * (Λ' + l) ≤ 1)
    (hc : (Λ' + l) • c = Λ' • cp + l • a)
    (hzp : -(F zp + Λ' • (zp - cp)) ∈ G zp) (hz : -(F z + (Λ' + l) • (z - c)) ∈ G z) :
    ‖z - a‖ ^ 2 ≤ 2 * ‖zp - a‖ ^ 2 ∧ ‖z - zp‖ ^ 2 ≤ ‖zp - a‖ ^ 2 := by
  have hρ := H.ρ_nonneg
  have hpair := H.reg_pair (Λ := Λ') cp z zp _ _ hz hzp
  have e1 : F z + -(F z + (Λ' + l) • (z - c)) + Λ' • (z - cp) -
      (F zp + -(F zp + Λ' • (zp - cp)) + Λ' • (zp - cp)) = -(l • (z - a)) := by
    have : (Λ' + l) • (z - c) = (Λ' + l) • z - (Λ' • cp + l • a) := by rw [smul_sub, hc]
    rw [this]; module
  rw [e1, norm_neg, norm_smul, mul_pow, Real.norm_of_nonneg hl.le, inner_neg_left,
    inner_smul_left] at hpair
  simp only [conj_trivial] at hpair
  set A := z - a
  set B := z - zp
  have hD : zp - a = A - B := by simp only [A, B]; abel
  have hDexp : ‖zp - a‖ ^ 2 = ‖A‖ ^ 2 - 2 * ⟪A, B⟫ + ‖B‖ ^ 2 := by
    rw [hD]; exact norm_sub_sq_real A B
  rw [hDexp]
  have hk : 0 < 1 - 2 * ρ * Λ' := by nlinarith
  have hk2 : 2 * ρ * l ≤ (1 - 2 * ρ * Λ') / 2 := by nlinarith
  have hAB : (1 - 2 * ρ * Λ') * l * ⟪A, B⟫ ≤ ρ * l ^ 2 * ‖A‖ ^ 2 - Λ' * (1 - ρ * Λ') * ‖B‖ ^ 2 := by
    linarith
  have hB0 : 0 ≤ Λ' * (1 - ρ * Λ') * ‖B‖ ^ 2 := by
    have : 0 ≤ 1 - ρ * Λ' := by nlinarith
    positivity
  have hkl : 0 < (1 - 2 * ρ * Λ') * l := mul_pos hk hl
  have hAB' : 2 * ⟪A, B⟫ ≤ ‖A‖ ^ 2 / 2 := by
    have h1 : (1 - 2 * ρ * Λ') * l * ⟪A, B⟫ ≤ ρ * l ^ 2 * ‖A‖ ^ 2 := by linarith
    have h2 : ρ * l ^ 2 * ‖A‖ ^ 2 ≤ (1 - 2 * ρ * Λ') * l * (‖A‖ ^ 2 / 4) := by
      have : 0 ≤ l * ‖A‖ ^ 2 := by positivity
      nlinarith
    have h3 : (1 - 2 * ρ * Λ') * l * ⟪A, B⟫ ≤ (1 - 2 * ρ * Λ') * l * (‖A‖ ^ 2 / 4) := h1.trans h2
    have h4 := le_of_mul_le_mul_left h3 hkl
    linarith
  have hAB0 : ⟪A, B⟫ ≤ ρ * l * ‖A‖ ^ 2 / (1 - 2 * ρ * Λ') := by
    rw [le_div_iff₀ hk]
    have h1 : (1 - 2 * ρ * Λ') * l * ⟪A, B⟫ ≤ ρ * l ^ 2 * ‖A‖ ^ 2 := by linarith
    have h2 : l * (⟪A, B⟫ * (1 - 2 * ρ * Λ')) ≤ l * (ρ * l * ‖A‖ ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left h2 hl
  have hA0 := sq_nonneg ‖A‖
  have hB0' := sq_nonneg ‖B‖
  constructor
  · linarith
  · linarith

lemma anchor_norm_step {Λ' l : ℝ} (cp c a zp z : E) (hΛ' : 0 ≤ Λ') (hl : 0 ≤ l)
    (hc : (Λ' + l) • c = Λ' • cp + l • a) :
    ‖(Λ' + l) • (z - c)‖ ≤ ‖Λ' • (zp - cp)‖ + Λ' * ‖z - zp‖ + l * ‖z - a‖ := by
  have e : (Λ' + l) • (z - c) = Λ' • (zp - cp) + Λ' • (z - zp) + l • (z - a) := by
    rw [smul_sub, hc]; module
  rw [e]
  refine (norm_add_le _ _).trans ?_
  refine add_le_add ((norm_add_le _ _).trans ?_) ?_
  · rw [norm_smul Λ' (z - zp), Real.norm_of_nonneg hΛ']
  · rw [norm_smul, Real.norm_of_nonneg hl]

lemma OpHyp.final_cert (H : OpHyp F G J L ρ) {γ Λ : ℝ} (c z x e xb : E) (hγ : 0 < γ)
    (hΛ : 0 ≤ Λ) (hγL : γ * (L + Λ) ≤ 1)
    (hz : -(F z + Λ • (z - c)) ∈ G z)
    (hxb : xb = J γ (x - γ • (F x + Λ • (x - c) + e))) :
    γ⁻¹ • ((x - γ • (F x + Λ • (x - c) + e)) - xb) ∈ G xb ∧
      ‖F xb + γ⁻¹ • ((x - γ • (F x + Λ • (x - c) + e)) - xb)‖ ≤
        8 / γ * ‖x - z‖ + 4 * ‖e‖ + ‖Λ • (z - c)‖ := by
  have hmem : γ⁻¹ • ((x - γ • (F x + Λ • (x - c) + e)) - xb) ∈ G xb := by
    rw [hxb]; exact H.res γ _ hγ
  refine ⟨hmem, ?_⟩
  have hLp : 0 ≤ L + Λ := by have := H.L_pos; linarith
  have hFL : ∀ y y', ‖(F y + Λ • (y - c)) - (F y' + Λ • (y' - c))‖ ≤ (L + Λ) * ‖y - y'‖ := by
    intro y y'
    have : (F y + Λ • (y - c)) - (F y' + Λ • (y' - c)) = (F y - F y') + Λ • (y - y') := by module
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hΛ, add_mul]
    exact add_le_add (H.lip y y') le_rfl
  have hzfix : J γ (z - γ • (F z + Λ • (z - c))) = z := by
    apply H.res_unique hγ
    have : γ⁻¹ • ((z - γ • (F z + Λ • (z - c))) - z) = -(F z + Λ • (z - c)) := by
      rw [show (z - γ • (F z + Λ • (z - c))) - z = -(γ • (F z + Λ • (z - c))) by abel, smul_neg,
        smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
    rw [this]; exact hz
  have hxbz : ‖xb - z‖ ≤ 2 * ‖x - z‖ + γ * ‖e‖ := by
    have hne := H.res_nonexp hγ (x - γ • (F x + Λ • (x - c) + e)) (z - γ • (F z + Λ • (z - c)))
    rw [hzfix, ← hxb] at hne
    refine hne.trans ?_
    have : (x - γ • (F x + Λ • (x - c) + e)) - (z - γ • (F z + Λ • (z - c))) =
        (x - z) - γ • ((F x + Λ • (x - c)) - (F z + Λ • (z - c))) - γ • e := by module
    rw [this]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans ?_) ?_
    · rw [norm_smul, Real.norm_of_nonneg hγ.le]
      have := hFL x z
      have h1 : γ * ‖(F x + Λ • (x - c)) - (F z + Λ • (z - c))‖ ≤ γ * ((L + Λ) * ‖x - z‖) :=
        mul_le_mul_of_nonneg_left this hγ.le
      have h2 := mul_le_mul_of_nonneg_right hγL (norm_nonneg (x - z))
      have e2 : γ * ((L + Λ) * ‖x - z‖) = γ * (L + Λ) * ‖x - z‖ := by ring
      linarith
    · rw [norm_smul, Real.norm_of_nonneg hγ.le]
  have hcert : F xb + γ⁻¹ • ((x - γ • (F x + Λ • (x - c) + e)) - xb) =
      (γ⁻¹ • (x - xb) - ((F x + Λ • (x - c)) - (F xb + Λ • (xb - c))) - e) -
        Λ • (xb - z) - Λ • (z - c) := by
    rw [show (x - γ • (F x + Λ • (x - c) + e)) - xb = (x - xb) - γ • (F x + Λ • (x - c) + e) by abel,
      smul_sub (γ⁻¹), smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
    module
  rw [hcert]
  have hxxb : ‖x - xb‖ ≤ 3 * ‖x - z‖ + γ * ‖e‖ := by
    have : x - xb = (x - z) - (xb - z) := by abel
    rw [this]; refine (norm_sub_le _ _).trans ?_; linarith
  have hw : ‖γ⁻¹ • (x - xb) - ((F x + Λ • (x - c)) - (F xb + Λ • (xb - c))) - e‖ ≤
      6 / γ * ‖x - z‖ + 3 * ‖e‖ := by
    refine (norm_sub_le _ _).trans ?_
    have h1 : ‖γ⁻¹ • (x - xb) - ((F x + Λ • (x - c)) - (F xb + Λ • (xb - c)))‖ ≤
        (γ⁻¹ + (L + Λ)) * ‖x - xb‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hγ).le, add_mul]
      exact add_le_add le_rfl (hFL x xb)
    have h2 : γ⁻¹ + (L + Λ) ≤ 2 / γ := by
      rw [show (2:ℝ) / γ = γ⁻¹ + γ⁻¹ by ring]
      have : L + Λ ≤ γ⁻¹ := by
        rw [← one_div, le_div_iff₀ hγ]; linarith [mul_comm γ (L + Λ)]
      linarith
    have h3 : (γ⁻¹ + (L + Λ)) * ‖x - xb‖ ≤ 2 / γ * (3 * ‖x - z‖ + γ * ‖e‖) :=
      mul_le_mul h2 hxxb (norm_nonneg _) (by positivity)
    have e3 : 2 / γ * (3 * ‖x - z‖ + γ * ‖e‖) = 6 / γ * ‖x - z‖ + 2 * ‖e‖ := by
      field_simp; ring
    linarith
  have hΛt : ‖Λ • (xb - z)‖ ≤ 2 / γ * ‖x - z‖ + ‖e‖ := by
    rw [norm_smul, Real.norm_of_nonneg hΛ]
    have h4 : Λ * ‖xb - z‖ ≤ Λ * (2 * ‖x - z‖ + γ * ‖e‖) := mul_le_mul_of_nonneg_left hxbz hΛ
    have hΛγ : Λ * γ ≤ 1 := by nlinarith [H.L_pos]
    have hΛ1 : Λ ≤ 1 / γ := by rw [le_div_iff₀ hγ]; linarith
    have h6 : Λ * (2 * ‖x - z‖) ≤ 1 / γ * (2 * ‖x - z‖) :=
      mul_le_mul_of_nonneg_right hΛ1 (by positivity)
    have h7 : Λ * (γ * ‖e‖) ≤ ‖e‖ := by
      have := mul_le_mul_of_nonneg_right hΛγ (norm_nonneg e)
      linarith [mul_assoc Λ γ ‖e‖]
    have e8 : 1 / γ * (2 * ‖x - z‖) = 2 / γ * ‖x - z‖ := by ring
    nlinarith
  calc ‖γ⁻¹ • (x - xb) - ((F x + Λ • (x - c)) - (F xb + Λ • (xb - c))) - e -
        Λ • (xb - z) - Λ • (z - c)‖
      ≤ ‖γ⁻¹ • (x - xb) - ((F x + Λ • (x - c)) - (F xb + Λ • (xb - c))) - e‖ +
          ‖Λ • (xb - z)‖ + ‖Λ • (z - c)‖ := by
        refine (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ (6 / γ * ‖x - z‖ + 3 * ‖e‖) + (2 / γ * ‖x - z‖ + ‖e‖) + ‖Λ • (z - c)‖ := by
        gcongr
    _ = 8 / γ * ‖x - z‖ + 4 * ‖e‖ + ‖Λ • (z - c)‖ := by ring

end OracleTemplate.StochasticCohypomonotone
