import LongTails.Proofs.CohypoRegularizedOperator

open scoped RealInnerProductSpace

namespace OracleTemplate.StochasticCohypomonotone

lemma young_ab {a b t : ℝ} (ht : 0 < t) : a * b ≤ t / 2 * a ^ 2 + 1 / (2 * t) * b ^ 2 := by
  have h : 0 ≤ (t * a - b) ^ 2 / (2 * t) := by positivity
  have e : t / 2 * a ^ 2 + 1 / (2 * t) * b ^ 2 - a * b = (t * a - b) ^ 2 / (2 * t) := by
    field_simp; ring
  linarith

lemma eg_scalar {ρ γ α Λ M L' A X P Q W nu nv ne T : ℝ} (hρ : 0 ≤ ρ) (hγ : 0 < γ) (hα : 0 < α)
    (hΛ : 0 ≤ Λ) (h2ρΛ : 2 * ρ * Λ < 1) (hγL : γ * L' < 1) (hL' : 0 ≤ L')
    (hcoef : (1 + α) * (2 * (ρ / (1 - 2 * ρ * Λ)) + α * γ) ≤ γ - M / 2)
    (hcontr : 2 * Λ * (γ / (1 - γ * L')) ^ 2 ≤ M / 2)
     (hnv : 0 ≤ nv) (hX : 0 ≤ X)
    (hT : T = A - 2 * (α * γ) * (P + Q) + (α * γ) ^ 2 * W)
    (hP : -ρ * W + Λ * (1 - ρ * Λ) * X ≤ (1 - 2 * ρ * Λ) * P)
    (hQ : γ / 2 * nu ^ 2 + (1 - (γ * L') ^ 2) / (2 * γ) * nv ^ 2 - ne * nv ≤ Q)
    (hW : W ≤ nu ^ 2 + 2 * nu * ne + ne ^ 2)
    (hVU : (1 - γ * L') / γ * nv ≤ nu)
    (hA : A ≤ 2 * X + 2 * nv ^ 2) :
    T ≤ (1 - α * γ * Λ) * A +
      (α * γ ^ 2 / (1 - (γ * L') ^ 2) +
        α * γ * (2 * (ρ / (1 - 2 * ρ * Λ)) + α * γ) * (1 + 1 / α)) * ne ^ 2 := by
  set ρ' := ρ / (1 - 2 * ρ * Λ) with hρ'
  have hk : 0 < 1 - 2 * ρ * Λ := by linarith
  have hgl : 0 < 1 - γ * L' := by linarith
  have hρ'0 : 0 ≤ ρ' := div_nonneg hρ hk.le
  have hag : 0 < α * γ := mul_pos hα hγ
  have hP' : -ρ' * W + Λ * X ≤ P := by
    have h2 : Λ * (1 - 2 * ρ * Λ) * X ≤ Λ * (1 - ρ * Λ) * X := by
      have : 0 ≤ Λ * X * (ρ * Λ) := by positivity
      nlinarith
    have hρk : ρ' * (1 - 2 * ρ * Λ) = ρ := by rw [hρ']; exact div_mul_cancel₀ _ hk.ne'
    have h3 : (-ρ' * W + Λ * X) * (1 - 2 * ρ * Λ) = -ρ * W + Λ * (1 - 2 * ρ * Λ) * X := by
      linear_combination (-W) * hρk
    have h4 : (-ρ' * W + Λ * X) * (1 - 2 * ρ * Λ) ≤ P * (1 - 2 * ρ * Λ) := by nlinarith
    exact le_of_mul_le_mul_right h4 hk
  set t := (1 - (γ * L') ^ 2) / γ with ht
  have hsq : (γ * L') ^ 2 < 1 := by
    have h0 : 0 ≤ γ * L' := by positivity
    nlinarith
  have htpos : 0 < t := by rw [ht]; exact div_pos (by linarith) hγ
  have hy := young_ab (a := nv) (b := ne) htpos
  have e4 : 1 / (2 * t) = γ / (2 * (1 - (γ * L') ^ 2)) := by rw [ht]; field_simp
  have e5 : t / 2 * nv ^ 2 = (1 - (γ * L') ^ 2) / (2 * γ) * nv ^ 2 := by rw [ht]; field_simp
  have hQ' : γ / 2 * nu ^ 2 - γ / (2 * (1 - (γ * L') ^ 2)) * ne ^ 2 ≤ Q := by
    rw [e4, e5] at hy; linarith [mul_comm ne nv]
  have hW' : W ≤ (1 + α) * nu ^ 2 + (1 + 1 / α) * ne ^ 2 := by
    have hy2 := young_ab (a := nu) (b := ne) hα
    have : 1 / α = 2 * (1 / (2 * α)) := by field_simp
    nlinarith
  have hV : nv ^ 2 ≤ (γ / (1 - γ * L')) ^ 2 * nu ^ 2 := by
    have h3 : nv ≤ γ / (1 - γ * L') * nu := by
      have : nv = γ / (1 - γ * L') * ((1 - γ * L') / γ * nv) := by field_simp
      rw [this]; gcongr
    have := pow_le_pow_left₀ hnv h3 2
    rw [mul_pow] at this; exact this
  have hU0 : 0 ≤ nu ^ 2 := sq_nonneg _
  have hN0 : 0 ≤ ne ^ 2 := sq_nonneg _
  have hcoef' : 0 ≤ 2 * (α * γ) * ρ' + (α * γ) ^ 2 := by positivity
  have s2 := mul_le_mul_of_nonneg_left hW' hcoef'
  have s3 : (α * γ) * (M / 2) * nu ^ 2 ≤ (α * γ) * (γ - (1 + α) * (2 * ρ' + α * γ)) * nu ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ hU0
    exact mul_le_mul_of_nonneg_left (by linarith) hag.le
  have s4 : (α * γ * Λ) * A ≤ (α * γ * Λ) * (2 * X + 2 * nv ^ 2) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have s5 : (α * γ * Λ) * (2 * nv ^ 2) ≤ (α * γ) * (M / 2) * nu ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hV (by positivity : (0:ℝ) ≤ α * γ * Λ * 2)
    have h2 := mul_le_mul_of_nonneg_left hcontr (mul_nonneg hag.le hU0)
    linear_combination h1 + h2
  have s1 : 2 * (α * γ) * (-ρ' * W + Λ * X + (γ / 2 * nu ^ 2 -
      γ / (2 * (1 - (γ * L') ^ 2)) * ne ^ 2)) ≤ 2 * (α * γ) * (P + Q) :=
    mul_le_mul_of_nonneg_left (add_le_add hP' hQ') (by linarith)
  have ek : α * γ ^ 2 / (1 - (γ * L') ^ 2) = 2 * (α * γ) * (γ / (2 * (1 - (γ * L') ^ 2))) := by
    field_simp
  rw [hT, ek]
  linear_combination s1 + s2 + s3 + s4 + s5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : E → E} {G : E → Set E} {J : ℝ → E → E} {L ρ : ℝ}

lemma OpHyp.eg_step (H : OpHyp F G J L ρ) {γ α Λ M : ℝ} (c z x e xb : E) (hγ : 0 < γ)
    (hα : 0 < α) (hΛ : 0 ≤ Λ) (h2ρΛ : 2 * ρ * Λ < 1) (hγL : γ * (L + Λ) < 1)
    (hcoef : (1 + α) * (2 * (ρ / (1 - 2 * ρ * Λ)) + α * γ) ≤ γ - M / 2)
    (hcontr : 2 * Λ * (γ / (1 - γ * (L + Λ))) ^ 2 ≤ M / 2)
    (hz : -(F z + Λ • (z - c)) ∈ G z)
    (hxb : xb = J γ (x - γ • (F x + Λ • (x - c) + e))) :
    ‖x - (α * γ) • (γ⁻¹ • (x - xb) - (F x + Λ • (x - c)) - e + (F xb + Λ • (xb - c))) - z‖ ^ 2 ≤
      (1 - α * γ * Λ) * ‖x - z‖ ^ 2 +
        (α * γ ^ 2 / (1 - (γ * (L + Λ)) ^ 2) +
          α * γ * (2 * (ρ / (1 - 2 * ρ * Λ)) + α * γ) * (1 + 1 / α)) * ‖e‖ ^ 2 := by
  have hρ := H.ρ_nonneg
  have hLp : 0 ≤ L + Λ := by have := H.L_pos; linarith
  have haG : γ⁻¹ • ((x - γ • (F x + Λ • (x - c) + e)) - xb) ∈ G xb := by
    rw [hxb]; exact H.res γ _ hγ
  have ha' : γ⁻¹ • ((x - γ • (F x + Λ • (x - c) + e)) - xb) =
      γ⁻¹ • (x - xb) - (F x + Λ • (x - c)) - e := by
    rw [show (x - γ • (F x + Λ • (x - c) + e)) - xb = (x - xb) - γ • (F x + Λ • (x - c) + e) by abel,
      smul_sub (γ⁻¹), smul_smul, inv_mul_cancel₀ hγ.ne', one_smul]
    abel
  rw [ha'] at haG
  have hpair := H.reg_pair (Λ := Λ) c xb z _ _ haG hz
  have hw : F xb + (γ⁻¹ • (x - xb) - (F x + Λ • (x - c)) - e) + Λ • (xb - c) -
      (F z + -(F z + Λ • (z - c)) + Λ • (z - c)) =
      γ⁻¹ • (x - xb) - (F x + Λ • (x - c)) - e + (F xb + Λ • (xb - c)) := by module
  rw [hw] at hpair
  obtain ⟨w, hwdef⟩ : ∃ w, w = γ⁻¹ • (x - xb) - (F x + Λ • (x - c)) - e + (F xb + Λ • (xb - c)) :=
    ⟨_, rfl⟩
  rw [← hwdef] at hpair ⊢
  obtain ⟨d, hddef⟩ : ∃ d, d = (F x + Λ • (x - c)) - (F xb + Λ • (xb - c)) := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u, u = γ⁻¹ • (x - xb) - d := ⟨_, rfl⟩
  have hwu : w = u - e := by rw [hwdef, hudef, hddef]; abel
  have hdn : ‖d‖ ≤ (L + Λ) * ‖x - xb‖ := by
    have : d = (F x - F xb) + Λ • (x - xb) := by rw [hddef]; module
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg hΛ, add_mul]
    exact add_le_add (H.lip x xb) le_rfl
  have hxz : x - z = (x - xb) + (xb - z) := by abel
  refine eg_scalar (P := ⟪w, xb - z⟫) (Q := ⟪w, x - xb⟫) (W := ‖w‖ ^ 2) (nu := ‖u‖)
    (nv := ‖x - xb‖) (ne := ‖e‖) (X := ‖xb - z‖ ^ 2) hρ hγ hα hΛ h2ρΛ hγL hLp hcoef hcontr
     (norm_nonneg _) (sq_nonneg _) ?_ hpair ?_ ?_ ?_ ?_
  · have : x - (α * γ) • w - z = (x - z) - (α * γ) • w := by abel
    rw [this, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm, hxz, inner_add_right]
    ring
  ·
    have huv : ⟪u, x - xb⟫ = γ / 2 * ‖u‖ ^ 2 + ‖x - xb‖ ^ 2 / (2 * γ) - γ / 2 * ‖d‖ ^ 2 := by
      have hU : ‖u‖ ^ 2 = (γ⁻¹) ^ 2 * ‖x - xb‖ ^ 2 - 2 * γ⁻¹ * ⟪d, x - xb⟫ + ‖d‖ ^ 2 := by
        rw [hudef, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inner_smul_left,
          real_inner_comm]
        simp only [conj_trivial]; try ring
      have hi : ⟪u, x - xb⟫ = γ⁻¹ * ‖x - xb‖ ^ 2 - ⟪d, x - xb⟫ := by
        rw [hudef, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
        simp only [conj_trivial]
      rw [hi, hU]; field_simp; try ring
    have hd2 : ‖d‖ ^ 2 ≤ (L + Λ) ^ 2 * ‖x - xb‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg d) hdn 2
      rwa [mul_pow] at this
    have hev : ⟪e, x - xb⟫ ≤ ‖e‖ * ‖x - xb‖ := real_inner_le_norm _ _
    rw [hwu, inner_sub_left, huv]
    have : γ / 2 * ‖d‖ ^ 2 ≤ γ / 2 * ((L + Λ) ^ 2 * ‖x - xb‖ ^ 2) := by gcongr
    have e7 : (1 - (γ * (L + Λ)) ^ 2) / (2 * γ) * ‖x - xb‖ ^ 2 =
        ‖x - xb‖ ^ 2 / (2 * γ) - γ / 2 * ((L + Λ) ^ 2 * ‖x - xb‖ ^ 2) := by
      field_simp; try ring
    linarith
  · rw [hwu, norm_sub_sq_real]
    have := real_inner_le_norm (-u) e
    rw [inner_neg_left, norm_neg] at this
    nlinarith
  · have h2 : ‖γ⁻¹ • (x - xb)‖ ≤ ‖u‖ + ‖d‖ := by
      have : γ⁻¹ • (x - xb) = u + d := by rw [hudef]; abel
      rw [this]; exact norm_add_le _ _
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hγ).le] at h2
    have : (1 - γ * (L + Λ)) / γ * ‖x - xb‖ = γ⁻¹ * ‖x - xb‖ - (L + Λ) * ‖x - xb‖ := by
      field_simp; try ring
    rw [this]; linarith [hdn, h2]
  · rw [hxz]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (x - xb) (xb - z)) 2
    nlinarith [sq_nonneg (‖x - xb‖ - ‖xb - z‖), norm_nonneg (x - xb), norm_nonneg (xb - z)]

end OracleTemplate.StochasticCohypomonotone
