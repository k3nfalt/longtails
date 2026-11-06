import LongTails.Proofs.QuasarCubicPotential

open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.QuasarCubicStepBound

open LongTails.Proofs.QuasarCubicPotential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radius_le {r R : ℝ} (hr : 0 ≤ r) (hR : 0 < R) : r ≤ R + r ^ 3 / R ^ 2 := by
  have h := young_cube hr (inv_pos.mpr hR)
  have e1 : (R⁻¹) ^ 2 * r ^ 3 / 3 = r ^ 3 / R ^ 2 / 3 := by field_simp
  have e2 : 2 / (3 * R⁻¹) = 2 * R / 3 := by field_simp
  rw [e1, e2] at h
  have : 0 ≤ r ^ 3 / R ^ 2 := by positivity
  linarith

lemma coupling_lower {τ X Y : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hY : 0 ≤ Y)
    (h : τ = 1 ∨ -Y ≤ X) : -Y ≤ (1 - τ) * X := by
  rcases h with h | h
  · simp [h, hY]
  · have h1 : 0 ≤ 1 - τ := by linarith
    nlinarith

lemma min_cond {a A1 M N γ r G : ℝ} (ha : 0 ≤ a) (hγ : 0 < γ) (hG0 : 0 ≤ G)
    (hM : 0 ≤ M) (hN : N = 7776 * M / γ ^ 3) (hG : G ≤ 3 * M / 4 * r ^ 2)
    (hcube : a ^ 3 ≤ 9 / 2 * A1 ^ 2) :
    16 / 9 * (a / γ * G) ^ 3 ≤ (M / 48 * A1 * r ^ 3) ^ 2 * N := by
  have hP : 0 ≤ M ^ 3 * r ^ 6 := by positivity
  have hG3 : G ^ 3 ≤ 27 / 64 * (M ^ 3 * r ^ 6) := by
    have := pow_le_pow_left₀ hG0 hG 3
    have e : (3 * M / 4 * r ^ 2) ^ 3 = 27 / 64 * (M ^ 3 * r ^ 6) := by ring
    linarith
  have h1 : a ^ 3 * G ^ 3 ≤ a ^ 3 * (27 / 64 * (M ^ 3 * r ^ 6)) :=
    mul_le_mul_of_nonneg_left hG3 (by positivity)
  have h2 : a ^ 3 * (M ^ 3 * r ^ 6) ≤ 9 / 2 * A1 ^ 2 * (M ^ 3 * r ^ 6) :=
    mul_le_mul_of_nonneg_right hcube hP
  have hl : 16 / 9 * (a / γ * G) ^ 3 = 16 / 9 * (a ^ 3 * G ^ 3) / γ ^ 3 := by
    field_simp
  have hr' : (M / 48 * A1 * r ^ 3) ^ 2 * N = 27 / 8 * (A1 ^ 2 * (M ^ 3 * r ^ 6)) / γ ^ 3 := by
    rw [hN]; field_simp; ring
  rw [hl, hr']
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith only [h1, h2]

lemma amgm_leftover {a A1 H D M γ Λ2 : ℝ} (hA1 : 0 < A1) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hM : 0 < M) (hγ : 0 < γ) (hcube : a ^ 3 ≤ 9 / 2 * A1 ^ 2)
    (hΛ2 : Λ2 = 1536 * H ^ 3 * D ^ 3 / (γ ^ 3 * M ^ 2)) :
    4 / 27 * (a / γ * H * D) ^ 3 / (M / 48 * A1) ^ 2 ≤ Λ2 := by
  rw [hΛ2, div_le_div_iff₀ (by positivity) (by positivity)]
  have e1 : 4 / 27 * (a / γ * H * D) ^ 3 * (γ ^ 3 * M ^ 2) =
      4 / 27 * a ^ 3 * (H ^ 3 * D ^ 3 * M ^ 2) := by field_simp
  have e2 : 1536 * H ^ 3 * D ^ 3 * (M / 48 * A1) ^ 2 = 2 / 3 * A1 ^ 2 * (H ^ 3 * D ^ 3 * M ^ 2) := by
    ring
  rw [e1, e2]
  have hp : 0 ≤ H ^ 3 * D ^ 3 * M ^ 2 := by positivity
  nlinarith only [mul_le_mul_of_nonneg_right hcube hp, hp]

lemma delta_term {a A1 δ D H R M γ r : ℝ} (ha : 0 ≤ a) (haA : a ≤ A1)
    (hH : 0 < H) (hD : 0 < D) (hR : 0 < R) (hM : 0 < M) (hγ : 0 < γ) (hr : 0 ≤ r)
    (hδ : δ ≤ γ * M * R ^ 2 / (48 * H * D ^ 2)) :
    a / γ * (δ * D ^ 2 * H * r ^ 3 / (2 * R ^ 2)) ≤ M / 96 * A1 * r ^ 3 := by
  have hq : δ * D ^ 2 * H / (2 * R ^ 2) ≤ γ * M / 96 := by
    rw [div_le_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hδ
    nlinarith only [hδ]
  have e : a / γ * (δ * D ^ 2 * H * r ^ 3 / (2 * R ^ 2)) =
      a / γ * (δ * D ^ 2 * H / (2 * R ^ 2)) * r ^ 3 := by ring
  rw [e]
  have h1 : a / γ * (δ * D ^ 2 * H / (2 * R ^ 2)) ≤ a / γ * (γ * M / 96) :=
    mul_le_mul_of_nonneg_left hq (div_nonneg ha hγ.le)
  have h2 : a / γ * (γ * M / 96) = a * M / 96 := by field_simp
  have h3 : a * M / 96 ≤ M / 96 * A1 := by nlinarith only [haA, hM]
  exact mul_le_mul_of_nonneg_right (h1.trans (h2 ▸ h3)) (by positivity)

lemma coupling_budget {Y H r v D δ Bn L R : ℝ} (hH : 0 < H) (hr : 0 ≤ r) (hv : 0 ≤ v)
    (hvD : v ≤ D) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hBn0 : 0 ≤ Bn) (hBn : Bn ≤ L + H * D)
    (hR : 0 < R) (hRD : 200 * R ≤ D)
    (hY : Y = H * r ^ 2 * v + δ * v ^ 2 * (Bn / 2 + H / 2 * r + H / 6 * (δ * v))) :
    Y ≤ H * D * r ^ 2 + δ * D ^ 2 * (L / 2 + H * D) + δ * D ^ 2 * H * r ^ 3 / (2 * R ^ 2) := by
  have hrR := radius_le hr hR
  have h1 : H * r ^ 2 * v ≤ H * D * r ^ 2 := by
    have := mul_le_mul_of_nonneg_left hvD (by positivity : 0 ≤ H * r ^ 2)
    linarith only [this]
  have h3 : δ * v ≤ D := by nlinarith only [hδ1, hvD, hv, hδ0]
  have h4 : H / 6 * (δ * v) ≤ H / 6 * D := mul_le_mul_of_nonneg_left h3 (by positivity)
  have h2 : H / 2 * r ≤ H / 2 * R + H * r ^ 3 / (2 * R ^ 2) := by
    have := mul_le_mul_of_nonneg_left hrR (by positivity : 0 ≤ H / 2)
    have e : H / 2 * (R + r ^ 3 / R ^ 2) = H / 2 * R + H * r ^ 3 / (2 * R ^ 2) := by
      field_simp
    linarith only [this, e]
  have hRD' : H / 2 * R ≤ H * D / 3 := by
    have h1 := mul_le_mul_of_nonneg_left hRD hH.le
    have h2 := mul_pos hH hR
    linarith only [h1, h2]
  have hin2 : Bn / 2 + H / 2 * r + H / 6 * (δ * v) ≤ L / 2 + H * D + H * r ^ 3 / (2 * R ^ 2) := by
    linarith only [h2, h4, hRD', hBn]
  have h5 : δ * v ^ 2 ≤ δ * D ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv hvD 2) hδ0.le
  have hpos : 0 ≤ Bn / 2 + H / 2 * r + H / 6 * (δ * v) := by positivity
  have h6 := mul_le_mul h5 hin2 hpos (by positivity)
  have e2 : δ * D ^ 2 * (L / 2 + H * D + H * r ^ 3 / (2 * R ^ 2)) =
      δ * D ^ 2 * (L / 2 + H * D) + δ * D ^ 2 * H * r ^ 3 / (2 * R ^ 2) := by ring
  rw [hY]
  linarith only [h1, h6, e2]

lemma potential_step {N M H γ δ D L R Λ2 Λ3 : ℝ} {x0 x v y z h gz s : E}
    {c fx fz ey q τ Bn : ℝ} {k : ℕ}
    (hN : N = 7776 * M / γ ^ 3) (hM : 2 * H ≤ M) (hH : 0 < H) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hR : 0 < R) (hD : 200 * R ≤ D) (hL : 0 ≤ L)
    (hv : v = center N x0 s) (hy : y = x + τ • (v - x)) (hz : z = y + h)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hI : total k * fx + M / 32 * q - (k * Λ2 + total k * Λ3) ≤ psi N x0 c s v)
    (hey : ey ≤ fx) (hdesc : fz ≤ ey - (M - H) / 6 * ‖h‖ ^ 3)
    (hin : (M - H) / 2 * ‖h‖ ^ 3 ≤ ⟪gz, -h⟫) (hgn : ‖gz‖ ≤ (M + H) / 2 * ‖h‖ ^ 2)
    (hcoup : τ = 1 ∨ -(H * ‖h‖ ^ 2 * ‖v - x‖ +
      δ * ‖v - x‖ ^ 2 * (Bn / 2 + H / 2 * ‖h‖ + H / 6 * (δ * ‖v - x‖))) ≤ ⟪gz, v - x⟫)
    (hdD : ‖v - x‖ ≤ D) (hBn0 : 0 ≤ Bn) (hBn : Bn ≤ L + H * D) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ : δ ≤ γ * M * R ^ 2 / (48 * H * D ^ 2))
    (hΛ2 : Λ2 = 1536 * H ^ 3 * D ^ 3 / (γ ^ 3 * M ^ 2))
    (hΛ3 : Λ3 = δ * D ^ 2 * (L / 2 + H * D) / γ) :
    total (k + 1) * fz + M / 32 * (q + total (k + 1) * ‖h‖ ^ 3) -
        ((k + 1 : ℕ) * Λ2 + total (k + 1) * Λ3) ≤
      psi N x0 (c + weight k * (fz - ⟪gz, z⟫ / γ)) (s + (weight k / γ) • gz)
        (center N x0 (s + (weight k / γ) • gz)) := by
  have ha : 0 < weight k := weight_pos k
  have hA1 : total (k + 1) = total k + weight k := total_succ k
  have hAk : 0 ≤ total k := total_nonneg k
  have haA : weight k ≤ total (k + 1) := weight_le_total k
  have hA1p : 0 < total (k + 1) := ha.trans_le haA
  have hcube := weight_cube_le k
  have hMpos : 0 < M := by linarith
  have hNpos : 0 < N := by rw [hN]; positivity
  have hD0 : 0 < D := by linarith
  have hr : 0 ≤ ‖h‖ := norm_nonneg h
  have hag : weight k ≤ weight k / γ := by rw [le_div_iff₀ hγ]; nlinarith only [ha, hγ1]
  have hagp : 0 ≤ weight k / γ := div_nonneg ha.le hγ.le
  set a := weight k
  set A1 := total (k + 1)
  set r := ‖h‖
  set v' := center N x0 (s + (a / γ) • gz)
  have hpsi : psi N x0 (c + a * (fz - ⟪gz, z⟫ / γ)) (s + (a / γ) • gz) v' =
      psi N x0 c s v' + a * fz + a / γ * ⟪gz, v' - z⟫ := by
    simp only [psi, inner_add_left, real_inner_smul_left, inner_sub_right]
    field_simp
    ring
  have hlow := psi_lower hNpos x0 c s v'
  rw [← hv] at hlow
  have hsplit : ⟪gz, v' - z⟫ = (1 - τ) * ⟪gz, v - x⟫ + ⟪gz, -h⟫ + ⟪gz, v' - v⟫ := by
    have : v' - z = (1 - τ) • (v - x) + -h + (v' - v) := by
      rw [hz, hy]; module
    rw [this, inner_add_right, inner_add_right, real_inner_smul_right]
  set t := ‖v' - v‖
  have ht : 0 ≤ t := norm_nonneg _
  have hcs : -(‖gz‖ * t) ≤ ⟪gz, v' - v⟫ := by
    have := abs_real_inner_le_norm gz (v' - v)
    linarith only [(abs_le.mp this).1]
  have hgn' : ‖gz‖ ≤ 3 * M / 4 * r ^ 2 := by
    have : (M + H) / 2 * r ^ 2 ≤ 3 * M / 4 * r ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [hM]) (by positivity)
    linarith only [this, hgn]
  have hmin : -(M / 48 * A1 * r ^ 3) ≤ N / 12 * t ^ 3 - (a / γ * ‖gz‖) * t :=
    cubic_min hNpos ht (mul_nonneg hagp (norm_nonneg _))
      (by have := hA1p.le; positivity)
      (min_cond ha.le hγ (norm_nonneg _) hMpos.le hN hgn' hcube)
  set Y := H * r ^ 2 * ‖v - x‖ + δ * ‖v - x‖ ^ 2 * (Bn / 2 + H / 2 * r + H / 6 * (δ * ‖v - x‖))
  have hY0 : 0 ≤ Y := by positivity
  have hcl := coupling_lower hτ0 hτ1 hY0 hcoup
  have hYle := coupling_budget (Y := Y) hH hr (norm_nonneg _) hdD hδ0 hδ1 hBn0 hBn hR hD rfl
  have hamgm := amgm_square (c := a / γ * H * D) (r := r) (θ := M / 48 * A1)
    (by have := hH.le; have := hD0.le; positivity) hr (by positivity)
  have hleft := amgm_leftover hA1p hH.le hD0.le hMpos hγ hcube hΛ2
  have hdelta := delta_term ha.le haA hH hD0 hR hMpos hγ hr hδ
  have hΛ3a : a / γ * (δ * D ^ 2 * (L / 2 + H * D)) = a * Λ3 := by rw [hΛ3]; field_simp
  have hcoupT : -(a / γ * Y) ≤ a / γ * ((1 - τ) * ⟪gz, v - x⟫) := by
    have := mul_le_mul_of_nonneg_left hcl hagp
    linarith only [this]
  have hYT : a / γ * Y ≤ a / γ * H * D * r ^ 2 + a * Λ3 + M / 96 * A1 * r ^ 3 := by
    have := mul_le_mul_of_nonneg_left hYle hagp
    have e : a / γ * (H * D * r ^ 2 + δ * D ^ 2 * (L / 2 + H * D) +
        δ * D ^ 2 * H * r ^ 3 / (2 * R ^ 2)) =
        a / γ * H * D * r ^ 2 + a / γ * (δ * D ^ 2 * (L / 2 + H * D)) +
          a / γ * (δ * D ^ 2 * H * r ^ 3 / (2 * R ^ 2)) := by ring
    linarith only [this, e, hΛ3a, hdelta]
  have hHD : a / γ * H * D * r ^ 2 ≤ M / 48 * A1 * r ^ 3 + Λ2 := by
    linarith only [hamgm, hleft]
  have hMH : 0 ≤ M - H := by linarith only [hM, hH]
  have hr3 : 0 ≤ r ^ 3 := by positivity
  have hpos1 : total k * ((M - H) / 6 * r ^ 3) ≤ total k * (fx - fz) := by
    apply mul_le_mul_of_nonneg_left _ hAk; linarith only [hey, hdesc]
  have hin0 : 0 ≤ ⟪gz, -h⟫ := le_trans (by positivity) hin
  have hpos2 : a * ((M - H) / 6 * r ^ 3) ≤ a / γ * ⟪gz, -h⟫ := by
    have h1 : (M - H) / 6 * r ^ 3 ≤ ⟪gz, -h⟫ := by
      have : 0 ≤ (M - H) * r ^ 3 := mul_nonneg hMH hr3
      linarith only [hin, this]
    calc a * ((M - H) / 6 * r ^ 3) ≤ a * ⟪gz, -h⟫ := mul_le_mul_of_nonneg_left h1 ha.le
      _ ≤ a / γ * ⟪gz, -h⟫ := mul_le_mul_of_nonneg_right hag hin0
  have hposA : M / 12 * A1 * r ^ 3 ≤ total k * ((M - H) / 6 * r ^ 3) + a * ((M - H) / 6 * r ^ 3) := by
    rw [hA1]
    have : 0 ≤ (total k + a) * r ^ 3 := mul_nonneg (by linarith only [hAk, ha]) hr3
    nlinarith only [this, hM, hH]
  have hmulmin : -(a / γ * ‖gz‖ * t) ≤ a / γ * ⟪gz, v' - v⟫ := by
    have := mul_le_mul_of_nonneg_left hcs hagp
    linarith only [this]
  have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
  rw [hpsi, hcast, hsplit]
  have hexp : a / γ * ((1 - τ) * ⟪gz, v - x⟫ + ⟪gz, -h⟫ + ⟪gz, v' - v⟫) =
      a / γ * ((1 - τ) * ⟪gz, v - x⟫) + a / γ * ⟪gz, -h⟫ + a / γ * ⟪gz, v' - v⟫ := by ring
  rw [hexp]
  have e1 : A1 * fz = total k * fz + a * fz := by rw [hA1]; ring
  have e2 : A1 * Λ3 = total k * Λ3 + a * Λ3 := by rw [hA1]; ring
  have e3 : total k * (fx - fz) = total k * fx - total k * fz := by ring
  have e4 : (a / γ * ‖gz‖) * t = a / γ * ‖gz‖ * t := by ring
  linarith only [hI, hlow, hmin, hmulmin, hcoupT, hYT, hHD, hpos1, hpos2, hposA, e1, e2, e3, e4]

end LongTails.Proofs.QuasarCubicStepBound
