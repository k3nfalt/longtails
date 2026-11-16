import LongTails.Proofs.GapBoundedSmoothMollification
import LongTails.Setups.GapGeneralizedSmoothConvex

namespace LongTails.Proofs.GapBoundedSmoothParameters

noncomputable def spacing (m : ℕ) (R : ℝ) : ℝ := R / (64 * (m : ℝ) * Real.sqrt m)
noncomputable def slope (m : ℕ) (R ε : ℝ) : ℝ := 320 * ε * Real.sqrt m / R

lemma spacing_pos {m : ℕ} (hm : 0 < m) (R : ℝ) (hR : 0 < R) : 0 < spacing m R := by
  unfold spacing
  positivity

lemma slope_pos {m : ℕ} (hm : 0 < m) (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    0 < slope m R ε := by unfold slope; positivity

lemma product {m : ℕ} (hm : 0 < m) (R ε : ℝ) (hR : 0 < R) :
    (m : ℝ) * spacing m R * slope m R ε = 5 * ε := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt m := by positivity
  unfold spacing slope
  field_simp
  ring

lemma separation {m : ℕ} (hm : 0 < m) (L₀ R ε : ℝ)
    (hR : 0 < R) (hbound : 819200000 * (m : ℝ) ^ 2 * ε ≤ L₀ * R ^ 2) :
    4 * slope m R ε ≤ (L₀ / 10000) * spacing m R := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt m := by positivity
  have hs2 := Real.sq_sqrt hm0.le
  apply (mul_le_mul_iff_of_pos_right (show 0 < 10000 * R * (64 * (m : ℝ) * Real.sqrt m) by positivity)).mp
  have hleft : 4 * slope m R ε * (10000 * R * (64 * (m : ℝ) * Real.sqrt m)) =
      819200000 * (m : ℝ) ^ 2 * ε := by
    unfold slope
    field_simp
    rw [hs2]
    ring
  have hright : (L₀ / 10000) * spacing m R *
      (10000 * R * (64 * (m : ℝ) * Real.sqrt m)) = L₀ * R ^ 2 := by
    unfold spacing
    field_simp
  rw [hleft, hright]
  exact hbound

lemma initial_gap {m : ℕ} (hm : 0 < m) (R ε ρ : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (hρ : ρ ≤ spacing m R / 128) :
    2 * (m : ℝ) * spacing m R * slope m R ε + slope m R ε * ρ ≤ 11 * ε := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hb := spacing_pos hm R hR
  have hG := slope_pos hm R ε hR hε
  have hprod := product hm R ε hR
  have hρ' := mul_le_mul_of_nonneg_left hρ hG.le
  have hm' := mul_le_mul_of_nonneg_right hm1 (mul_nonneg hb.le hG.le)
  nlinarith

lemma hidden_gap {m : ℕ} (hm : 0 < m) (L R ε ρ : ℝ)
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) (hρ : ρ ≤ spacing m R / 128)
    (hsep : 4 * slope m R ε ≤ L * spacing m R) :
    3 * ε ≤ slope m R ε * ((m : ℝ) * spacing m R - spacing m R / 4 - ρ) -
      slope m R ε ^ 2 / (2 * L) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hb := spacing_pos hm R hR
  have hG := slope_pos hm R ε hR hε
  have hprod := product hm R ε hR
  have hpen : slope m R ε ^ 2 / (2 * L) ≤ slope m R ε * spacing m R / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * L)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsep hG.le]
  have hρ' := mul_le_mul_of_nonneg_left hρ hG.le
  have hm' := mul_le_mul_of_nonneg_right hm1 (mul_nonneg hb.le hG.le)
  nlinarith

lemma radius {m : ℕ} (hm : 0 < m) (R ρ : ℝ) (hR : 0 < R)
    (hρ : ρ ≤ spacing m R / 128) :
    Real.sqrt m * (2 * (m : ℝ) * spacing m R + ρ) ≤ R / 16 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt m := by positivity
  have hb := spacing_pos hm R hR
  have he : Real.sqrt m * (m : ℝ) * spacing m R = R / 64 := by
    unfold spacing
    field_simp
  have hsmall := mul_le_mul_of_nonneg_right hm1 (mul_nonneg hs.le hb.le)
  have hρ' := mul_le_mul_of_nonneg_left hρ hs.le
  nlinarith

lemma slope_radius {m : ℕ} (hm : 0 < m) (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R)
    (hsep : 4 * slope m R ε ≤ L * spacing m R) : slope m R ε / R ≤ L / 256 := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hs1 : 1 ≤ Real.sqrt m := Real.one_le_sqrt.mpr hm1
  have hb : spacing m R ≤ R / 64 := by
    unfold spacing
    apply (div_le_iff₀ (by positivity : 0 < 64 * (m : ℝ) * Real.sqrt m)).mpr
    nlinarith [mul_le_mul hm1 hs1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (m : ℝ))]
  have hh := mul_le_mul_of_nonneg_left hb hL.le
  apply (div_le_iff₀ hR).mpr
  nlinarith

lemma localized_curvature_budget {m : ℕ} (hm : 0 < m) (L R ε : ℝ)
    (hL : 0 < L) (hR : 0 < R) (hsep : 4 * slope m R ε ≤ L * spacing m R) :
    L + 376 * (slope m R ε / R + L) ≤ 10000 * L := by
  have hh := slope_radius hm L R ε hL hR hsep
  linarith

lemma hiding_ratio {m : ℕ} (hm : 0 < m) (R : ℝ) (hR : 0 < R) :
    (4 * R) ^ 2 / (spacing m R / 4) ^ 2 = 1048576 * (m : ℝ) ^ 3 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt m := by positivity
  have hs2 := Real.sq_sqrt hm0.le
  unfold spacing
  field_simp
  rw [hs2]
  ring

lemma hiding_dimension (p : LongTails.Setups.GapGeneralizedSmoothConvex.Params)
    (hp : LongTails.Setups.GapGeneralizedSmoothConvex.spec.valid p) {m : ℕ} (hm : 0 < m)
    (hms : (m : ℝ) ≤ Real.sqrt (p.L0 * p.R ^ 2 / p.ε)) :
    2 * (m : ℝ) ^ 2 * ((4 * p.R) ^ 2 / (spacing m p.R / 4) ^ 2) + (m : ℝ) ≤ p.d := by
  rw [hiding_ratio hm p.R hp.2.2.1]
  let U := 1 + p.L1 * p.R + Real.sqrt (p.L0 * p.R ^ 2 / p.ε)
  have hU : 1 ≤ U := by
    dsimp [U]
    linarith [mul_nonneg hp.2.1 hp.2.2.1.le, Real.sqrt_nonneg (p.L0 * p.R ^ 2 / p.ε)]
  have hmU : (m : ℝ) ≤ U := by
    dsimp [U]
    linarith [mul_nonneg hp.2.1 hp.2.2.1.le]
  have hm5 := pow_le_pow_left₀ (Nat.cast_nonneg m : (0 : ℝ) ≤ m) hmU 5
  have h5 : U ^ 5 ≤ U ^ 10 := pow_le_pow_right₀ hU (by norm_num)
  have h1 : U ≤ U ^ 10 := by simpa using pow_le_pow_right₀ hU (show 1 ≤ 10 by norm_num)
  have hdim := Nat.le_ceil (1208925819614629174706176 * U ^ 10)
  have hpdim : (⌈1208925819614629174706176 * U ^ 10⌉₊ : ℝ) ≤ p.d := by
    exact_mod_cast hp.2.2.2.2.2.2
  have hpow : 0 ≤ U ^ 10 := by positivity
  nlinarith only [hm5, h5, h1, hmU, hdim, hpdim, hpow]

end LongTails.Proofs.GapBoundedSmoothParameters
