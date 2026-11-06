import LongTails.Algorithms.StochasticEquality
import LongTails.Proofs.StochasticEqualityStopped

namespace LongTails.Proofs.StochasticEqualityTuning

open LongTails.Algorithms.StochasticEquality
open LongTails.Setups.StochasticRegularEqualities

noncomputable def scale (p : Public) : ℝ :=
  2 + p.Lf + p.Lc + p.LJ + p.ν + 1 / p.ν + p.Δ + p.C0 + p.Lnoise

lemma scale_bounds (p : Params) (hp : spec.valid p) :
    2 ≤ scale p.toPublic ∧ 2 + p.Lf ≤ scale p.toPublic ∧
    1 + p.Lc ≤ scale p.toPublic ∧ 1 + p.C0 ≤ scale p.toPublic ∧
    p.LJ ≤ scale p.toPublic ∧ p.ν ≤ scale p.toPublic ∧
    1 / p.ν ≤ scale p.toPublic ∧ p.Δ ≤ scale p.toPublic ∧ p.Lnoise ≤ scale p.toPublic := by
  rcases hp with ⟨_, _, _, hν, hf, hc, hJ, _, hn, hd, hC, _, _⟩
  have hinv : 0 ≤ 1 / p.ν := by positivity
  dsimp [scale]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma positiveCeil_lower (x : ℝ) : x ≤ (positiveCeil x : ℝ) := by
  exact (Nat.le_ceil x).trans (by exact_mod_cast le_max_right 1 ⌈x⌉₊)

lemma positiveCeil_upper {x : ℝ} (hx : 0 ≤ x) : (positiveCeil x : ℝ) ≤ x + 1 := by
  change ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ x + 1
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (Nat.ceil_lt_add_one hx).le

lemma log_factor_square {S : ℝ} (hS : 1 ≤ S) : (1 + Real.log S) ^ 2 ≤ 4 * S := by
  have hpos : 0 < S := by linarith
  have hs := Real.sqrt_pos.mpr hpos
  have hlog := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hpos.le] at hlog
  have hnonneg := Real.log_nonneg hS
  have hsq := Real.sq_sqrt hpos.le
  have hle : 1 + Real.log S ≤ 2 * Real.sqrt S := by linarith
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ 1 + Real.log S) hle 2
  nlinarith

lemma log_factor_le {S ε : ℝ} (hS : 1 ≤ S) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ 1 + Real.log (S / ε) ∧ 1 + Real.log (S / ε) ≤ S / ε := by
  have hratio : 1 ≤ S / ε := (le_div_iff₀ hε).mpr (by linarith)
  constructor
  · linarith [Real.log_nonneg hratio]
  · linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hratio)]

lemma tuned_joint_caps {S L : ℝ} (hS : 2 ≤ S) (hL : 1 + L ≤ S) :
    8 * (1 + L) * (10 ^ 6 * S ^ 10) ≤ (4000 * S ^ 6) ^ 2 ∧
      16 * (10 ^ 6 * S ^ 10) ≤ (10 ^ 10 * S ^ 24) * (1 / (10 * S ^ 7)) ^ 2 := by
  have hpos : 0 < S := by linarith
  constructor
  · have hpow : S ^ 11 ≤ S ^ 12 := by
      apply pow_le_pow_right₀ (by linarith : 1 ≤ S)
      norm_num
    have h₁ := mul_le_mul_of_nonneg_right hL (show 0 ≤ 8 * (10 ^ 6 * S ^ 10) by positivity)
    nlinarith [pow_nonneg hpos.le 12]
  · field_simp [hpos.ne']
    nlinarith [pow_nonneg hpos.le 24]

lemma multiplier_coefficient_bound {S Lf Lc LJ ν : ℝ} (hS : 1 ≤ S) (hν : 0 < ν)
    (hf : 0 ≤ Lf) (hJ : 0 ≤ LJ)
    (hfS : Lf ≤ S) (hcS : Lc ≤ S) (hJS : LJ ≤ S) (hinv : ν⁻¹ ≤ S) :
    (Lc * Lf + Lc * LJ * (4000 * S ^ 6) / ν + LJ * (4000 * S ^ 6)) / ν ^ 2 ≤
      8001 * S ^ 11 := by
  have hS0 : 0 ≤ S := by linarith
  have hν0 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  simp only [div_eq_mul_inv, ← inv_pow]
  calc
    _ ≤ (S * S + S * S * (4000 * S ^ 6) * S + S * (4000 * S ^ 6)) * S ^ 2 := by gcongr
    _ = S ^ 4 + 4000 * S ^ 11 + 4000 * S ^ 9 := by ring
    _ ≤ _ := by
      have h4 : S ^ 4 ≤ S ^ 11 := pow_le_pow_right₀ hS (by norm_num)
      have h9 : S ^ 9 ≤ S ^ 11 := pow_le_pow_right₀ hS (by norm_num)
      linarith

lemma direction_coefficient_bound {S Lc ν : ℝ} (hS : 1 ≤ S) (hν : 0 < ν)
    (hc : 0 ≤ Lc) (hcS : Lc ≤ S) (hinv : ν⁻¹ ≤ S) :
    (1 + 4 * Lc ^ 2 / ν ^ 2) +
      ((1 + 4 * Lc ^ 2 / ν ^ 2) * (4000 * S ^ 6) / ν +
        4 * Lc * (4000 * S ^ 6) / ν ^ 2 + 4 * (4000 * S ^ 6) / ν) +
      Lc + 1 / (10 * S ^ 7) ≤ 10 ^ 6 * S ^ 11 := by
  have hS0 : 0 ≤ S := by linarith
  have hν0 : 0 ≤ ν⁻¹ := inv_nonneg.mpr hν.le
  have hα : 1 + 4 * Lc ^ 2 * (ν⁻¹) ^ 2 ≤ 5 * S ^ 4 := by
    calc
      _ ≤ 1 + 4 * S ^ 2 * S ^ 2 := by gcongr
      _ ≤ _ := by nlinarith [one_le_pow₀ hS (n := 4)]
  have hM : 1 / (10 * S ^ 7) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 10 * S ^ 7)).mpr
    nlinarith [one_le_pow₀ hS (n := 7)]
  simp only [div_eq_mul_inv, ← inv_pow] at hM ⊢
  calc
    _ ≤ 5 * S ^ 4 + (5 * S ^ 4 * (4000 * S ^ 6) * S +
        4 * S * (4000 * S ^ 6) * S ^ 2 + 4 * (4000 * S ^ 6) * S) + S + 1 := by gcongr
    _ = 5 * S ^ 4 + 20000 * S ^ 11 + 16000 * S ^ 9 + 16000 * S ^ 7 + S + 1 := by ring
    _ ≤ _ := by
      have h4 : S ^ 4 ≤ S ^ 11 := pow_le_pow_right₀ hS (by norm_num)
      have h9 : S ^ 9 ≤ S ^ 11 := pow_le_pow_right₀ hS (by norm_num)
      have h7 : S ^ 7 ≤ S ^ 11 := pow_le_pow_right₀ hS (by norm_num)
      have h1 : S ≤ S ^ 11 := by simpa using pow_le_pow_right₀ hS (show 1 ≤ 11 by omega)
      have h0 : 1 ≤ S ^ 11 := one_le_pow₀ hS
      norm_num
      linarith

lemma penalty_bound {S ν : ℝ} (hS : 1 ≤ S) (hν : 0 < ν) (hinv : ν⁻¹ ≤ S) :
    8 * (((8001 * S ^ 11) / ν) ^ 2 + (8001 * S ^ 11) / ν + 1) ≤ 10 ^ 10 * S ^ 24 := by
  have hS0 : 0 ≤ S := by linarith
  have hκ : (8001 * S ^ 11) / ν ≤ 8001 * S ^ 12 := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ 8001 * S ^ 11 * S := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  calc
    _ ≤ 8 * ((8001 * S ^ 12) ^ 2 + 8001 * S ^ 12 + 1) := by gcongr
    _ ≤ _ := by
      have h12 : S ^ 12 ≤ S ^ 24 := pow_le_pow_right₀ hS (by norm_num)
      have h0 : 1 ≤ S ^ 24 := one_le_pow₀ hS
      nlinarith

lemma coercivity_penalty_bound {S L ν : ℝ} (hS : 1 ≤ S) (hν : 0 < ν)
    (hLS : L ≤ S) (hinv : ν⁻¹ ≤ S) :
    4 * L / ν ^ 2 ≤ 10 ^ 10 * S ^ 24 := by
  have hS0 : 0 ≤ S := by linarith
  simp only [div_eq_mul_inv, ← inv_pow]
  calc
    _ ≤ 4 * S * S ^ 2 := by gcongr
    _ = 4 * S ^ 3 := by ring
    _ ≤ _ := by
      have h3 : S ^ 3 ≤ S ^ 24 := pow_le_pow_right₀ hS (by norm_num)
      nlinarith [pow_nonneg hS0 24]

lemma curvature_step_bound {S Lf Lc LJ ν : ℝ} (hS : 1 ≤ S)
    (hc : 0 ≤ Lc) (hJ : 0 ≤ LJ)
    (hfS : Lf ≤ S) (hcS : Lc ≤ S) (hJS : LJ ≤ S) (hinv : ν⁻¹ ≤ S) :
    (Lf + ((4000 * S ^ 6) / ν) * LJ + (8001 * S ^ 11) * Lc +
      (10 ^ 10 * S ^ 24) * ((1 / (10 * S ^ 7)) * LJ + Lc ^ 2 / 2)) *
        (1 / (10 ^ 12 * S ^ 26)) ≤ 1 / 16 := by
  have hSpos : 0 < S := by linarith
  have hB : (4000 * S ^ 6) / ν ≤ 4000 * S ^ 7 := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ 4000 * S ^ 6 * S := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = _ := by ring
  have hD : Lf + ((4000 * S ^ 6) / ν) * LJ + (8001 * S ^ 11) * Lc +
      (10 ^ 10 * S ^ 24) * ((1 / (10 * S ^ 7)) * LJ + Lc ^ 2 / 2) ≤ 6000012002 * S ^ 26 := by
    calc
      _ ≤ S + (4000 * S ^ 7) * S + (8001 * S ^ 11) * S +
          (10 ^ 10 * S ^ 24) * ((1 / (10 * S ^ 7)) * S + S ^ 2 / 2) := by gcongr
      _ = S + 4000 * S ^ 8 + 8001 * S ^ 12 + 10 ^ 9 * S ^ 18 + 5 * 10 ^ 9 * S ^ 26 := by
        field_simp
        ring
      _ ≤ _ := by
        have h1 : S ≤ S ^ 26 := by simpa using pow_le_pow_right₀ hS (show 1 ≤ 26 by omega)
        have h8 : S ^ 8 ≤ S ^ 26 := pow_le_pow_right₀ hS (by norm_num)
        have h12 : S ^ 12 ≤ S ^ 26 := pow_le_pow_right₀ hS (by norm_num)
        have h18 : S ^ 18 ≤ S ^ 26 := pow_le_pow_right₀ hS (by norm_num)
        norm_num
        linarith
  apply (mul_le_mul_of_nonneg_right hD (by positivity : 0 ≤ 1 / (10 ^ 12 * S ^ 26))).trans
  rw [mul_one_div]
  apply (div_le_iff₀ (by positivity : 0 < 10 ^ 12 * S ^ 26)).mpr
  nlinarith [pow_nonneg hSpos.le 26]

lemma positiveCeil_le_twice {x : ℝ} (hx : 1 ≤ x) : (positiveCeil x : ℝ) ≤ 2 * x := by
  have h := positiveCeil_upper (show 0 ≤ x by linarith)
  linarith

lemma increment_ratio_bound {S q b : ℝ} (hS : 0 < S) (hb : 0 < b)
    (hbatch : 100 * q / S ^ 4 ≤ b) : q / b ≤ S ^ 4 / 100 := by
  have h := (div_le_iff₀ (pow_pos hS 4)).mp hbatch
  apply (div_le_iff₀ hb).mpr
  nlinarith only [h]

lemma noise_ratio_bound {S ε σ B : ℝ} (hS : 0 < S) (hε : 0 < ε) (hB : 0 < B)
    (hbatch : 10 ^ 32 * S ^ 48 * σ ^ 2 / ε ^ 2 ≤ B) :
    σ ^ 2 / B ≤ ε ^ 2 / (10 ^ 32 * S ^ 48) := by
  have h := (div_le_iff₀ (sq_pos_of_pos hε)).mp hbatch
  apply (div_le_div_iff₀ hB (by positivity : 0 < 10 ^ 32 * S ^ 48)).mpr
  nlinarith only [h]

lemma feedback_coefficient_bound {S ρ : ℝ} (hS : 1 ≤ S) (hρ : ρ ≤ S ^ 6 / 100) :
    ρ * (4 * (10 ^ 10 * S ^ 24 + 3) + 2) * (1 / (10 ^ 12 * S ^ 26)) ^ 2 *
      (10 ^ 6 * S ^ 11) ^ 2 ≤ 1 / 2 := by
  have hSpos : 0 < S := by linarith
  have hm := mul_le_mul_of_nonneg_right hρ
    (show 0 ≤ (4 * (10 ^ 10 * S ^ 24 + 3) + 2) *
      (1 / (10 ^ 12 * S ^ 26)) ^ 2 * (10 ^ 6 * S ^ 11) ^ 2 by positivity)
  calc
    _ ≤ (S ^ 6 / 100) * ((4 * (10 ^ 10 * S ^ 24 + 3) + 2) *
        (1 / (10 ^ 12 * S ^ 26)) ^ 2 * (10 ^ 6 * S ^ 11) ^ 2) := by
      convert hm using 1
      ring
    _ = (4 * 10 ^ 10 * S ^ 24 + 14) / (10 ^ 14 * S ^ 24) := by
      field_simp
      ring
    _ ≤ _ := by
      apply (div_le_iff₀ (by positivity : 0 < 10 ^ 14 * S ^ 24)).mpr
      have hpow : 1 ≤ S ^ 24 := one_le_pow₀ hS
      nlinarith

lemma tuning_increment_ratio (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    (cfg.epoch : ℝ) * p.Lnoise ^ 2 / (cfg.incrementBatch : ℝ) ≤ S ^ 6 / 100 := by
  let S := scale p.toPublic
  let cfg := tuning p.toPublic
  obtain ⟨hS, _, _, _, _, _, _, _, hnS⟩ := scale_bounds p hp
  have hn := hp.2.2.2.2.2.2.2.2.1
  have hSpos : 0 < S := by dsimp [S]; linarith
  have hratio : (cfg.epoch : ℝ) * p.Lnoise ^ 2 / (cfg.incrementBatch : ℝ) ≤ S ^ 6 / 100 := by
    have hb : 0 < (cfg.incrementBatch : ℝ) := by exact_mod_cast cfg.incrementBatch.pos
    have hbatch : 100 * (cfg.epoch : ℝ) / S ^ 4 ≤ (cfg.incrementBatch : ℝ) := by
      exact positiveCeil_lower _
    have hr := increment_ratio_bound hSpos hb hbatch
    calc
      _ = ((cfg.epoch : ℝ) / (cfg.incrementBatch : ℝ)) * p.Lnoise ^ 2 := by ring
      _ ≤ (S ^ 4 / 100) * S ^ 2 := mul_le_mul hr (pow_le_pow_left₀ hn hnS 2)
        (sq_nonneg _) (by positivity)
      _ = _ := by ring
  exact hratio

lemma tuning_geometry (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    let κ := 8001 * S ^ 11
    let β := 10 ^ 10 * S ^ 24
    let K := 10 ^ 6 * S ^ 11
    0 < cfg.step ∧ 0 ≤ cfg.gradientCap ∧ 0 ≤ cfg.constraintCap ∧
    (p.Lc * p.Lf + p.Lc * p.LJ * cfg.gradientCap / p.ν + p.LJ * cfg.gradientCap) / p.ν ^ 2 ≤ κ ∧
    (1 + 4 * p.Lc ^ 2 / p.ν ^ 2) +
      ((1 + 4 * p.Lc ^ 2 / p.ν ^ 2) * cfg.gradientCap / p.ν +
        4 * p.Lc * cfg.gradientCap / p.ν ^ 2 + 4 * cfg.gradientCap / p.ν) + p.Lc + cfg.constraintCap ≤ K ∧
    8 * ((κ / p.ν) ^ 2 + κ / p.ν + 1) ≤ β ∧ 2 ≤ β ∧
    (p.Lf + (cfg.gradientCap / p.ν) * p.LJ + κ * p.Lc +
      β * (cfg.constraintCap * p.LJ + p.Lc ^ 2 / 2)) * cfg.step ≤ 1 / 16 ∧
    4 * (1 + p.Lf) / p.ν ^ 2 ≤ β ∧
    ((cfg.epoch : ℝ) * p.Lnoise ^ 2 / (cfg.incrementBatch : ℝ)) *
      (4 * (β + 3) + 2) * cfg.step ^ 2 * K ^ 2 ≤ 1 / 2 := by
  let S := scale p.toPublic
  let cfg := tuning p.toPublic
  have hratio := tuning_increment_ratio p hp
  obtain ⟨hS, hfS, hcS, _, hJS, _, hinvS, _, hnS⟩ := scale_bounds p hp
  rcases hp with ⟨_, _, _, hν, hf, hc, hJ, _, hn, _, _, _, _⟩
  have hS1 : 1 ≤ S := by dsimp [S]; linarith
  have hSpos : 0 < S := by linarith
  have hfS' : p.Lf ≤ S := by dsimp [S]; linarith
  have hcS' : p.Lc ≤ S := by dsimp [S]; linarith
  have hinv : p.ν⁻¹ ≤ S := by simpa only [one_div] using hinvS
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change 0 < 1 / (10 ^ 12 * S ^ 26)
    positivity
  · change 0 ≤ 4000 * S ^ 6
    positivity
  · change 0 ≤ 1 / (10 * S ^ 7)
    positivity
  · exact multiplier_coefficient_bound hS1 hν hf hJ hfS' hcS' hJS hinv
  · exact direction_coefficient_bound hS1 hν hc hcS' hinv
  · exact penalty_bound hS1 hν hinv
  · change 2 ≤ 10 ^ 10 * S ^ 24
    have hpow : 1 ≤ S ^ 24 := one_le_pow₀ hS1
    nlinarith
  · exact curvature_step_bound hS1 hc hJ hfS' hcS' hJS hinv
  · exact coercivity_penalty_bound hS1 hν (show 1 + p.Lf ≤ S by dsimp [S]; linarith) hinv
  · exact feedback_coefficient_bound hS1 hratio

lemma tuning_variance_parameters (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    10 ^ 24 * S ^ 38 / p.ε ^ 2 ≤ (cfg.steps : ℝ) ∧
    (cfg.steps : ℝ) ≤ 2 * (10 ^ 24 * S ^ 38 / p.ε ^ 2) ∧
    p.σ ^ 2 / (cfg.resetBatch : ℝ) ≤ p.ε ^ 2 / (10 ^ 32 * S ^ 48) := by
  let S := scale p.toPublic
  let cfg := tuning p.toPublic
  have hS : 1 ≤ S := by have h := (scale_bounds p hp).1; dsimp [S]; linarith
  have hSpos : 0 < S := by linarith
  rcases hp with ⟨_, _, _, _, _, _, _, _, _, _, _, hε, hε1⟩
  have hε2 : p.ε ^ 2 ≤ 1 := by nlinarith
  have hnom : 1 ≤ 10 ^ 24 * S ^ 38 / p.ε ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    have hpow : 1 ≤ S ^ 38 := one_le_pow₀ hS
    nlinarith
  refine ⟨?_, ?_, ?_⟩
  · exact positiveCeil_lower _
  · exact positiveCeil_le_twice hnom
  · have hB : 0 < (cfg.resetBatch : ℝ) := by exact_mod_cast cfg.resetBatch.pos
    exact noise_ratio_bound hSpos hε hB (positiveCeil_lower _)

lemma error_energy_margin {S ε T v ρ E : ℝ} (hS : 1 ≤ S) (hε : 0 < ε)
    (hT0 : 0 ≤ T) (hT : T ≤ 2 * (10 ^ 24 * S ^ 38 / ε ^ 2))
    (hv : v ≤ ε ^ 2 / (10 ^ 32 * S ^ 48)) (hρ : ρ ≤ S ^ 6 / 100)
    (hE : E ≤ 2 * T * v + 8 * ρ * (1 / (10 ^ 12 * S ^ 26)) * (10 ^ 6 * S ^ 10)) :
    (1 / (10 ^ 12 * S ^ 26)) * (2 * 10 ^ 10 * S ^ 24) *
      (10 ^ 6 * S ^ 11) ^ 2 * E ≤ (10 ^ 6 * S ^ 10) / 100 := by
  have hSpos : 0 < S := by linarith
  have he : E ≤ 2 * (2 * (10 ^ 24 * S ^ 38 / ε ^ 2)) *
      (ε ^ 2 / (10 ^ 32 * S ^ 48)) +
      8 * (S ^ 6 / 100) * (1 / (10 ^ 12 * S ^ 26)) * (10 ^ 6 * S ^ 10) := by
    apply hE.trans
    apply add_le_add
    · exact (mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2 * T)).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (by norm_num)) (by positivity))
    · gcongr
  have hm := mul_le_mul_of_nonneg_left he
    (show 0 ≤ (1 / (10 ^ 12 * S ^ 26)) * (2 * 10 ^ 10 * S ^ 24) *
      (10 ^ 6 * S ^ 11) ^ 2 by positivity)
  apply hm.trans
  have hid : (1 / (10 ^ 12 * S ^ 26)) * (2 * 10 ^ 10 * S ^ 24) *
      (10 ^ 6 * S ^ 11) ^ 2 *
      (2 * (2 * (10 ^ 24 * S ^ 38 / ε ^ 2)) * (ε ^ 2 / (10 ^ 32 * S ^ 48)) +
      8 * (S ^ 6 / 100) * (1 / (10 ^ 12 * S ^ 26)) * (10 ^ 6 * S ^ 10)) =
      (3 / 1250) * (10 ^ 6 * S ^ 10) := by
    field_simp
    ring
  rw [hid]
  nlinarith [pow_nonneg hSpos.le 10]

lemma residual_energy_accuracy {S ε T E R : ℝ} (hS : 1 ≤ S) (hε : 0 < ε)
    (hTpos : 0 < T) (hT : 10 ^ 24 * S ^ 38 / ε ^ 2 ≤ T) (hE : 0 ≤ E)
    (hmargin : (1 / (10 ^ 12 * S ^ 26)) * (2 * 10 ^ 10 * S ^ 24) *
      (10 ^ 6 * S ^ 11) ^ 2 * E ≤ (10 ^ 6 * S ^ 10) / 100)
    (hR : R ≤ 2 * (10 ^ 6 * S ^ 10) / (1 / (10 ^ 12 * S ^ 26)) +
      2 * (10 ^ 10 * S ^ 24 + 3) * (10 ^ 6 * S ^ 11) ^ 2 * E) :
    R / T ≤ (ε / (32 * S)) ^ 2 / 100 := by
  have hSpos : 0 < S := by linarith
  have hη : 0 < 1 / (10 ^ 12 * S ^ 26) := by positivity
  have hβ : 3 ≤ 10 ^ 10 * S ^ 24 := by
    have hh := one_le_pow₀ hS (n := 24)
    nlinarith
  have hR' : (1 / (10 ^ 12 * S ^ 26)) * R ≤ 3 * (10 ^ 6 * S ^ 10) := by
    have hm := mul_le_mul_of_nonneg_left hR hη.le
    have hc : (1 / (10 ^ 12 * S ^ 26)) *
        (2 * (10 ^ 10 * S ^ 24 + 3) * (10 ^ 6 * S ^ 11) ^ 2 * E) ≤
        2 * ((1 / (10 ^ 12 * S ^ 26)) * (2 * 10 ^ 10 * S ^ 24) *
          (10 ^ 6 * S ^ 11) ^ 2 * E) := by
      have hmul := mul_le_mul_of_nonneg_right
        (show 10 ^ 10 * S ^ 24 + 3 ≤ 2 * 10 ^ 10 * S ^ 24 by linarith)
        (show 0 ≤ 2 * (1 / (10 ^ 12 * S ^ 26)) * (10 ^ 6 * S ^ 11) ^ 2 * E by positivity)
      convert hmul using 1 <;> ring
    have hid : (1 / (10 ^ 12 * S ^ 26)) *
        (2 * (10 ^ 6 * S ^ 10) / (1 / (10 ^ 12 * S ^ 26))) = 2 * (10 ^ 6 * S ^ 10) := by
      field_simp
    rw [mul_add, hid] at hm
    nlinarith [pow_nonneg hSpos.le 10]
  have htarget : 3 * (10 ^ 6 * S ^ 10) ≤
      (1 / (10 ^ 12 * S ^ 26)) * T * ((ε / (32 * S)) ^ 2 / 100) := by
    have hm := mul_le_mul_of_nonneg_right hT
      (show 0 ≤ (1 / (10 ^ 12 * S ^ 26)) * ((ε / (32 * S)) ^ 2 / 100) by positivity)
    have hid : (10 ^ 24 * S ^ 38 / ε ^ 2) *
        ((1 / (10 ^ 12 * S ^ 26)) * ((ε / (32 * S)) ^ 2 / 100)) =
        (10 ^ 12 / 102400) * S ^ 10 := by
      field_simp
      ring
    rw [hid] at hm
    nlinarith [pow_nonneg hSpos.le 10]
  apply (div_le_iff₀ hTpos).mpr
  apply (mul_le_mul_iff_right₀ hη).mp
  nlinarith only [hR'.trans htarget]

lemma tuning_energy_accuracy (p : Params) (hp : spec.valid p) (E R : ℝ)
    (hE0 : 0 ≤ E)
    (hE : E ≤ 2 * (tuning p.toPublic).steps * (p.σ ^ 2 / (tuning p.toPublic).resetBatch) +
      8 * ((tuning p.toPublic).epoch * p.Lnoise ^ 2 / (tuning p.toPublic).incrementBatch) *
      (tuning p.toPublic).step * (10 ^ 6 * (scale p.toPublic) ^ 10))
    (hR : R ≤ 2 * (10 ^ 6 * (scale p.toPublic) ^ 10) / (tuning p.toPublic).step +
      2 * (10 ^ 10 * (scale p.toPublic) ^ 24 + 3) * (10 ^ 6 * (scale p.toPublic) ^ 11) ^ 2 * E) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    cfg.step * (2 * 10 ^ 10 * S ^ 24) * (10 ^ 6 * S ^ 11) ^ 2 * E ≤
      (10 ^ 6 * S ^ 10) / 100 ∧ R / cfg.steps ≤ (p.ε / (32 * S)) ^ 2 / 100 := by
  have hS : 1 ≤ scale p.toPublic := by have h := (scale_bounds p hp).1; linarith
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨hTlo, hThi, hv⟩ := tuning_variance_parameters p hp
  have hρ := tuning_increment_ratio p hp
  have hTpos : 0 < ((tuning p.toPublic).steps : ℝ) := by
    exact_mod_cast (tuning p.toPublic).steps.pos
  have hm := error_energy_margin hS hε hTpos.le hThi hv hρ hE
  exact ⟨hm, residual_energy_accuracy hS hε hTpos hTlo hE0 hm hR⟩

lemma robust_batch_precision {t σ B : ℝ} (ht : 0 < t) (hB : 0 < B)
    (hsize : 144 * σ ^ 2 / t ^ 2 ≤ B) : σ ^ 2 / B ≤ t ^ 2 / 144 := by
  have hh := (div_le_iff₀ (sq_pos_of_pos ht)).mp hsize
  apply (div_le_div_iff₀ hB (by norm_num : (0 : ℝ) < 144)).mpr
  nlinarith only [hh]

lemma tuning_robust_precision (p : Params) (hp : spec.valid p) :
    let cfg := tuning p.toPublic
    p.σ ^ 2 / (cfg.restoreBatch : ℝ) ≤ cfg.restoreTolerance ^ 2 / 144 ∧
    p.σ ^ 2 / (cfg.validationBatch : ℝ) ≤ cfg.validationTolerance ^ 2 / 144 := by
  let S := scale p.toPublic
  have hSpos : 0 < S := by have hh := (scale_bounds p hp).1; dsimp [S]; linarith only [hh]
  have hε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  constructor
  · apply robust_batch_precision (by change 0 < 1 / (10 ^ 8 * S ^ 9); positivity)
      (by exact_mod_cast (tuning p.toPublic).restoreBatch.pos)
    apply le_trans ?_ (positiveCeil_lower _)
    change 144 * p.σ ^ 2 / (1 / (10 ^ 8 * S ^ 9)) ^ 2 ≤ 10 ^ 19 * S ^ 18 * p.σ ^ 2
    have hid : 144 * p.σ ^ 2 / (1 / (10 ^ 8 * S ^ 9)) ^ 2 =
        (144 * 10 ^ 16) * S ^ 18 * p.σ ^ 2 := by field_simp
    rw [hid]
    nlinarith [mul_nonneg (pow_nonneg hSpos.le 18) (sq_nonneg p.σ)]
  · apply robust_batch_precision (by change 0 < p.ε / (10 ^ 6 * S ^ 7); positivity)
      (by exact_mod_cast (tuning p.toPublic).validationBatch.pos)
    apply le_trans ?_ (positiveCeil_lower _)
    change 144 * p.σ ^ 2 / (p.ε / (10 ^ 6 * S ^ 7)) ^ 2 ≤
      10 ^ 15 * S ^ 14 * p.σ ^ 2 / p.ε ^ 2
    have hid : 144 * p.σ ^ 2 / (p.ε / (10 ^ 6 * S ^ 7)) ^ 2 =
        (144 * 10 ^ 12) * S ^ 14 * p.σ ^ 2 / p.ε ^ 2 := by field_simp
    rw [hid]
    apply div_le_div_of_nonneg_right ?_ (sq_nonneg _)
    nlinarith [mul_nonneg (pow_nonneg hSpos.le 14) (sq_nonneg p.σ)]

lemma restoration_log_bound {S C : ℝ} (hS : 1 ≤ S) (hC : 0 ≤ C) (hCS : C ≤ S) :
    Real.log (16 * (1 + C ^ 2) / (1 / (10 ^ 6 * S ^ 7)) ^ 2) ≤
      64 * (1 + Real.log S) := by
  have hSpos : 0 < S := by linarith
  have harg : 16 * (1 + C ^ 2) / (1 / (10 ^ 6 * S ^ 7)) ^ 2 ≤ (2 : ℝ) ^ 45 * S ^ 16 := by
    have hid : 16 * (1 + C ^ 2) / (1 / (10 ^ 6 * S ^ 7)) ^ 2 =
        16 * 10 ^ 12 * (1 + C ^ 2) * S ^ 14 := by field_simp
    rw [hid]
    have hc2 := pow_le_pow_left₀ hC hCS 2
    have hs2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
    have hm := mul_le_mul_of_nonneg_right (show 1 + C ^ 2 ≤ 2 * S ^ 2 by linarith)
      (show 0 ≤ 16 * 10 ^ 12 * S ^ 14 by positivity)
    have hh : S ^ 2 * S ^ 14 = S ^ 16 := by ring
    nlinarith [pow_nonneg hSpos.le 16]
  have hh := Real.log_le_log (by positivity : 0 < 16 * (1 + C ^ 2) / (1 / (10 ^ 6 * S ^ 7)) ^ 2) harg
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hh
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog := Real.log_nonneg hS
  norm_num only [Nat.cast_ofNat] at hh
  linarith

lemma tuning_restoration_steps (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    Real.log (16 * (1 + p.C0 ^ 2) / (1 / (10 ^ 6 * S ^ 7)) ^ 2) ≤
      (cfg.restoreStep * p.ν ^ 2) * (cfg.restoreSteps : ℝ) := by
  let S := scale p.toPublic
  obtain ⟨hS, _, _, hCS, _, _, hinv, _, _⟩ := scale_bounds p hp
  rcases hp with ⟨_, _, _, hν, _, _, _, _, _, _, hC, _, _⟩
  have hS1 : 1 ≤ S := by dsimp [S]; linarith only [hS]
  have hSpos : 0 < S := by linarith only [hS1]
  have hell : 0 ≤ 1 + Real.log S := by linarith [Real.log_nonneg hS1]
  have hN : 4096 * S ^ 4 * (1 + Real.log S) ≤ ((tuning p.toPublic).restoreSteps : ℝ) :=
    positiveCeil_lower _
  have hνS : 1 ≤ S * p.ν := (div_le_iff₀ hν).mp hinv
  have hsquare : 1 ≤ (S * p.ν) ^ 2 := one_le_pow₀ hνS
  have hm := mul_le_mul_of_nonneg_left hN
    (show 0 ≤ (1 / (64 * S ^ 2)) * p.ν ^ 2 by positivity)
  have hid : (1 / (64 * S ^ 2)) * p.ν ^ 2 *
      (4096 * S ^ 4 * (1 + Real.log S)) = 64 * (S * p.ν) ^ 2 * (1 + Real.log S) := by
    field_simp
    ring
  rw [hid] at hm
  have hlower : 64 * (1 + Real.log S) ≤
      (1 / (64 * S ^ 2)) * p.ν ^ 2 * ((tuning p.toPublic).restoreSteps : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hsquare (show 0 ≤ 64 * (1 + Real.log S) by positivity)
    nlinarith only [hm, hh]
  exact (restoration_log_bound hS1 hC (by dsimp [S]; linarith only [hCS])).trans hlower

lemma tuning_restoration_geometry (p : Params) (hp : spec.valid p) :
    let S := scale p.toPublic
    let cfg := tuning p.toPublic
    0 < cfg.restoreStep ∧ cfg.restoreStep * p.ν ^ 2 ≤ 1 ∧
    (cfg.restoreCap * p.LJ + p.Lc ^ 2 / 2) * cfg.restoreStep ≤ 1 / 16 ∧
    (p.Lc + cfg.restoreCap) * cfg.restoreTolerance ≤ p.ν * (1 / (10 ^ 6 * S ^ 7)) / 8 := by
  let S := scale p.toPublic
  obtain ⟨hS, _, hcS, hCS, hJS, hνS, hinv, _, _⟩ := scale_bounds p hp
  rcases hp with ⟨_, _, _, hν, _, hc, hJ, _, _, _, hC, _, _⟩
  have hSpos : 0 < S := by dsimp [S]; linarith only [hS]
  have hνS' : p.ν ≤ S := hνS
  have hcS' : p.Lc ≤ S := by dsimp [S]; linarith only [hcS]
  have hCS' : p.C0 + 1 ≤ S := by dsimp [S]; linarith only [hCS]
  have hpν : 1 ≤ S * p.ν := (div_le_iff₀ hν).mp hinv
  refine ⟨?_, ?_, ?_, ?_⟩
  · change 0 < 1 / (64 * S ^ 2)
    positivity
  · change (1 / (64 * S ^ 2)) * p.ν ^ 2 ≤ 1
    have hs := pow_le_pow_left₀ hν.le hνS' 2
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity : 0 < 64 * S ^ 2)).mpr
    nlinarith [sq_nonneg S]
  · change ((p.C0 + 1) * p.LJ + p.Lc ^ 2 / 2) * (1 / (64 * S ^ 2)) ≤ 1 / 16
    have hc2 := pow_le_pow_left₀ hc hcS' 2
    have hprod := mul_le_mul hCS' hJS hJ (by positivity : 0 ≤ S)
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 64 * S ^ 2)).mpr
    nlinarith [sq_nonneg S]
  · change (p.Lc + (p.C0 + 1)) * (1 / (10 ^ 8 * S ^ 9)) ≤
      p.ν * (1 / (10 ^ 6 * S ^ 7)) / 8
    have hbound : p.Lc + (p.C0 + 1) ≤ 2 * S := by linarith only [hcS', hCS']
    have hm := mul_le_mul_of_nonneg_right hpν (show 0 ≤ S ^ 8 by positivity)
    have hr : S * p.ν * S ^ 8 = p.ν * S ^ 9 := by ring
    rw [hr, one_mul] at hm
    rw [mul_one_div, mul_one_div, div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < 10 ^ 8 * S ^ 9)
      (by positivity : 0 < 10 ^ 6 * S ^ 7 * 8)).mpr
    have hs := mul_le_mul_of_nonneg_right hbound (show 0 ≤ 10 ^ 6 * S ^ 7 * 8 by positivity)
    nlinarith only [hm, hs, pow_nonneg hSpos.le 8]

lemma restoration_group_failure {S : ℝ} (hS : 1 ≤ S) (k : ℕ)
    (hk : 100 * (1 + Real.log S) ≤ (k : ℝ)) :
    (1 / 2 : ℝ) ^ k ≤ 1 / (10 ^ 8 * S ^ 5) := by
  have hSpos : 0 < S := by linarith only [hS]
  have hlog : 0 ≤ Real.log S := Real.log_nonneg hS
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  have htwo : 1 / 2 ≤ Real.log 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [hhalf] at hh
    linarith only [hh]
  have hklog := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hexp : (k : ℝ) * Real.log (1 / 2 : ℝ) ≤ -(30 + 5 * Real.log S) := by
    rw [hhalf]
    nlinarith only [hk, hklog, hlog]
  have h30 : (10 ^ 8 : ℝ) ≤ Real.exp 30 := by
    calc
      _ ≤ (2 : ℝ) ^ 30 := by norm_num
      _ ≤ (Real.exp 1) ^ 30 := pow_le_pow_left₀ (by norm_num)
        (by linarith only [Real.add_one_le_exp (1 : ℝ)]) 30
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  calc
    _ = Real.exp ((k : ℝ) * Real.log (1 / 2 : ℝ)) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (-(30 + 5 * Real.log S)) := Real.exp_le_exp.mpr hexp
    _ = 1 / (Real.exp 30 * S ^ 5) := by
      rw [Real.exp_neg, Real.exp_add, show (5 : ℝ) = (5 : ℕ) by norm_num,
        Real.exp_nat_mul, Real.exp_log hSpos]
      simp only [one_div]
    _ ≤ _ := one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_right h30 (pow_nonneg hSpos.le 5))

lemma tuning_restoration_failure (p : Params) (hp : spec.valid p) :
    let cfg := tuning p.toPublic
    2 * (cfg.restoreSteps : ℝ) * (1 / 2 : ℝ) ^ (cfg.restoreGroups : ℕ) ≤ 1 / 100 := by
  let S := scale p.toPublic
  let cfg := tuning p.toPublic
  have hS : 1 ≤ S := by have hh := (scale_bounds p hp).1; dsimp [S]; linarith only [hh]
  have hSpos : 0 < S := by linarith only [hS]
  have hell : 1 ≤ 1 + Real.log S := by linarith [Real.log_nonneg hS]
  have hnom : 1 ≤ 4096 * S ^ 4 * (1 + Real.log S) := by
    have hh : 1 ≤ S ^ 4 := one_le_pow₀ hS
    nlinarith only [hh, hell]
  have hN : (cfg.restoreSteps : ℝ) ≤ 8192 * S ^ 5 := by
    have hh := positiveCeil_le_twice hnom
    have hl : 1 + Real.log S ≤ S := by
      linarith only [Real.log_le_sub_one_of_pos hSpos]
    have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 8192 * S ^ 4 by positivity)
    change (cfg.restoreSteps : ℝ) ≤ 2 * (4096 * S ^ 4 * (1 + Real.log S)) at hh
    nlinarith only [hh, hm]
  have hk : 100 * (1 + Real.log S) ≤ (cfg.restoreGroups : ℝ) := positiveCeil_lower _
  have hδ := restoration_group_failure hS cfg.restoreGroups hk
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hN (by norm_num : (0 : ℝ) ≤ 2)) hδ
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) _) (by positivity : 0 ≤ 2 * (8192 * S ^ 5))
  apply hh.trans
  have he : 2 * (8192 * S ^ 5) * (1 / (10 ^ 8 * S ^ 5)) = 16384 / 10 ^ 8 := by field_simp; norm_num
  rw [he]
  norm_num

lemma half_pow_le_exp {a : ℝ} {k : ℕ} (hk : 2 * a ≤ (k : ℝ)) :
    (1 / 2 : ℝ) ^ k ≤ Real.exp (-a) := by
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  have htwo : 1 / 2 ≤ Real.log 2 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    rw [hhalf] at hh
    linarith only [hh]
  have hklog := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  calc
    _ = Real.exp ((k : ℝ) * Real.log (1 / 2 : ℝ)) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (-a) := by
      apply Real.exp_le_exp.mpr
      rw [hhalf]
      nlinarith only [hk, hklog]

lemma validation_union_exp {ell : ℝ} (hell : 1 ≤ ell) (R k : ℕ)
    (hR : (R : ℝ) ≤ 201 * ell) (hk : 300 * ell ≤ (k : ℝ)) :
    3 * (R : ℝ) * (1 / 2 : ℝ) ^ k ≤ Real.exp (-(100 * ell)) := by
  have ht := half_pow_le_exp (a := 150 * ell) (by linarith only [hk])
  have hell0 : 0 ≤ ell := by linarith only [hell]
  have hc : (603 : ℝ) ≤ Real.exp 49 := by
    calc
      _ ≤ (2 : ℝ) ^ 49 := by norm_num
      _ ≤ (Real.exp 1) ^ 49 := pow_le_pow_left₀ (by norm_num)
        (by linarith only [Real.add_one_le_exp (1 : ℝ)]) 49
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have he : 603 * ell ≤ Real.exp (50 * ell) := by
    calc
      _ ≤ Real.exp 49 * Real.exp ell := mul_le_mul hc
        (by linarith only [Real.add_one_le_exp ell]) hell0 (Real.exp_pos 49).le
      _ = Real.exp (49 + ell) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (50 * ell) := Real.exp_le_exp.mpr (by linarith only [hell])
  calc
    _ ≤ (603 * ell) * Real.exp (-(150 * ell)) :=
      mul_le_mul (by linarith only [hR]) ht (by positivity) (by positivity)
    _ ≤ Real.exp (50 * ell) * Real.exp (-(150 * ell)) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma amplification_exp_small {S ε : ℝ} (hS : 2 ≤ S) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Real.exp (-(100 * (1 + Real.log (S / ε)))) ≤ ε ^ 6 / (10 ^ 35 * S ^ 38) := by
  have hS0 : 0 < S := by linarith only [hS]
  have hS1 : 1 ≤ S := by linarith only [hS]
  have hpowS : (2 : ℝ) ^ 62 ≤ S ^ 62 := pow_le_pow_left₀ (by norm_num) hS _
  have h100 : (2 : ℝ) ^ 100 ≤ Real.exp 100 := by
    calc
      _ ≤ (Real.exp 1) ^ 100 := pow_le_pow_left₀ (by norm_num)
        (by linarith only [Real.add_one_le_exp (1 : ℝ)]) 100
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hden : (10 ^ 35 : ℝ) ≤ Real.exp 100 * S ^ 62 := by
    calc
      _ ≤ (2 : ℝ) ^ 100 * 2 ^ 62 := by norm_num
      _ ≤ _ := mul_le_mul h100 hpowS (by positivity) (Real.exp_pos _).le
  have heps : ε ^ 94 ≤ 1 := pow_le_one₀ hε.le hε1
  have heq : Real.exp (-(100 * (1 + Real.log (S / ε)))) =
      ε ^ 100 / (Real.exp 100 * S ^ 100) := by
    rw [mul_add, mul_one, Real.exp_neg, Real.exp_add,
      show (100 : ℝ) = (100 : ℕ) by norm_num, Real.exp_nat_mul,
      Real.exp_log (div_pos hS0 hε), div_pow]
    field_simp
  rw [heq]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hh := mul_le_mul heps hden (by positivity : (0 : ℝ) ≤ 10 ^ 35) (by norm_num : (0 : ℝ) ≤ 1)
  have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ ε ^ 6 * S ^ 38 by positivity)
  nlinarith only [hm]

lemma tuning_amplification_failure (p : Params) (hp : spec.valid p) :
    (1 / 2 : ℝ) ^ ((tuning p.toPublic).trials : ℕ) ≤
        p.ε ^ 6 / (10 ^ 35 * scale p.toPublic ^ 38) ∧
      3 * ((tuning p.toPublic).trials : ℝ) *
        (1 / 2 : ℝ) ^ ((tuning p.toPublic).validationGroups : ℕ) ≤
        p.ε ^ 6 / (10 ^ 35 * scale p.toPublic ^ 38) := by
  let S := scale p.toPublic
  let ell := 1 + Real.log (S / p.ε)
  have hS : 2 ≤ S := (scale_bounds p hp).1
  have hε : 0 < p.ε := hp.2.2.2.2.2.2.2.2.2.2.2.1
  have hε1 : p.ε ≤ 1 := hp.2.2.2.2.2.2.2.2.2.2.2.2
  have hell : 1 ≤ ell := by
    have hh : 1 ≤ S / p.ε := (le_div_iff₀ hε).mpr (by linarith only [hS, hε1])
    dsimp [ell]
    linarith only [Real.log_nonneg hh]
  have hR : 200 * ell ≤ ((tuning p.toPublic).trials : ℝ) := positiveCeil_lower _
  have hRu : ((tuning p.toPublic).trials : ℝ) ≤ 201 * ell := by
    have hh := positiveCeil_upper (show 0 ≤ 200 * ell by linarith only [hell])
    change ((tuning p.toPublic).trials : ℝ) ≤ 200 * ell + 1 at hh
    linarith only [hh, hell]
  have hk : 300 * ell ≤ ((tuning p.toPublic).validationGroups : ℝ) := positiveCeil_lower _
  have he := amplification_exp_small hS hε hε1
  constructor
  · exact (half_pow_le_exp (a := 100 * ell) (by linarith only [hR])).trans he
  · exact (validation_union_exp hell _ _ hRu hk).trans he

lemma residual_envelope {S ε a b : ℝ} (hS : 1 ≤ S) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : a ≤ 2 * S + S * (10 ^ 16 * S ^ 18 / ε ^ 2) + 8000 * S ^ 8)
    (hb : b ≤ S + S * (10 ^ 16 * S ^ 18 / ε ^ 2)) :
    a ^ 2 + b ^ 2 ≤ 10 ^ 33 * S ^ 38 / ε ^ 4 := by
  have hS0 : 0 < S := by linarith only [hS]
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith only [hε, hε1]
  have h18 : 0 ≤ S ^ 18 := pow_nonneg hS0.le _
  have h8 : S ≤ S ^ 8 := le_self_pow₀ hS (by norm_num)
  have h19 : S ^ 8 ≤ S ^ 19 := pow_le_pow_right₀ hS (by norm_num)
  have hsmall : 2 * S + 8000 * S ^ 8 ≤ 10 ^ 16 * S ^ 19 / ε ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
    have hh := mul_le_mul_of_nonneg_left hε2
      (show 0 ≤ 2 * S + 8000 * S ^ 8 by positivity)
    nlinarith only [hh, h8, h19, pow_nonneg hS0.le 19]
  have he : S * (10 ^ 16 * S ^ 18 / ε ^ 2) = 10 ^ 16 * S ^ 19 / ε ^ 2 := by ring
  have hB : 0 ≤ 2 * (10 ^ 16 * S ^ 19 / ε ^ 2) := by positivity
  have haB : a ≤ 2 * (10 ^ 16 * S ^ 19 / ε ^ 2) := by
    rw [he] at ha
    linarith only [ha, hsmall]
  have hbB : b ≤ 2 * (10 ^ 16 * S ^ 19 / ε ^ 2) := by
    rw [he] at hb
    nlinarith only [hb, hsmall, hS0, pow_nonneg hS0.le 8]
  have haa := (sq_le_sq₀ ha0 hB).mpr haB
  have hbb := (sq_le_sq₀ hb0 hB).mpr hbB
  have heq : (2 * (10 ^ 16 * S ^ 19 / ε ^ 2)) ^ 2 +
      (2 * (10 ^ 16 * S ^ 19 / ε ^ 2)) ^ 2 = 8 * 10 ^ 32 * S ^ 38 / ε ^ 4 := by ring
  exact ((add_le_add haa hbb).trans_eq heq).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hS0.le 38)) (by positivity))
end LongTails.Proofs.StochasticEqualityTuning
