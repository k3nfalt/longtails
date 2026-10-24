import LongTails.Proofs.ManySampleConvolutionalPerceptronConstants

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronParameters

open ManySampleConvolutionalPerceptronConstants

noncomputable def burnIn (ρ δ : ℝ) : ℕ := ⌈8 / ρ ^ 2 * Real.log (1 / δ)⌉₊ + 2

structure Tuning where
  ρ : ℝ
  δ : ℝ
  κ : ℝ
  rho_pos : 0 < ρ
  rho_le : ρ ≤ 1 / 2
  delta_pos : 0 < δ
  delta_le : δ ≤ Real.exp (-1)
  kappa_pos : 0 < κ
  kappa_le : κ ≤ 1
  small_cubic : δ * (burnIn ρ δ + 1 : ℝ) ^ 3 ≤ κ ^ 3 / 16777216
  small_quadratic : δ * (burnIn ρ δ + 1 : ℝ) ^ 2 ≤ κ ^ 2 * ρ ^ 4 / 16777216

namespace Tuning

noncomputable def unit (p : Tuning) : ℝ := (burnIn p.ρ p.δ + 1) / p.κ
noncomputable def height (p : Tuning) : ℝ := 256 * p.unit
noncomputable def negatives (p : Tuning) : ℕ := ⌈4096 * p.unit ^ 2⌉₊
noncomputable def nuisance (p : Tuning) : ℝ := 8 * p.δ * (p.height + 1) / p.ρ ^ 2

lemma unit_ge_one (p : Tuning) : 1 ≤ p.unit := by
  apply (le_div_iff₀ p.kappa_pos).mpr
  have hB : (0 : ℝ) ≤ burnIn p.ρ p.δ := Nat.cast_nonneg _
  linarith [p.kappa_le]

lemma unit_pos (p : Tuning) : 0 < p.unit := lt_of_lt_of_le zero_lt_one p.unit_ge_one

lemma normalized_cubic (p : Tuning) : p.δ * p.unit ^ 3 ≤ 1 / 16777216 := by
  dsimp only [unit]
  have hd := div_le_div_of_nonneg_right p.small_cubic (pow_nonneg p.kappa_pos.le 3)
  convert hd using 1 <;> field_simp [ne_of_gt p.kappa_pos]

lemma normalized_quadratic (p : Tuning) : p.δ * p.unit ^ 2 ≤ p.ρ ^ 4 / 16777216 := by
  dsimp only [unit]
  have hd := div_le_div_of_nonneg_right p.small_quadratic (sq_nonneg p.κ)
  convert hd using 1 <;> field_simp [ne_of_gt p.kappa_pos]

lemma negatives_upper (p : Tuning) : (p.negatives : ℝ) ≤ 4097 * p.unit ^ 2 := by
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 4096 * p.unit ^ 2 by positivity)
  have hu := p.unit_ge_one
  dsimp only [negatives]
  nlinarith

lemma negatives_lower (p : Tuning) : 4096 * p.unit ^ 2 ≤ p.negatives := Nat.le_ceil _

lemma burnIn_le_unit (p : Tuning) : (burnIn p.ρ p.δ : ℝ) ≤ p.unit := by
  have hk := p.kappa_le
  have hb : (0 : ℝ) ≤ burnIn p.ρ p.δ := Nat.cast_nonneg _
  dsimp only [unit]
  apply (le_div_iff₀ p.kappa_pos).mpr
  nlinarith

lemma kappa_unit (p : Tuning) : 1 ≤ p.κ * p.unit := by
  have he : p.κ * p.unit = (burnIn p.ρ p.δ : ℝ) + 1 := by
    dsimp only [unit]
    field_simp [ne_of_gt p.kappa_pos]
  rw [he]
  have hb : (0 : ℝ) ≤ burnIn p.ρ p.δ := Nat.cast_nonneg _
  linarith

lemma delta_small (p : Tuning) : p.δ ≤ 1 / 16777216 := by
  have hu := p.unit_ge_one
  have hmul := mul_le_mul_of_nonneg_left (show 1 ≤ p.unit ^ 2 by nlinarith) p.delta_pos.le
  have hr : p.ρ ^ 2 ≤ 1 := by nlinarith [p.rho_pos, p.rho_le]
  have hr4 : p.ρ ^ 4 ≤ 1 := by nlinarith [sq_nonneg (p.ρ ^ 2)]
  have hs := p.normalized_quadratic
  nlinarith

lemma nuisance_le_margin (p : Tuning) : p.nuisance ≤ p.κ / 4 :=
  nuisance_small p.delta_pos.le p.unit_ge_one p.rho_pos (p.rho_le.trans (by norm_num))
    p.kappa_pos.le p.kappa_unit p.normalized_quadratic

lemma height_pos (p : Tuning) : 0 < p.height := mul_pos (by norm_num) p.unit_pos

lemma global_threshold (p : Tuning) :
    3 + 12 * (p.δ * p.height + p.δ ^ 2) / p.ρ ^ 2 ≤ 4 :=
  global_mass_threshold p.delta_pos.le (p.delta_small.trans (by norm_num)) p.unit_ge_one
    p.rho_pos (p.rho_le.trans (by norm_num)) p.normalized_quadratic

lemma post_threshold (p : Tuning) :
    3 * p.δ ^ 2 + 12 * (p.δ * p.height + p.δ ^ 2) / p.ρ ^ 2 ≤ 2 * p.nuisance :=
  post_mass_threshold p.delta_pos.le (p.delta_small.trans (by norm_num)) p.height_pos.le
    p.rho_pos (p.rho_le.trans (by norm_num))

lemma nuisance_pos (p : Tuning) : 0 < p.nuisance := by
  dsimp only [nuisance]
  have := p.height_pos
  have := p.delta_pos
  have := p.rho_pos
  positivity

lemma noise_threshold (p : Tuning) : p.nuisance ^ 2 / p.δ + (p.nuisance + 3 / 2) ^ 2 ≤ 4 := by
  have hn := norm_increment_small p.delta_pos.le p.unit_ge_one p.rho_pos
    p.kappa_pos.le p.kappa_le p.normalized_quadratic
  have ha := p.nuisance_le_margin
  have ha0 := p.nuisance_pos
  have he : p.nuisance ^ 2 / p.δ = 64 * p.δ * (p.height + 1) ^ 2 / p.ρ ^ 4 := by
    dsimp only [nuisance]
    field_simp [ne_of_gt p.delta_pos, ne_of_gt p.rho_pos]
    ring
  rw [he]
  change 64 * p.δ * (256 * p.unit + 1) ^ 2 / p.ρ ^ 4 + (p.nuisance + 3 / 2) ^ 2 ≤ 4
  nlinarith [p.kappa_pos]

lemma drift_threshold (p : Tuning) : p.δ * p.negatives * p.height ≤ 1 / 2 :=
  (drift_small p.delta_pos.le p.unit_pos.le p.negatives_upper p.normalized_cubic).le

lemma early_threshold (p : Tuning) : 4 * (burnIn p.ρ p.δ : ℝ) ≤ p.height := by
  have hb := p.burnIn_le_unit
  have hu := p.unit_pos
  change _ ≤ 256 * p.unit
  linarith

lemma height_threshold (p : Tuning) :
    16 * (burnIn p.ρ p.δ : ℝ) ^ 2 + 4 * p.negatives ≤ p.height ^ 2 :=
  (height_small p.unit_pos (Nat.cast_nonneg _) p.burnIn_le_unit p.negatives_upper).le

lemma decay_threshold (p : Tuning) {j : ℕ} (hj : burnIn p.ρ p.δ ≤ j) :
    (1 - p.ρ ^ 2 / 2) ^ (j / 2) ≤ p.δ ^ 2 := by
  apply burnin_decay p.rho_pos (p.rho_le.trans (by norm_num)) p.delta_pos
  have hh := burnin_half (8 / p.ρ ^ 2 * Real.log (1 / p.δ))
  have hdiv : (((burnIn p.ρ p.δ) / 2 : ℕ) : ℝ) ≤ ((j / 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_le_div_right hj
  dsimp only [burnIn] at hdiv
  have he : 8 / p.ρ ^ 2 * Real.log (1 / p.δ) / 2 =
      4 / p.ρ ^ 2 * Real.log (1 / p.δ) := by ring
  rw [he] at hh
  exact hh.trans hdiv

lemma kick_small (p : Tuning) : p.δ ^ 2 ≤ 1 / 2 := by
  have hd := p.delta_small
  have hp := p.delta_pos
  nlinarith

lemma burnIn_lt_negatives (p : Tuning) : burnIn p.ρ p.δ < p.negatives := by
  have hb := p.burnIn_le_unit
  have hm := p.negatives_lower
  have hu := p.unit_ge_one
  have h : (burnIn p.ρ p.δ : ℝ) < p.negatives := by nlinarith
  exact_mod_cast h

lemma separation_threshold (p : Tuning) {m : ℝ} (hm : 0 ≤ m) (hmB : m ≤ burnIn p.ρ p.δ) :
    2 * p.height < p.κ / 4 * ((p.negatives : ℝ) - m) := by
  have hM := mul_le_mul_of_nonneg_left p.negatives_lower p.kappa_pos.le
  have hU := mul_le_mul_of_nonneg_right p.kappa_unit p.unit_pos.le
  have hmκ := mul_le_mul_of_nonneg_right p.kappa_le hm
  have hBU := p.burnIn_le_unit
  have hUp := p.unit_pos
  change 2 * (256 * p.unit) < _
  nlinarith

noncomputable def referenceLength (p : Tuning) : ℕ := ⌈4 / p.ρ * Real.log (8 / p.δ ^ 2)⌉₊ + 2

lemma kick_le_rho (p : Tuning) : p.δ ^ 2 ≤ p.ρ := by
  have hu := p.unit_ge_one
  have hd := mul_le_mul_of_nonneg_left (show 1 ≤ p.unit ^ 2 by nlinarith) p.delta_pos.le
  have hs := p.normalized_quadratic
  have hr2 : p.ρ ^ 2 ≤ p.ρ := by nlinarith [p.rho_pos, p.rho_le]
  have hr4 : p.ρ ^ 4 ≤ p.ρ ^ 2 := by nlinarith [p.rho_pos, p.rho_le, sq_nonneg (p.ρ ^ 2)]
  have hδ1 := p.delta_small
  nlinarith [p.delta_pos, p.rho_pos]

lemma referenceLength_pos (p : Tuning) : 0 < p.referenceLength := by
  dsimp only [referenceLength]
  omega

lemma reference_growth (p : Tuning) : 8 ≤ p.δ ^ 2 * (1 + p.ρ) ^ (p.referenceLength - 1) := by
  apply escape_amplification p.rho_pos (p.rho_le.trans (by norm_num)) (sq_pos_of_pos p.delta_pos)
  have hratio : 1 ≤ 8 / p.δ ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos p.delta_pos)).mpr
    nlinarith [p.kick_small]
  have hlog : 0 ≤ Real.log (8 / p.δ ^ 2) := Real.log_nonneg hratio
  have hc := Nat.le_ceil (4 / p.ρ * Real.log (8 / p.δ ^ 2))
  have hnonneg : 0 ≤ 2 / p.ρ * Real.log (8 / p.δ ^ 2) :=
    mul_nonneg (div_nonneg (by norm_num) p.rho_pos.le) hlog
  have he : p.referenceLength - 1 = ⌈4 / p.ρ * Real.log (8 / p.δ ^ 2)⌉₊ + 1 := by
    dsimp only [referenceLength]
    omega
  rw [he, Nat.cast_add, Nat.cast_one]
  have hid : 4 / p.ρ * Real.log (8 / p.δ ^ 2) = 2 * (2 / p.ρ * Real.log (8 / p.δ ^ 2)) := by ring
  have hc' : 2 * (2 / p.ρ * Real.log (8 / p.δ ^ 2)) ≤
      (⌈4 / p.ρ * Real.log (8 / p.δ ^ 2)⌉₊ : ℝ) := hid ▸ hc
  linarith

end Tuning

end LongTails.Proofs.ManySampleConvolutionalPerceptronParameters
