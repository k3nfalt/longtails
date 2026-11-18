import LongTails.Setups.AdditiveCubeFixedPoint
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped ENNReal

namespace LongTails.Proofs.AdditiveFixedPointLowerBudget

noncomputable def width (b : ℕ) : ℕ := ⌈16 * (1 + Real.log (2 + b))⌉₊

noncomputable def tolerance (b : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / (8 * ((b : ℝ) + 1)))

lemma width_bound {b n : ℕ} (hn : n ≤ b) {B : ℝ} (hB : n * B ≤ (width b : ℝ) / 8) :
    ENNReal.ofReal (Real.exp B) ^ n * ((n : ℝ≥0∞) / 2 ^ width b) ≤ tolerance b ^ 2 := by
  have hl : 0 ≤ Real.log (2 + (b : ℝ)) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) b])
  have hk : 16 * (1 + Real.log (2 + (b : ℝ))) ≤ width b := Nat.le_ceil _
  have hlog : Real.log (b + 1 : ℝ) ≤ Real.log (2 + (b : ℝ)) :=
    Real.log_le_log (by positivity) (by linarith)
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have he : n * B + 6 * Real.log 2 + 3 * Real.log ((b : ℝ) + 1) ≤ width b * Real.log 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) (width b))]
  have hex := Real.exp_le_exp.mpr he
  have h6 : Real.exp (6 * Real.log 2) = (2 : ℝ) ^ 6 := by
    convert Real.exp_nat_mul (Real.log 2) 6 using 1
    · norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have h3 : Real.exp (3 * Real.log ((b : ℝ) + 1)) = ((b : ℝ) + 1) ^ 3 := by
    convert Real.exp_nat_mul (Real.log ((b : ℝ) + 1)) 3 using 1
    · simp [Real.exp_log (by positivity : 0 < (b : ℝ) + 1)]
  rw [Real.exp_add, Real.exp_add, h6, h3, Real.exp_nat_mul, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hex
  have hn' : (n : ℝ) ≤ b + 1 := by exact_mod_cast Nat.le_succ_of_le hn
  have hreal : Real.exp B ^ n * ((n : ℝ) / 2 ^ width b) ≤ (1 / (8 * ((b : ℝ) + 1))) ^ 2 := by
    have hpos : 0 < (2 : ℝ) ^ width b := by positivity
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hn' (show 0 ≤ Real.exp B ^ n * (8 * ((b : ℝ) + 1)) ^ 2 by positivity)]
  have hh := ENNReal.ofReal_le_ofReal hreal
  simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ Real.exp B ^ n),
    ENNReal.ofReal_pow (Real.exp_pos B).le, ENNReal.ofReal_div_of_pos (by positivity : 0 < (2 : ℝ) ^ width b),
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : ℝ)),
    ENNReal.ofReal_ofNat, tolerance, ENNReal.ofReal_pow (by positivity : 0 ≤ 1 / (8 * ((b : ℝ) + 1)))] using hh

lemma small_phase {b n : ℕ} (hn : n ≤ b) :
    (n : ℝ≥0∞) / 2 ^ width b ≤ tolerance b := by
  have h := width_bound hn (B := 0) (by rw [mul_zero]; positivity)
  simp only [Real.exp_zero, ENNReal.ofReal_one, one_pow, one_mul] at h
  have ht : tolerance b ≤ 1 := by
    rw [tolerance, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) b]))
  apply h.trans
  calc tolerance b ^ 2 = tolerance b * tolerance b := sq _
       _ ≤ tolerance b * 1 := by gcongr
       _ = _ := mul_one _

def chunks (b n : ℕ) : List ℕ := List.replicate (b / n) n ++ [b % n]

lemma chunks_sum (b n : ℕ) : (chunks b n).sum = b := by
  simp [chunks, List.sum_replicate, Nat.div_add_mod' b n]

lemma chunks_size {b n : ℕ} (hn : 0 < n) (hn' : n ≤ b) :
    ((chunks b n).length : ℝ) ≤ 2 * (b : ℝ) / n := by
  rw [le_div_iff₀ (by exact_mod_cast hn)]
  have hb := Nat.div_mul_le_self b n
  simp only [chunks, List.length_append, List.length_replicate, List.length_singleton, Nat.cast_add, Nat.cast_one]
  nlinarith [show ((b / n : ℕ) : ℝ) * n ≤ b by exact_mod_cast hb,
    show (n : ℝ) ≤ b by exact_mod_cast hn']

lemma chunks_le {b n j : ℕ} (hn : 0 < n) (hj : j ∈ chunks b n) : j ≤ n := by
  simp only [chunks, List.mem_append, List.mem_singleton] at hj
  rcases hj with h | rfl
  · exact (List.eq_of_mem_replicate h).le
  · exact (Nat.mod_lt _ hn).le

open LongTails.Setups.AdditiveCubeFixedPoint

noncomputable def variance (p : Params) : NNReal :=
  ⟨p.σ ^ 2 / (4 * (2 + Real.log ((max 1 p.d : ℕ) : ℝ))), by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (max 1 p.d : ℕ) by exact_mod_cast le_max_left 1 p.d)
    positivity⟩

noncomputable def capacity (p : Params) : ℕ := max 1 ⌊(variance p : ℝ) / (16 * (16 * p.ε) ^ 2)⌋₊

lemma variance_eq (p : Params) (hd : 0 < p.d) :
    (variance p : ℝ) = p.σ ^ 2 / (4 * (2 + Real.log p.d)) := by
  change p.σ ^ 2 / (4 * (2 + Real.log ((max 1 p.d : ℕ) : ℝ))) = _
  rw [max_eq_right (show 1 ≤ p.d by omega)]

lemma variance_admissible (p : Params) (hd : 0 < p.d) :
    4 * (variance p : ℝ) * (Real.log p.d + 2) ≤ p.σ ^ 2 := by
  rw [variance_eq p hd]
  have hlog := Real.log_nonneg (show 1 ≤ (p.d : ℝ) by exact_mod_cast hd)
  field_simp
  linarith

lemma capacity_pos (p : Params) : 0 < capacity p := (Nat.le_max_left 1 _)

lemma capacity_lower (p : Params) (hd : 0 < p.d) (he : 0 < p.ε) :
    1 + (p.σ / p.ε) ^ 2 / (2 + Real.log p.d) ≤ 32769 * (capacity p : ℝ) := by
  have h1 : (1 : ℝ) ≤ capacity p := by exact_mod_cast capacity_pos p
  let q := (variance p : ℝ) / (16 * (16 * p.ε) ^ 2)
  have hq : q < (capacity p : ℝ) + 1 :=
    (Nat.lt_floor_add_one q).trans_le (by gcongr; exact_mod_cast Nat.le_max_right 1 ⌊q⌋₊)
  have hlog := Real.log_nonneg (show 1 ≤ (p.d : ℝ) by exact_mod_cast hd)
  have hid : (p.σ / p.ε) ^ 2 / (2 + Real.log p.d) = 16384 * q := by
    dsimp only [q]
    rw [variance_eq p hd]
    field_simp
    ring
  rw [hid]
  linarith

lemma width_upper {T U : ℝ} (ht : 1 ≤ T) (hu : 0 ≤ U) {b : ℕ}
    (hb : (b : ℝ) ≤ T * (1 + U ^ 2)) :
    (width b : ℝ) ≤ 65 * (1 + Real.log (2 + T + U)) := by
  let a := 2 + T + U
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have ha' : 1 + U ≤ a := by dsimp [a]; linarith
  have ha2 : 1 + U ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_le_sq₀ (by linarith : 0 ≤ 1 + U) (by linarith : 0 ≤ a) |>.mpr ha']
  have hp : 2 + (b : ℝ) ≤ a ^ 3 := by
    have hprod := mul_le_mul_of_nonneg_left ha2 (by linarith : 0 ≤ T)
    have hprod' := mul_le_mul_of_nonneg_right (show 2 + T ≤ a by dsimp [a]; linarith)
      (sq_nonneg a)
    nlinarith [sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ a) |>.mpr ha]
  have hlg := Real.log_le_log (by positivity : 0 < 2 + (b : ℝ)) hp
  rw [Real.log_pow] at hlg
  have hceil : (width b : ℝ) < 16 * (1 + Real.log (2 + (b : ℝ))) + 1 :=
    Nat.ceil_lt_add_one (by have := Real.log_nonneg (show 1 ≤ 2 + (b : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) b]); positivity)
  dsimp only [a] at *
  norm_num at hlg
  linarith [Real.log_nonneg ha]

lemma capacity_energy (p : Params) (he : 0 < p.ε) (hc : 1 < capacity p)
    {n : ℕ} (hn : n ≤ capacity p) :
    variance p ≠ 0 ∧ n * ((16 * p.ε) ^ 2 / (variance p : ℝ)) ≤ 1 / 16 := by
  let q := (variance p : ℝ) / (16 * (16 * p.ε) ^ 2)
  have hfloor : capacity p = ⌊q⌋₊ := by
    change max 1 ⌊q⌋₊ = _
    change 1 < max 1 ⌊q⌋₊ at hc
    omega
  have hcap : (capacity p : ℝ) ≤ q := by rw [hfloor]; exact Nat.floor_le (by dsimp [q]; positivity)
  have hvp : 0 < (variance p : ℝ) := by
    by_contra! hnpos
    have hz := le_antisymm hnpos (variance p).coe_nonneg
    simp [q, hz] at hcap
    omega
  refine ⟨by exact_mod_cast hvp.ne', ?_⟩
  have hn' : (n : ℝ) ≤ q := (Nat.cast_le.mpr hn).trans hcap
  have hx := (le_div_iff₀ (show 0 < 16 * (16 * p.ε) ^ 2 by positivity)).mp hn'
  rw [← mul_div_assoc, div_le_iff₀ hvp]
  linarith

lemma phase_condition (p : Params) (he : 0 < p.ε) {b : ℕ} (hb : capacity p ≤ b)
    {n : ℕ} (hn : n ∈ chunks b (capacity p)) :
    (n ≤ 1 ∧ (n : ℝ≥0∞) / 2 ^ width b ≤ tolerance b) ∨
    (variance p ≠ 0 ∧ ENNReal.ofReal (Real.exp (width b * ((2 * (8 * p.ε)) ^ 2 /
      (variance p : ℝ)))) ^ n * ((n : ℝ≥0∞) / 2 ^ width b) ≤ tolerance b ^ 2) := by
  have hnc := chunks_le (capacity_pos p) hn
  by_cases hc : capacity p ≤ 1
  · exact Or.inl ⟨hnc.trans hc, small_phase (hnc.trans hb)⟩
  obtain ⟨hv, hx⟩ := capacity_energy p he (by omega) hnc
  refine Or.inr ⟨hv, width_bound (hnc.trans hb) ?_⟩
  have := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg (α := ℝ) (width b))
  linarith only [show (n : ℝ) * (width b * ((2 * (8 * p.ε)) ^ 2 / (variance p : ℝ))) =
    width b * (n * ((16 * p.ε) ^ 2 / (variance p : ℝ))) by ring, this,
    Nat.cast_nonneg (α := ℝ) (width b)]

lemma chain_size (p : Params) (hd : 0 < p.d) (he : 0 < p.ε) (hs : 0 ≤ p.σ)
    (hr : 128 * p.ε ≤ p.R) {b : ℕ} (hc : capacity p ≤ b)
    (hb : b ≤ ⌊(p.R / p.ε) * (1 + (p.σ / p.ε) ^ 2 / (2 + Real.log p.d)) /
      (67108864 * (1 + Real.log (2 + ((p.R : ℝ) + p.σ) / p.ε)))⌋₊) :
    ((chunks b (capacity p)).length * width b : ℕ) ≤ (p.R : ℝ) / p.ε / 8 := by
  let T := (p.R : ℝ) / p.ε
  let U := p.σ / p.ε
  let D := 2 + Real.log p.d
  let H := 1 + Real.log (2 + T + U)
  have ht : 128 ≤ T := (le_div_iff₀ he).mpr hr
  have hu : 0 ≤ U := div_nonneg hs he.le
  have hd' : 2 ≤ D := by dsimp [D]; linarith [Real.log_nonneg (show (1 : ℝ) ≤ p.d by exact_mod_cast hd)]
  have hh : 1 ≤ H := by dsimp [H]; linarith [Real.log_nonneg (show 1 ≤ 2 + T + U by linarith)]
  rw [add_div, ← add_assoc] at hb
  have hb' : (b : ℝ) ≤ T * (1 + U ^ 2 / D) / (67108864 * H) :=
    (Nat.cast_le.mpr hb).trans (Nat.floor_le (by change 0 ≤ T * (1 + U^2 / D) / (67108864 * H); positivity))
  have hb'' := (le_div_iff₀ (by positivity)).mp hb'
  have hu2 : U ^ 2 / D ≤ U ^ 2 := div_le_self (sq_nonneg _) (by linarith)
  have hrough : (b : ℝ) ≤ T * (1 + U ^ 2) := by
    calc (b : ℝ) ≤ b * (67108864 * H) := le_mul_of_one_le_right (by positivity) (by linarith)
         _ ≤ T * (1 + U ^ 2 / D) := hb''
         _ ≤ _ := by gcongr
  have hk := width_upper (by linarith : 1 ≤ T) hu hrough
  have hz := capacity_lower p hd he
  change 1 + U ^ 2 / D ≤ _ at hz
  have hmul := hb''.trans (mul_le_mul_of_nonneg_left hz (by linarith))
  have hm := mul_le_mul_of_nonneg_left hk (show 0 ≤ (b : ℝ) by positivity)
  change (b : ℝ) * width b ≤ b * (65 * H) at hm
  have hprod : (b : ℝ) * width b * 16 ≤ T * capacity p := by
    nlinarith only [hm, hmul, mul_nonneg (Nat.cast_nonneg (α := ℝ) b) (show 0 ≤ H by linarith)]
  have hlen := chunks_size (capacity_pos p) hc
  have hpos : 0 < (capacity p : ℝ) := by exact_mod_cast capacity_pos p
  have hlen' := (le_div_iff₀ hpos).mp hlen
  have hp := mul_le_mul_of_nonneg_right hlen' (Nat.cast_nonneg (α := ℝ) (width b))
  push_cast
  change _ ≤ T / 8
  apply (le_of_mul_le_mul_right (a := (capacity p : ℝ)) _ hpos)
  nlinarith only [hp, hprod]

end LongTails.Proofs.AdditiveFixedPointLowerBudget
