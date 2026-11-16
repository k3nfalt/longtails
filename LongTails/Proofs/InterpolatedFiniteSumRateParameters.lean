import LongTails.Proofs.InterpolatedFiniteSumLinkLength

namespace LongTails.Proofs.InterpolatedFiniteSumRateParameters

lemma logarithm_bound (n q H c : ℝ) (hn : 0 ≤ n) (hq : 0 ≤ q) (hH : 0 < H)
    (hc : 0 ≤ c) (hcH : c ≤ H) :
    Real.log (1 + c * q ^ 2 / H) ≤ 2 * Real.log (2 + n + q + H) := by
  let N := 2 + n + q + H
  have hN : 0 < N := by dsimp [N]; linarith
  have hbase : 0 < 1 + c * q ^ 2 / H := by positivity
  have hfrac : c * q ^ 2 / H ≤ q ^ 2 := by
    apply (div_le_iff₀ hH).mpr
    exact mul_le_mul_of_nonneg_right hcH (sq_nonneg q) |>.trans_eq (by ring)
  have hsq : 1 + q ^ 2 ≤ N ^ 2 := by
    have hNq : q + 1 ≤ N := by dsimp [N]; linarith
    nlinarith only [hNq, hq, sq_nonneg (N - (q + 1))]
  calc
    _ ≤ Real.log (N ^ 2) := Real.log_le_log hbase (by linarith)
    _ = _ := by rw [Real.log_pow]; rfl

lemma log_scale (n q H : ℝ) (hn : 0 ≤ n) (hq : 0 ≤ q) (hH : 0 ≤ H) :
    1 ≤ 1 + Real.log (2 + n + q + H) := by
  have hh : 1 ≤ 2 + n + q + H := by linarith
  have := Real.log_nonneg hh
  linarith

lemma floor_half (x : ℝ) (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have hf := Nat.lt_floor_add_one x
  have h1 : 1 ≤ ⌊x⌋₊ := (Nat.one_le_floor_iff x).mpr hx
  have h1R : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast h1
  linarith

lemma four_terms (a b c d B : ℝ) (h : B ≤ (a + b + c + d) / 4) :
    B ≤ a ∨ B ≤ b ∨ B ≤ c ∨ B ≤ d := by
  by_contra hn
  push Not at hn
  linarith

lemma exponential_budget (n g b : ℕ) (hg : 0 < g) (hng : n ≤ 3 * g)
    (q η D : ℝ) (hq : 0 ≤ q) (hη : 0 < η) (hD : 1 ≤ D) (hηD : η ≤ 2 * D)
    (hactive : 84 * η * Real.sqrt g ≤ q)
    (hb : 1000000 * D ^ 2 * b ≤ Real.sqrt n * q) :
    64 * η * b ≤ (g : ℝ) * ⌊q / (84 * η * Real.sqrt g)⌋₊ := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hsg : 0 < Real.sqrt g := Real.sqrt_pos.mpr hgR
  have hnR : (n : ℝ) ≤ 3 * g := by exact_mod_cast hng
  have hsn := Real.sq_sqrt (Nat.cast_nonneg n)
  have hsgsq := Real.sq_sqrt hgR.le
  have hnsg : Real.sqrt n ≤ 2 * Real.sqrt g := by
    have hsn0 := Real.sqrt_nonneg (n : ℝ)
    nlinarith only [hsn, hsgsq, hnR, hsn0, hsg]
  have hr : 1 ≤ q / (84 * η * Real.sqrt g) := (le_div_iff₀ (by positivity)).mpr (by simpa using hactive)
  have hf := mul_le_mul_of_nonneg_left (floor_half _ hr) hgR.le
  have hqmul := mul_le_mul_of_nonneg_right hnsg hq
  have heta2 : η ^ 2 ≤ 4 * D ^ 2 := by nlinarith only [hηD, hη, hD]
  have hm := mul_le_mul_of_nonneg_right heta2 (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
  have hDb : 0 ≤ D ^ 2 * (b : ℝ) := by positivity
  have hcore : 21504 * η ^ 2 * b ≤ 2 * Real.sqrt g * q := by nlinarith only [hb, hqmul, hm, hDb]
  have hscaled := mul_le_mul_of_nonneg_right hf (show 0 ≤ 168 * η * Real.sqrt g by positivity)
  have hid : ((g : ℝ) * (q / (84 * η * Real.sqrt g) / 2)) * (168 * η * Real.sqrt g) = g * q := by field_simp; ring
  rw [hid] at hscaled
  have hcore' := mul_le_mul_of_nonneg_right hcore hsg.le
  have hid' : 2 * Real.sqrt g * q * Real.sqrt g = 2 * g * q := by
    calc _ = 2 * (Real.sqrt g) ^ 2 * q := by ring
         _ = _ := by rw [hsgsq]
  rw [hid'] at hcore'
  apply (mul_le_mul_iff_left₀ (show 0 < 168 * η * Real.sqrt g by positivity)).mp
  nlinarith only [hscaled, hcore']

end LongTails.Proofs.InterpolatedFiniteSumRateParameters
