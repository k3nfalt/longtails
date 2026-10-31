import LongTails.Proofs.NoisyBatchQuadraticPerceptronMoments
import LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialConstants
open LongTails.Setups.NoisyBatchQuadraticPerceptron
namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronBudget
lemma tuned_cycle_failure (A ρ : ℝ) (hA : 0 ≤ A) (hρ : 0 < ρ) :
    (1 - Real.exp (-A)) ^ ⌈Real.exp A * Real.log (2 / ρ)⌉₊ ≤ ρ / 2 := by
  have hp : 0 ≤ 1 - Real.exp (-A) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hbase : 1 - Real.exp (-A) ≤ Real.exp (-Real.exp (-A)) := by
    simpa only [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-Real.exp (-A))
  have hpow := pow_le_pow_left₀ hp hbase ⌈Real.exp A * Real.log (2 / ρ)⌉₊
  rw [← Real.exp_nat_mul] at hpow
  have hj := Nat.le_ceil (Real.exp A * Real.log (2 / ρ))
  have hjp := mul_le_mul_of_nonneg_left hj (Real.exp_nonneg (-A))
  rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul] at hjp
  have he : Real.exp ((⌈Real.exp A * Real.log (2 / ρ)⌉₊ : ℝ) * (-Real.exp (-A))) ≤
      Real.exp (-Real.log (2 / ρ)) := Real.exp_le_exp.mpr (by nlinarith [hjp])
  have hf : Real.exp (-Real.log (2 / ρ)) = ρ / 2 := by
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2 / ρ)]
    field_simp
  exact hpow.trans (he.trans_eq hf)
lemma tuned_clock_tail (C ρ : ℝ) (J : ℕ) (hC : 0 < C) (hρ : 0 < ρ) :
    0 < ⌈(2 / ρ) * 128 ^ J * C⌉₊ ∧
    128 ^ J * C / (⌈(2 / ρ) * 128 ^ J * C⌉₊ : ℝ) ≤ ρ / 2 := by
  have hx : 0 < (2 / ρ) * 128 ^ J * C := by positivity
  have hceil := Nat.le_ceil ((2 / ρ) * 128 ^ J * C)
  have hn : (0 : ℝ) < ⌈(2 / ρ) * 128 ^ J * C⌉₊ := hx.trans_le hceil
  refine ⟨by exact_mod_cast hn, ?_⟩
  apply (div_le_iff₀ hn).mpr
  have hm := mul_le_mul_of_nonneg_left hceil (le_of_lt (div_pos hρ (by norm_num : (0 : ℝ) < 2)))
  have he : (ρ / 2) * ((2 / ρ) * 128 ^ J * C) = 128 ^ J * C := by field_simp
  rw [he] at hm
  exact hm
lemma log_128_le_five : Real.log 128 ≤ 5 := by
  have he : (128 : ℝ) = 2 ^ (7 : ℕ) := by norm_num
  rw [he, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith [Real.log_two_lt_d9]
lemma trial_power_bound (A ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (128 : ℝ) ^ ⌈Real.exp A * Real.log (2 / ρ)⌉₊ ≤
      128 * (2 / ρ) ^ (5 * Real.exp A) := by
  have hx : 0 < 2 / ρ := by positivity
  have hx1 : 1 ≤ 2 / ρ := (le_div_iff₀ hρ).mpr (by linarith)
  have hl : 0 ≤ Real.log (2 / ρ) := Real.log_nonneg hx1
  have hl128 : 0 ≤ Real.log 128 := Real.log_nonneg (by norm_num)
  have hj := Nat.ceil_lt_add_one (mul_nonneg (Real.exp_nonneg A) hl)
  have hm := mul_le_mul_of_nonneg_right hj.le hl128
  have hb := mul_le_mul_of_nonneg_left log_128_le_five (mul_nonneg (Real.exp_nonneg A) hl)
  calc
    _ = Real.exp ((⌈Real.exp A * Real.log (2 / ρ)⌉₊ : ℝ) * Real.log 128) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 128)]
    _ ≤ Real.exp (Real.log 128 + Real.log (2 / ρ) * (5 * Real.exp A)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    _ = _ := by rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 128),
      ← Real.rpow_def_of_pos hx]
lemma simplified_call_budget (n B J : ℕ) (M e ρ T : ℝ)
    (hM : 4 ≤ M) (he : 0 ≤ e) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hT : 1 ≤ T) (hB : (B : ℝ) ≤ 129 * M) (hJ : (128 : ℝ) ^ J ≤ 128 * T) :
    n * (⌈(2 / ρ) * (128 : ℝ) ^ J * (2 + e + 2 * (B : ℝ))⌉₊ + 1) ≤
      ⌈100000 * (n : ℝ) * (M + e) * T / ρ⌉₊ := by
  let C : ℝ := 2 + e + 2 * (B : ℝ)
  let H := ⌈(2 / ρ) * (128 : ℝ) ^ J * C⌉₊
  have hC : 0 < C := by dsimp [C]; positivity
  have hCU : C ≤ 260 * (M + e) := by dsimp [C]; nlinarith
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ (2 / ρ) * (128 : ℝ) ^ J * C by positivity)
  have hmul := mul_le_mul_of_nonneg_left hceil.le hρ.le
  have hid : ρ * ((2 / ρ) * (128 : ℝ) ^ J * C + 1) = 2 * (128 : ℝ) ^ J * C + ρ := by field_simp
  rw [hid] at hmul
  have hp := mul_le_mul_of_nonneg_right hJ hC.le
  have hc := mul_le_mul_of_nonneg_left hCU (by linarith : 0 ≤ T)
  have hu : 4 ≤ M + e := by linarith
  have htu : 4 ≤ T * (M + e) := by
    have hh := mul_le_mul_of_nonneg_right hT (by linarith : 0 ≤ M + e)
    nlinarith
  have hscalar : (H : ℝ) + 1 ≤ 100000 * (M + e) * T / ρ := by
    apply (le_div_iff₀ hρ).mpr
    dsimp [H]
    nlinarith
  have hn := mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg (α := ℝ) n)
  have hreal : ((n * (H + 1) : ℕ) : ℝ) ≤ 100000 * (n : ℝ) * (M + e) * T / ρ := by
    push_cast
    convert hn using 1
    ring
  change n * (H + 1) ≤ _
  exact_mod_cast hreal.trans (Nat.le_ceil (100000 * (n : ℝ) * (M + e) * T / ρ))
lemma tuned_call_budget (P : Public) (η ρ : ℝ)
    (hδ : 0 < P.margin) (hδR : P.margin ≤ P.radius) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (htune : η = P.margin / (8 * ((P.count : ℝ) + 1) * P.radius ^ 2)) :
    let B := ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊ + 2
    let A := 25000 * (P.dimension + 1 : ℝ) ^ 2 * (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2) ^ 2
    let J := ⌈Real.exp A * Real.log (2 / ρ)⌉₊
    let N := ⌈(2 / ρ) * 128 ^ J * (2 + ‖P.start‖ ^ 2 / (P.noiseScale ^ 2 * (P.dimension + 1)) + 2 * B)⌉₊
    (P.count : ℕ) * (N + 1) ≤
      ⌈100000 * (P.count : ℝ) * (((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2 +
        ‖P.start‖ ^ 2 / (P.noiseScale ^ 2 * (P.dimension + 1))) * (2 / ρ) ^ (5 * Real.exp A) / ρ⌉₊ := by
  dsimp only
  let M := ((P.count : ℝ) + 1) ^ 2 * (P.radius / P.margin) ^ 2
  let e := ‖P.start‖ ^ 2 / (P.noiseScale ^ 2 * (P.dimension + 1 : ℝ))
  let B := ⌈16 * (P.count : ℝ) / (η * P.margin)⌉₊ + 2
  let A := 25000 * (P.dimension + 1 : ℝ) ^ 2 * M ^ 2
  let J := ⌈Real.exp A * Real.log (2 / ρ)⌉₊
  have hn : 1 ≤ (P.count : ℝ) := by exact_mod_cast P.count.property
  have hr : 1 ≤ P.radius / P.margin := (le_div_iff₀ hδ).mpr (by simpa using hδR)
  have hn2 : (4 : ℝ) ≤ ((P.count : ℝ) + 1) ^ 2 := by nlinarith
  have hr2 : 1 ≤ (P.radius / P.margin) ^ 2 := by nlinarith
  have hM : 4 ≤ M := by
    have hh := mul_le_mul hn2 hr2 (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
    simpa only [mul_one] using hh
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hB := LongTails.Proofs.NoisyBatchQuadraticPerceptronTrialConstants.tuned_block_length
    P.count P.radius P.margin η hn hδ hδR htune
  have hT : 1 ≤ (2 / ρ) ^ (5 * Real.exp A) := Real.one_le_rpow
    ((le_div_iff₀ hρ).mpr (by linarith)) (by positivity)
  have hJ := trial_power_bound A ρ hρ hρ1
  have hh := simplified_call_budget P.count B J M e ρ ((2 / ρ) ^ (5 * Real.exp A))
    hM he hρ hρ1 hT hB hJ
  simpa only [M, e, B, A, J, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using hh
end LongTails.Proofs.NoisyBatchQuadraticPerceptronBudget
