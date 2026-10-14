import LongTails.Algorithms.ScalarHeavyTailEstimator
import Mathlib.Tactic

namespace OracleTemplate.ScalarHeavyTailEstimator

lemma amplification_exponent (j h : ℕ) :
    16 * (j + 1) ≤ (2 + h / 2) * (1 + 32 * (j + 1) / (1 + h)) := by
  have hrem := Nat.mod_lt (32 * (j + 1)) (show 0 < 1 + h by omega)
  have he := Nat.mod_add_div (32 * (j + 1)) (1 + h)
  have hh := Nat.mod_lt h (by decide : 0 < 2)
  have hh' := Nat.mod_add_div h 2
  nlinarith

lemma repetitions_fine (σ u : ℝ) (j : ℕ) : repetitions σ u j ≤ 33 * (j + 1) := by
  unfold repetitions
  have h := Nat.div_le_self (32 * (j + 1)) (1 + (j - noiseLevel σ u))
  omega

lemma repetitions_coarse (σ u : ℝ) (j : ℕ)
    (hj : 3 * noiseLevel σ u ≤ 2 * j + 2) : repetitions σ u j ≤ 97 := by
  unfold repetitions
  have hN : noiseLevel σ u ≤ j + 1 := by omega
  have hratio : 32 * (j + 1) < 97 * (1 + (j - noiseLevel σ u)) := by omega
  have hdiv : 32 * (j + 1) / (1 + (j - noiseLevel σ u)) < 97 :=
    (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
  omega

lemma weighted_half_sum (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j) =
      4 - (2 * n + 4) * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

lemma weighted_half_sum_le (n : ℕ) :
    (∑ j ∈ Finset.range n, ((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j) ≤ 4 := by
  rw [weighted_half_sum]
  have h : 0 ≤ (2 * (n : ℝ) + 4) * (1 / 2 : ℝ) ^ n := by positivity
  linarith

lemma radius_pos {σ p u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) : 0 < radius σ p u := by
  unfold radius
  positivity

lemma radius_power {σ p u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) :
    (radius σ p u / 2) ^ (p - 1) = 256 * (σ + u) ^ p / u := by
  unfold radius
  rw [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), one_div,
    Real.rpow_inv_rpow (by positivity) (by linarith)]

lemma radius_large {σ p u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u)
    (hp : 1 < p) (hp2 : p ≤ 2) : 256 * (σ + u) ≤ radius σ p u / 2 := by
  have hs : 0 < σ + u := by positivity
  have he : p - 1 + 1 = p := by ring
  have hpow : (σ + u) ^ (p - 1) * (σ + u) = (σ + u) ^ p := by
    simpa only [he, Real.rpow_one] using (Real.rpow_add hs (p - 1) 1).symm
  have h256 : (256 : ℝ) ^ (p - 1) ≤ 256 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 256) (show p - 1 ≤ 1 by linarith)
  have hr := radius_pos (p := p) hσ hu
  apply (Real.rpow_le_rpow_iff (by positivity) (by positivity) (by linarith : 0 < p - 1)).mp
  rw [radius_power hσ hu hp, Real.mul_rpow (by norm_num) hs.le]
  apply (le_div_iff₀ hu).mpr
  have h1 := mul_le_mul_of_nonneg_right h256 (Real.rpow_nonneg hs.le (p - 1))
  have h2 : (σ + u) ^ (p - 1) * u ≤ (σ + u) ^ p := by
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hs.le _)
  nlinarith

lemma radius_bias {σ p u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) :
    σ ^ p / (radius σ p u / 2) ^ (p - 1) ≤ u / 256 := by
  rw [radius_power hσ hu hp]
  have hs : 0 < (σ + u) ^ p := Real.rpow_pos_of_pos (by positivity) _
  have hpow : σ ^ p ≤ (σ + u) ^ p := Real.rpow_le_rpow hσ (by linarith) (by linarith)
  apply (div_le_iff₀ (by positivity : 0 < 256 * (σ + u) ^ p / u)).mpr
  convert hpow using 1; field_simp

lemma batch_variance {σ p u : ℝ} (hu : 0 < u) :
    ((2 * radius σ p u) ^ (2 - p) * σ ^ p / (batchSize σ p u : ℝ)) /
      (u / 2) ^ 2 ≤ 1 / 4096 := by
  let v := (2 * radius σ p u) ^ (2 - p) * σ ^ p
  have hn : 0 < (batchSize σ p u : ℝ) := by unfold batchSize; positivity
  have hv : 16384 * v / u ^ 2 = 16384 * (2 * radius σ p u) ^ (2 - p) * σ ^ p / u ^ 2 := by
    dsimp [v]
    ring
  have hceil := Nat.le_ceil (16384 * (2 * radius σ p u) ^ (2 - p) * σ ^ p / u ^ 2)
  have hb : 16384 * v / u ^ 2 ≤ (batchSize σ p u : ℝ) := by
    rw [hv]
    unfold batchSize
    push_cast
    linarith
  have hmul := (div_le_iff₀ (sq_pos_of_pos hu)).mp hb
  change (v / (batchSize σ p u : ℝ)) / (u / 2) ^ 2 ≤ _
  apply (div_le_iff₀ (by positivity : 0 < (u / 2) ^ 2)).mpr
  apply (div_le_iff₀ hn).mpr
  nlinarith

lemma half_scale_power (N : ℕ) : N + N / 2 + 1 ≤ 2 ^ (N - N / 2 + 1) := by
  induction N using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more N ih ih1 =>
    by_cases h0 : N = 0
    · subst N
      norm_num
    by_cases h1 : N = 1
    · subst N
      norm_num
    have hdiv : (N + 2) / 2 = N / 2 + 1 := by omega
    have hexp : N + 2 - (N + 2) / 2 + 1 = (N - N / 2 + 1) + 1 := by omega
    rw [hexp, pow_succ, hdiv]
    omega

lemma sum_two_powers (N : ℕ) : (∑ j ∈ Finset.range N, 2 ^ j) + 1 = 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

lemma prefix_cost_power (N : ℕ) :
    33 * (N + N / 2 + 1) * 2 ^ (N + N / 2 + 1) ≤ 132 * 4 ^ N := by
  have h := half_scale_power N
  calc
    _ ≤ 33 * 2 ^ (N - N / 2 + 1) * 2 ^ (N + N / 2 + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 33 h)
    _ = 132 * 4 ^ N := by
      rw [Nat.mul_assoc, ← Nat.pow_add]
      have he : N - N / 2 + 1 + (N + N / 2 + 1) = 2 * N + 2 := by omega
      rw [he, Nat.pow_add, Nat.pow_mul]
      ring

lemma discovery_repetitions_sum (σ u : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), 2 ^ j * repetitions σ u j) ≤
      132 * 4 ^ noiseLevel σ u + 194 * 2 ^ J := by
  let N := noiseLevel σ u
  let K := N + N / 2
  have hpoint (j : ℕ) : 2 ^ j * repetitions σ u j ≤
      97 * 2 ^ j + 33 * (K + 1) * (if j ≤ K then 2 ^ j else 0) := by
    by_cases hj : j ≤ K
    · rw [ite_eq_left hj]
      have hk := (repetitions_fine σ u j).trans (Nat.mul_le_mul_left 33 (Nat.succ_le_succ hj))
      have h := Nat.mul_le_mul_left (2 ^ j) hk
      simp only [Nat.succ_eq_add_one] at h
      calc
        _ ≤ 2 ^ j * (33 * (K + 1)) := h
        _ = 33 * (K + 1) * 2 ^ j := Nat.mul_comm _ _
        _ ≤ _ := Nat.le_add_left _ _
    · rw [ite_eq_right hj]
      have hN : 3 * noiseLevel σ u ≤ 2 * j + 2 := by dsimp [K, N] at hj; omega
      have h := Nat.mul_le_mul_left (2 ^ j) (repetitions_coarse σ u j hN)
      nlinarith
  have hlow : (∑ j ∈ Finset.range (J + 1), if j ≤ K then 2 ^ j else 0) ≤ 2 ^ (K + 1) := by
    rw [← Finset.sum_filter]
    have hp : (∑ j ∈ Finset.range (K + 1), 2 ^ j) ≤ 2 ^ (K + 1) := by
      have h := sum_two_powers (K + 1)
      omega
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (by intros; positivity)) hp
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega
  have hall : (∑ j ∈ Finset.range (J + 1), 2 ^ j) ≤ 2 ^ (J + 1) := by
    have h := sum_two_powers (J + 1)
    omega
  have hsum := Finset.sum_le_sum (s := Finset.range (J + 1)) (fun j _ => hpoint j)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have h1 := Nat.mul_le_mul_left 97 hall
  have h2 := Nat.mul_le_mul_left (33 * (K + 1)) hlow
  have h3 : 33 * (K + 1) * 2 ^ (K + 1) ≤ 132 * 4 ^ N := prefix_cost_power N
  rw [pow_succ] at h1
  change _ ≤ 132 * 4 ^ N + 194 * 2 ^ J
  omega

lemma dyadic_noise_power {r q : ℝ} (hr : 0 ≤ r) (hq : 2 ≤ q) (j : ℕ) :
    (2 : ℝ) ^ j * (r / (2 : ℝ) ^ j) ^ q ≤ r ^ q * (1 / 2 : ℝ) ^ j := by
  have ht : 0 < (2 : ℝ) ^ j := by positivity
  have ht1 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hz0 : 0 ≤ 1 / (2 : ℝ) ^ j := by positivity
  have hz1 : 1 / (2 : ℝ) ^ j ≤ 1 := (div_le_one ht).mpr ht1
  have hpow := Real.rpow_le_rpow_of_exponent_ge (by positivity : 0 < 1 / (2 : ℝ) ^ j) hz1 hq
  rw [Real.rpow_two] at hpow
  have he : (r / (2 : ℝ) ^ j) ^ q = r ^ q * (1 / (2 : ℝ) ^ j) ^ q := by
    rw [div_eq_mul_inv, Real.mul_rpow hr (by positivity), one_div]
  rw [he]
  calc
    _ ≤ (2 : ℝ) ^ j * (r ^ q * (1 / (2 : ℝ) ^ j) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hr q)) ht.le
    _ = r ^ q * (1 / 2 : ℝ) ^ j := by
      rw [show (1 / 2 : ℝ) ^ j = 1 / (2 : ℝ) ^ j by rw [div_pow, one_pow]]
      field_simp

lemma discovery_noise_sum {r q : ℝ} (hr : 0 ≤ r) (hq : 2 ≤ q)
    (σ u : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j * (repetitions σ u j : ℝ) *
      (r / (2 : ℝ) ^ j) ^ q) ≤ 132 * r ^ q := by
  have hpoint (j : ℕ) : (2 : ℝ) ^ j * (repetitions σ u j : ℝ) *
      (r / (2 : ℝ) ^ j) ^ q ≤ 33 * r ^ q * (((j : ℝ) + 1) * (1 / 2 : ℝ) ^ j) := by
    have hk : (repetitions σ u j : ℝ) ≤ 33 * ((j : ℝ) + 1) := by
      exact_mod_cast repetitions_fine σ u j
    calc
      _ = (repetitions σ u j : ℝ) * ((2 : ℝ) ^ j * (r / (2 : ℝ) ^ j) ^ q) := by ring
      _ ≤ (33 * ((j : ℝ) + 1)) * (r ^ q * (1 / 2 : ℝ) ^ j) :=
        mul_le_mul hk (dyadic_noise_power hr hq j) (by positivity) (by positivity)
      _ = _ := by ring
  have h := Finset.sum_le_sum (s := Finset.range (J + 1)) (fun j _ => hpoint j)
  rw [← Finset.mul_sum] at h
  exact h.trans (by nlinarith [weighted_half_sum_le (J + 1), Real.rpow_nonneg hr q])

lemma dyadic_ceil_lower (a : ℝ) :
    a ≤ (2 : ℝ) ^ ⌈Real.logb 2 (max 1 a)⌉₊ := by
  have hp : 0 < max 1 a := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hp).mp
    (Nat.le_ceil (Real.logb 2 (max 1 a)))
  rw [Real.rpow_natCast] at h
  exact (le_max_right _ _).trans h

lemma dyadic_ceil_upper (a : ℝ) :
    (2 : ℝ) ^ ⌈Real.logb 2 (max 1 a)⌉₊ ≤ 2 * max 1 a := by
  have hp : 0 < max 1 a := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hlog := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (le_max_left 1 a)
  have hc := Nat.ceil_lt_add_one hlog
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hc.le
  rw [Real.rpow_natCast, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hp,
    Real.rpow_one, mul_comm] at h
  exact h

lemma noiseLevel_power {σ u : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) :
    (4 : ℝ) ^ noiseLevel σ u ≤ 65536 * (1 + (σ / u) ^ 2) := by
  have h := dyadic_ceil_upper (128 * σ / u)
  change (2 : ℝ) ^ noiseLevel σ u ≤ 2 * max 1 (128 * σ / u) at h
  have ht : 0 ≤ (2 : ℝ) ^ noiseLevel σ u := by positivity
  have he : (4 : ℝ) ^ noiseLevel σ u = ((2 : ℝ) ^ noiseLevel σ u) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [he]
  have hr := div_nonneg hσ hu.le
  by_cases hlarge : 1 ≤ 128 * σ / u
  · rw [max_eq_right hlarge] at h
    have heq : 128 * σ / u = 128 * (σ / u) := by ring
    rw [heq] at h
    nlinarith
  · rw [max_eq_left (le_of_not_ge hlarge)] at h
    nlinarith [sq_nonneg (σ / u)]

lemma coarse_scale_ratio {σ u : ℝ} (hu : 0 < u) (j : ℕ)
    (hj : noiseLevel σ u ≤ j) :
    σ / (u * (2 : ℝ) ^ j) ≤ 1 / (128 * (2 : ℝ) ^ (j - noiseLevel σ u)) := by
  have hl := dyadic_ceil_lower (128 * σ / u)
  change 128 * σ / u ≤ (2 : ℝ) ^ noiseLevel σ u at hl
  have hs := (div_le_iff₀ hu).mp hl
  have hmul := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ (2 : ℝ) ^ (j - noiseLevel σ u))
  have he : (2 : ℝ) ^ noiseLevel σ u * 2 ^ (j - noiseLevel σ u) = 2 ^ j := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [he]

lemma coarse_scale_raw {σ u : ℝ} (hu : 0 < u) (j : ℕ)
    (hj : noiseLevel σ u ≤ j) : 128 * σ ≤ u * (2 : ℝ) ^ j := by
  have hl := dyadic_ceil_lower (128 * σ / u)
  change 128 * σ / u ≤ (2 : ℝ) ^ noiseLevel σ u at hl
  have hs := (div_le_iff₀ hu).mp hl
  have hp : (2 : ℝ) ^ noiseLevel σ u ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  nlinarith

lemma dyadic_block_confidence (h : ℕ) :
    1 / (128 * (2 : ℝ) ^ h) ≤ 1 / ((2 : ℝ) ^ (3 + h / 2)) ^ 2 := by
  have he : ((2 : ℝ) ^ (3 + h / 2)) ^ 2 = 2 ^ (6 + 2 * (h / 2)) := by
    rw [← pow_mul]
    congr 1
    omega
  have hl : 6 + 2 * (h / 2) ≤ 7 + h := by omega
  apply one_div_le_one_div_of_le (by positivity)
  rw [he]
  calc
    (2 : ℝ) ^ (6 + 2 * (h / 2)) ≤ 2 ^ (7 + h) := pow_le_pow_right₀ (by norm_num) hl
    _ = 128 * 2 ^ h := by rw [pow_add]; norm_num

lemma radius_homogeneous {σ u p : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) :
    radius σ p u = u * radius (σ / u) p 1 := by
  have hr : 0 ≤ σ / u + 1 := by positivity
  have he : σ + u = u * (σ / u + 1) := by field_simp
  have hbase : 256 * (σ + u) ^ p / u = u ^ (p - 1) * (256 * (σ / u + 1) ^ p) := by
    rw [he, Real.mul_rpow hu.le hr, Real.rpow_sub_one hu.ne']
    ring
  have hexp : (p - 1) * (1 / (p - 1)) = 1 := by field_simp [sub_ne_zero.mpr (ne_of_gt hp)]
  unfold radius
  rw [hbase, Real.mul_rpow (Real.rpow_nonneg hu.le _) (by positivity),
    ← Real.rpow_mul hu.le, hexp, Real.rpow_one]
  simp only [div_one]
  ring

lemma batch_expression_homogeneous {σ u p : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) :
    16384 * (2 * radius σ p u) ^ (2 - p) * σ ^ p / u ^ 2 =
      16384 * (2 * radius (σ / u) p 1) ^ (2 - p) * (σ / u) ^ p := by
  have hr : 0 ≤ σ / u := div_nonneg hσ hu.le
  have hR : 0 ≤ 2 * radius (σ / u) p 1 := by unfold radius; positivity
  have hC : 2 * radius σ p u = u * (2 * radius (σ / u) p 1) := by
    rw [radius_homogeneous hσ hu hp]
    ring
  have hσeq : σ = u * (σ / u) := by field_simp
  have hpow : σ ^ p = u ^ p * (σ / u) ^ p := by
    conv_lhs => rw [hσeq]
    exact Real.mul_rpow hu.le hr
  rw [hC, Real.mul_rpow hu.le hR, hpow]
  calc
    _ = 16384 * (u ^ (2 - p) * u ^ p) *
        (2 * radius (σ / u) p 1) ^ (2 - p) * (σ / u) ^ p / u ^ 2 := by ring
    _ = _ := by
      rw [← Real.rpow_add hu, sub_add_cancel, Real.rpow_two]
      field_simp

lemma unit_radius_bound {r p : ℝ} (hr : 0 ≤ r) (hp : 1 < p) (hp2 : p ≤ 2) :
    radius r p 1 ≤ 2 * (1024 : ℝ) ^ (1 / (p - 1)) * (max 1 r) ^ (p / (p - 1)) := by
  have hR : 0 ≤ max 1 r := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
  have hsum : r + 1 ≤ 2 * max 1 r := by linarith [le_max_left (1 : ℝ) r, le_max_right (1 : ℝ) r]
  have h2 : (2 : ℝ) ^ p ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp2
    norm_num at h
    exact h
  have hb : 256 * (r + 1) ^ p ≤ 1024 * (max 1 r) ^ p := by
    have h := Real.rpow_le_rpow (by positivity : 0 ≤ r + 1) hsum (by linarith : 0 ≤ p)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR] at h
    have hmul := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hR p)
    linarith
  have he : p * (1 / (p - 1)) = p / (p - 1) := by ring
  calc
    radius r p 1 = 2 * (256 * (r + 1) ^ p) ^ (1 / (p - 1)) := by simp [radius]
    _ ≤ 2 * (1024 * (max 1 r) ^ p) ^ (1 / (p - 1)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb (by positivity)) (by norm_num)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1024) (Real.rpow_nonneg hR p),
        ← Real.rpow_mul hR, he]
      ring

lemma unit_batch_bound {r p : ℝ} (hr : 0 ≤ r) (hp : 1 < p) (hp2 : p ≤ 2) :
    16384 * (2 * radius r p 1) ^ (2 - p) * r ^ p ≤
      (2 : ℝ) ^ (26 / (p - 1)) * (max 1 r) ^ (p / (p - 1)) := by
  let R := max 1 r
  have hR : 0 ≤ R := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
  have hd : 0 < p - 1 := by linarith
  have hd1 : p - 1 ≤ 1 := by linarith
  have ha : 0 ≤ 2 - p := by linarith
  have hC : 2 * radius r p 1 ≤ 4 * (1024 : ℝ) ^ (1 / (p - 1)) * R ^ (p / (p - 1)) := by
    have h := unit_radius_bound hr hp hp2
    dsimp [R]
    linarith
  have hpow := Real.rpow_le_rpow (by unfold radius; positivity : 0 ≤ 2 * radius r p 1) hC ha
  have hrpow := Real.rpow_le_rpow hr (le_max_right 1 r) (by linarith : 0 ≤ p)
  have hexp : p / (p - 1) * (2 - p) + p = p / (p - 1) := by field_simp; ring
  have h4 : (4 : ℝ) ^ (2 - p) ≤ 4 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4)
      (show 2 - p ≤ 1 by linarith)
  have h1024 : (1024 : ℝ) ^ ((1 / (p - 1)) * (2 - p)) ≤ 1024 ^ (1 / (p - 1)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hmul := mul_le_mul_of_nonneg_left (show 2 - p ≤ 1 by linarith) (le_of_lt (one_div_pos.mpr hd))
    simpa using hmul
  have hconstant : (65536 : ℝ) * 1024 ^ (1 / (p - 1)) ≤ 2 ^ (26 / (p - 1)) := by
    have he : (65536 : ℝ) * 1024 ^ (1 / (p - 1)) = 2 ^ (16 + 10 / (p - 1)) := by
      rw [show (65536 : ℝ) = 2 ^ (16 : ℝ) by norm_num,
        show (1024 : ℝ) = 2 ^ (10 : ℝ) by norm_num,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    rw [he]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply (le_div_iff₀ hd).mpr
    have he' : (16 + 10 / (p - 1)) * (p - 1) = 16 * (p - 1) + 10 := by field_simp
    rw [he']
    linarith
  calc
    _ ≤ 16384 * (4 * (1024 : ℝ) ^ (1 / (p - 1)) * R ^ (p / (p - 1))) ^ (2 - p) * R ^ p := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num)) hrpow
        (Real.rpow_nonneg hr _) (by positivity)
    _ = 16384 * (4 : ℝ) ^ (2 - p) * 1024 ^ ((1 / (p - 1)) * (2 - p)) * R ^ (p / (p - 1)) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hR _),
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1024), ← Real.rpow_mul hR]
      have hRp : R ^ (p / (p - 1) * (2 - p)) * R ^ p = R ^ (p / (p - 1)) := by
        rw [← Real.rpow_add (by dsimp [R]; positivity), hexp]
      calc
        _ = (16384 * 4 ^ (2 - p) * 1024 ^ ((1 / (p - 1)) * (2 - p))) *
          (R ^ (p / (p - 1) * (2 - p)) * R ^ p) := by ring
        _ = _ := by rw [hRp]
    _ ≤ 65536 * (1024 : ℝ) ^ (1 / (p - 1)) * R ^ (p / (p - 1)) := by
      have hm := mul_le_mul h4 h1024 (by positivity) (by norm_num : (0 : ℝ) ≤ 4)
      have hm' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 16384))
        (Real.rpow_nonneg hR (p / (p - 1)))
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hR _)

lemma blockSize_bound {σ u p : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2) :
    (blockSize σ p u : ℝ) ≤
      (2 : ℝ) ^ (28 / (p - 1)) * max 1 ((σ / u) ^ (p / (p - 1))) := by
  let r := σ / u
  let q := p / (p - 1)
  let B := (2 : ℝ) ^ (26 / (p - 1)) * max 1 (r ^ q)
  have hr : 0 ≤ r := div_nonneg hσ hu.le
  have hd : 0 < p - 1 := by linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hB : 1 ≤ B := by
    apply one_le_mul_of_one_le_of_one_le
    · exact Real.one_le_rpow (by norm_num) (by positivity)
    · exact le_max_left _ _
  have hconstant : 4 * (2 : ℝ) ^ (26 / (p - 1)) ≤ 2 ^ (28 / (p - 1)) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    apply (le_div_iff₀ hd).mpr
    have he : (2 + 26 / (p - 1)) * (p - 1) = 2 * (p - 1) + 26 := by field_simp
    rw [he]
    linarith
  have h4B : 4 * B ≤ (2 : ℝ) ^ (28 / (p - 1)) * max 1 (r ^ q) := by
    simpa only [B, mul_assoc] using mul_le_mul_of_nonneg_right hconstant
      (show 0 ≤ max 1 (r ^ q) by positivity)
  have hV : 16384 * (2 * radius σ p u) ^ (2 - p) * σ ^ p / u ^ 2 ≤ B := by
    rw [batch_expression_homogeneous hσ hu hp]
    have h := unit_batch_bound hr hp hp2
    rw [Real.rpow_max (by norm_num : (0 : ℝ) ≤ 1) hr hq, Real.one_rpow] at h
    exact h
  have hrad : 0 ≤ radius σ p u := (radius_pos hσ hu).le
  unfold blockSize
  split_ifs with hraw
  · simp only [Nat.cast_one]
    exact (show (1 : ℝ) ≤ 4 * B by linarith).trans h4B
  · have hn := Nat.ceil_lt_add_one (show 0 ≤ 16384 * (2 * radius σ p u) ^ (2 - p) * σ ^ p / u ^ 2 by positivity)
    unfold batchSize
    push_cast
    linarith


lemma calls_bound {σ u p : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2) (k : ℕ) :
    (calls σ p u k : ℝ) ≤ (k : ℝ) * (2 : ℝ) ^ (28 / (p - 1)) *
      (1 + (σ / u) ^ (p / (p - 1))) := by
  have h := blockSize_bound hσ hu hp hp2
  have hv : 0 ≤ (σ / u) ^ (p / (p - 1)) := Real.rpow_nonneg (div_nonneg hσ hu.le) _
  have hmax : max 1 ((σ / u) ^ (p / (p - 1))) ≤ 1 + (σ / u) ^ (p / (p - 1)) := by
    apply max_le <;> linarith
  have h' := h.trans (mul_le_mul_of_nonneg_left hmax (by positivity))
  unfold calls
  push_cast
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h' (Nat.cast_nonneg k)

lemma discovery_calls_sum {σ u p : ℝ} (hσ : 0 ≤ σ) (hu : 0 < u) (hp : 1 < p) (hp2 : p ≤ 2)
    (J : ℕ) :
    (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j *
      (calls σ p (u * (2 : ℝ) ^ j) (repetitions σ u j) : ℝ)) ≤
      (2 : ℝ) ^ (28 / (p - 1)) * (132 * (4 : ℝ) ^ noiseLevel σ u +
        194 * (2 : ℝ) ^ J + 132 * (σ / u) ^ (p / (p - 1))) := by
  let C := (2 : ℝ) ^ (28 / (p - 1))
  let q := p / (p - 1)
  have hq : 2 ≤ q := by
    apply (le_div_iff₀ (by linarith : 0 < p - 1)).mpr
    linarith
  have hpoint (j : ℕ) : (2 : ℝ) ^ j *
      (calls σ p (u * (2 : ℝ) ^ j) (repetitions σ u j) : ℝ) ≤
      C * ((2 : ℝ) ^ j * (repetitions σ u j : ℝ) +
        (2 : ℝ) ^ j * (repetitions σ u j : ℝ) * ((σ / u) / (2 : ℝ) ^ j) ^ q) := by
    have h := mul_le_mul_of_nonneg_left (calls_bound hσ (by positivity : 0 < u * (2 : ℝ) ^ j)
      hp hp2 (repetitions σ u j)) (by positivity : 0 ≤ (2 : ℝ) ^ j)
    have he : σ / (u * (2 : ℝ) ^ j) = (σ / u) / (2 : ℝ) ^ j := by ring
    rw [he] at h
    dsimp only [C, q]
    convert h using 1; ring
  have hk : (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j * (repetitions σ u j : ℝ)) ≤
      132 * (4 : ℝ) ^ noiseLevel σ u + 194 * (2 : ℝ) ^ J := by
    exact_mod_cast discovery_repetitions_sum σ u J
  have hn := discovery_noise_sum (div_nonneg hσ hu.le) hq σ u J
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1), C * ((2 : ℝ) ^ j * (repetitions σ u j : ℝ) +
        (2 : ℝ) ^ j * (repetitions σ u j : ℝ) * ((σ / u) / (2 : ℝ) ^ j) ^ q) :=
      Finset.sum_le_sum (fun j _ => hpoint j)
    _ = C * ((∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j * (repetitions σ u j : ℝ)) +
        ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j * (repetitions σ u j : ℝ) *
          ((σ / u) / (2 : ℝ) ^ j) ^ q) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hk hn) (by dsimp [C]; positivity)

end OracleTemplate.ScalarHeavyTailEstimator
