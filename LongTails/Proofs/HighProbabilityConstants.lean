import LongTails.Algorithms.HighProbabilityStationarity
import LongTails.Proofs.HighProbabilityEstimator
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.HighProbabilityConstants

open LongTails.Algorithms.HighProbabilityStationarity LongTails.Setups.HighProbabilityStationarity
open LongTails.Proofs.HighProbabilityEstimator

lemma pow_clog_le (n : ℕ) : 2 ^ Nat.clog 2 n ≤ 2 * n + 1 := by
  rcases Nat.lt_or_ge 1 n with hn | hn
  · have h := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hn
    have hpos := Nat.clog_pos (b := 2) (by norm_num) hn
    have : 2 ^ Nat.clog 2 n = 2 * 2 ^ (Nat.clog 2 n).pred := by
      rw [← pow_succ']
      congr 1
      exact (Nat.succ_pred_eq_of_pos hpos).symm
    omega
  · rw [Nat.clog_of_right_le_one hn]
    omega

lemma eight_mul_le_two_pow {n : ℕ} (hn : 6 ≤ n) : 8 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h8 : 8 ≤ 2 ^ n := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
    rw [pow_succ]
    omega

lemma exp_le_of_small {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1) : Real.exp c ≤ 1 / (1 - c) := by
  have h := Real.add_one_le_exp (-c)
  rw [le_div_iff₀ (by linarith)]
  have he : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos c]

lemma half_pow_le_exp (m : ℕ) : (1 / 2 : ℝ) ^ m ≤ Real.exp (-(m / 2 : ℝ)) := by
  have h2 : (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2)) := by
    have := Real.add_one_le_exp (-(1 / 2 : ℝ))
    linarith
  calc (1 / 2 : ℝ) ^ m ≤ Real.exp (-(1 / 2)) ^ m := pow_le_pow_left₀ (by norm_num) h2 m
    _ = Real.exp (-(m / 2 : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf


noncomputable def roundBound (k0 Λ n : ℕ) : ℝ :=
  if n ≤ Λ then (1 + Real.sqrt ((1 / 2 : ℝ) ^ (k0 * 2 ^ n))) ^ (2 ^ (Λ - n)) *
    Real.sqrt ((1 / 2 : ℝ) ^ (k0 * 2 ^ n)) ^ (2 ^ (Λ - n) / 6 + 1) else 0

lemma roundBound_nonneg (k0 Λ n : ℕ) : 0 ≤ roundBound k0 Λ n := by
  unfold roundBound
  split_ifs <;> positivity

lemma roundBound_le {Λ n : ℕ} (hn : n ≤ Λ) :
    roundBound 8 Λ n ≤ Real.exp (-(13 / 48 : ℝ) * 2 ^ Λ) := by
  unfold roundBound
  rw [ite_eq_left hn]
  set u : ℕ := 2 ^ n with hu
  set K : ℕ := 2 ^ (Λ - n) with hK
  have huK : u * K = 2 ^ Λ := by
    rw [hu, hK, ← pow_add, Nat.add_sub_cancel' hn]
  have hu1 : 1 ≤ u := Nat.one_le_two_pow
  have hsq : Real.sqrt ((1 / 2 : ℝ) ^ (8 * u)) = (1 / 2 : ℝ) ^ (4 * u) := by
    rw [show 8 * u = 2 * (4 * u) by ring, pow_mul', Real.sqrt_sq (by positivity)]
  rw [hsq]
  set x : ℝ := (1 / 2 : ℝ) ^ (4 * u) with hx
  have hx0 : 0 ≤ x := by positivity
  have hx16 : x ≤ 1 / 16 := by
    have : (1 / 2 : ℝ) ^ (4 * u) ≤ (1 / 2) ^ 4 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [hx]; norm_num at this ⊢; linarith
  have h1 : (1 + x) ^ K ≤ Real.exp (K / 16) := by
    calc (1 + x) ^ K ≤ Real.exp x ^ K := pow_le_pow_left₀ (by linarith)
          (by linarith [Real.add_one_le_exp x]) K
      _ = Real.exp (K * x) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (K / 16) := Real.exp_le_exp.mpr (by
          have : (0 : ℝ) ≤ K := by positivity
          nlinarith)
  have h2 : x ^ (K / 6 + 1) ≤ Real.exp (-(2 ^ Λ / 3 : ℝ)) := by
    have hpow : x ^ (K / 6 + 1) = (1 / 2 : ℝ) ^ (4 * u * (K / 6 + 1)) := by
      rw [hx, ← pow_mul]
    rw [hpow]
    refine (half_pow_le_exp _).trans (Real.exp_le_exp.mpr ?_)
    have h6 : u * K ≤ 6 * (u * (K / 6 + 1)) := by
      have := Nat.lt_div_mul_add (a := K) (b := 6) (by norm_num)
      nlinarith
    have : ((2 ^ Λ : ℕ) : ℝ) ≤ 6 * (u * (K / 6 + 1) : ℕ) := by
      rw [← huK]; exact_mod_cast h6
    push_cast at this ⊢
    nlinarith
  have hK2 : (K : ℝ) ≤ 2 ^ Λ := by
    have : K ≤ 2 ^ Λ := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)
    exact_mod_cast this
  calc (1 + x) ^ K * x ^ (K / 6 + 1) ≤ Real.exp (K / 16) * Real.exp (-(2 ^ Λ / 3 : ℝ)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = Real.exp (K / 16 - 2 ^ Λ / 3) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-(13 / 48 : ℝ) * 2 ^ Λ) := Real.exp_le_exp.mpr (by linarith)

variable {q : Params}

section Basic

variable (hv : 0 < q.L ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε ∧ 0 < q.δ ∧ q.δ ≤ 1 / 4)
include hv

lemma confidence_ge : 4 ≤ confidence q := by
  unfold confidence
  have h64 : (64 : ℝ) ≤ 16 / q.δ := by
    rw [le_div_iff₀ hv.2.2.2.2.1]; linarith [hv.2.2.2.2.2]
  have hl : Real.log 64 ≤ Real.log (16 / q.δ) := Real.log_le_log (by norm_num) h64
  have h6 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_gt_d9]

lemma exp_neg_confidence : Real.exp (-confidence q) = q.δ / 16 := by
  unfold confidence
  rw [Real.exp_neg, Real.exp_log (by have := hv.2.2.2.2.1; positivity)]
  field_simp

lemma eps_le_noise : q.ε ≤ noiseScale q := by unfold noiseScale; linarith [hv.2.1]

lemma sigma_le_noise : q.σ ≤ noiseScale q := by unfold noiseScale; linarith [hv.2.2.2.1]

lemma noise_pos : 0 < noiseScale q := lt_of_lt_of_le hv.2.2.2.1 (eps_le_noise hv)

omit hv in
lemma eps_le_grad : q.ε ≤ gradientScale q := by
  unfold gradientScale; linarith [Real.sqrt_nonneg (q.L * q.Δ)]

lemma grad_pos : 0 < gradientScale q := lt_of_lt_of_le hv.2.2.2.1 (eps_le_grad (q := q))

lemma radius_pos : 0 < radius q := by
  unfold radius; have := noise_pos hv; have := hv.2.2.2.1; positivity

lemma radius_ge : 2 ^ 20 * noiseScale q ≤ radius q := by
  unfold radius
  have hS := noise_pos hv
  have hSe := eps_le_noise hv
  have he := hv.2.2.2.1
  rw [le_div_iff₀ he]
  nlinarith

lemma radius_eq : radius q * q.ε = 2 ^ 20 * noiseScale q ^ 2 := by
  unfold radius; field_simp [hv.2.2.2.1.ne']

lemma steps_ge : 2 ^ 20 * (q.L * q.Δ / q.ε ^ 2 + confidence q + 1) ≤ (steps q : ℝ) := by
  unfold steps baseSteps
  push_cast
  linarith [Nat.le_ceil (2 ^ 20 * (q.L * q.Δ / q.ε ^ 2 + confidence q + 1))]

lemma steps_le : (steps q : ℝ) ≤ 2 ^ 20 * (q.L * q.Δ / q.ε ^ 2 + confidence q + 1) + 2 := by
  unfold steps baseSteps
  have hnn : 0 ≤ 2 ^ 20 * (q.L * q.Δ / q.ε ^ 2 + confidence q + 1) := by
    have := confidence_ge hv
    have : 0 ≤ q.L * q.Δ / q.ε ^ 2 := div_nonneg (mul_nonneg hv.1.le hv.2.2.1) (sq_nonneg _)
    positivity
  push_cast
  linarith [Nat.ceil_lt_add_one hnn]

omit hv in
lemma steps_pos : (0 : ℝ) < steps q := by unfold steps; positivity

omit hv in
lemma clip_ge : 2 ^ 40 * noiseScale q ^ 2 / q.ε ^ 2 ≤ (clipSize q : ℝ) := by
  unfold clipSize; exact Nat.le_ceil _

lemma clip_le : (clipSize q : ℝ) ≤ 2 ^ 41 * noiseScale q ^ 2 / q.ε ^ 2 := by
  unfold clipSize
  have he := hv.2.2.2.1
  have hS := eps_le_noise hv
  have h1 : 1 ≤ noiseScale q ^ 2 / q.ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hnn : 0 ≤ 2 ^ 40 * noiseScale q ^ 2 / q.ε ^ 2 := by have := noise_pos hv; positivity
  have h := Nat.ceil_lt_add_one hnn
  have h2 : 2 ^ 41 * noiseScale q ^ 2 / q.ε ^ 2 = 2 ^ 40 * noiseScale q ^ 2 / q.ε ^ 2 +
      2 ^ 40 * (noiseScale q ^ 2 / q.ε ^ 2) := by ring
  rw [h2]
  nlinarith

lemma clip_pos : 0 < clipSize q := by
  have h := clip_ge (q := q)
  have : 0 < 2 ^ 40 * noiseScale q ^ 2 / q.ε ^ 2 := by
    have := noise_pos hv; have := hv.2.2.2.1; positivity
  exact_mod_cast lt_of_lt_of_le this h

omit hv in
lemma pilot_ge : 2 ^ 24 * (noiseScale q ^ 2 / q.ε ^ 2 +
    gradientScale q * (confidence q + 4) / (steps q * q.ε)) ≤ (pilotSize q : ℝ) := by
  unfold pilotSize; exact Nat.le_ceil _

lemma noise_ratio_ge : 1 ≤ noiseScale q ^ 2 / q.ε ^ 2 := by
  have he := hv.2.2.2.1
  have hS := eps_le_noise hv
  rw [le_div_iff₀ (by positivity)]; nlinarith

lemma pilot_ge_noise : 2 ^ 24 * (noiseScale q ^ 2 / q.ε ^ 2) ≤ (pilotSize q : ℝ) := by
  have h := pilot_ge (q := q)
  have : 0 ≤ gradientScale q * (confidence q + 4) / (steps q * q.ε) := by
    have := grad_pos hv; have := confidence_ge hv; have := steps_pos (q := q); have := hv.2.2.2.1
    positivity
  nlinarith

lemma pilot_ge_nat : 2 ^ 24 ≤ pilotSize q := by
  have h := pilot_ge_noise hv
  have h1 := noise_ratio_ge hv
  have : (2 : ℝ) ^ 24 ≤ pilotSize q := by nlinarith
  exact_mod_cast this

lemma stepSize_nonneg : 0 ≤ stepSize q := by
  unfold stepSize
  have := hv.1; have := hv.2.2.1; have := hv.2.2.2.1; have := steps_pos (q := q)
  positivity

end Basic

noncomputable def scales (q : Params) : ℕ := Nat.clog 2 ⌈3 * gradientScale q / radius q⌉₊

noncomputable def counts (q : Params) (j : ℕ) : ℝ :=
  steps q * q.ε / (2 ^ 16 * radius q) * ((1 / 4 : ℝ) ^ j + (1 / 2 : ℝ) ^ scales q)

noncomputable def halfExp (q : Params) (j : ℕ) : ℕ := pilotSize q * (j + 15) / 2

lemma W_bound (T ε B : ℝ) (hT : 0 ≤ T) (hε : 0 < ε) (hB : 0 < B) (J : ℕ) :
    2 * (T * ε / 512) + ∑ j ∈ Finset.range (J + 1),
      8 * (2 ^ j * B) * (T * ε / (2 ^ 16 * B) * ((1 / 4 : ℝ) ^ j + (1 / 2 : ℝ) ^ J)) ≤
        T * ε / 128 := by
  have hterm (j : ℕ) : 8 * (2 ^ j * B) * (T * ε / (2 ^ 16 * B) * ((1 / 4 : ℝ) ^ j + (1 / 2 : ℝ) ^ J)) =
      T * ε / 2 ^ 13 * ((1 / 2 : ℝ) ^ j + 2 ^ j * (1 / 2 : ℝ) ^ J) := by
    have h4 : (1 / 4 : ℝ) ^ j = (1 / 2) ^ j * (1 / 2) ^ j := by rw [← mul_pow]; norm_num
    have h2 : (2 : ℝ) ^ j * (1 / 2) ^ j = 1 := by rw [← mul_pow]; norm_num
    rw [h4]
    field_simp
    have : (2 : ℝ) ^ j * ((1 / 2) ^ j * (1 / 2) ^ j) = (1 / 2) ^ j := by
      rw [← mul_assoc, h2, one_mul]
    nlinarith [this]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.mul_sum, Finset.sum_add_distrib,
    ← Finset.sum_mul]
  have hg1 := sum_geometric_two_le (J + 1)
  have hg2 : (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j) = 2 ^ (J + 1) - 1 := by
    rw [geom_sum_eq (by norm_num)]; ring
  have hg3 : (2 : ℝ) ^ (J + 1) * (1 / 2) ^ J = 2 := by
    rw [pow_succ, mul_comm ((2 : ℝ) ^ J) 2, mul_assoc, ← mul_pow]; norm_num
  have hg4 : (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j) * (1 / 2) ^ J ≤ 2 := by
    rw [hg2]; nlinarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) J]
  have hc : 0 ≤ T * ε / 2 ^ 13 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hg1 hg4) hc]

lemma descent_room {L Δ ε G T : ℝ} (hL : 0 < L) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hG : Real.sqrt (L * Δ) + ε ≤ G) (hT : 8192 * (L * Δ / ε ^ 2 + 1) ≤ T) :
    let η := 128 * (Δ + ε ^ 2 / L) / (T * ε)
    Δ + η * (T * ε / 128) + T * (L / 2 * η ^ 2) ≤ η * (3 * T * ε / 128) ∧
      2 * L * (Δ + η * (T * ε / 128) + T * (L / 2 * η ^ 2)) ≤ (3 * G) ^ 2 := by
  intro η
  have hTpos : 0 < T := by
    have : 0 ≤ L * Δ / ε ^ 2 := div_nonneg (mul_nonneg hL.le hΔ) (sq_nonneg _)
    linarith
  obtain ⟨D, hD⟩ : ∃ D, D = Δ + ε ^ 2 / L := ⟨_, rfl⟩
  have hεL : 0 < ε ^ 2 / L := by positivity
  have hDpos : 0 < D := by rw [hD]; linarith
  have hηD : η = 128 * D / (T * ε) := by rw [hD]
  have hLL : L * (ε ^ 2 / L) = ε ^ 2 := by field_simp
  have hLD : L * D = L * Δ + ε ^ 2 := by rw [hD, mul_add, hLL]
  have h1 : η * (T * ε / 128) = D := by
    rw [hηD]
    field_simp
  have hηnn : 0 ≤ η := by rw [hηD]; positivity
  have hLη : T * (L / 2 * η) ≤ T * ε / 128 := by
    have e : T * (L / 2 * η) = 64 * (L * D) / ε := by
      rw [hηD]
      field_simp
      ring
    rw [e, hLD, div_le_div_iff₀ hε (by norm_num)]
    have h := mul_le_mul_of_nonneg_right hT (sq_nonneg ε)
    have he : (L * Δ / ε ^ 2 + 1) * ε ^ 2 = L * Δ + ε ^ 2 := by field_simp
    nlinarith
  have h2 : T * (L / 2 * η ^ 2) ≤ D := by
    have : T * (L / 2 * η ^ 2) = η * (T * (L / 2 * η)) := by ring
    rw [this]
    calc η * (T * (L / 2 * η)) ≤ η * (T * ε / 128) := mul_le_mul_of_nonneg_left hLη hηnn
      _ = D := h1
  have h3 : η * (3 * T * ε / 128) = 3 * D := by rw [← h1]; ring
  have hΔD : Δ ≤ D := by rw [hD]; linarith
  refine ⟨by rw [h1, h3]; linarith, ?_⟩
  have hG0 : 0 ≤ Real.sqrt (L * Δ) + ε := by positivity
  have hG2 : (Real.sqrt (L * Δ) + ε) ^ 2 ≤ G ^ 2 := pow_le_pow_left₀ hG0 hG 2
  have hsq : Real.sqrt (L * Δ) ^ 2 = L * Δ := Real.sq_sqrt (mul_nonneg hL.le hΔ)
  rw [h1]
  nlinarith [Real.sqrt_nonneg (L * Δ)]

variable (hv : 0 < q.L ∧ 0 ≤ q.σ ∧ 0 ≤ q.Δ ∧ 0 < q.ε ∧ 0 < q.δ ∧ q.δ ≤ 1 / 4)
include hv

lemma scales_cover : 3 * gradientScale q ≤ 4 * (2 ^ scales q * radius q) := by
  have hB := radius_pos hv
  have h1 : 3 * gradientScale q / radius q ≤ (⌈3 * gradientScale q / radius q⌉₊ : ℝ) :=
    Nat.le_ceil _
  have h2 : (⌈3 * gradientScale q / radius q⌉₊ : ℝ) ≤ 2 ^ scales q := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have h3 : 3 * gradientScale q ≤ 2 ^ scales q * radius q := by
    rw [div_le_iff₀ hB] at h1; nlinarith
  nlinarith

lemma scales_le_cap : 2 ^ scales q * radius q ≤ 6 * gradientScale q + 3 * radius q := by
  have hB := radius_pos hv
  have hG := grad_pos hv
  have h1 : (2 : ℝ) ^ scales q ≤ 2 * ⌈3 * gradientScale q / radius q⌉₊ + 1 := by
    exact_mod_cast pow_clog_le _
  have h2 : (⌈3 * gradientScale q / radius q⌉₊ : ℝ) < 3 * gradientScale q / radius q + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h3 : (2 : ℝ) ^ scales q < 2 * (3 * gradientScale q / radius q) + 3 := by linarith
  have h4 : (2 * (3 * gradientScale q / radius q) + 3) * radius q =
      6 * gradientScale q + 3 * radius q := by field_simp; ring
  nlinarith

lemma scales_le_levels : scales q ≤ levels q := by
  have hB := radius_pos hv
  have he := hv.2.2.2.1
  have hS := eps_le_noise hv
  have hG := grad_pos hv
  have hr : 3 * gradientScale q / radius q ≤ gradientScale q / q.ε := by
    unfold radius
    rw [div_le_div_iff₀ (by have := noise_pos hv; positivity) he]
    have : 3 * q.ε ^ 2 ≤ 2 ^ 20 * noiseScale q ^ 2 := by nlinarith
    have h' : 3 * gradientScale q * q.ε * q.ε ≤ gradientScale q * (2 ^ 20 * noiseScale q ^ 2) := by
      nlinarith
    calc 3 * gradientScale q * q.ε = 3 * gradientScale q * q.ε * q.ε / q.ε := by field_simp
      _ ≤ gradientScale q * (2 ^ 20 * noiseScale q ^ 2) / q.ε :=
          div_le_div_of_nonneg_right h' he.le
      _ = gradientScale q * (2 ^ 20 * noiseScale q ^ 2 / q.ε) := by ring
  unfold scales levels
  have := Nat.clog_mono_right 2 (Nat.ceil_mono hr)
  omega

lemma ok_tail_const :
    (steps q : ℝ) * (Real.log 5 + (clipRadius q.σ (radius q) (clipSize q) 0 / clipSize q +
      12 * radius q / clipSize q) / (2 * (12 * radius q / clipSize q))) -
      1 / (2 * (12 * radius q / clipSize q)) * (steps q * q.ε / 512) ≤ -confidence q := by
  have hB := radius_pos hv
  have hmc : (0 : ℝ) < clipSize q := by exact_mod_cast clip_pos hv
  have he := hv.2.2.2.1
  have hS := noise_pos hv
  have hσ := hv.2.1
  have hσS := sigma_le_noise hv
  have hT := steps_pos (q := q)
  have hTl := steps_ge hv
  have hl := confidence_ge hv
  have hBeq := radius_eq hv
  have hmcl := clip_le hv
  have hmcg := clip_ge (q := q)
  have hratio : (clipRadius q.σ (radius q) (clipSize q) 0 / clipSize q + 12 * radius q / clipSize q) /
      (2 * (12 * radius q / clipSize q)) =
      (3 * Real.sqrt (clipSize q) * q.σ + 22 * clipSize q * q.σ ^ 2 / radius q) / (24 * radius q) + 1 := by
    unfold clipRadius
    field_simp
    ring
  have hsq : Real.sqrt (clipSize q) ≤ 2 ^ 21 * noiseScale q / q.ε := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (2 ^ 21 * noiseScale q / q.ε) ^ 2 = 2 ^ 42 * noiseScale q ^ 2 / q.ε ^ 2 := by
      field_simp
    rw [this]
    have : 0 ≤ 2 ^ 41 * noiseScale q ^ 2 / q.ε ^ 2 := by positivity
    have h2 : 2 ^ 42 * noiseScale q ^ 2 / q.ε ^ 2 = 2 * (2 ^ 41 * noiseScale q ^ 2 / q.ε ^ 2) := by ring
    linarith
  have hA : 3 * Real.sqrt (clipSize q) * q.σ ≤ 6 * radius q := by
    have : 3 * Real.sqrt (clipSize q) * q.σ ≤ 3 * (2 ^ 21 * noiseScale q / q.ε) * noiseScale q := by
      have := Real.sqrt_nonneg (clipSize q)
      have h1 : Real.sqrt (clipSize q) * q.σ ≤ (2 ^ 21 * noiseScale q / q.ε) * noiseScale q :=
        mul_le_mul hsq hσS hσ (by positivity)
      linarith
    have h2 : 3 * (2 ^ 21 * noiseScale q / q.ε) * noiseScale q = 6 * radius q := by
      unfold radius; field_simp; ring
    linarith
  have hC : 22 * clipSize q * q.σ ^ 2 / radius q ≤ 44 * radius q := by
    rw [div_le_iff₀ hB]
    have hσ2 : q.σ ^ 2 ≤ noiseScale q ^ 2 := pow_le_pow_left₀ hσ hσS 2
    have h1 : clipSize q * q.σ ^ 2 ≤ 2 ^ 41 * noiseScale q ^ 2 / q.ε ^ 2 * noiseScale q ^ 2 :=
      mul_le_mul hmcl hσ2 (sq_nonneg _) (by positivity)
    have h2 : 2 ^ 41 * noiseScale q ^ 2 / q.ε ^ 2 * noiseScale q ^ 2 = 2 * (radius q * radius q) := by
      unfold radius; field_simp
    nlinarith
  have hfrac : (3 * Real.sqrt (clipSize q) * q.σ + 22 * clipSize q * q.σ ^ 2 / radius q) /
      (24 * radius q) ≤ 50 / 24 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hlog5 : Real.log 5 ≤ 4 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num); linarith
  have hthe : 1 / (2 * (12 * radius q / clipSize q)) * (steps q * q.ε / 512) =
      clipSize q * q.ε / radius q * (steps q / 12288) := by
    field_simp; ring
  have hmcB : 2 ^ 20 ≤ clipSize q * q.ε / radius q := by
    rw [le_div_iff₀ hB]
    have : 2 ^ 20 * radius q = 2 ^ 40 * noiseScale q ^ 2 / q.ε ^ 2 * q.ε := by
      unfold radius; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right hmcg he.le
  rw [hratio, hthe]
  have hTe : (2 : ℝ) ^ 20 * (steps q / 12288) ≤ clipSize q * q.ε / radius q * (steps q / 12288) :=
    mul_le_mul_of_nonneg_right hmcB (by positivity)
  have hTl' : confidence q ≤ steps q := by
    have : 0 ≤ q.L * q.Δ / q.ε ^ 2 := div_nonneg (mul_nonneg hv.1.le hv.2.2.1) (sq_nonneg _)
    nlinarith
  nlinarith

lemma halfExp_ge (j : ℕ) : pilotSize q + 2 * j + 13 ≤ halfExp q j := by
  have h := pilot_ge_nat hv
  unfold halfExp
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

omit hv in
lemma halfExp_two_le (j : ℕ) : 2 * halfExp q j ≤ pilotSize q * (j + 15) := by
  unfold halfExp
  exact Nat.mul_div_le _ _

lemma halfExp_real_ge (j : ℕ) : (pilotSize q : ℝ) * (j + 14) / 2 ≤ halfExp q j := by
  have h := pilot_ge_nat hv
  have h2 : pilotSize q * (j + 14) ≤ 2 * halfExp q j := by
    unfold halfExp
    have := Nat.lt_div_mul_add (a := pilotSize q * (j + 15)) (b := 2) (by norm_num)
    nlinarith
  have : ((pilotSize q * (j + 14) : ℕ) : ℝ) ≤ ((2 * halfExp q j : ℕ) : ℝ) := by exact_mod_cast h2
  push_cast at this
  linarith

lemma scale_prob (j : ℕ) :
    (10 * noiseScale q / (2 ^ j * radius q / 2)) ^ pilotSize q ≤
      (1 / 2 : ℝ) ^ (2 * halfExp q j) := by
  have hB := radius_pos hv
  have hS := noise_pos hv
  have he := hv.2.2.2.1
  have hSe := eps_le_noise hv
  have hbase : 10 * noiseScale q / (2 ^ j * radius q / 2) ≤ (1 / 2 : ℝ) ^ (j + 15) := by
    rw [div_le_iff₀ (by positivity)]
    have hR : 2 ^ 20 * noiseScale q ≤ radius q := radius_ge hv
    have h2 : (1 / 2 : ℝ) ^ (j + 15) * (2 ^ j * radius q / 2) = radius q / 2 ^ 16 := by
      rw [pow_add, show ((1 / 2 : ℝ) ^ 15) = 1 / 2 ^ 15 by norm_num]
      have : (1 / 2 : ℝ) ^ j * 2 ^ j = 1 := by rw [← mul_pow]; norm_num
      field_simp
      nlinarith [this]
    rw [h2, le_div_iff₀ (by positivity)]
    nlinarith
  have hnn : 0 ≤ 10 * noiseScale q / (2 ^ j * radius q / 2) := by positivity
  calc (10 * noiseScale q / (2 ^ j * radius q / 2)) ^ pilotSize q ≤
        ((1 / 2 : ℝ) ^ (j + 15)) ^ pilotSize q := pow_le_pow_left₀ hnn hbase _
    _ = (1 / 2 : ℝ) ^ (pilotSize q * (j + 15)) := by rw [← pow_mul, mul_comm]
    _ ≤ (1 / 2 : ℝ) ^ (2 * halfExp q j) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (halfExp_two_le (q := q) j)

lemma pilot_mass : 2 ^ 24 * (confidence q + 1) * (radius q + gradientScale q) ≤
    pilotSize q * steps q * q.ε := by
  have hp := pilot_ge (q := q)
  have hT := steps_pos (q := q)
  have hTl := steps_ge hv
  have he := hv.2.2.2.1
  have hl := confidence_ge hv
  have hG := grad_pos hv
  have h1 : (pilotSize q : ℝ) * steps q * q.ε ≥
      2 ^ 24 * (steps q * noiseScale q ^ 2 / q.ε + gradientScale q * (confidence q + 4)) := by
    have := mul_le_mul_of_nonneg_right hp (show 0 ≤ (steps q : ℝ) * q.ε by positivity)
    have he2 : 2 ^ 24 * (noiseScale q ^ 2 / q.ε ^ 2 + gradientScale q * (confidence q + 4) /
        (steps q * q.ε)) * (steps q * q.ε) =
        2 ^ 24 * (steps q * noiseScale q ^ 2 / q.ε + gradientScale q * (confidence q + 4)) := by
      field_simp
    nlinarith
  have h2 : (confidence q + 1) * radius q ≤ steps q * noiseScale q ^ 2 / q.ε := by
    unfold radius
    have : (confidence q + 1) * 2 ^ 20 ≤ steps q := by
      have : 0 ≤ q.L * q.Δ / q.ε ^ 2 := div_nonneg (mul_nonneg hv.1.le hv.2.2.1) (sq_nonneg _)
      nlinarith
    have hS := noise_pos hv
    calc (confidence q + 1) * (2 ^ 20 * noiseScale q ^ 2 / q.ε) =
          (confidence q + 1) * 2 ^ 20 * (noiseScale q ^ 2 / q.ε) := by ring
      _ ≤ steps q * (noiseScale q ^ 2 / q.ε) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  nlinarith

lemma scale_term (j : ℕ) :
    (steps q : ℝ) * (1 / 2 : ℝ) ^ halfExp q j - halfExp q j * Real.log 2 * counts q j ≤
      -(confidence q + j + 1) := by
  have hB := radius_pos hv
  have hS := noise_pos hv
  have he := hv.2.2.2.1
  have hT := steps_pos (q := q)
  have hl := confidence_ge hv
  have hG := grad_pos hv
  have hlog : (1 / 2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hn1 : (pilotSize q : ℝ) + 2 * j + 13 ≤ halfExp q j := by
    exact_mod_cast halfExp_ge hv j
  have hmp := pilot_ge_noise hv
  have hmpn := pilot_ge_nat hv
  set c := (steps q : ℝ) * q.ε / (2 ^ 16 * radius q) with hc
  have hcpos : 0 < c := by positivity
  set n : ℝ := (halfExp q j : ℝ) with hn
  have hnpos : 1 ≤ n := by
    have : (2 : ℝ) ^ 24 ≤ pilotSize q := by exact_mod_cast hmpn
    linarith
  have hfirst : (steps q : ℝ) * (1 / 2 : ℝ) ^ halfExp q j ≤ n * Real.log 2 * (c * (1 / 4) ^ j) := by
    have hpow : (1 / 2 : ℝ) ^ halfExp q j ≤ (1 / 2) ^ (pilotSize q + 2 * j + 13) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (halfExp_ge hv j)
    have hsplit : (1 / 2 : ℝ) ^ (pilotSize q + 2 * j + 13) =
        (1 / 2) ^ pilotSize q * (1 / 4) ^ j / 8192 := by
      rw [pow_add, pow_add, pow_mul]
      ring
    have h2mp : (2 : ℝ) ^ 24 * (noiseScale q ^ 2 / q.ε ^ 2) ≤ 2 ^ pilotSize q := by
      have h := Nat.lt_two_pow_self (n := pilotSize q)
      have : (pilotSize q : ℝ) ≤ 2 ^ pilotSize q := by exact_mod_cast h.le
      linarith
    have hhalf : (1 / 2 : ℝ) ^ pilotSize q * 2 ^ pilotSize q = 1 := by
      rw [← mul_pow]; norm_num
    have hkey : (1 / 2 : ℝ) ^ pilotSize q * (2 ^ 24 * (noiseScale q ^ 2 / q.ε ^ 2)) ≤ 1 := by
      calc (1 / 2 : ℝ) ^ pilotSize q * (2 ^ 24 * (noiseScale q ^ 2 / q.ε ^ 2)) ≤
            (1 / 2) ^ pilotSize q * 2 ^ pilotSize q :=
            mul_le_mul_of_nonneg_left h2mp (by positivity)
        _ = 1 := hhalf
    have hcB : c = steps q * q.ε ^ 2 / (2 ^ 36 * noiseScale q ^ 2) := by
      rw [hc]; unfold radius; field_simp
    have h4 : 0 < (1 / 4 : ℝ) ^ j := by positivity
    calc (steps q : ℝ) * (1 / 2 : ℝ) ^ halfExp q j ≤
          steps q * ((1 / 2) ^ pilotSize q * (1 / 4) ^ j / 8192) := by
          rw [← hsplit]; exact mul_le_mul_of_nonneg_left hpow hT.le
      _ ≤ 1 * (1 / 2) * (c * (1 / 4) ^ j) := by
          rw [hcB]
          have hR : (1 / 2 : ℝ) ^ pilotSize q ≤ q.ε ^ 2 / (2 ^ 24 * noiseScale q ^ 2) := by
            rw [le_div_iff₀ (by positivity)]
            have hm := mul_le_mul_of_nonneg_right hkey (sq_nonneg q.ε)
            have he2 : (1 / 2 : ℝ) ^ pilotSize q * (2 ^ 24 * (noiseScale q ^ 2 / q.ε ^ 2)) * q.ε ^ 2 =
                (1 / 2 : ℝ) ^ pilotSize q * (2 ^ 24 * noiseScale q ^ 2) := by
              rw [mul_assoc, mul_assoc, div_mul_cancel₀ _ (by positivity)]
            linarith
          have : (steps q : ℝ) * ((1 / 2) ^ pilotSize q * (1 / 4) ^ j / 8192) ≤
              steps q * (q.ε ^ 2 / (2 ^ 24 * noiseScale q ^ 2) * (1 / 4) ^ j / 8192) := by
            gcongr
          refine this.trans (le_of_eq ?_)
          ring
      _ ≤ n * Real.log 2 * (c * (1 / 4) ^ j) := by
          have : 1 * (1 / 2 : ℝ) ≤ n * Real.log 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this (by positivity)
  have hsecond : confidence q + j + 1 ≤ n * Real.log 2 * (c * (1 / 2) ^ scales q) := by
    have hcap := scales_le_cap hv
    have hmass := pilot_mass hv
    have hnr := halfExp_real_ge hv j
    have hmM : 42 * (confidence q + 1) ≤ pilotSize q * (c * (1 / 2) ^ scales q) := by
      have h2 : c * (1 / 2) ^ scales q = steps q * q.ε / (2 ^ 16 * (2 ^ scales q * radius q)) := by
        rw [hc, one_div_pow]
        ring
      rw [h2]
      have hcp : 0 < 2 ^ scales q * radius q := by positivity
      rw [show (pilotSize q : ℝ) * (steps q * q.ε / (2 ^ 16 * (2 ^ scales q * radius q))) =
        pilotSize q * steps q * q.ε / (2 ^ 16 * (2 ^ scales q * radius q)) by ring]
      rw [le_div_iff₀ (by positivity)]
      have : 2 ^ scales q * radius q ≤ 6 * (radius q + gradientScale q) := by linarith
      have hm := mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ confidence q + 1 by linarith)
      nlinarith
    have hpos : 0 ≤ c * (1 / 2) ^ scales q := by positivity
    have : (pilotSize q : ℝ) * (j + 14) / 2 * (c * (1 / 2) ^ scales q) ≤
        n * (c * (1 / 2) ^ scales q) := mul_le_mul_of_nonneg_right hnr hpos
    have hj : (0 : ℝ) ≤ j := by positivity
    have hn0 : 0 ≤ n := by linarith
    have s1 := mul_nonneg (mul_nonneg hn0 hpos) (show (0 : ℝ) ≤ Real.log 2 - 1 / 2 by linarith)
    have s3 := mul_le_mul_of_nonneg_right hmM (show (0 : ℝ) ≤ j + 14 by linarith)
    have s4 := mul_nonneg (show (0 : ℝ) ≤ confidence q by linarith) hj
    nlinarith
  have hsplit : counts q j = c * (1 / 4) ^ j + c * (1 / 2) ^ scales q := by
    unfold counts; rw [hc]; ring
  rw [hsplit]
  nlinarith

lemma scale_sum :
    ∑ j ∈ Finset.range (scales q + 1), Real.exp ((steps q : ℝ) * (1 / 2 : ℝ) ^ halfExp q j -
      halfExp q j * Real.log 2 * counts q j) ≤ Real.exp (-confidence q) := by
  have he1 : Real.exp (-1) ≤ 1 / 2 := by
    have := Real.add_one_le_exp (1 : ℝ)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  calc ∑ j ∈ Finset.range (scales q + 1), Real.exp ((steps q : ℝ) * (1 / 2 : ℝ) ^ halfExp q j -
        halfExp q j * Real.log 2 * counts q j) ≤
      ∑ j ∈ Finset.range (scales q + 1), Real.exp (-confidence q) * (1 / 2) * (1 / 2 : ℝ) ^ j := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine (Real.exp_le_exp.mpr (scale_term hv j)).trans ?_
        have : Real.exp (-(confidence q + j + 1)) =
            Real.exp (-confidence q) * Real.exp (-1) * Real.exp (-1) ^ j := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; ring_nf
        rw [this]
        have h0 : 0 ≤ Real.exp (-1) := (Real.exp_pos _).le
        gcongr
    _ = Real.exp (-confidence q) * (1 / 2) * ∑ j ∈ Finset.range (scales q + 1), (1 / 2 : ℝ) ^ j := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-confidence q) * (1 / 2) * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
    _ = Real.exp (-confidence q) := by ring

omit hv in
lemma rounds_pow_ge : 64 * confidence q ≤ (2 : ℝ) ^ rounds q := by
  have h1 : 64 * confidence q ≤ (⌈64 * confidence q⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈64 * confidence q⌉₊ : ℝ) ≤ 2 ^ rounds q := by
    unfold rounds; exact_mod_cast Nat.le_pow_clog (by norm_num) _
  linarith

lemma rounds_pow_le : (2 : ℝ) ^ rounds q ≤ 2 ^ 8 * confidence q := by
  have hl := confidence_ge hv
  have h1 : (2 : ℝ) ^ rounds q ≤ 2 * ⌈64 * confidence q⌉₊ + 1 := by
    unfold rounds; exact_mod_cast pow_clog_le _
  have h2 : (⌈64 * confidence q⌉₊ : ℝ) < 64 * confidence q + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  nlinarith

lemma rounds_ge : 6 ≤ rounds q := by
  by_contra h
  push Not at h
  have hl := confidence_ge hv
  have h1 := rounds_pow_ge (q := q)
  have h2 : (2 : ℝ) ^ rounds q ≤ 2 ^ 5 := pow_le_pow_right₀ (by norm_num) (by omega)
  nlinarith

lemma rounds_sum :
    ∑ n ∈ Finset.range (rounds q + 1), roundBound 8 (rounds q) n ≤ Real.exp (-confidence q) := by
  have hl := confidence_ge hv
  have hJ := rounds_pow_ge (q := q)
  have h8 : 8 * rounds q ≤ 2 ^ rounds q := eight_mul_le_two_pow (rounds_ge hv)
  have h8r : (8 : ℝ) * rounds q ≤ 2 ^ rounds q := by exact_mod_cast h8
  calc ∑ n ∈ Finset.range (rounds q + 1), roundBound 8 (rounds q) n ≤
        ∑ _n ∈ Finset.range (rounds q + 1), Real.exp (-(13 / 48 : ℝ) * 2 ^ rounds q) :=
        Finset.sum_le_sum fun n hn => roundBound_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))
    _ = (rounds q + 1) * Real.exp (-(13 / 48 : ℝ) * 2 ^ rounds q) := by simp
    _ ≤ Real.exp (rounds q) * Real.exp (-(13 / 48 : ℝ) * 2 ^ rounds q) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (rounds q : ℝ)])
          (Real.exp_pos _).le
    _ = Real.exp (rounds q - (13 / 48 : ℝ) * 2 ^ rounds q) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-confidence q) := Real.exp_le_exp.mpr (by nlinarith)

lemma seed_bound :
    (1 + Real.sqrt (1 / 16)) ^ (2 ^ rounds q) * Real.sqrt (1 / 16) ^ (2 ^ rounds q / 3 + 1) ≤
      Real.exp (-confidence q) := by
  have hl := confidence_ge hv
  have hJ := rounds_pow_ge (q := q)
  have hs : Real.sqrt (1 / 16 : ℝ) = 1 / 4 := by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs]
  set J := 2 ^ rounds q with hJdef
  have h1 : (1 + 1 / 4 : ℝ) ^ J ≤ Real.exp (J / 4) := by
    calc (1 + 1 / 4 : ℝ) ^ J ≤ Real.exp (1 / 4) ^ J :=
          pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 / 4 : ℝ)]) J
      _ = Real.exp (J / 4) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : (1 / 4 : ℝ) ^ (J / 3 + 1) ≤ Real.exp (-(J / 3 : ℝ)) := by
    have h4 : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    calc (1 / 4 : ℝ) ^ (J / 3 + 1) ≤ Real.exp (-1) ^ (J / 3 + 1) :=
          pow_le_pow_left₀ (by norm_num) h4 _
      _ = Real.exp (-((J / 3 + 1 : ℕ) : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(J / 3 : ℝ)) := by
          refine Real.exp_le_exp.mpr ?_
          have : J ≤ 3 * (J / 3 + 1) := by omega
          have : (J : ℝ) ≤ 3 * ((J / 3 + 1 : ℕ) : ℝ) := by exact_mod_cast this
          linarith
  have hJr : ((J : ℕ) : ℝ) = (2 : ℝ) ^ rounds q := by rw [hJdef]; push_cast; ring
  calc (1 + 1 / 4 : ℝ) ^ J * (1 / 4) ^ (J / 3 + 1) ≤ Real.exp (J / 4) * Real.exp (-(J / 3 : ℝ)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = Real.exp (-(J / 12 : ℝ)) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-confidence q) := Real.exp_le_exp.mpr (by rw [hJr]; linarith)

lemma accuracy_pos : 0 < accuracy q := by
  unfold accuracy; have := hv.2.2.2.1; positivity

lemma accuracy_final : q.ε / 2 + 2 * ((rounds q : ℝ) + 1) * accuracy q ≤ q.ε := by
  unfold accuracy
  have := hv.2.2.2.1
  have h : 2 * ((rounds q : ℝ) + 1) * (q.ε / (64 * (rounds q + 1))) = q.ε / 32 := by
    field_simp; ring
  rw [h]; linarith

lemma blockSize_pos : 0 < blockSize q := by
  unfold blockSize
  apply Nat.ceil_pos.mpr
  have := noise_pos hv; have := hv.2.2.2.1
  positivity

lemma block_accuracy : 144 * q.σ ^ 2 ≤ (blockSize q : ℝ) * accuracy q ^ 2 := by
  have h := Nat.le_ceil (2 ^ 22 * noiseScale q ^ 2 * (rounds q + 1) ^ 2 / q.ε ^ 2)
  have he := hv.2.2.2.1
  have hσ := hv.2.1
  have hσS := sigma_le_noise hv
  have hσ2 : q.σ ^ 2 ≤ noiseScale q ^ 2 := pow_le_pow_left₀ hσ hσS 2
  have hacc : accuracy q ^ 2 = q.ε ^ 2 / (4096 * ((rounds q : ℝ) + 1) ^ 2) := by
    unfold accuracy; field_simp; ring
  have hm := mul_le_mul_of_nonneg_right h (show 0 ≤ accuracy q ^ 2 by positivity)
  have heq : 2 ^ 22 * noiseScale q ^ 2 * ((rounds q : ℝ) + 1) ^ 2 / q.ε ^ 2 * accuracy q ^ 2 =
      1024 * noiseScale q ^ 2 := by
    rw [hacc]; field_simp; ring
  unfold blockSize
  nlinarith

lemma rounds_le_log : (rounds q : ℝ) + 1 ≤ 11 * Real.log (2 + confidence q) := by
  have hl := confidence_ge hv
  have hJ := rounds_pow_le hv
  have hlog1 : 1 ≤ Real.log (2 + confidence q) := by
    rw [← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have h1 : (rounds q : ℝ) * Real.log 2 ≤ 8 * Real.log 2 + Real.log (2 + confidence q) := by
    have h := Real.log_le_log (by positivity) hJ
    rw [Real.log_pow, Real.log_mul (by positivity) (by linarith), Real.log_pow] at h
    have : Real.log (confidence q) ≤ Real.log (2 + confidence q) :=
      Real.log_le_log (by linarith) (by linarith)
    push_cast at h
    linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' : Real.log 2 < 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have h2 : Real.log 2 ≠ 1 := by
      intro h; have := Real.exp_log (show (0 : ℝ) < 2 by norm_num); rw [h] at this
      have := Real.exp_one_gt_d9; linarith
    exact lt_of_le_of_ne (by linarith) h2
  have hr : (rounds q : ℝ) ≤ 8 + Real.log (2 + confidence q) / Real.log 2 := by
    rw [← sub_le_iff_le_add', le_div_iff₀ (by linarith)]
    linarith
  have hdiv : Real.log (2 + confidence q) / Real.log 2 ≤ 3 / 2 * Real.log (2 + confidence q) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

lemma plan_le_budget :
    (8 * blockSize q * 2 ^ rounds q) * (rounds q + 1) + (pilotSize q + clipSize q) * steps q ≤
      ⌈2 ^ 71 * ((1 + q.σ ^ 2 / q.ε ^ 2) * (q.L * q.Δ / q.ε ^ 2 + Real.log (16 / q.δ) * Real.log (2 + Real.log (16 / q.δ)) ^ 3) + Real.sqrt (q.L * q.Δ) * Real.log (16 / q.δ) / q.ε)⌉₊ := by
  have hl := confidence_ge hv
  have hl0 : 0 < confidence q := by linarith
  have he := hv.2.2.2.1
  have hσ := hv.2.1
  have hL := hv.1
  have hΔ := hv.2.2.1
  have hA0 : 0 ≤ q.L * q.Δ / q.ε ^ 2 := div_nonneg (mul_nonneg hL.le hΔ) (sq_nonneg _)
  have hσ0 : 0 ≤ q.σ ^ 2 / q.ε ^ 2 := by positivity
  have hlogdef : Real.log (16 / q.δ) = confidence q := rfl
  rw [hlogdef]
  have hS2 : noiseScale q ^ 2 / q.ε ^ 2 ≤ 2 * (1 + q.σ ^ 2 / q.ε ^ 2) := by
    have h1 : noiseScale q ^ 2 ≤ 2 * (q.ε ^ 2 + q.σ ^ 2) := by
      unfold noiseScale; nlinarith [sq_nonneg (q.σ - q.ε)]
    calc noiseScale q ^ 2 / q.ε ^ 2 ≤ 2 * (q.ε ^ 2 + q.σ ^ 2) / q.ε ^ 2 :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = 2 * (1 + q.σ ^ 2 / q.ε ^ 2) := by field_simp
  have hT := steps_le hv
  have hTpos := steps_pos (q := q)
  have hT2 : (steps q : ℝ) ≤ 2 ^ 21 * (q.L * q.Δ / q.ε ^ 2 + confidence q) := by linarith
  have hmc : (clipSize q : ℝ) ≤ 2 ^ 42 * (1 + q.σ ^ 2 / q.ε ^ 2) := by
    have h1 := clip_le hv
    have h2 : 2 ^ 41 * noiseScale q ^ 2 / q.ε ^ 2 = 2 ^ 41 * (noiseScale q ^ 2 / q.ε ^ 2) := by ring
    rw [h2] at h1
    linarith
  have hG : gradientScale q / q.ε = Real.sqrt (q.L * q.Δ) / q.ε + 1 := by
    unfold gradientScale; rw [add_div, div_self he.ne']
  have hX : 0 ≤ gradientScale q * (confidence q + 4) / (steps q * q.ε) := by
    have := grad_pos hv; positivity
  have hmp : (pilotSize q : ℝ) ≤ 2 ^ 26 * (1 + q.σ ^ 2 / q.ε ^ 2) +
      2 ^ 24 * (gradientScale q * (confidence q + 4) / (steps q * q.ε)) := by
    have hnn : 0 ≤ 2 ^ 24 * (noiseScale q ^ 2 / q.ε ^ 2 +
        gradientScale q * (confidence q + 4) / (steps q * q.ε)) := by
      have := noise_pos hv; positivity
    have h := Nat.ceil_lt_add_one hnn
    have hpdef : (pilotSize q : ℝ) = (⌈2 ^ 24 * (noiseScale q ^ 2 / q.ε ^ 2 +
        gradientScale q * (confidence q + 4) / (steps q * q.ε))⌉₊ : ℝ) := rfl
    rw [hpdef]
    linarith
  have hphase1 : ((pilotSize q : ℝ) + clipSize q) * steps q ≤
      2 ^ 65 * ((q.L * q.Δ / q.ε ^ 2 + confidence q) * (1 + q.σ ^ 2 / q.ε ^ 2)) +
        2 ^ 25 * (Real.sqrt (q.L * q.Δ) * confidence q / q.ε) := by
    have hgT : 2 ^ 24 * (gradientScale q * (confidence q + 4) / (steps q * q.ε)) * steps q =
        2 ^ 24 * (gradientScale q / q.ε) * (confidence q + 4) := by
      field_simp
    rw [hG] at hgT
    have hsum : (pilotSize q : ℝ) + clipSize q ≤ 2 ^ 43 * (1 + q.σ ^ 2 / q.ε ^ 2) +
        2 ^ 24 * (gradientScale q * (confidence q + 4) / (steps q * q.ε)) := by linarith
    have h1 : ((pilotSize q : ℝ) + clipSize q) * steps q ≤
        2 ^ 43 * (1 + q.σ ^ 2 / q.ε ^ 2) * steps q +
          2 ^ 24 * (Real.sqrt (q.L * q.Δ) / q.ε + 1) * (confidence q + 4) := by
      have h := mul_le_mul_of_nonneg_right hsum hTpos.le
      linarith
    have h2 : 2 ^ 43 * (1 + q.σ ^ 2 / q.ε ^ 2) * steps q ≤
        2 ^ 43 * (1 + q.σ ^ 2 / q.ε ^ 2) * (2 ^ 21 * (q.L * q.Δ / q.ε ^ 2 + confidence q)) :=
      mul_le_mul_of_nonneg_left hT2 (by positivity)
    have hg0 : 0 ≤ Real.sqrt (q.L * q.Δ) / q.ε := by positivity
    have e : Real.sqrt (q.L * q.Δ) * confidence q / q.ε =
        Real.sqrt (q.L * q.Δ) / q.ε * confidence q := by ring
    rw [e]
    have h3 := mul_nonneg hg0 (show (0 : ℝ) ≤ confidence q - 4 by linarith)
    have h4 := mul_nonneg (add_nonneg hA0 hl0.le) hσ0
    nlinarith
  have hrl := rounds_le_log hv
  have hJ := rounds_pow_le hv
  have hR0 : (0 : ℝ) ≤ (rounds q : ℝ) + 1 := by positivity
  have hr : (blockSize q : ℝ) ≤ 2 ^ 24 * (1 + q.σ ^ 2 / q.ε ^ 2) * ((rounds q : ℝ) + 1) ^ 2 := by
    have hnn : 0 ≤ 2 ^ 22 * noiseScale q ^ 2 * ((rounds q : ℝ) + 1) ^ 2 / q.ε ^ 2 := by
      have := noise_pos hv; positivity
    have h := Nat.ceil_lt_add_one hnn
    have hbdef : (blockSize q : ℝ) =
        (⌈2 ^ 22 * noiseScale q ^ 2 * ((rounds q : ℝ) + 1) ^ 2 / q.ε ^ 2⌉₊ : ℝ) := rfl
    have h2 : 2 ^ 22 * noiseScale q ^ 2 * ((rounds q : ℝ) + 1) ^ 2 / q.ε ^ 2 =
        2 ^ 22 * (noiseScale q ^ 2 / q.ε ^ 2) * ((rounds q : ℝ) + 1) ^ 2 := by ring
    have h1 : (1 : ℝ) ≤ ((rounds q : ℝ) + 1) ^ 2 := by nlinarith
    have h3 : 2 ^ 22 * (noiseScale q ^ 2 / q.ε ^ 2) * ((rounds q : ℝ) + 1) ^ 2 ≤
        2 ^ 23 * (1 + q.σ ^ 2 / q.ε ^ 2) * ((rounds q : ℝ) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h5 := mul_le_mul (show (1 : ℝ) ≤ 2 ^ 23 * (1 + q.σ ^ 2 / q.ε ^ 2) by linarith) h1
      zero_le_one (by positivity)
    rw [hbdef]
    linarith
  have hlg0 : 0 ≤ Real.log (2 + confidence q) := Real.log_nonneg (by linarith)
  have hcube : ((rounds q : ℝ) + 1) ^ 3 ≤ 2 ^ 11 * Real.log (2 + confidence q) ^ 3 := by
    have h := pow_le_pow_left₀ hR0 hrl 3
    have e : (11 * Real.log (2 + confidence q)) ^ 3 = 1331 * Real.log (2 + confidence q) ^ 3 := by
      ring
    have hl3 : 0 ≤ Real.log (2 + confidence q) ^ 3 := pow_nonneg hlg0 3
    linarith
  have hphase2 : (8 * (blockSize q : ℝ) * 2 ^ rounds q) * ((rounds q : ℝ) + 1) ≤
      2 ^ 46 * ((1 + q.σ ^ 2 / q.ε ^ 2) * confidence q * Real.log (2 + confidence q) ^ 3) := by
    have h1 : (8 * (blockSize q : ℝ) * 2 ^ rounds q) * ((rounds q : ℝ) + 1) ≤
        8 * (2 ^ 24 * (1 + q.σ ^ 2 / q.ε ^ 2) * ((rounds q : ℝ) + 1) ^ 2) * (2 ^ 8 * confidence q) *
          ((rounds q : ℝ) + 1) := by
      gcongr
    have h3 : 0 ≤ (1 + q.σ ^ 2 / q.ε ^ 2) * confidence q := by positivity
    have h4 := mul_le_mul_of_nonneg_left hcube h3
    linarith
  have hlg1 : 1 ≤ Real.log (2 + confidence q) := by
    rw [← Real.log_exp 1]
    refine Real.log_le_log (Real.exp_pos 1) ?_
    have := Real.exp_one_lt_d9; norm_num at this; linarith
  have hlg3 : 1 ≤ Real.log (2 + confidence q) ^ 3 := one_le_pow₀ hlg1
  have hρℓ : 0 ≤ (1 + q.σ ^ 2 / q.ε ^ 2) * confidence q := by positivity
  have hmono := mul_le_mul_of_nonneg_left hlg3 hρℓ
  have hreal : (((8 * blockSize q * 2 ^ rounds q) * (rounds q + 1) +
      (pilotSize q + clipSize q) * steps q : ℕ) : ℝ) ≤
      2 ^ 71 * ((1 + q.σ ^ 2 / q.ε ^ 2) * (q.L * q.Δ / q.ε ^ 2 +
        confidence q * Real.log (2 + confidence q) ^ 3) +
        Real.sqrt (q.L * q.Δ) * confidence q / q.ε) := by
    push_cast
    have : 0 ≤ Real.sqrt (q.L * q.Δ) * confidence q / q.ε := by positivity
    have : 0 ≤ (q.L * q.Δ / q.ε ^ 2) * (1 + q.σ ^ 2 / q.ε ^ 2) := by positivity
    have : 0 ≤ (1 + q.σ ^ 2 / q.ε ^ 2) * confidence q * Real.log (2 + confidence q) ^ 3 := by
      positivity
    linarith
  exact_mod_cast hreal.trans (Nat.le_ceil _)

end LongTails.Proofs.HighProbabilityConstants
