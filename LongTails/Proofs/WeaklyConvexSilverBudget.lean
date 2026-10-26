import LongTails.Algorithms.WeaklyConvexSilver
import LongTails.Proofs.WeaklyConvexSilverCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Proofs.WeaklyConvexSilverBudget

open LongTails.Setups.SmoothWeaklyConvex
open LongTails.Algorithms.SilverSchedule
open LongTails.Algorithms.WeaklyConvexSilver
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.WeaklyConvexSilverCertificate

lemma ratio_pos' : 0 < ratio := by have := ratio_bounds; linarith

lemma two_div_ratio_pow (K : ℕ) :
    (2 / ratio) ^ K ≤ ((7 / 2 : ℝ) ^ K) ^ (-(3 / 20) : ℝ) := by
  have hb := ratio_bounds
  have hr := ratio_pos'
  have h20 : (2 / ratio) ^ 20 ≤ (2 / 7) ^ 3 := by
    rw [div_pow, div_le_iff₀ (pow_pos hr 20)]
    have h1 : (2414213 / 1000000 : ℝ) ^ 20 ≤ ratio ^ 20 :=
      pow_le_pow_left₀ (by norm_num) hb.1.le 20
    have h2 : (2 : ℝ) ^ 20 ≤ (2 / 7) ^ 3 * (2414213 / 1000000) ^ 20 := by norm_num
    nlinarith
  have hbase : 2 / ratio ≤ (7 / 2 : ℝ) ^ (-(3 / 20) : ℝ) := by
    have h0 : 0 ≤ 2 / ratio := div_nonneg (by norm_num) hr.le
    have h0' : (0 : ℝ) ≤ (7 / 2 : ℝ) ^ (-(3 / 20) : ℝ) := by positivity
    rw [← pow_le_pow_iff_left₀ h0 h0' (by norm_num : (20 : ℕ) ≠ 0)]
    have e1 : ((7 / 2 : ℝ) ^ (-(3 / 20) : ℝ)) ^ (20 : ℕ) = (2 / 7) ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      have : (-(3 / 20) : ℝ) * ((20 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) := by norm_num
      rw [this, Real.rpow_neg (by norm_num), Real.rpow_natCast]
      norm_num
    rw [e1]
    exact h20
  calc (2 / ratio) ^ K ≤ ((7 / 2 : ℝ) ^ (-(3 / 20) : ℝ)) ^ K :=
        pow_le_pow_left₀ (div_nonneg (by norm_num) hr.le) hbase K
    _ = ((7 / 2 : ℝ) ^ K) ^ (-(3 / 20) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (7 / 2 : ℝ) K,
        ← Real.rpow_mul (by norm_num), mul_comm]

lemma two_pow_le (m : ℕ) : (2 : ℝ) ^ m ≤ (ratio ^ m) ^ (4 / 5 : ℝ) := by
  have hb := ratio_bounds
  have hr := ratio_pos'
  have h1 : (2 : ℝ) ≤ ratio ^ (4 / 5 : ℝ) := by
    have h0 : (0 : ℝ) ≤ ratio ^ (4 / 5 : ℝ) := by positivity
    rw [← pow_le_pow_iff_left₀ (by norm_num) h0 (by norm_num : (5 : ℕ) ≠ 0)]
    rw [← Real.rpow_natCast (ratio ^ (4 / 5 : ℝ)), ← Real.rpow_mul hr.le]
    norm_num
    have : (2414213 / 1000000 : ℝ) ^ 4 ≤ ratio ^ 4 := pow_le_pow_left₀ (by norm_num) hb.1.le 4
    nlinarith
  calc (2 : ℝ) ^ m ≤ (ratio ^ (4 / 5 : ℝ)) ^ m := pow_le_pow_left₀ (by norm_num) h1 m
    _ = (ratio ^ m) ^ (4 / 5 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_natCast ratio m,
        ← Real.rpow_mul hr.le, mul_comm]

lemma four_rpow : (4 : ℝ) ^ (4 / 5 : ℝ) ≤ 13 / 4 := by
  have h0 : (0 : ℝ) ≤ (4 : ℝ) ^ (4 / 5 : ℝ) := by positivity
  rw [← pow_le_pow_iff_left₀ h0 (by norm_num) (by norm_num : (5 : ℕ) ≠ 0)]
  rw [← Real.rpow_natCast ((4 : ℝ) ^ (4 / 5 : ℝ)), ← Real.rpow_mul (by norm_num)]
  norm_num

lemma cap_lower (p : Params) (hcap : 1 ≤ levelCap p) :
    ratio ^ (levelCap p - 1) < 4 * p.L * p.Δ / p.ε ^ 2 := by
  classical
  have h := Nat.find_min (levelCap_exists (4 * p.L * p.Δ / p.ε ^ 2))
    (show levelCap p - 1 < levelCap p by omega)
  simp only [not_le] at h
  convert h

lemma cap_upper (p : Params) : 4 * p.L * p.Δ / p.ε ^ 2 ≤ ratio ^ levelCap p := by
  classical
  exact Nat.find_spec (levelCap_exists (4 * p.L * p.Δ / p.ε ^ 2))

lemma level_eq (p : Params) (hK : 2 ≤ level p) : level p = levelRaw p := by
  unfold level at hK ⊢
  omega

lemma level_spec (p : Params) (hK : 2 ≤ level p) :
    250000 * p.ρ * (7 / 2) ^ level p ≤ p.L ∧ level p ≤ levelCap p := by
  have hK' := level_eq p hK
  have h0 : levelRaw p ≠ 0 := by omega
  rw [hK']
  unfold levelRaw at h0 ⊢
  exact ⟨Nat.findGreatest_of_ne_zero rfl h0, Nat.findGreatest_le _⟩

lemma pow_two_le_cap (p : Params) (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (hcap : 2 ≤ levelCap p) {K : ℕ} (hK : K ≤ levelCap p) :
    (2 : ℝ) ^ K ≤ 13 / 2 * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ) := by
  have hb := ratio_bounds
  have hr := ratio_pos'
  set y := 4 * p.L * p.Δ / p.ε ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have h1 := cap_lower p (by omega)
  have h2 : (2 : ℝ) ^ (levelCap p - 1) ≤ y ^ (4 / 5 : ℝ) :=
    (two_pow_le _).trans (Real.rpow_le_rpow (by positivity) h1.le (by norm_num))
  have h3 : (2 : ℝ) ^ K ≤ 2 ^ levelCap p := pow_le_pow_right₀ (by norm_num) hK
  have h4 : (2 : ℝ) ^ levelCap p = 2 * 2 ^ (levelCap p - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h5 : y ^ (4 / 5 : ℝ) = (4 : ℝ) ^ (4 / 5 : ℝ) * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ) := by
    rw [hy, show 4 * p.L * p.Δ / p.ε ^ 2 = 4 * (p.L * p.Δ / p.ε ^ 2) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  have h6 := four_rpow
  have h7 : (0 : ℝ) ≤ (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ) := by positivity
  nlinarith

lemma budget_blocks (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (hK : 2 ≤ level p) :
    (max 1 ⌈4 * p.L * p.Δ / (ratio ^ level p * p.ε ^ 2)⌉₊) * (steps (level p)).length + 1 ≤
      ⌈32 * p.L * (p.ρ / p.L) ^ (3 / 20 : ℝ) * p.Δ / p.ε ^ 2⌉₊ +
        ⌈13 * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ)⌉₊ + 3 := by
  classical
  have hb := ratio_bounds
  have hr := ratio_pos'
  obtain ⟨hsmall, hcapK⟩ := level_spec p hK
  set K := level p with hKdef
  set y := 4 * p.L * p.Δ / p.ε ^ 2 with hy
  have hy0 : 0 ≤ y := by positivity
  have hrK : 0 < ratio ^ K := pow_pos hr K
  have hcap2 : 2 ≤ levelCap p := le_trans hK hcapK
  have hlen : ((steps K).length : ℝ) + 1 = 2 ^ K := by exact_mod_cast steps_length K
  have hJ : ((max 1 ⌈4 * p.L * p.Δ / (ratio ^ K * p.ε ^ 2)⌉₊ : ℕ) : ℝ) ≤ y / ratio ^ K + 1 := by
    have ha : 0 ≤ 4 * p.L * p.Δ / (ratio ^ K * p.ε ^ 2) := by positivity
    have hc := Nat.ceil_lt_add_one ha
    have he : 4 * p.L * p.Δ / (ratio ^ K * p.ε ^ 2) = y / ratio ^ K := by
      rw [hy, div_div, mul_comm (ratio ^ K)]
    push_cast
    rw [he] at hc ⊢
    apply max_le
    · have : 0 ≤ y / ratio ^ K := by positivity
      linarith
    · exact hc.le
  have hmain : y * (2 / ratio) ^ K ≤
      32 * p.L * (p.ρ / p.L) ^ (3 / 20 : ℝ) * p.Δ / p.ε ^ 2 + 2 ^ K := by
    rcases lt_or_eq_of_le hcapK with hlt | heq
    · have hnot : ¬ (250000 * p.ρ * (7 / 2) ^ (K + 1) ≤ p.L) := by
        have hKfg := level_eq p hK
        rw [← hKdef] at hKfg
        have hlt' : levelRaw p < K + 1 := by omega
        unfold levelRaw at hlt'
        exact Nat.findGreatest_is_greatest hlt' (by omega)
      simp only [not_le] at hnot
      rw [pow_succ] at hnot
      have hρpos : 0 < p.ρ := by
        by_contra h0
        have : p.ρ = 0 := le_antisymm (not_lt.mp h0) hρ
        rw [this] at hnot
        linarith
      have ha0 : (0 : ℝ) < (7 / 2) ^ K := by positivity
      have hinv : ((7 / 2 : ℝ) ^ K)⁻¹ ≤ 875000 * (p.ρ / p.L) := by
        rw [inv_eq_one_div, div_le_iff₀ ha0]
        have e : 875000 * (p.ρ / p.L) * (7 / 2) ^ K = 875000 * p.ρ * (7 / 2) ^ K / p.L := by ring
        rw [e, le_div_iff₀ hL]
        linarith
      set a := (7 / 2 : ℝ) ^ K with ha
      have h1 := two_div_ratio_pow K
      rw [← ha, Real.rpow_neg ha0.le, ← Real.inv_rpow ha0.le] at h1
      have h2 : a⁻¹ ^ (3 / 20 : ℝ) ≤ (875000 * (p.ρ / p.L)) ^ (3 / 20 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hinv (by norm_num)
      rw [Real.mul_rpow (by norm_num) (by positivity)] at h2
      have h3 : (875000 : ℝ) ^ (3 / 20 : ℝ) ≤ 8 := by
        have h0 : (0 : ℝ) ≤ (875000 : ℝ) ^ (3 / 20 : ℝ) := by positivity
        rw [← pow_le_pow_iff_left₀ h0 (by norm_num) (by norm_num : (20 : ℕ) ≠ 0)]
        rw [← Real.rpow_natCast ((875000 : ℝ) ^ (3 / 20 : ℝ)), ← Real.rpow_mul (by norm_num)]
        norm_num
      have hq0 : 0 ≤ (p.ρ / p.L) ^ (3 / 20 : ℝ) := by positivity
      have h4 : (2 / ratio) ^ K ≤ 8 * (p.ρ / p.L) ^ (3 / 20 : ℝ) := by
        have := mul_le_mul_of_nonneg_right h3 hq0
        linarith
      have h5 : y * (2 / ratio) ^ K ≤ y * (8 * (p.ρ / p.L) ^ (3 / 20 : ℝ)) :=
        mul_le_mul_of_nonneg_left h4 hy0
      have h6 : y * (8 * (p.ρ / p.L) ^ (3 / 20 : ℝ)) =
          32 * p.L * (p.ρ / p.L) ^ (3 / 20 : ℝ) * p.Δ / p.ε ^ 2 := by
        rw [hy]; ring
      have h7 : (0 : ℝ) ≤ 2 ^ K := by positivity
      linarith
    · have hup := cap_upper p
      rw [← hy, ← heq] at hup
      have h1 : y * (2 / ratio) ^ K = y / ratio ^ K * 2 ^ K := by rw [div_pow]; ring
      have h2 : y / ratio ^ K ≤ 1 := by rw [div_le_one hrK]; exact hup
      have h3 : (0 : ℝ) ≤ 32 * p.L * (p.ρ / p.L) ^ (3 / 20 : ℝ) * p.Δ / p.ε ^ 2 := by positivity
      rw [h1]
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) K]
  have hpow := pow_two_le_cap p hL hΔ hε hcap2 hcapK
  have hJn : ((max 1 ⌈4 * p.L * p.Δ / (ratio ^ K * p.ε ^ 2)⌉₊ : ℕ) : ℝ) *
      ((steps K).length : ℝ) ≤ y * (2 / ratio) ^ K + 2 ^ K := by
    have hn : ((steps K).length : ℝ) ≤ 2 ^ K := by linarith
    have hJ0 : (0 : ℝ) ≤ ((max 1 ⌈4 * p.L * p.Δ / (ratio ^ K * p.ε ^ 2)⌉₊ : ℕ) : ℝ) := by positivity
    have e1 : (y / ratio ^ K + 1) * 2 ^ K = y * (2 / ratio) ^ K + 2 ^ K := by
      rw [div_pow]; ring
    calc ((max 1 ⌈4 * p.L * p.Δ / (ratio ^ K * p.ε ^ 2)⌉₊ : ℕ) : ℝ) * ((steps K).length : ℝ)
        ≤ ((max 1 ⌈4 * p.L * p.Δ / (ratio ^ K * p.ε ^ 2)⌉₊ : ℕ) : ℝ) * 2 ^ K :=
          mul_le_mul_of_nonneg_left hn hJ0
      _ ≤ (y / ratio ^ K + 1) * 2 ^ K := mul_le_mul_of_nonneg_right hJ (by positivity)
      _ = _ := e1
  have hc1 := Nat.le_ceil (32 * p.L * (p.ρ / p.L) ^ (3 / 20 : ℝ) * p.Δ / p.ε ^ 2)
  have hc2 := Nat.le_ceil (13 * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ))
  have hfin : ((max 1 ⌈4 * p.L * p.Δ / (ratio ^ K * p.ε ^ 2)⌉₊ * (steps K).length + 1 : ℕ) : ℝ) ≤
      ((⌈32 * p.L * (p.ρ / p.L) ^ (3 / 20 : ℝ) * p.Δ / p.ε ^ 2⌉₊ +
        ⌈13 * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ)⌉₊ + 3 : ℕ) : ℝ) := by
    push_cast
    push_cast at hJn
    nlinarith
  exact_mod_cast hfin

lemma budget_single (p : Params) (hL : 0 < p.L) (_hρ : 0 ≤ p.ρ) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (hK : level p = 1) :
    ⌈ratio * p.L * p.Δ / p.ε ^ 2⌉₊ + 1 ≤
      ⌈32 * p.L * (p.ρ / p.L) ^ (3 / 20 : ℝ) * p.Δ / p.ε ^ 2⌉₊ +
        ⌈13 * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ)⌉₊ + 3 := by
  classical
  have hb := ratio_bounds
  have hr := ratio_pos'
  rcases le_or_gt 2 (levelCap p) with hcap | hcap
  · have hnot : ¬ (250000 * p.ρ * (7 / 2) ^ 2 ≤ p.L) := by
      intro h2
      have h3 : 2 ≤ levelRaw p := by
        unfold levelRaw
        exact Nat.le_findGreatest hcap h2
      unfold level at hK
      omega
    simp only [not_le] at hnot
    have hq : 1 / 3062500 ≤ p.ρ / p.L := by
      rw [le_div_iff₀ hL]
      nlinarith
    have h1 : (1 / 10 : ℝ) ≤ (p.ρ / p.L) ^ (3 / 20 : ℝ) := by
      have h0 : (1 / 3062500 : ℝ) ^ (3 / 20 : ℝ) ≤ (p.ρ / p.L) ^ (3 / 20 : ℝ) :=
        Real.rpow_le_rpow (by norm_num) hq (by norm_num)
      have h2 : (1 / 10 : ℝ) ≤ (1 / 3062500 : ℝ) ^ (3 / 20 : ℝ) := by
        have hz : (0 : ℝ) ≤ (1 / 3062500 : ℝ) ^ (3 / 20 : ℝ) := by positivity
        rw [← pow_le_pow_iff_left₀ (by norm_num) hz (by norm_num : (20 : ℕ) ≠ 0)]
        rw [← Real.rpow_natCast ((1 / 3062500 : ℝ) ^ (3 / 20 : ℝ)), ← Real.rpow_mul (by norm_num)]
        norm_num
      linarith
    have h2 : ratio * p.L * p.Δ / p.ε ^ 2 ≤ 32 * p.L * (p.ρ / p.L) ^ (3 / 20 : ℝ) * p.Δ / p.ε ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hLΔ : 0 ≤ p.L * p.Δ := by positivity
      nlinarith
    have h3 := Nat.ceil_le_ceil h2
    omega
  · have hup := cap_upper p
    have hle : ratio ^ levelCap p ≤ ratio := by
      rcases (show levelCap p = 0 ∨ levelCap p = 1 by omega) with h | h
      · rw [h]; simp; linarith
      · rw [h]; simp
    have h1 : ratio * p.L * p.Δ / p.ε ^ 2 ≤ 2 := by
      have : p.L * p.Δ / p.ε ^ 2 ≤ ratio / 4 := by
        have h4 : 4 * p.L * p.Δ / p.ε ^ 2 ≤ ratio := hup.trans hle
        have e : 4 * p.L * p.Δ / p.ε ^ 2 = 4 * (p.L * p.Δ / p.ε ^ 2) := by ring
        linarith
      have e : ratio * p.L * p.Δ / p.ε ^ 2 = ratio * (p.L * p.Δ / p.ε ^ 2) := by ring
      rw [e]
      have : 0 ≤ p.L * p.Δ / p.ε ^ 2 := by positivity
      nlinarith
    have h2 : ⌈ratio * p.L * p.Δ / p.ε ^ 2⌉₊ ≤ 2 := by
      rw [Nat.ceil_le]; exact_mod_cast h1
    omega

end LongTails.Proofs.WeaklyConvexSilverBudget
