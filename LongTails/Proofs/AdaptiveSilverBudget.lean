import LongTails.Proofs.AdaptiveSilverParams
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace LongTails.Proofs.AdaptiveSilverBudget

open LongTails.Setups.SmoothHessianLipschitzGd
open LongTails.Algorithms.SilverSchedule
open LongTails.Algorithms.AdaptiveSilverGd
open LongTails.Proofs.SilverCertificate
open LongTails.Proofs.AdaptiveSilverParams

lemma ratio_bounds' : 2.414 ≤ ratio ∧ ratio ≤ 2.415 := by
  unfold ratio
  have h1 : (1.414 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le (by norm_num)
  have h2 : Real.sqrt 2 ≤ 1.415 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  constructor <;> linarith

lemma rpow_root {a b : ℝ} (ha : 0 ≤ a) {k : ℕ} (hk : 0 < k) (h : a ^ k ≤ b) :
    a ≤ b ^ (1 / (k : ℝ)) := by
  have h1 : (a ^ k) ^ (1 / (k : ℝ)) ≤ b ^ (1 / (k : ℝ)) :=
    Real.rpow_le_rpow (by positivity) h (by positivity)
  rwa [← Real.rpow_natCast, ← Real.rpow_mul ha, mul_one_div_cancel (by exact_mod_cast hk.ne'),
    Real.rpow_one] at h1

lemma two_pow_le (k : ℕ) : (2 : ℝ) ^ k ≤ (ratio ^ k) ^ (4 / 5 : ℝ) := by
  have hr := ratio_bounds'
  have h4' : (2.414 : ℝ) ^ 4 ≤ ratio ^ 4 := pow_le_pow_left₀ (by norm_num) hr.1 4
  have h5 : (2 : ℝ) ^ 5 ≤ ratio ^ 4 := by norm_num at h4' ⊢; linarith
  have h6 : ((2 : ℝ) ^ k) ^ 5 ≤ (ratio ^ k) ^ 4 := by
    rw [← pow_mul, ← pow_mul, mul_comm k 5, mul_comm k 4, pow_mul, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) h5 k
  have hroot := rpow_root (by positivity) (k := 5) (by norm_num) h6
  rw [← Real.rpow_natCast (ratio ^ k) 4, ← Real.rpow_mul (pow_nonneg ratio_pos.le k)] at hroot
  convert hroot using 2
  norm_num

lemma maximal_bound {K : ℕ} {q : ℝ} (hq : 0 ≤ q)
    (hfail : 1 < 256 * q ^ 2 * ratio ^ (9 * (K + 1))) :
    (2 / ratio) ^ K ≤ 1.4 * q ^ (1 / 22 : ℝ) := by
  have hr := ratio_bounds'
  have hrp : 0 < ratio := ratio_pos
  have h44 : (2 : ℝ) ^ 44 ≤ ratio ^ 35 := by
    have h1 : (2.414 : ℝ) ^ 35 ≤ ratio ^ 35 := pow_le_pow_left₀ (by norm_num) hr.1 35
    have h2 : (2 : ℝ) ^ 44 ≤ 2.414 ^ 35 := by norm_num
    linarith
  have h9 : 256 * ratio ^ 9 ≤ (1.4 : ℝ) ^ 44 := by
    have h1 : ratio ^ 9 ≤ (2.415 : ℝ) ^ 9 := pow_le_pow_left₀ hrp.le hr.2 9
    have h2 : (256 : ℝ) * 2.415 ^ 9 ≤ 1.4 ^ 44 := by norm_num
    linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 ^ K := ⟨_, rfl⟩
  obtain ⟨r, hrr⟩ : ∃ r : ℝ, r = ratio ^ K := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  have hr0 : 0 < r := by rw [hrr]; exact pow_pos hrp K
  have e1 : (2 / ratio) ^ K = a / r := by rw [div_pow, ha, hrr]
  have e2 : ratio ^ (9 * (K + 1)) = ratio ^ 9 * r ^ 9 := by
    rw [hrr, ← pow_mul, ← pow_add]; congr 1; ring
  have e3 : ((2 : ℝ) ^ 44 / ratio ^ 35) ^ K = a ^ 44 / r ^ 35 := by
    rw [div_pow, ← pow_mul, ← pow_mul, ha, hrr, ← pow_mul, ← pow_mul, mul_comm 44 K, mul_comm 35 K]
  rw [e2] at hfail
  rw [e1]
  have hb : (2 : ℝ) ^ 44 / ratio ^ 35 ≤ 1 := by
    rw [div_le_one (by positivity)]; exact h44
  have hpow : a ^ 44 / r ^ 35 ≤ 1 := by
    rw [← e3]; exact pow_le_one₀ (by positivity) hb
  have hA : (a / r / 1.4) ^ 44 * (256 * (ratio ^ 9 * r ^ 9)) ≤ 1 := by
    have e4 : (a / r / 1.4) ^ 44 * (256 * (ratio ^ 9 * r ^ 9)) =
        (256 * ratio ^ 9 / 1.4 ^ 44) * (a ^ 44 / r ^ 35) := by
      field_simp
    rw [e4]
    have hc : 256 * ratio ^ 9 / 1.4 ^ 44 ≤ 1 := by
      rw [div_le_one (by norm_num)]; exact h9
    calc (256 * ratio ^ 9 / 1.4 ^ 44) * (a ^ 44 / r ^ 35) ≤ 1 * 1 :=
          mul_le_mul hc hpow (by positivity) (by norm_num)
      _ = 1 := by ring
  have hpos : 0 < 256 * (ratio ^ 9 * r ^ 9) := by positivity
  have hkey : (a / r / 1.4) ^ 44 ≤ q ^ 2 := by
    have h1 : (a / r / 1.4) ^ 44 ≤ 1 / (256 * (ratio ^ 9 * r ^ 9)) := by
      rw [le_div_iff₀ hpos]; exact hA
    have h2 : 1 / (256 * (ratio ^ 9 * r ^ 9)) < q ^ 2 := by
      rw [div_lt_iff₀ hpos]
      have : 256 * q ^ 2 * (ratio ^ 9 * r ^ 9) = q ^ 2 * (256 * (ratio ^ 9 * r ^ 9)) := by ring
      linarith
    linarith
  have hroot := rpow_root (by positivity) (k := 44) (by norm_num) hkey
  rw [← Real.rpow_natCast q 2, ← Real.rpow_mul hq] at hroot
  have h3 : a / r / 1.4 ≤ q ^ (1 / 22 : ℝ) := by
    convert hroot using 2; norm_num
  have : a / r = a / r / 1.4 * 1.4 := by field_simp
  rw [this]
  nlinarith

lemma fifty_rpow : (50 : ℝ) ^ (4 / 5 : ℝ) ≤ 23 := by
  have h : ((50 : ℝ) ^ (4 / 5 : ℝ)) ^ (5 : ℕ) ≤ 23 ^ 5 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by norm_num)).mp h

lemma lc_mono (p : Params) {k : ℕ} (hk : 2 ≤ k)
    (h : 256 * p.ρ ^ 2 * p.ε ^ 2 * ratio ^ (9 * k) ≤ p.L ^ 4) : good p := by
  unfold good
  have h1 : ratio ^ (9 * 2) ≤ ratio ^ (9 * k) :=
    pow_le_pow_right₀ (by linarith [ratio_gt_two]) (by omega)
  have h0 : 0 ≤ 256 * p.ρ ^ 2 * p.ε ^ 2 := by positivity
  calc 256 * p.ρ ^ 2 * p.ε ^ 2 * ratio ^ (9 * 2) ≤ 256 * p.ρ ^ 2 * p.ε ^ 2 * ratio ^ (9 * k) :=
        mul_le_mul_of_nonneg_left h1 h0
    _ ≤ p.L ^ 4 := h

lemma not_good_level (p : Params) (hg : ¬ good p) : level p = 2 := by
  unfold level
  rcases le_or_gt (levelRaw p) 2 with h | h
  · exact max_eq_left h
  · exact absurd (lc_mono p h.le (levelRaw_spec p (by omega))) hg

lemma level_le_cap (p : Params) (hK : 2 < level p) : level p ≤ levelCap p := by
  have h3 : level p = max 2 (levelRaw p) := rfl
  rcases le_or_gt (levelRaw p) 2 with h | h
  · rw [max_eq_left h] at h3; omega
  · rw [max_eq_right h.le] at h3; rw [h3]; exact levelRaw_le p

lemma cap_bound (p : Params) (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ levelCap p) :
    (2 : ℝ) ^ (k - 1) ≤ 23 * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ) := by
  classical
  have hlt : ratio ^ (k - 1) < 50 * p.L * p.Δ / p.ε ^ 2 := by
    have := Nat.find_min (levelCap_exists (50 * p.L * p.Δ / p.ε ^ 2))
      (show k - 1 < levelCap p by unfold levelCap at hk ⊢; omega)
    exact lt_of_not_ge this
  have h1 := two_pow_le (k - 1)
  have hX : 0 ≤ p.L * p.Δ / p.ε ^ 2 := by positivity
  have hle : ratio ^ (k - 1) ≤ 50 * (p.L * p.Δ / p.ε ^ 2) := by
    have e : 50 * (p.L * p.Δ / p.ε ^ 2) = 50 * p.L * p.Δ / p.ε ^ 2 := by ring
    rw [e]; exact hlt.le
  have h2 : (ratio ^ (k - 1)) ^ (4 / 5 : ℝ) ≤ (50 * (p.L * p.Δ / p.ε ^ 2)) ^ (4 / 5 : ℝ) :=
    Real.rpow_le_rpow (pow_nonneg ratio_pos.le _) hle (by norm_num)
  rw [Real.mul_rpow (by norm_num) hX] at h2
  have h3 := fifty_rpow
  have h4 : 0 ≤ (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ) := by positivity
  calc (2 : ℝ) ^ (k - 1) ≤ (ratio ^ (k - 1)) ^ (4 / 5 : ℝ) := h1
    _ ≤ 50 ^ (4 / 5 : ℝ) * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ) := h2
    _ ≤ 23 * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ) := mul_le_mul_of_nonneg_right h3 h4

lemma threshold_sq_ge (p : Params) (hgood : good p) :
    p.ε ^ 2 * blockSum p / (25 * blockLength p) ≤ threshold p ^ 2 := by
  classical
  have hx : 0 ≤ blockSum p / (25 * blockLength p) := by
    have := blockSum_ge p; have := blockLength_three p; positivity
  have hs : Real.sqrt (blockSum p / (25 * blockLength p)) ≤
      max 1 (Real.sqrt (blockSum p / (25 * blockLength p))) := le_max_right _ _
  have hsq : (Real.sqrt (blockSum p / (25 * blockLength p))) ^ 2 ≤
      (max 1 (Real.sqrt (blockSum p / (25 * blockLength p)))) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  rw [Real.sq_sqrt hx] at hsq
  unfold threshold
  simp only [hgood, ↓reduceIte, mul_pow]
  have e : p.ε ^ 2 * blockSum p / (25 * blockLength p) =
      p.ε ^ 2 * (blockSum p / (25 * blockLength p)) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)

lemma n_over_sigma (p : Params) : (blockLength p : ℝ) / blockSum p ≤ (2 / ratio) ^ level p := by
  rw [blockLength_eq, blockSum_eq, div_pow]
  have hr := ratio_gt_two
  have h2 : (2 : ℝ) ^ level p ≤ ratio ^ level p := pow_le_pow_left₀ (by norm_num) hr.le _
  have hpos : 0 < ratio ^ level p - 1 := by
    have := ratio_pow_ge p
    have := ratio_square
    nlinarith
  rw [div_le_div_iff₀ hpos (pow_pos ratio_pos _)]
  nlinarith [pow_pos ratio_pos (level p), pow_pos (by norm_num : (0 : ℝ) < 2) (level p)]

noncomputable def budgetFormula (p : Params) : ℕ :=
  ⌈90 * p.L * p.Δ * (p.ρ * p.ε / p.L ^ 2) ^ (1 / 22 : ℝ) / p.ε ^ 2⌉₊ +
    ⌈400 * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ)⌉₊ + 8

lemma budget_real (p : Params) :
    90 * (p.L * p.Δ / p.ε ^ 2) * (p.ρ * p.ε / p.L ^ 2) ^ (1 / 22 : ℝ) +
      400 * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ) + 8 ≤ budgetFormula p := by
  have e : 90 * p.L * p.Δ * (p.ρ * p.ε / p.L ^ 2) ^ (1 / 22 : ℝ) / p.ε ^ 2 =
      90 * (p.L * p.Δ / p.ε ^ 2) * (p.ρ * p.ε / p.L ^ 2) ^ (1 / 22 : ℝ) := by ring
  have h1 : 90 * (p.L * p.Δ / p.ε ^ 2) * (p.ρ * p.ε / p.L ^ 2) ^ (1 / 22 : ℝ) ≤
      (⌈90 * p.L * p.Δ * (p.ρ * p.ε / p.L ^ 2) ^ (1 / 22 : ℝ) / p.ε ^ 2⌉₊ : ℝ) := by
    rw [← e]; exact Nat.le_ceil _
  have h2 := Nat.le_ceil (400 * (p.L * p.Δ / p.ε ^ 2) ^ (4 / 5 : ℝ))
  unfold budgetFormula
  push_cast
  linarith

lemma A_le_two (p : Params) (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    2 * p.L * p.Δ / threshold p ^ 2 ≤ 2 * (p.L * p.Δ / p.ε ^ 2) := by
  have hG := threshold_ge p hε
  have hsq : p.ε ^ 2 ≤ threshold p ^ 2 := pow_le_pow_left₀ hε.le hG 2
  have e : 2 * (p.L * p.Δ / p.ε ^ 2) = 2 * p.L * p.Δ / p.ε ^ 2 := by ring
  rw [e]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq

lemma A_le_fifty (p : Params) (hL : 0 < p.L) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) (hgood : good p) :
    2 * p.L * p.Δ / threshold p ^ 2 ≤ 50 * (p.L * p.Δ / p.ε ^ 2) * (2 / ratio) ^ level p := by
  have hG2 := threshold_sq_ge p hgood
  have hn3 := blockLength_three p
  have hσ4 := blockSum_ge p
  have hns := n_over_sigma p
  have hpos : 0 < p.ε ^ 2 * blockSum p / (25 * blockLength p) := by positivity
  have h1 : 2 * p.L * p.Δ / threshold p ^ 2 ≤
      2 * p.L * p.Δ / (p.ε ^ 2 * blockSum p / (25 * blockLength p)) :=
    div_le_div_of_nonneg_left (by positivity) hpos hG2
  have e : 2 * p.L * p.Δ / (p.ε ^ 2 * blockSum p / (25 * blockLength p)) =
      50 * (p.L * p.Δ / p.ε ^ 2) * (blockLength p / blockSum p) := by
    field_simp; ring
  rw [e] at h1
  have h0 : 0 ≤ 50 * (p.L * p.Δ / p.ε ^ 2) := by positivity
  exact h1.trans (mul_le_mul_of_nonneg_left hns h0)

lemma key_not_good (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (hg : ¬ good p) :
    2 * p.L * p.Δ / threshold p ^ 2 + 2 * (blockLength p : ℝ) < budgetFormula p := by
  have hK := not_good_level p hg
  have hn : (blockLength p : ℝ) = 3 := by rw [blockLength_eq, hK]; norm_num
  have hA := A_le_two p hL hΔ hε
  have hB := budget_real p
  obtain ⟨X, hX⟩ : ∃ X, X = p.L * p.Δ / p.ε ^ 2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = p.ρ * p.ε / p.L ^ 2 := ⟨_, rfl⟩
  rw [← hX] at hA hB
  rw [← hq] at hB
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hr := ratio_bounds'
  have hqb : (1 / 45 : ℝ) ^ (22 : ℕ) ≤ q := by
    unfold good at hg
    have hlt : p.L ^ 4 < 256 * p.ρ ^ 2 * p.ε ^ 2 * ratio ^ (9 * 2) := lt_of_not_ge hg
    have h18 : ratio ^ (9 * 2) ≤ (2.415 : ℝ) ^ 18 := pow_le_pow_left₀ ratio_pos.le hr.2 18
    have hL4 : 0 < p.L ^ 4 := by positivity
    have e : 256 * p.ρ ^ 2 * p.ε ^ 2 = 256 * (p.L ^ 4 * q ^ 2) := by
      rw [hq]; field_simp
    rw [e] at hlt
    have h1 : 256 * (p.L ^ 4 * q ^ 2) * ratio ^ (9 * 2) ≤ 256 * (p.L ^ 4 * q ^ 2) * 2.415 ^ 18 :=
      mul_le_mul_of_nonneg_left h18 (by positivity)
    have hq2' : 1 < 256 * (2.415 : ℝ) ^ 18 * q ^ 2 := by
      by_contra hc
      have h2 := mul_le_mul_of_nonneg_left (not_lt.mp hc) hL4.le
      have : p.L ^ 4 < p.L ^ 4 :=
        calc p.L ^ 4 < 256 * (p.L ^ 4 * q ^ 2) * ratio ^ (9 * 2) := hlt
          _ ≤ 256 * (p.L ^ 4 * q ^ 2) * 2.415 ^ 18 := h1
          _ = p.L ^ 4 * (256 * 2.415 ^ 18 * q ^ 2) := by ring
          _ ≤ p.L ^ 4 * 1 := h2
          _ = p.L ^ 4 := mul_one _
      exact lt_irrefl _ this
    have hsmall : 256 * (2.415 : ℝ) ^ 18 * ((1 / 45 : ℝ) ^ (22 : ℕ)) ^ 2 ≤ 1 := by norm_num
    have hsq : ((1 / 45 : ℝ) ^ (22 : ℕ)) ^ 2 ≤ q ^ 2 := by
      by_contra hc
      have h' : q ^ 2 < ((1 / 45 : ℝ) ^ (22 : ℕ)) ^ 2 := lt_of_not_ge hc
      have : 256 * (2.415 : ℝ) ^ 18 * q ^ 2 ≤ 256 * 2.415 ^ 18 * ((1 / 45 : ℝ) ^ (22 : ℕ)) ^ 2 :=
        mul_le_mul_of_nonneg_left h'.le (by norm_num)
      linarith
    exact (pow_le_pow_iff_left₀ (by positivity) hq0 (by norm_num)).mp hsq
  have hyb : 1 / 45 ≤ q ^ (1 / 22 : ℝ) := by
    have := rpow_root (by norm_num) (k := 22) (by norm_num) hqb
    convert this using 2
  have hZ : 0 ≤ X ^ (4 / 5 : ℝ) := by positivity
  have h90 : 2 * X ≤ 90 * X * q ^ (1 / 22 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hyb (show 0 ≤ 90 * X by positivity)
    linarith
  rw [hn]
  linarith

lemma key_good (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε)
    (hgood : good p) :
    2 * p.L * p.Δ / threshold p ^ 2 + 2 * (blockLength p : ℝ) < budgetFormula p := by
  have hA50 := A_le_fifty p hL hΔ hε hgood
  have hB := budget_real p
  have hn := blockLength_eq p
  have hK2 := level_ge p
  obtain ⟨X, hX⟩ : ∃ X, X = p.L * p.Δ / p.ε ^ 2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = p.ρ * p.ε / p.L ^ 2 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = 2 * p.L * p.Δ / threshold p ^ 2 := ⟨_, rfl⟩
  obtain ⟨K, hKd⟩ : ∃ K, K = level p := ⟨_, rfl⟩
  rw [← hX, ← hA, ← hKd] at hA50
  rw [← hX, ← hq] at hB
  rw [← hKd] at hn hK2
  rw [← hA]
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hZ0 : 0 ≤ X ^ (4 / 5 : ℝ) := by positivity
  have hy0 : 0 ≤ q ^ (1 / 22 : ℝ) := by positivity
  have hr := ratio_bounds'
  have hrp := ratio_pos
  have h2n : 2 * (blockLength p : ℝ) + 1 ≤ 8 + 92 * X ^ (4 / 5 : ℝ) := by
    rcases Nat.lt_or_ge 2 K with hK3 | hK2'
    · have hKcap : K ≤ levelCap p := by rw [hKd]; exact level_le_cap p (by omega)
      have hcb := cap_bound p hL hΔ hε (k := K) (by omega) hKcap
      rw [← hX] at hcb
      have h2K : (2 : ℝ) ^ K = 2 * 2 ^ (K - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [hn]; linarith
    · have hK2e : K = 2 := by omega
      rw [hn, hK2e]; norm_num; linarith
  by_cases hmax : 256 * p.ρ ^ 2 * p.ε ^ 2 * ratio ^ (9 * (K + 1)) ≤ p.L ^ 4
  · have hcapK : levelCap p ≤ K := by
      by_contra hlt
      have hlt' : K + 1 ≤ levelCap p := by omega
      have hge := le_levelRaw p hlt' hmax
      have : K = max 2 (levelRaw p) := hKd
      omega
    have hXK : 50 * X ≤ ratio ^ K := by
      have h1 := Nat.find_spec (levelCap_exists (50 * p.L * p.Δ / p.ε ^ 2))
      have h2 : ratio ^ levelCap p ≤ ratio ^ K := pow_le_pow_right₀ (by linarith) hcapK
      have e : 50 * X = 50 * p.L * p.Δ / p.ε ^ 2 := by rw [hX]; ring
      rw [e]
      unfold levelCap at h2
      linarith
    have hAK : A ≤ 2 ^ K := by
      have e : 50 * X * (2 / ratio) ^ K = 2 ^ K * (50 * X / ratio ^ K) := by
        rw [div_pow]; field_simp
      have h1 : 50 * X / ratio ^ K ≤ 1 := by
        rw [div_le_one (pow_pos hrp K)]; exact hXK
      have h2 : 2 ^ K * (50 * X / ratio ^ K) ≤ 2 ^ K * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    rcases Nat.lt_or_ge 2 K with hK3 | hK2'
    · have hKcap : K ≤ levelCap p := by rw [hKd]; exact level_le_cap p (by omega)
      have hcb := cap_bound p hL hΔ hε (k := K) (by omega) hKcap
      rw [← hX] at hcb
      have h2K : (2 : ℝ) ^ K = 2 * 2 ^ (K - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hmul : 0 ≤ 90 * X * q ^ (1 / 22 : ℝ) := by positivity
      linarith
    · have hK2e : K = 2 := by omega
      rw [hK2e] at hXK hA50
      have hX1 : X ≤ 1 := by
        have : ratio ^ 2 ≤ (2.415 : ℝ) ^ 2 := pow_le_pow_left₀ hrp.le hr.2 2
        nlinarith
      have hXp : X ≤ X ^ (4 / 5 : ℝ) := by
        rcases hX0.lt_or_eq with hXpos | hXz
        · have := Real.rpow_le_rpow_of_exponent_ge hXpos hX1 (show (4 / 5 : ℝ) ≤ 1 by norm_num)
          simpa using this
        · rw [← hXz]; simp
      have h2r : (2 / ratio) ^ 2 ≤ 1 := by
        rw [div_pow, div_le_one (by positivity)]; nlinarith
      have hA1 : A ≤ 50 * X := by
        have := mul_le_mul_of_nonneg_left h2r (show 0 ≤ 50 * X by positivity)
        linarith
      have hmul : 0 ≤ 90 * X * q ^ (1 / 22 : ℝ) := by positivity
      linarith
  · have hfail : 1 < 256 * q ^ 2 * ratio ^ (9 * (K + 1)) := by
      have hlt : p.L ^ 4 < 256 * p.ρ ^ 2 * p.ε ^ 2 * ratio ^ (9 * (K + 1)) := lt_of_not_ge hmax
      have hL4 : 0 < p.L ^ 4 := by positivity
      have e : 256 * p.ρ ^ 2 * p.ε ^ 2 * ratio ^ (9 * (K + 1)) =
          p.L ^ 4 * (256 * q ^ 2 * ratio ^ (9 * (K + 1))) := by
        rw [hq]; field_simp
      rw [e] at hlt
      by_contra hc
      have := mul_le_mul_of_nonneg_left (not_lt.mp hc) hL4.le
      linarith
    have hmb := maximal_bound hq0 hfail
    have hAy : A ≤ 70 * X * q ^ (1 / 22 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hmb (show 0 ≤ 50 * X by positivity)
      linarith
    have hmul : 0 ≤ X * q ^ (1 / 22 : ℝ) := by positivity
    linarith

lemma budget_suffices (p : Params) (hL : 0 < p.L) (hρ : 0 ≤ p.ρ) (hΔ : 0 ≤ p.Δ) (hε : 0 < p.ε) :
    p.Δ < ((budgetFormula p - 2 * blockLength p : ℕ) : ℝ) * (threshold p ^ 2 / (2 * p.L)) := by
  have hkey : 2 * p.L * p.Δ / threshold p ^ 2 + 2 * (blockLength p : ℝ) < budgetFormula p := by
    by_cases hgood : good p
    · exact key_good p hL hρ hΔ hε hgood
    · exact key_not_good p hL hρ hΔ hε hgood
  have hG : 0 < threshold p := lt_of_lt_of_le hε (threshold_ge p hε)
  have hA0 : 0 ≤ 2 * p.L * p.Δ / threshold p ^ 2 := by positivity
  have hle : 2 * blockLength p ≤ budgetFormula p := by
    have : (2 * blockLength p : ℝ) < budgetFormula p := by linarith
    exact_mod_cast this.le
  rw [Nat.cast_sub hle]
  push_cast
  have h1 : 2 * p.L * p.Δ / threshold p ^ 2 < (budgetFormula p : ℝ) - 2 * blockLength p := by
    linarith
  rw [div_lt_iff₀ (by positivity)] at h1
  rw [show ((budgetFormula p : ℝ) - 2 * blockLength p) * (threshold p ^ 2 / (2 * p.L)) =
    ((budgetFormula p : ℝ) - 2 * blockLength p) * threshold p ^ 2 / (2 * p.L) by ring]
  rw [lt_div_iff₀ (by positivity)]
  linarith

end LongTails.Proofs.AdaptiveSilverBudget
