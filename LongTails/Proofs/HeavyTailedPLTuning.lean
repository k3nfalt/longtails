import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace OracleTemplate.HeavyTailedPL

lemma burn_start {t0 Δ L M n s2 R : ℝ} (ht0 : 3 ≤ t0) (hΔ : 0 ≤ Δ) (hL : 0 < L) (hM : 0 < M)
    (hR2 : R ^ 2 = L * Δ) (hR : 0 ≤ R) (hns : t0 * M * R ≤ n * s2) :
    (t0 - 1) * (t0 - 2) * Δ * (L * M ^ 2) ≤ (n * s2) ^ 2 := by
  have hw : (t0 - 1) * (t0 - 2) ≤ t0 ^ 2 := by nlinarith
  have h1 : (t0 - 1) * (t0 - 2) * Δ * (L * M ^ 2) ≤ t0 ^ 2 * Δ * (L * M ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hw hΔ) (by positivity)
  have h2 : (t0 * M * R) ^ 2 ≤ (n * s2) ^ 2 := pow_le_pow_left₀ (by positivity) hns 2
  have h3 : (t0 * M * R) ^ 2 = t0 ^ 2 * Δ * (L * M ^ 2) := by
    rw [mul_pow, mul_pow, hR2]; ring
  linarith

lemma burn_martingale {μ L M Λ σ n s2 : ℝ} (hμ : 0 < μ) (hn : 0 < n) (hs : σ ^ 2 ≤ s2)
    (h64 : 64 * L * M ^ 2 * Λ ≤ μ * σ ^ 2 * n) :
    32 * n * s2 * Λ / μ * (L * M ^ 2) ≤ (n * s2) ^ 2 / 2 := by
  have hs0 : 0 ≤ s2 := (sq_nonneg σ).trans hs
  have h1 := mul_le_mul_of_nonneg_right h64 (show 0 ≤ n * s2 by positivity)
  have h2 : μ * σ ^ 2 * n * (n * s2) ≤ μ * s2 * n * (n * s2) := by
    have : μ * σ ^ 2 ≤ μ * s2 := mul_le_mul_of_nonneg_left hs hμ.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hn.le) (by positivity)
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hμ (by norm_num)]
  nlinarith

lemma burn_variance {μ L M σ n s2 T : ℝ} (hT0 : 0 ≤ T) (hTn : T ≤ n) (hs : σ ^ 2 ≤ s2)
    (h64 : 64 * L ^ 2 * M ^ 2 ≤ μ ^ 2 * σ ^ 2 * n) (hμ : 0 < μ) :
    32 * L * T * σ ^ 2 / μ ^ 2 * (L * M ^ 2) ≤ (n * s2) ^ 2 / 2 := by
  have h1 := mul_le_mul_of_nonneg_right h64 (show 0 ≤ T * σ ^ 2 by positivity)
  have h2 : μ ^ 2 * σ ^ 2 * n * (T * σ ^ 2) ≤ μ ^ 2 * σ ^ 2 * n * (n * σ ^ 2) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hTn (sq_nonneg σ)) (by
      have : 0 ≤ n := hT0.trans hTn
      positivity)
  have h3 : (σ ^ 2) ^ 2 ≤ s2 ^ 2 := pow_le_pow_left₀ (sq_nonneg σ) hs 2
  have h4 : μ ^ 2 * n ^ 2 * (σ ^ 2) ^ 2 ≤ μ ^ 2 * n ^ 2 * s2 ^ 2 :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

lemma burn_square {μ L M Λ σ n s2 : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (hΛ : 1 ≤ Λ) (hs : σ ^ 2 ≤ s2)
    (h64 : 64 * L ^ 2 * M ^ 2 * Λ ≤ μ ^ 2 * σ ^ 2 * n) :
    16 * L / μ ^ 2 * M ^ 2 * Λ * (L * M ^ 2) ≤ (n * s2) ^ 2 / 2 := by
  have hL : 0 < L := hμ.trans_le hμL
  have hlhs0 : 0 ≤ 64 * L ^ 2 * M ^ 2 * Λ := by positivity
  have hsq := pow_le_pow_left₀ hlhs0 h64 2
  have hμ2 : μ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hμ.le hμL 2
  have hk : 32 * L ^ 2 * M ^ 4 * Λ * μ ^ 2 ≤ (64 * L ^ 2 * M ^ 2 * Λ) ^ 2 := by
    have e : (64 * L ^ 2 * M ^ 2 * Λ) ^ 2 = 4096 * L ^ 4 * M ^ 4 * Λ ^ 2 := by ring
    rw [e]
    have hΛ2 : Λ ≤ Λ ^ 2 := by nlinarith
    have a1 : 32 * L ^ 2 * M ^ 4 * Λ * μ ^ 2 ≤ 32 * L ^ 2 * M ^ 4 * Λ * L ^ 2 :=
      mul_le_mul_of_nonneg_left hμ2 (by positivity)
    have a2 : 32 * L ^ 2 * M ^ 4 * Λ * L ^ 2 ≤ 4096 * L ^ 4 * M ^ 4 * Λ ^ 2 := by
      have : 32 * Λ ≤ 4096 * Λ ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ L ^ 4 * M ^ 4 by positivity)]
    linarith
  have h3 : (σ ^ 2) ^ 2 ≤ s2 ^ 2 := pow_le_pow_left₀ (sq_nonneg σ) hs 2
  have h5 : (μ ^ 2 * σ ^ 2 * n) ^ 2 ≤ μ ^ 2 * μ ^ 2 * (n ^ 2 * s2 ^ 2) := by
    have e : (μ ^ 2 * σ ^ 2 * n) ^ 2 = μ ^ 2 * μ ^ 2 * (n ^ 2 * (σ ^ 2) ^ 2) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (sq_nonneg n)) (by positivity)
  have h6 : 32 * L ^ 2 * M ^ 4 * Λ * μ ^ 2 ≤ μ ^ 2 * μ ^ 2 * (n ^ 2 * s2 ^ 2) := by linarith
  have h7 : 32 * L ^ 2 * M ^ 4 * Λ ≤ μ ^ 2 * (n ^ 2 * s2 ^ 2) := by
    have hμ2p : 0 < μ ^ 2 := by positivity
    have e : μ ^ 2 * μ ^ 2 * (n ^ 2 * s2 ^ 2) = μ ^ 2 * (n ^ 2 * s2 ^ 2) * μ ^ 2 := by ring
    rw [e] at h6
    exact le_of_mul_le_mul_right h6 hμ2p
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity)
    (by norm_num)]
  nlinarith

lemma burn_bias {μ L M σ n s2 : ℝ} (hμ : 0 < μ) (hn : 0 < n) (hs : σ ^ 2 ≤ s2)
    (h16 : 16 * L * M ^ 2 ≤ μ * σ ^ 2 * n) :
    8 * n * σ ^ 2 / μ * (L * M ^ 2) ≤ (n * s2) ^ 2 / 2 := by
  have h1 := mul_le_mul_of_nonneg_left h16 (show 0 ≤ n * σ ^ 2 by positivity)
  have h3 : (σ ^ 2) ^ 2 ≤ s2 ^ 2 := pow_le_pow_left₀ (sq_nonneg σ) hs 2
  have h4 : μ * n ^ 2 * (σ ^ 2) ^ 2 ≤ μ * n ^ 2 * s2 ^ 2 :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hμ (by norm_num)]
  nlinarith

lemma cross_term {t0 M R Λ μ L Δ : ℝ} (hμ : 0 < μ) (hL : 0 < L) (hΔ : 0 ≤ Δ)
    (hR : R = Real.sqrt (L * Δ)) :
    128 * t0 * M * R * Λ / μ ≤ t0 ^ 2 * Δ + 4096 * L * M ^ 2 * Λ ^ 2 / μ ^ 2 := by
  have hRL : R = Real.sqrt L * Real.sqrt Δ := by rw [hR, Real.sqrt_mul hL.le]
  have hsL : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
  have hsΔ : Real.sqrt Δ ^ 2 = Δ := Real.sq_sqrt hΔ
  have hsq := sq_nonneg (t0 * Real.sqrt Δ - 64 * M * Real.sqrt L * Λ / μ)
  have e : (t0 * Real.sqrt Δ - 64 * M * Real.sqrt L * Λ / μ) ^ 2 =
      t0 ^ 2 * Real.sqrt Δ ^ 2 + 4096 * M ^ 2 * Real.sqrt L ^ 2 * Λ ^ 2 / μ ^ 2 -
        128 * t0 * M * (Real.sqrt L * Real.sqrt Δ) * Λ / μ := by
    field_simp; ring
  rw [e, hsL, hsΔ] at hsq
  rw [hRL]
  have e2 : 4096 * M ^ 2 * L * Λ ^ 2 / μ ^ 2 = 4096 * L * M ^ 2 * Λ ^ 2 / μ ^ 2 := by ring
  linarith

lemma core_burn {μ L σ M Λ Δ T t0 β n s2 lam R N : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L) (hσ : 0 < σ)
    (hM : 0 < M) (hΛ : 1 ≤ Λ) (hΔ : 0 ≤ Δ) (hT : 1 ≤ T) (ht0 : 3 ≤ t0)
    (hTβ : T * β ≤ σ ^ 2) (hn : n = T + t0) (hR : R = Real.sqrt (L * Δ))
    (hs2 : s2 = σ ^ 2 + t0 * M * R / n) (hlam : lam = μ / (32 * n * s2))
    (hρ : 64 * L ^ 2 * M ^ 2 * Λ ≤ μ ^ 2 * σ ^ 2 * n)
    (hN : N = (t0 - 1) * (t0 - 2) * Δ + Λ / lam +
      16 * L / μ ^ 2 * M ^ 2 * (T * (2 * σ ^ 2 / M ^ 2) + Λ) + 8 * T * (T + t0) * β / μ) :
    N < μ ^ 2 / (256 * L * lam ^ 2 * M ^ 2) := by
  have hL : 0 < L := hμ.trans_le hμL
  have hn0 : 0 < n := by rw [hn]; linarith
  have hTn : T ≤ n := by rw [hn]; linarith
  have hR0 : 0 ≤ R := by rw [hR]; exact Real.sqrt_nonneg _
  have hR2 : R ^ 2 = L * Δ := by rw [hR]; exact Real.sq_sqrt (by positivity)
  have hcross0 : 0 ≤ t0 * M * R / n := by positivity
  have hs2σ : σ ^ 2 ≤ s2 := by rw [hs2]; linarith
  have hs2pos : 0 < s2 := lt_of_lt_of_le (by positivity) hs2σ
  have hns2 : t0 * M * R ≤ n * s2 := by
    have e : n * s2 = n * σ ^ 2 + t0 * M * R := by
      rw [hs2, mul_add, mul_div_cancel₀ _ hn0.ne']
    have : 0 ≤ n * σ ^ 2 := by positivity
    linarith
  have hlamdef : Λ / lam = 32 * n * s2 * Λ / μ := by
    rw [hlam]; field_simp
  have hbound : μ ^ 2 / (256 * L * lam ^ 2 * M ^ 2) = 4 * ((n * s2) ^ 2 / (L * M ^ 2)) := by
    rw [hlam]; field_simp; ring
  have h64a : 64 * L * M ^ 2 * Λ ≤ μ * σ ^ 2 * n := by
    have h1 : 64 * L * M ^ 2 * Λ * μ ≤ 64 * L ^ 2 * M ^ 2 * Λ := by
      have := mul_le_mul_of_nonneg_left hμL (show 0 ≤ 64 * L * M ^ 2 * Λ by positivity)
      have e : 64 * L * M ^ 2 * Λ * L = 64 * L ^ 2 * M ^ 2 * Λ := by ring
      linarith
    have h2 : 64 * L * M ^ 2 * Λ * μ ≤ μ * σ ^ 2 * n * μ := by
      have e : μ ^ 2 * σ ^ 2 * n = μ * σ ^ 2 * n * μ := by ring
      linarith
    exact le_of_mul_le_mul_right h2 hμ
  have h64b : 64 * L ^ 2 * M ^ 2 ≤ μ ^ 2 * σ ^ 2 * n := by
    have : 64 * L ^ 2 * M ^ 2 * 1 ≤ 64 * L ^ 2 * M ^ 2 * Λ :=
      mul_le_mul_of_nonneg_left hΛ (by positivity)
    linarith
  have h16 : 16 * L * M ^ 2 ≤ μ * σ ^ 2 * n := by
    have : 64 * L * M ^ 2 * 1 ≤ 64 * L * M ^ 2 * Λ :=
      mul_le_mul_of_nonneg_left hΛ (by positivity)
    have : 0 ≤ L * M ^ 2 := by positivity
    linarith
  have hbeta : 8 * T * (T + t0) * β / μ ≤ 8 * n * σ ^ 2 / μ := by
    apply div_le_div_of_nonneg_right _ hμ.le
    have e : 8 * T * (T + t0) * β = 8 * n * (T * β) := by rw [hn]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hTβ (by positivity)
  have hexpand : 16 * L / μ ^ 2 * M ^ 2 * (T * (2 * σ ^ 2 / M ^ 2) + Λ) =
      32 * L * T * σ ^ 2 / μ ^ 2 + 16 * L / μ ^ 2 * M ^ 2 * Λ := by
    field_simp; ring
  have hLM : 0 < L * M ^ 2 := by positivity
  have T1 := burn_start ht0 hΔ hL hM hR2 hR0 hns2
  have T2 := burn_martingale hμ hn0 hs2σ h64a
  have T3 := burn_variance (by linarith) hTn hs2σ h64b hμ
  have T4 := burn_square hμ hμL hΛ hs2σ hρ
  have T5 := burn_bias hμ hn0 hs2σ h16
  have hb5 := mul_le_mul_of_nonneg_right hbeta hLM.le
  have hNe : N * (L * M ^ 2) = (t0 - 1) * (t0 - 2) * Δ * (L * M ^ 2) +
      32 * n * s2 * Λ / μ * (L * M ^ 2) + 32 * L * T * σ ^ 2 / μ ^ 2 * (L * M ^ 2) +
      16 * L / μ ^ 2 * M ^ 2 * Λ * (L * M ^ 2) + 8 * T * (T + t0) * β / μ * (L * M ^ 2) := by
    rw [hN, hlamdef, hexpand]; ring
  have hN3 : N * (L * M ^ 2) ≤ 3 * (n * s2) ^ 2 := by linarith
  have hN3' : N ≤ 3 * ((n * s2) ^ 2 / (L * M ^ 2)) := by
    rw [mul_div_assoc', le_div_iff₀ hLM]; exact hN3
  have hX : 0 < (n * s2) ^ 2 / (L * M ^ 2) := by positivity
  rw [hbound]; linarith

lemma core_accuracy {μ L σ M Λ Δ ε T t0 β n s2 lam R N : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hσ : 0 < σ) (hM : 0 < M) (hΛ : 1 ≤ Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hT : 1 ≤ T) (ht0 : 3 ≤ t0)
    (hTβ : T * β ≤ σ ^ 2) (hn : n = T + t0) (hR : R = Real.sqrt (L * Δ))
    (hs2 : s2 = σ ^ 2 + t0 * M * R / n) (hlam : lam = μ / (32 * n * s2))
    (hρ : 64 * L ^ 2 * M ^ 2 * Λ ≤ μ ^ 2 * σ ^ 2 * n)
    (hb1 : 4 * t0 * Real.sqrt (Δ / ε) ≤ n)
    (hb2 : 1024 * σ ^ 2 * (L / μ + Λ) / (μ * ε) ≤ n)
    (hN : N = (t0 - 1) * (t0 - 2) * Δ + Λ / lam +
      16 * L / μ ^ 2 * M ^ 2 * (T * (2 * σ ^ 2 / M ^ 2) + Λ) + 8 * T * (T + t0) * β / μ) :
    N / ((n - 1) * (n - 2)) ≤ ε := by
  have hL : 0 < L := hμ.trans_le hμL
  have hn4 : 4 ≤ n := by rw [hn]; linarith
  have hn0 : 0 < n := by linarith
  have hTn : T ≤ n := by rw [hn]; linarith
  have hlamdef : Λ / lam = 32 * n * s2 * Λ / μ := by
    have hs2pos : 0 < s2 := by
      rw [hs2]
      have : 0 ≤ t0 * M * R / n := by
        have : 0 ≤ R := by rw [hR]; exact Real.sqrt_nonneg _
        positivity
      positivity
    rw [hlam]; field_simp
  have h64a : 64 * L * M ^ 2 * Λ ≤ μ * σ ^ 2 * n := by
    have h1 : 64 * L * M ^ 2 * Λ * μ ≤ 64 * L ^ 2 * M ^ 2 * Λ := by
      have := mul_le_mul_of_nonneg_left hμL (show 0 ≤ 64 * L * M ^ 2 * Λ by positivity)
      have e : 64 * L * M ^ 2 * Λ * L = 64 * L ^ 2 * M ^ 2 * Λ := by ring
      linarith
    have h2 : 64 * L * M ^ 2 * Λ * μ ≤ μ * σ ^ 2 * n * μ := by
      have e : μ ^ 2 * σ ^ 2 * n = μ * σ ^ 2 * n * μ := by ring
      linarith
    exact le_of_mul_le_mul_right h2 hμ
  have hbeta : 8 * T * (T + t0) * β / μ ≤ 8 * n * σ ^ 2 / μ := by
    apply div_le_div_of_nonneg_right _ hμ.le
    have e : 8 * T * (T + t0) * β = 8 * n * (T * β) := by rw [hn]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hTβ (by positivity)
  have hexpand : 16 * L / μ ^ 2 * M ^ 2 * (T * (2 * σ ^ 2 / M ^ 2) + Λ) =
      32 * L * T * σ ^ 2 / μ ^ 2 + 16 * L / μ ^ 2 * M ^ 2 * Λ := by
    field_simp; ring
  have hW : n ^ 2 / 4 ≤ (n - 1) * (n - 2) := by
    have h := mul_nonneg (show 0 ≤ n - 4 by linarith) hn0.le
    nlinarith only [h]
  have hWpos : 0 < (n - 1) * (n - 2) := by
    have h1 : 0 < n - 1 := by linarith
    have h2 : 0 < n - 2 := by linarith
    exact mul_pos h1 h2
  rw [div_le_iff₀ hWpos]
  have hcross := cross_term (t0 := t0) (M := M) (Λ := Λ) hμ hL hΔ hR
  obtain ⟨A, hA⟩ : ∃ A, A = σ ^ 2 * Λ * n / μ := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = L / μ * σ ^ 2 * n / μ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hc2 : 4096 * L * M ^ 2 * Λ ^ 2 / μ ^ 2 ≤ 64 * A := by
    rw [div_le_iff₀ (by positivity)]
    have h := mul_le_mul_of_nonneg_left h64a (show 0 ≤ 64 * Λ by positivity)
    have e : 64 * A * μ ^ 2 = 64 * Λ * (μ * σ ^ 2 * n) := by rw [hA]; field_simp
    have e2 : 64 * Λ * (64 * L * M ^ 2 * Λ) = 4096 * L * M ^ 2 * Λ ^ 2 := by ring
    linarith
  have hc3 : 4 * (32 * L * T * σ ^ 2 / μ ^ 2) ≤ 128 * B := by
    have e : 128 * B = 128 * L * σ ^ 2 * n / μ ^ 2 := by rw [hB]; field_simp
    have e2 : 4 * (32 * L * T * σ ^ 2 / μ ^ 2) = 128 * L * σ ^ 2 * T / μ ^ 2 := by ring
    rw [e, e2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hTn (by positivity)
  have hc4 : 4 * (16 * L / μ ^ 2 * M ^ 2 * Λ) ≤ A := by
    have e1 : 4 * (16 * L / μ ^ 2 * M ^ 2 * Λ) = 64 * L * M ^ 2 * Λ / μ ^ 2 := by ring
    have e2 : A = Λ * (μ * σ ^ 2 * n) / μ ^ 2 := by rw [hA]; field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h1 : 64 * L * M ^ 2 * Λ * 1 ≤ 64 * L * M ^ 2 * Λ * Λ :=
      mul_le_mul_of_nonneg_left hΛ (by positivity)
    have h2 := mul_le_mul_of_nonneg_left h64a (show 0 ≤ Λ by linarith)
    have e3 : 64 * L * M ^ 2 * Λ * Λ = Λ * (64 * L * M ^ 2 * Λ) := by ring
    linarith
  have hc5 : 4 * (8 * n * σ ^ 2 / μ) ≤ 32 * A := by
    have e : 4 * (8 * n * σ ^ 2 / μ) = 32 * (σ ^ 2 * n / μ) := by ring
    have h : σ ^ 2 * n / μ ≤ A := by
      rw [hA]
      apply div_le_div_of_nonneg_right _ hμ.le
      have := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ σ ^ 2 * n by positivity)
      have e2 : σ ^ 2 * n * Λ = σ ^ 2 * Λ * n := by ring
      linarith
    linarith
  have hs2e : 32 * n * s2 * Λ / μ = 32 * A + 32 * t0 * M * R * Λ / μ := by
    rw [hs2, hA]; field_simp
  have hw0 : (t0 - 1) * (t0 - 2) * Δ ≤ t0 ^ 2 * Δ := by
    have e : (t0 - 1) * (t0 - 2) = t0 ^ 2 - 3 * t0 + 2 := by ring
    have h : (t0 - 1) * (t0 - 2) ≤ t0 ^ 2 := by rw [e]; linarith only [ht0]
    exact mul_le_mul_of_nonneg_right h hΔ
  have hfirst : 4 * N ≤ 5 * (t0 ^ 2 * Δ) + 225 * A + 128 * B := by
    have hNsum : 4 * N = 4 * ((t0 - 1) * (t0 - 2) * Δ) + 128 * A + 4 * (32 * t0 * M * R * Λ / μ) +
        4 * (32 * L * T * σ ^ 2 / μ ^ 2) + 4 * (16 * L / μ ^ 2 * M ^ 2 * Λ) +
        4 * (8 * T * (T + t0) * β / μ) := by
      rw [hN, hlamdef, hexpand, hs2e]; ring
    have hcross' : 4 * (32 * t0 * M * R * Λ / μ) ≤ t0 ^ 2 * Δ + 4096 * L * M ^ 2 * Λ ^ 2 / μ ^ 2 := by
      have e : 4 * (32 * t0 * M * R * Λ / μ) = 128 * t0 * M * R * Λ / μ := by ring
      rw [e]; exact hcross
    have hb4 : 4 * (8 * T * (T + t0) * β / μ) ≤ 4 * (8 * n * σ ^ 2 / μ) :=
      mul_le_mul_of_nonneg_left hbeta (by norm_num)
    have hw4 : 4 * ((t0 - 1) * (t0 - 2) * Δ) ≤ 4 * (t0 ^ 2 * Δ) :=
      mul_le_mul_of_nonneg_left hw0 (by norm_num)
    generalize 4 * ((t0 - 1) * (t0 - 2) * Δ) = a1 at hNsum hw4
    generalize 4 * (32 * t0 * M * R * Λ / μ) = a2 at hNsum hcross'
    generalize 4 * (32 * L * T * σ ^ 2 / μ ^ 2) = a3 at hNsum hc3
    generalize 4 * (16 * L / μ ^ 2 * M ^ 2 * Λ) = a4 at hNsum hc4
    generalize 4 * (8 * T * (T + t0) * β / μ) = a5 at hNsum hb4
    generalize 4 * (8 * n * σ ^ 2 / μ) = a6 at hb4 hc5
    generalize 4096 * L * M ^ 2 * Λ ^ 2 / μ ^ 2 = a7 at hcross' hc2
    generalize t0 ^ 2 * Δ = a8 at hw4 hcross' ⊢
    linarith only [hNsum, hw4, hcross', hc2, hc3, hc4, hb4, hc5]
  have hlast1 : 16 * (t0 ^ 2 * Δ) ≤ ε * n ^ 2 := by
    have hsq : (4 * t0 * Real.sqrt (Δ / ε)) ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ (by positivity) hb1 2
    have e : (4 * t0 * Real.sqrt (Δ / ε)) ^ 2 = 16 * t0 ^ 2 * (Δ / ε) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    rw [e] at hsq
    have h := mul_le_mul_of_nonneg_left hsq hε.le
    have e2 : ε * (16 * t0 ^ 2 * (Δ / ε)) = 16 * (t0 ^ 2 * Δ) := by field_simp
    linarith
  have hlast2 : 1024 * (A + B) ≤ ε * n ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hb2 (show 0 ≤ ε * n by positivity)
    have e : ε * n * (1024 * σ ^ 2 * (L / μ + Λ) / (μ * ε)) = 1024 * (A + B) := by
      rw [hA, hB]; field_simp; ring
    have e2 : ε * n * n = ε * n ^ 2 := by ring
    linarith
  have hεW := mul_le_mul_of_nonneg_left hW hε.le
  have hp3 : 0 ≤ t0 ^ 2 * Δ := by positivity
  have e3 : ε * (n ^ 2 / 4) = ε * n ^ 2 / 4 := by ring
  linarith only [hfirst, hlast1, hlast2, hεW, hp3, e3, hA0, hB0]

lemma core_tuning {μ L σ M Λ Δ ε T t0 β n s2 lam R N : ℝ} (hμ : 0 < μ) (hμL : μ ≤ L)
    (hσ : 0 < σ) (hM : 0 < M) (hΛ : 1 ≤ Λ) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (hT : 1 ≤ T) (ht0 : 3 ≤ t0)
    (hTβ : T * β ≤ σ ^ 2) (hn : n = T + t0) (hR : R = Real.sqrt (L * Δ))
    (hs2 : s2 = σ ^ 2 + t0 * M * R / n) (hlam : lam = μ / (32 * n * s2))
    (hρ : 64 * L ^ 2 * M ^ 2 * Λ ≤ μ ^ 2 * σ ^ 2 * n)
    (hb1 : 4 * t0 * Real.sqrt (Δ / ε) ≤ n)
    (hb2 : 1024 * σ ^ 2 * (L / μ + Λ) / (μ * ε) ≤ n)
    (hN : N = (t0 - 1) * (t0 - 2) * Δ + Λ / lam +
      16 * L / μ ^ 2 * M ^ 2 * (T * (2 * σ ^ 2 / M ^ 2) + Λ) + 8 * T * (T + t0) * β / μ) :
    N < μ ^ 2 / (256 * L * lam ^ 2 * M ^ 2) ∧ N / ((n - 1) * (n - 2)) ≤ ε :=
  ⟨core_burn hμ hμL hσ hM hΛ hΔ hT ht0 hTβ hn hR hs2 hlam hρ hN,
    core_accuracy hμ hμL hσ hM hΛ hΔ hε hT ht0 hTβ hn hR hs2 hlam hρ hb1 hb2 hN⟩

end OracleTemplate.HeavyTailedPL
