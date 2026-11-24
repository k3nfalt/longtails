import LongTails.Proofs.MeanSquaredPLHard

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.MeanSquaredPLParameters

open LongTails.Proofs.ThirdOrderMaskedOracle LongTails.Proofs.MeanSquaredPLHard
open LongTails.Proofs.RelativeHessianLocalized (radius)
open LongTails.Proofs.AbcHardOracle (Scale)
open LongTails.Setups.HighDimensionalMeanSquaredSmoothPL

theorem chain_failure_at (p : Params) (hv : spec.valid p) (qc nreal : ℝ) (hq0 : 0 < qc)
    (hq1 : qc ≤ 1) (hvar : (1 - qc) * (2 ^ 116 * p.μ * p.ε) ≤ qc * p.σ ^ 2)
    (hn16 : 16 ≤ nreal) (hnL : 2 ^ 65 * p.μ * nreal ≤ p.L)
    (hnLbar : (2 ^ 69 * p.μ * nreal) ^ 2 ≤ p.Lbar ^ 2 * qc)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) (N : ℕ)
    (hN : (N : ℝ) * qc * 64 ≤ nreal) (hdim : 2 ^ 138 * ((N : ℝ) + 1) * nreal ^ 3 ≤ p.d) :
    ∃ (I : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (oracle : Oracle (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
        (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p I oracle ∧
        ¬ spec.successful p I
          (fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
            execute oracle A (fun _ => N) seed.1 seed.2)
          ⟨(A.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩ := by
  have hv' := hv
  obtain ⟨⟨hμ, hL, hLbar, hσ, hΔ, hε⟩, hκ, hΔε, hd⟩ := hv'
  change 0 < p.μ at hμ
  change 0 < p.ε at hε
  have hn0 : 0 ≤ nreal := by linarith
  set T := ⌊nreal⌋₊ with hTdef
  have hT16 : 16 ≤ T := Nat.le_floor (by exact_mod_cast hn16)
  have hTle : (T : ℝ) ≤ nreal := Nat.floor_le hn0
  have hTgt : nreal < (T : ℝ) + 1 := Nat.lt_floor_add_one nreal
  have hTR : (16 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT16
  have hTpos : (0 : ℝ) < (T : ℝ) := by linarith
  obtain ⟨n, hn1⟩ : ∃ n, n + 1 = T := ⟨T - 1, by omega⟩
  have hn1R : ((n + 1 : ℕ) : ℝ) = (T : ℝ) := by rw [hn1]
  have hnR : (n : ℝ) = (T : ℝ) - 1 := by
    have : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    linarith
  set a : ℝ := 16 * p.ε / T with hadef
  set ρ : ℝ := 2 ^ 10 * p.μ * T with hρdef
  have ha : 0 < a := by positivity
  have hρ : 0 < ρ := by positivity
  have hlam : 0 < √(a / ρ) := Real.sqrt_pos.mpr (div_pos ha hρ)
  let S : Scale := ⟨a, √(a / ρ), ha, hlam⟩
  have hSa : S.a = a := rfl
  have hlam2 : S.lam ^ 2 = a / ρ := Real.sq_sqrt (div_pos ha hρ).le
  have hρa : ρ * (a / ρ) = a := by
    rw [mul_comm]
    exact div_mul_cancel₀ a hρ.ne'
  have haρ0 : a / ρ ≠ 0 := (div_pos ha hρ).ne'
  have hratio : S.a / S.lam ^ 2 = ρ := by
    rw [hlam2, hSa, div_eq_iff haρ0]
    exact hρa.symm
  have hTT : 16 * p.ε / (T : ℝ) * (T : ℝ) = 16 * p.ε := div_mul_cancel₀ _ hTpos.ne'
  have haρ : a * ρ = 2 ^ 14 * p.μ * p.ε := by
    calc a * ρ = 2 ^ 10 * p.μ * (16 * p.ε / (T : ℝ) * (T : ℝ)) := by
          rw [hadef, hρdef]
          ring
      _ = 2 ^ 14 * p.μ * p.ε := by
          rw [hTT]
          ring
  have hratio2 : (S.a / S.lam) ^ 2 = 2 ^ 14 * p.μ * p.ε := by
    rw [div_pow, hlam2, hSa, div_eq_iff haρ0]
    calc a ^ 2 = a * (ρ * (a / ρ)) := by rw [hρa]; ring
      _ = 2 ^ 14 * p.μ * p.ε * (a / ρ) := by rw [← haρ]; ring
  have hC : ChainData p n S qc := by
    refine ⟨hq0, hq1, ?_, ?_, ?_, ?_, ?_⟩
    · rw [mul_div_assoc, hratio, hρdef]
      have : 2 ^ 65 * p.μ * (T : ℝ) ≤ 2 ^ 65 * p.μ * nreal :=
        mul_le_mul_of_nonneg_left hTle (by positivity)
      linarith
    · rw [mul_div_assoc, hratio, hρdef, div_le_iff₀ hq0]
      have h1 : 2 ^ 59 * (2 ^ 10 * p.μ * (T : ℝ)) ≤ 2 ^ 69 * p.μ * nreal := by
        have : 2 ^ 69 * p.μ * (T : ℝ) ≤ 2 ^ 69 * p.μ * nreal :=
          mul_le_mul_of_nonneg_left hTle (by positivity)
        linarith
      have h2 : (2 ^ 59 * (2 ^ 10 * p.μ * (T : ℝ))) ^ 2 ≤ (2 ^ 69 * p.μ * nreal) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      linarith
    · rw [mul_pow, hratio2]
      have h1 : (1 / qc - 1) * (2 ^ 116 * p.μ * p.ε) ≤ p.σ ^ 2 := by
        have hqq : 1 / qc * qc = 1 := by rw [one_div, inv_mul_cancel₀ hq0.ne']
        have h2 : (1 / qc - 1) * (2 ^ 116 * p.μ * p.ε) =
            (1 - qc) * (2 ^ 116 * p.μ * p.ε) / qc := by
          rw [eq_div_iff hq0.ne']
          calc (1 / qc - 1) * (2 ^ 116 * p.μ * p.ε) * qc =
                (1 / qc * qc - qc) * (2 ^ 116 * p.μ * p.ε) := by ring
            _ = (1 - qc) * (2 ^ 116 * p.μ * p.ε) := by rw [hqq]
        rw [h2, div_le_iff₀ hq0]
        linarith
      refine le_trans (le_of_eq ?_) h1
      ring
    · rw [hn1R, hlam2, hSa, ← hρdef]
      exact le_of_eq hρa
    · rw [hn1R, hSa, hadef]
      have h1 : 16 * p.ε / (T : ℝ) * (4 * (T : ℝ)) = 64 * p.ε := by
        calc 16 * p.ε / (T : ℝ) * (4 * (T : ℝ)) = 4 * (16 * p.ε / (T : ℝ) * (T : ℝ)) := by ring
          _ = 64 * p.ε := by rw [hTT]; ring
      rw [h1]
      exact hΔε
  have hT2 : 8 ≤ T / 2 := by omega
  obtain ⟨M, hM⟩ : ∃ M, M + 1 = T / 2 := ⟨T / 2 - 1, by omega⟩
  have hhalf1 : 2 * (T / 2) ≤ T := Nat.mul_div_le T 2
  have hhalf2 : T < 2 * (T / 2) + 2 := by omega
  have hMR : (M : ℝ) + 1 = ((T / 2 : ℕ) : ℝ) := by
    have : ((M + 1 : ℕ) : ℝ) = ((T / 2 : ℕ) : ℝ) := by rw [hM]
    push_cast at this
    exact this
  have hhalf1R : 2 * ((T / 2 : ℕ) : ℝ) ≤ (T : ℝ) := by exact_mod_cast hhalf1
  have hhalf2R : (T : ℝ) < 2 * ((T / 2 : ℕ) : ℝ) + 2 := by exact_mod_cast hhalf2
  have hNq : (N : ℝ) * qc * 8 ≤ (M : ℝ) + 1 := by
    rw [hMR]
    linarith
  have hloss : 64 * p.ε < 49 * (S.a * ((n : ℝ) - ((M : ℝ) + 1))) := by
    rw [hMR, hnR, hSa, hadef]
    have h1 : (7 : ℝ) / 16 * T ≤ (T : ℝ) - 1 - ((T / 2 : ℕ) : ℝ) := by linarith
    have h2 : 16 * p.ε / (T : ℝ) * ((7 : ℝ) / 16 * T) ≤
        16 * p.ε / (T : ℝ) * ((T : ℝ) - 1 - ((T / 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 16 * p.ε / (T : ℝ) * ((7 : ℝ) / 16 * T) = 7 * p.ε := by
      calc 16 * p.ε / (T : ℝ) * ((7 : ℝ) / 16 * T) =
            7 / 16 * (16 * p.ε / (T : ℝ) * (T : ℝ)) := by ring
        _ = 7 * p.ε := by rw [hTT]; ring
    linarith
  have hdim' : 8 * ((2 * (N + 1 : ℕ) : ℕ) * ((n + 1 : ℕ) : ℝ) *
      ((2 * radius n) ^ 2 / (1 / 40) ^ 2)) + (n + 1 : ℕ) ≤ p.d := by
    have hrad : radius n = 2 ^ 60 * (T : ℝ) := by
      unfold radius
      rw [hn1R]
    rw [hn1R, hrad]
    push_cast
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have hT3 : (T : ℝ) ^ 3 ≤ nreal ^ 3 := pow_le_pow_left₀ hTpos.le hTle 3
    have hT2 : (1 : ℝ) ≤ (T : ℝ) ^ 2 := by nlinarith
    have hT3' : (T : ℝ) ≤ (T : ℝ) ^ 3 := by
      have h1 := mul_le_mul_of_nonneg_left hT2 hTpos.le
      have h2 : (T : ℝ) ^ 3 = (T : ℝ) * (T : ℝ) ^ 2 := by ring
      linarith
    have hT30 : (0 : ℝ) ≤ (T : ℝ) ^ 3 := pow_nonneg hTpos.le 3
    have hA : (T : ℝ) ≤ ((N : ℝ) + 1) * (T : ℝ) ^ 3 := by
      have := mul_nonneg hN0 hT30
      linarith
    have hNT : ((N : ℝ) + 1) * (T : ℝ) ^ 3 ≤ ((N : ℝ) + 1) * nreal ^ 3 :=
      mul_le_mul_of_nonneg_left hT3 (by linarith)
    have hY0 : 0 ≤ ((N : ℝ) + 1) * (T : ℝ) ^ 3 := mul_nonneg (by linarith) hT30
    have hkey : 25600 * 2 ^ 122 * (((N : ℝ) + 1) * (T : ℝ) ^ 3) + (T : ℝ) ≤ p.d := by
      have hB : 25600 * 2 ^ 122 * (((N : ℝ) + 1) * (T : ℝ) ^ 3) + (T : ℝ) ≤
          2 ^ 138 * (((N : ℝ) + 1) * (T : ℝ) ^ 3) := by linarith
      have hC : 2 ^ 138 * (((N : ℝ) + 1) * (T : ℝ) ^ 3) ≤
          2 ^ 138 * (((N : ℝ) + 1) * nreal ^ 3) :=
        mul_le_mul_of_nonneg_left hNT (by positivity)
      linarith
    refine le_trans (le_of_eq ?_) hkey
    ring
  obtain ⟨π, hπ⟩ := chain_failure p hv S qc hC A N M hNq hloss hdim'
  exact ⟨objective S π p.x0, hardOracle p S qc π, hard_admissible p hv S qc hC π, hπ⟩

end LongTails.Proofs.MeanSquaredPLParameters
