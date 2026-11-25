import LongTails.Proofs.MeanSquaredPLParameters
import LongTails.Proofs.MeanSquaredPLQuadratic

open MeasureTheory OracleTemplate

namespace LongTails.Proofs.MeanSquaredPLLowerBound

open LongTails.Proofs.MeanSquaredPLParameters LongTails.Proofs.MeanSquaredPLQuadratic
open LongTails.Setups.HighDimensionalMeanSquaredSmoothPL

theorem failure_at (p : Params) (hv : spec.valid p)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
      (EuclideanSpace ℝ (Fin p.d))) (N : ℕ)
    (hN : (N : ℝ) ≤ (p.L / p.μ + (p.σ / √(p.μ * p.ε)) ^ 2 +
      min (p.L / p.μ * (p.σ / √(p.μ * p.ε)) ^ 2) (p.Lbar / p.μ * (p.σ / √(p.μ * p.ε)))) /
        2 ^ 200) :
    ∃ (I : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (oracle : Oracle (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))
        (EuclideanSpace ℝ (Fin p.d) × EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p I oracle ∧
        ¬ spec.successful p I
          (fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
            execute oracle A (fun _ => N) seed.1 seed.2)
          ⟨(A.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩ := by
  have hv' := hv
  obtain ⟨⟨hμ, hL, hLbar, hσ, hΔ, hε⟩, hκ73, hΔε, hdim⟩ := hv'
  change 0 < p.μ at hμ
  change p.μ ≤ p.L at hL
  change p.L ≤ p.Lbar at hLbar
  change 0 ≤ p.σ at hσ
  change 0 < p.ε at hε
  have hμε : 0 < p.μ * p.ε := mul_pos hμ hε
  have hr : 0 < √(p.μ * p.ε) := Real.sqrt_pos.mpr hμε
  have hr2 : √(p.μ * p.ε) ^ 2 = p.μ * p.ε := Real.sq_sqrt hμε.le
  set s := p.σ / √(p.μ * p.ε) with hs
  set κ := p.L / p.μ with hκdef
  set κb := p.Lbar / p.μ with hκbdef
  have hs0 : 0 ≤ s := div_nonneg hσ hr.le
  have hσs : p.σ ^ 2 = s ^ 2 * (p.μ * p.ε) := by
    rw [hs, div_pow, hr2, div_mul_cancel₀ _ hμε.ne']
  have hκ : (2 : ℝ) ^ 73 ≤ κ := by
    rw [hκdef, le_div_iff₀ hμ]
    exact hκ73
  have hκκb : κ ≤ κb := div_le_div_of_nonneg_right hLbar hμ.le
  have hLκ : p.L = κ * p.μ := by rw [hκdef, div_mul_cancel₀ _ hμ.ne']
  have hLbκ : p.Lbar = κb * p.μ := by rw [hκbdef, div_mul_cancel₀ _ hμ.ne']
  have hκ0 : 0 < κ := lt_of_lt_of_le (by positivity) hκ
  have hκb0 : 0 < κb := lt_of_lt_of_le hκ0 hκκb
  have hκ1 : (1 : ℝ) ≤ κ := le_trans (by norm_num) hκ
  have hs20 : 0 ≤ s ^ 2 := sq_nonneg s
  have hκs2 : 0 ≤ κ * s ^ 2 := mul_nonneg hκ0.le hs20
  have hκbs : 0 ≤ κb * s := mul_nonneg hκb0.le hs0
  have hdim' : κ ^ 4 * (1 + s ^ 2) ≤ p.d := by
    have h1 : p.σ ^ 2 / (p.μ * p.ε) = s ^ 2 := by
      rw [hσs, mul_div_assoc, div_self hμε.ne', mul_one]
    rw [← h1]
    exact hdim
  have hmin_le1 : min (κ * s ^ 2) (κb * s) ≤ κ * s ^ 2 := min_le_left _ _
  have hmin_le2 : min (κ * s ^ 2) (κb * s) ≤ κb * s := min_le_right _ _
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hNle : (N : ℝ) * 2 ^ 200 ≤ κ + s ^ 2 + min (κ * s ^ 2) (κb * s) := by
    rwa [le_div_iff₀ (by positivity)] at hN
  have hd0 : 0 < p.d := by
    have h1 : (0 : ℝ) < κ ^ 4 * (1 + s ^ 2) := by positivity
    have h2 : (0 : ℝ) < (p.d : ℝ) := lt_of_lt_of_le h1 hdim'
    exact_mod_cast h2
  have hKS : 0 ≤ κ * (1 + s ^ 2) := mul_nonneg hκ0.le (by linarith)
  have hN1 : (N : ℝ) + 1 ≤ κ * (1 + s ^ 2) := by
    have h1 : (N : ℝ) * 2 ^ 200 ≤ κ + s ^ 2 + κ * s ^ 2 := by linarith
    have h2 : s ^ 2 ≤ κ * s ^ 2 := by
      have := mul_le_mul_of_nonneg_right hκ1 hs20
      linarith
    have h3 : κ * (1 + s ^ 2) = κ + κ * s ^ 2 := by ring
    have h4 : (N : ℝ) ≤ (κ + s ^ 2 + κ * s ^ 2) / 2 ^ 200 := by
      rw [le_div_iff₀ (by positivity)]
      exact h1
    have h5 : (κ + s ^ 2 + κ * s ^ 2) / 2 ^ 200 ≤ (κ + s ^ 2 + κ * s ^ 2) / 2 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) (by norm_num)
    linarith
  have chain_dim : ∀ nreal : ℝ, 0 ≤ nreal → 2 ^ 65 * nreal ≤ κ →
      2 ^ 138 * ((N : ℝ) + 1) * nreal ^ 3 ≤ p.d := by
    intro nreal hn0 hn
    have h1 : (2 ^ 65 * nreal) ^ 3 ≤ κ ^ 3 := pow_le_pow_left₀ (by positivity) hn 3
    have hn3 : 0 ≤ nreal ^ 3 := pow_nonneg hn0 3
    have h2 : 2 ^ 138 * nreal ^ 3 ≤ κ ^ 3 := by
      have h6 : (2 ^ 65 * nreal) ^ 3 = 2 ^ 195 * nreal ^ 3 := by ring
      rw [h6] at h1
      linarith
    have h4 : 0 ≤ 2 ^ 138 * nreal ^ 3 := by positivity
    have h3 : ((N : ℝ) + 1) * (2 ^ 138 * nreal ^ 3) ≤ (κ * (1 + s ^ 2)) * κ ^ 3 :=
      mul_le_mul hN1 h2 h4 hKS
    have h7 : 2 ^ 138 * ((N : ℝ) + 1) * nreal ^ 3 = ((N : ℝ) + 1) * (2 ^ 138 * nreal ^ 3) := by
      ring
    have h8 : κ * (1 + s ^ 2) * κ ^ 3 = κ ^ 4 * (1 + s ^ 2) := by ring
    linarith
  by_cases hcase1 : s ^ 2 ≤ 2 ^ 116
  · have hT : κ + s ^ 2 + min (κ * s ^ 2) (κb * s) ≤ 2 ^ 118 * κ := by
      have h1 : κ * s ^ 2 ≤ κ * 2 ^ 116 := mul_le_mul_of_nonneg_left hcase1 hκ0.le
      linarith
    have hn0 : (0 : ℝ) ≤ κ / 2 ^ 69 := div_nonneg hκ0.le (by positivity)
    have hκμ : 0 < κ * p.μ := mul_pos hκ0 hμ
    refine chain_failure_at p hv 1 (κ / 2 ^ 69) (by norm_num) le_rfl ?_ ?_ ?_ ?_ A N ?_ ?_
    · simp only [sub_self, zero_mul, one_mul]
      positivity
    · rw [le_div_iff₀ (by positivity)]
      linarith
    · rw [hLκ]
      have h1 : 2 ^ 65 * p.μ * (κ / 2 ^ 69) = κ * p.μ / 16 := by ring
      rw [h1]
      linarith
    · rw [hLbκ, mul_one]
      have h1 : 2 ^ 69 * p.μ * (κ / 2 ^ 69) = κ * p.μ := by ring
      rw [h1]
      exact pow_le_pow_left₀ hκμ.le (mul_le_mul_of_nonneg_right hκκb hμ.le) 2
    · rw [mul_one, le_div_iff₀ (by positivity)]
      linarith
    · apply chain_dim _ hn0
      have h1 : 2 ^ 65 * (κ / 2 ^ 69) = κ / 16 := by ring
      rw [h1]
      linarith
  · push Not at hcase1
    have hs1 : (2 : ℝ) ^ 58 < s := by
      by_contra hcon
      push Not at hcon
      have h1 : s ^ 2 ≤ (2 ^ 58) ^ 2 := pow_le_pow_left₀ hs0 hcon 2
      have h2 : ((2 : ℝ) ^ 58) ^ 2 = 2 ^ 116 := by norm_num
      linarith
    have hspos : 0 < s := lt_trans (by positivity) hs1
    have hs2 : 0 < s ^ 2 := by positivity
    have hs1' : (1 : ℝ) ≤ s := le_trans (by norm_num) hs1.le
    have hss : s * s = s ^ 2 := by ring
    have hs21 : (1 : ℝ) ≤ s ^ 2 := le_trans (by norm_num) hcase1.le
    by_cases hcase2 : 2 ^ 15 * s ≤ κb
    · have hκm : κ ≤ min (κ * s ^ 2) (κb * s) := by
        apply le_min
        · have := mul_le_mul_of_nonneg_left hs21 hκ0.le
          linarith
        · have := mul_le_mul_of_nonneg_left hs1' hκb0.le
          linarith
      have hsm : s ^ 2 ≤ min (κ * s ^ 2) (κb * s) := by
        apply le_min
        · have := mul_le_mul_of_nonneg_right hκ1 hs20
          linarith
        · have h1 : s ≤ κb := by nlinarith
          have := mul_le_mul_of_nonneg_right h1 hs0
          linarith
      have hT : κ + s ^ 2 + min (κ * s ^ 2) (κb * s) ≤ 3 * min (κ * s ^ 2) (κb * s) := by
        linarith
      set qc : ℝ := 2 ^ 116 / s ^ 2 with hqc
      have hq0 : 0 < qc := by positivity
      have hq1 : qc ≤ 1 := by
        rw [hqc, div_le_one hs2]
        exact hcase1.le
      have hqσ : qc * p.σ ^ 2 = 2 ^ 116 * p.μ * p.ε := by
        rw [hqc, hσs, ← mul_assoc, div_mul_cancel₀ _ hs2.ne']
        ring
      set nreal : ℝ := min (κ / 2 ^ 65) (κb / (2 ^ 11 * s)) with hnreal
      have hn16 : 16 ≤ nreal := by
        apply le_min
        · rw [le_div_iff₀ (by positivity)]
          linarith
        · rw [le_div_iff₀ (by positivity)]
          linarith
      have hnle1 : nreal ≤ κ / 2 ^ 65 := min_le_left _ _
      have hnle2 : nreal ≤ κb / (2 ^ 11 * s) := min_le_right _ _
      have hn0 : 0 ≤ nreal := by linarith
      have hn65 : 2 ^ 65 * nreal ≤ κ := by
        rw [le_div_iff₀ (by positivity)] at hnle1
        linarith
      refine chain_failure_at p hv qc nreal hq0 hq1 ?_ hn16 ?_ ?_ A N ?_ ?_
      · rw [hqσ]
        have h1 : 0 ≤ 2 ^ 116 * p.μ * p.ε := by positivity
        have h2 := mul_nonneg hq0.le h1
        linarith
      · rw [hLκ]
        have := mul_le_mul_of_nonneg_left hn65 hμ.le
        linarith
      · rw [hLbκ]
        have h1 : 2 ^ 69 * p.μ * nreal ≤ 2 ^ 69 * p.μ * (κb / (2 ^ 11 * s)) :=
          mul_le_mul_of_nonneg_left hnle2 (by positivity)
        have h2 : (2 ^ 69 * p.μ * nreal) ^ 2 ≤ (2 ^ 69 * p.μ * (κb / (2 ^ 11 * s))) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h1 2
        refine h2.trans (le_of_eq ?_)
        rw [hqc]
        ring
      · have hgoal1 : (N : ℝ) * qc * 64 ≤ κ / 2 ^ 65 := by
          rw [hqc, le_div_iff₀ (by positivity)]
          have h1 : (N : ℝ) * (2 ^ 116 / s ^ 2) * 64 * 2 ^ 65 = (N : ℝ) * 2 ^ 187 / s ^ 2 := by
            ring
          rw [h1, div_le_iff₀ hs2]
          linarith
        have hgoal2 : (N : ℝ) * qc * 64 ≤ κb / (2 ^ 11 * s) := by
          rw [hqc, le_div_iff₀ (by positivity)]
          have e : (2 : ℝ) ^ 116 / s ^ 2 * s = 2 ^ 116 / s := by
            rw [div_mul_eq_mul_div, pow_two, mul_div_mul_right _ _ hspos.ne']
          have h1 : (N : ℝ) * (2 ^ 116 / s ^ 2) * 64 * (2 ^ 11 * s) =
              (N : ℝ) * 2 ^ 133 / s := by
            calc (N : ℝ) * (2 ^ 116 / s ^ 2) * 64 * (2 ^ 11 * s) =
                  (N : ℝ) * 64 * 2 ^ 11 * (2 ^ 116 / s ^ 2 * s) := by ring
              _ = (N : ℝ) * 64 * 2 ^ 11 * (2 ^ 116 / s) := by rw [e]
              _ = (N : ℝ) * 2 ^ 133 / s := by ring
          rw [h1, div_le_iff₀ hspos]
          linarith
        exact le_min hgoal1 hgoal2
      · exact chain_dim nreal hn0 hn65
    · push Not at hcase2
      have hσ5 : 5 * p.μ * p.ε ≤ p.σ ^ 2 := by
        rw [hσs]
        have := mul_le_mul_of_nonneg_right (show (5 : ℝ) ≤ s ^ 2 by linarith) hμε.le
        linarith
      refine quad_failure_at p hv hσ5 A N ?_ hd0
      rw [hσs]
      have hT : κ + s ^ 2 + min (κ * s ^ 2) (κb * s) ≤ 2 ^ 17 * s ^ 2 := by
        have h1 : κb * s ≤ 2 ^ 15 * s * s := mul_le_mul_of_nonneg_right hcase2.le hs0
        have h4 : 2 ^ 15 * s ≤ 2 ^ 15 * s * s := by
          have := mul_le_mul_of_nonneg_left hs1' (by positivity : (0 : ℝ) ≤ 2 ^ 15 * s)
          linarith
        have h5 : 2 ^ 15 * s * s = 2 ^ 15 * s ^ 2 := by ring
        linarith
      have h3 : (N : ℝ) * 10 ≤ s ^ 2 := by linarith
      have := mul_le_mul_of_nonneg_right h3 hμε.le
      linarith

end LongTails.Proofs.MeanSquaredPLLowerBound
