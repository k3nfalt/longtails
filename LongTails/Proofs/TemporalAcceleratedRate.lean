import LongTails.Proofs.QuadraticTemporalEnergy
import LongTails.Proofs.TemporalLinearResponse
import LongTails.Proofs.GdPL

noncomputable section

namespace OracleTemplate.TemporalDiscrepancy

open LongTails.Setups.QuadraticTemporalDiscrepancy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma accelerated_tail_seminorm (A : E →L[ℝ] E) {μ θ L D : ℝ}
    (hμ : 0 < μ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hD : 0 ≤ D)
    (hstep : θ ^ 2 * L ≤ μ)
    (hlower : ∀ x, μ * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    (hupper : ∀ x, ‖A x‖ ^ 2 ≤ L * ‖x‖ ^ 2)
    (v : ℕ → E × E) (e : ℕ → E)
    (hv : ∀ k, v (k + 1) = transition A μ θ (v k) + injection μ θ (e k))
    (he : ∀ n, ‖∑ k ∈ Finset.range n, e k‖ ≤ D)
    (start count : ℕ) (hc : 0 < count) :
    energySeminorm A μ (tailAverage v start count) ≤
      (Real.sqrt (1 - θ)) ^ start * energySeminorm A μ (v 0) +
        4 * Real.sqrt (2 / μ) * D / count := by
  let ρ := Real.sqrt (1 - θ)
  have hρ : 0 ≤ ρ := Real.sqrt_nonneg _
  have hs : ρ ^ 2 = 1 - θ := Real.sq_sqrt (sub_nonneg.mpr hθ1)
  have hρ1 : ρ < 1 := by nlinarith
  have hden : 0 < 1 - ρ := by linarith
  have hn : (0 : ℝ) < count := by exact_mod_cast hc
  have h := tail_average_bound (transition A μ θ) (injection μ θ)
    (energySeminorm A μ) v e hv hρ hρ1
    (show 0 ≤ θ * Real.sqrt (2 / μ) by positivity) hD
    (transition_contracts A hμ hθ.le hθ1 hstep hlower hupper)
    (injection_bound A hμ hθ.le hstep hupper) he start count hc
  change energySeminorm A μ (tailAverage v start count) ≤ _ at h
  apply h.trans
  refine add_le_add (le_refl _) ?_
  have ht : θ ≤ 2 * (1 - ρ) := by nlinarith [sq_nonneg (1 - ρ)]
  have hh : 2 * (θ * Real.sqrt (2 / μ)) * D / (1 - ρ) ≤
      4 * Real.sqrt (2 / μ) * D := by
    apply (div_le_iff₀ hden).mpr
    have hm := mul_le_mul_of_nonneg_right ht
      (show 0 ≤ 2 * Real.sqrt (2 / μ) * D by positivity)
    nlinarith
  calc
    _ = (2 * (θ * Real.sqrt (2 / μ)) * D / (1 - ρ)) / count := by rw [div_div]
    _ ≤ _ := div_le_div_of_nonneg_right hh hn.le

lemma accelerated_tail_rate (A : E →L[ℝ] E) {μ θ L D Δ : ℝ}
    (hμ : 0 < μ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hD : 0 ≤ D)
    (hstep : θ ^ 2 * L ≤ μ)
    (hlower : ∀ x, μ * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2)
    (hupper : ∀ x, ‖A x‖ ^ 2 ≤ L * ‖x‖ ^ 2)
    (v : ℕ → E × E) (e : ℕ → E) (r : E) (hzero : v 0 = (r, r))
    (hinit : ‖A r‖ ^ 2 / 2 ≤ Δ)
    (hv : ∀ k, v (k + 1) = transition A μ θ (v k) + injection μ θ (e k))
    (he : ∀ n, ‖∑ k ∈ Finset.range n, e k‖ ≤ D)
    (start count : ℕ) (hc : 0 < count) :
    ‖A (tailAverage v start count).1‖ ^ 2 / 2 ≤
      4 * Δ * (1 - θ) ^ start + 32 * D ^ 2 / (μ * (count : ℝ) ^ 2) := by
  let p := energySeminorm A μ
  let a := (Real.sqrt (1 - θ)) ^ start * p (v 0)
  let b := 4 * Real.sqrt (2 / μ) * D / count
  have hb := accelerated_tail_seminorm A hμ hθ hθ1 hD hstep hlower hupper v e hv he start count hc
  change p (tailAverage v start count) ≤ a + b at hb
  have ha0 : 0 ≤ a := mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (apply_nonneg p _)
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hsq := pow_le_pow_left₀ (apply_nonneg p _) hb 2
  have hp0 : p (v 0) ^ 2 ≤ 4 * Δ := by
    dsimp [p]
    rw [hzero, energySeminorm_sq A hμ.le]
    have hl := hlower r
    dsimp
    linarith
  have hs : (Real.sqrt (1 - θ)) ^ 2 = 1 - θ := Real.sq_sqrt (sub_nonneg.mpr hθ1)
  have ha : a ^ 2 ≤ 4 * Δ * (1 - θ) ^ start := by
    dsimp [a]
    rw [mul_pow, ← pow_mul, Nat.mul_comm start 2, pow_mul, hs]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp0
      (pow_nonneg (sub_nonneg.mpr hθ1) start)
  have hb2 : b ^ 2 = 32 * D ^ 2 / (μ * (count : ℝ) ^ 2) := by
    dsimp [b]
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (show 0 ≤ 2 / μ by positivity)]
    ring
  have hp := energySeminorm_sq A hμ.le (tailAverage v start count)
  change p (tailAverage v start count) ^ 2 = _ at hp
  have hz : 0 ≤ μ * ‖(tailAverage v start count).2‖ ^ 2 := by positivity
  nlinarith [sq_nonneg (a - b)]

lemma tail_budget {μ θ D Δ ε : ℝ} (hμ : 0 < μ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hD : 0 ≤ D) (hΔ : 0 ≤ Δ) (hε : 0 < ε) (K : ℕ)
    (hbudget : max 1 ⌈(1 / θ) * Real.log (1 + 8 * Δ / ε) + 8 * D / Real.sqrt (μ * ε)⌉₊ ≤ K) :
    4 * Δ * (1 - θ) ^ K + 32 * D ^ 2 / (μ * (K : ℝ) ^ 2) ≤ ε := by
  have hK : 0 < K := lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hbudget)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hs : 0 < Real.sqrt (μ * ε) := Real.sqrt_pos.mpr (mul_pos hμ hε)
  have hlog : 0 ≤ Real.log (1 + 8 * Δ / ε) :=
    Real.log_nonneg (by have := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hΔ) hε.le; linarith)
  have hceil : (1 / θ) * Real.log (1 + 8 * Δ / ε) + 8 * D / Real.sqrt (μ * ε) ≤ (K : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 _).trans hbudget)
  have hKg : ⌈(1 / θ) * Real.log (1 + 8 * Δ / ε)⌉₊ ≤ K := by
    apply (Nat.ceil_mono (show (1 / θ) * Real.log (1 + 8 * Δ / ε) ≤
      (1 / θ) * Real.log (1 + 8 * Δ / ε) + 8 * D / Real.sqrt (μ * ε) by
        have hn : 0 ≤ 8 * D / Real.sqrt (μ * ε) := by positivity
        linarith)).trans
    exact (le_max_right _ _).trans hbudget
  have hg := PLGradient.geometric_budget 1 θ (4 * Δ) (ε / 2) hθ hθ1
    (by positivity) (by positivity)
  have hdiv : 4 * Δ / (ε / 2) = 8 * Δ / ε := by ring
  simp only [div_one, hdiv] at hg
  have hpow := mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (sub_nonneg.mpr hθ1) (by linarith : 1 - θ ≤ 1) hKg)
    (show 0 ≤ 4 * Δ by positivity)
  have hgeom : 4 * Δ * (1 - θ) ^ K ≤ ε / 2 := by nlinarith [hpow.trans hg]
  have hn : 8 * D / Real.sqrt (μ * ε) ≤ (K : ℝ) := by
    have hp : 0 ≤ (1 / θ) * Real.log (1 + 8 * Δ / ε) := by positivity
    linarith
  have hn' := (div_le_iff₀ hs).mp hn
  have hn2 := pow_le_pow_left₀ (show 0 ≤ 8 * D by positivity) hn' 2
  simp only [mul_pow, Real.sq_sqrt (mul_nonneg hμ.le hε.le)] at hn2
  have hnoise : 32 * D ^ 2 / (μ * (K : ℝ) ^ 2) ≤ ε / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < μ * (K : ℝ) ^ 2)).mpr
    nlinarith
  change 4 * Δ * (1 - θ) ^ K + 32 * D ^ 2 / (μ * (K : ℝ) ^ 2) ≤ ε
  linarith

end OracleTemplate.TemporalDiscrepancy
