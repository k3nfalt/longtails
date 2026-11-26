import LongTails.Algorithms.CompositeGapQuadraticWeights
import LongTails.Proofs.CompositeGapBudget

namespace LongTails.Proofs.CompositeGapQuadraticWeights

open LongTails.Setups.CompositeGapSmooth
open OracleTemplate.CompositeGapQuadraticWeights
open OracleTemplate.CompositeGapAccelerated (phases)

lemma level_pos (p : Params) (h : 0 < p.Δ) (k : ℕ) : 0 < level p k := by
  dsimp [level]; positivity

lemma level_succ (p : Params) (k : ℕ) : level p (k + 1) = level p k / 2 := by
  simp [level, pow_succ, div_div]

lemma cost_eq_sum (p : Params) (S : ℕ) :
    cost p S = 2 * ∑ k ∈ Finset.range S, iterations p k := by
  induction S with
  | zero => simp [cost]
  | succ S ih => rw [cost, Finset.sum_range_succ, ih, Nat.mul_add, Nat.add_comm]

lemma iterations_eq (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (k : ℕ) :
    iterations p k = ⌈Real.sqrt (128 + 256 * p.H1 * p.R ^ 2 + 256 * p.H0 * p.R ^ 2 / level p k)⌉₊ := by
  have hd := level_pos p hΔ k
  unfold iterations
  congr 1
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 16), ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  dsimp [scale, curvature]
  field_simp
  ring

lemma zero_calls (p : Params) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) (hle : p.Δ ≤ p.ε) :
    cost p (phases p) = 0 := by
  have hl := Real.log_nonpos (show 0 ≤ p.Δ / p.ε by positivity) ((div_le_one hε).mpr hle)
  have hz : phases p = 0 := Nat.ceil_eq_zero.mpr
    (div_nonpos_of_nonpos_of_nonneg hl (Real.log_nonneg (by norm_num)))
  rw [hz, cost]

lemma iteration_cost (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1) (hR : 0 < p.R)
    (hΔ : 0 < p.Δ) (k : ℕ) :
    (2 : ℝ) * iterations p k ≤ 34 * (1 + p.R * Real.sqrt p.H1) +
      32 * p.R * Real.sqrt (p.H0 / level p k) := by
  let d := level p k
  have hd : 0 < d := level_pos p hΔ k
  have he : scale p d = 1 / 2 + p.R ^ 2 * p.H1 + p.R ^ 2 * (p.H0 / d) := by
    dsimp [scale, curvature]; field_simp; ring
  have hs : Real.sqrt (scale p d) ≤ 1 + p.R * Real.sqrt p.H1 + p.R * Real.sqrt (p.H0 / d) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by rw [he]; positivity), he]
    have h₁ := Real.sq_sqrt h1
    have h₂ := Real.sq_sqrt (show 0 ≤ p.H0 / d by positivity)
    nlinarith only [congrArg (p.R ^ 2 * ·) h₁, congrArg (p.R ^ 2 * ·) h₂,
      mul_nonneg hR.le (Real.sqrt_nonneg p.H1), mul_nonneg hR.le (Real.sqrt_nonneg (p.H0 / d)),
      mul_nonneg (mul_nonneg (sq_nonneg p.R) (Real.sqrt_nonneg p.H1)) (Real.sqrt_nonneg (p.H0 / d))]
  have hh := Nat.ceil_lt_add_one (show 0 ≤ 16 * Real.sqrt (scale p d) by positivity)
  change (⌈16 * Real.sqrt (scale p d)⌉₊ : ℝ) < _ at hh
  change 2 * (⌈16 * Real.sqrt (scale p d)⌉₊ : ℝ) ≤ _
  change _ ≤ 34 * (1 + p.R * Real.sqrt p.H1) + 32 * p.R * Real.sqrt (p.H0 / d)
  nlinarith only [hs, hh, mul_nonneg hR.le (Real.sqrt_nonneg p.H1)]

lemma accumulated_cost (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1) (hR : 0 < p.R)
    (hΔ : 0 < p.Δ) (k : ℕ) :
    (cost p (k + 1) : ℝ) ≤ (k + 1 : ℝ) * (34 * (1 + p.R * Real.sqrt p.H1)) +
      32 * (2 + Real.sqrt 2) * p.R * Real.sqrt (p.H0 / level p k) := by
  have hh := iteration_cost p h0 h1 hR hΔ
  induction k with
  | zero =>
    simp only [cost, Nat.cast_mul, Nat.cast_zero, Nat.cast_ofNat, zero_add, add_zero, one_mul]
    nlinarith only [hh 0, mul_nonneg hR.le (Real.sqrt_nonneg (p.H0 / level p 0)),
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hR.le) (Real.sqrt_nonneg (p.H0 / level p 0))]
  | succ k ih =>
    let u := Real.sqrt (p.H0 / level p k)
    have he : Real.sqrt (p.H0 / level p (k + 1)) = Real.sqrt 2 * u := by
      rw [level_succ, show p.H0 / (level p k / 2) = 2 * (p.H0 / level p k) by ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hs := hh (k + 1)
    rw [he] at hs ⊢
    rw [cost]; push_cast
    have hz := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    change _ ≤ _ + 32 * (2 + Real.sqrt 2) * p.R * u at ih
    nlinarith only [ih, hs, congrArg (· * (32 * p.R * u)) hz]

lemma budget_bound (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1) (hR : 0 < p.R)
    (hΔ : 0 < p.Δ) (hε : 0 < p.ε) :
    cost p (phases p) ≤ ⌈32 * (2 + Real.sqrt 2) * p.R * Real.sqrt (p.H0 / p.ε) +
      85 * (1 + p.R * Real.sqrt p.H1) * Real.log (2 + p.Δ / p.ε)⌉₊ := by
  cases he : phases p with
  | zero => simp [cost]
  | succ k =>
    have hk : k < phases p := by omega
    have hd := CompositeGapGrowth.stage_gap_gt p hΔ hε hk
    change p.ε < level p k at hd
    have hr : 1 < p.Δ / p.ε := by
      by_contra! hn
      have hl := Real.log_nonpos (show 0 ≤ p.Δ / p.ε by positivity) hn
      have hz : phases p = 0 := Nat.ceil_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg hl (Real.log_nonneg (by norm_num)))
      omega
    have hS := CompositeGapBudget.rounded_phases_bound hr
    change (phases p : ℝ) ≤ _ at hS
    rw [he, Nat.cast_succ] at hS
    have ht := Real.sqrt_le_sqrt (div_le_div_of_nonneg_left h0 hε hd.le)
    have hu := accumulated_cost p h0 h1 hR hΔ k
    apply (Nat.cast_le (α := ℝ)).mp
    apply le_trans _ (Nat.le_ceil _)
    nlinarith only [hu, mul_le_mul_of_nonneg_right hS (show 0 ≤ 34 * (1 + p.R * Real.sqrt p.H1) by positivity),
      mul_le_mul_of_nonneg_left ht (show 0 ≤ 32 * (2 + Real.sqrt 2) * p.R by positivity)]

end LongTails.Proofs.CompositeGapQuadraticWeights
