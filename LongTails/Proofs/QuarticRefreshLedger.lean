import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace LongTails.Proofs.QuarticRefreshLedger

lemma movement_charge {μ q D s : ℝ} (hμ : 0 < μ) (hq : 0 < q) (hs : 0 ≤ s)
    (hD : q ≤ D) (he : μ * s ^ 2 ≤ 256 * D) :
    Real.sqrt (μ * q) * s ≤ 16 * D := by
  have hD₀ : 0 ≤ D := hq.le.trans hD
  have h₁ := mul_le_mul_of_nonneg_left hD hD₀
  have h₂ := mul_le_mul_of_nonneg_right he hq.le
  have hr := Real.sq_sqrt (mul_pos hμ hq).le
  have hsq : (Real.sqrt (μ * q) * s) ^ 2 ≤ (16 * D) ^ 2 := by nlinarith
  exact (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hs) (mul_nonneg (by norm_num) hD₀)).mp hsq

lemma refresh_step {r V W s C D : ℝ} {refresh : Bool}
    (hreset : refresh = true → r / 4 < V)
    (hmovement : W ≤ (if refresh then 0 else V) + s)
    (hcharge : s ≤ C * D) :
    (if refresh then r / 4 else 0) + W - V ≤ C * D := by
  cases refresh <;> simp_all
  all_goals linarith

lemma terminal_step {r V : ℝ} {refresh : Bool}
    (hV : 0 ≤ V) (hreset : refresh = true → r / 4 < V) :
    (if refresh then r / 4 else 0) - V ≤ 0 := by
  cases refresh <;> simp_all
  all_goals linarith

lemma ledger_sum {r C : ℝ} {V D : ℕ → ℝ} {refresh : ℕ → Bool}
    (hzero : V 0 = 0)
    (hstep : ∀ t, (if refresh t then r / 4 else 0) + V (t + 1) - V t ≤ C * D t)
    (T : ℕ) :
    (∑ t ∈ Finset.range T, if refresh t then r / 4 else 0) + V T ≤
      C * ∑ t ∈ Finset.range T, D t := by
  induction T with
  | zero => simp [hzero]
  | succ T ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hh := hstep T
    nlinarith

lemma refresh_count {r C Δ : ℝ} {V D : ℕ → ℝ} {refresh : ℕ → Bool}
    (hr : 0 < r) (hC : 0 ≤ C) (hzero : V 0 = 0)
    (hstep : ∀ t, (if refresh t then r / 4 else 0) + V (t + 1) - V t ≤ C * D t)
    (T : ℕ) (hV : 0 ≤ V T) (hD : ∑ t ∈ Finset.range T, D t ≤ Δ) :
    (∑ t ∈ Finset.range T, if refresh t then (1 : ℝ) else 0) ≤ 4 * C * Δ / r := by
  have hh := ledger_sum hzero hstep T
  have hs : (∑ t ∈ Finset.range T, if refresh t then r / 4 else 0) =
      r / 4 * ∑ t ∈ Finset.range T, if refresh t then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    split <;> simp_all
  rw [hs] at hh
  have hd := mul_le_mul_of_nonneg_left hD hC
  apply (le_div_iff₀ hr).mpr
  nlinarith

lemma ledger_prefix {r C : ℝ} {V D : ℕ → ℝ} {refresh : ℕ → Bool}
    (hzero : V 0 = 0) (T : ℕ)
    (hstep : ∀ t < T, (if refresh t then r / 4 else 0) + V (t + 1) - V t ≤ C * D t) :
    (∑ t ∈ Finset.range T, if refresh t then r / 4 else 0) + V T ≤
      C * ∑ t ∈ Finset.range T, D t := by
  induction T with
  | zero => simp [hzero]
  | succ T ih =>
    have hh := hstep T (by omega)
    have ht := ih (fun t h => hstep t (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    nlinarith

lemma refresh_prefix {r C Δ : ℝ} {V D : ℕ → ℝ} {refresh : ℕ → Bool}
    (hr : 0 < r) (hC : 0 ≤ C) (hzero : V 0 = 0) (T : ℕ)
    (hstep : ∀ t < T, (if refresh t then r / 4 else 0) + V (t + 1) - V t ≤ C * D t)
    (hV : 0 ≤ V T) (hD : ∑ t ∈ Finset.range T, D t ≤ Δ) :
    (∑ t ∈ Finset.range T, if refresh t then (1 : ℝ) else 0) ≤ 4 * C * Δ / r := by
  have hh := ledger_prefix hzero T hstep
  have hs : (∑ t ∈ Finset.range T, if refresh t then r / 4 else 0) =
      r / 4 * ∑ t ∈ Finset.range T, if refresh t then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    split <;> simp_all
  rw [hs] at hh
  have hd := mul_le_mul_of_nonneg_left hD hC
  apply (le_div_iff₀ hr).mpr
  nlinarith

end LongTails.Proofs.QuarticRefreshLedger
