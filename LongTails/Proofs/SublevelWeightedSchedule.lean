import LongTails.Algorithms.SublevelWeightedGradient

namespace OracleTemplate.SublevelWeighted

lemma inv_sqrt_sum (K : ℕ) :
    ∑ j ∈ Finset.range K, (1 : ℝ) / Real.sqrt (j + 1) ≤ 2 * Real.sqrt K := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have ha := Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ) + 1)
    have hb := Real.sq_sqrt (by positivity : 0 ≤ (k : ℝ))
    have hc := Real.sqrt_le_sqrt (by linarith : (k : ℝ) ≤ k + 1)
    have hd : 0 < Real.sqrt ((k : ℝ) + 1) := by positivity
    have hstep : 1 / Real.sqrt ((k : ℝ) + 1) ≤
        2 * (Real.sqrt (k + 1) - Real.sqrt k) := by
      rw [div_le_iff₀ hd]
      nlinarith [sq_nonneg (Real.sqrt (k + 1) - Real.sqrt k)]
    linarith

lemma calls_eq (b : ℕ → ℕ) (K : ℕ) : calls b K = ∑ j ∈ Finset.range K, b j := by
  induction K with
  | zero => simp [calls]
  | succ k ih => simp [calls, ih, Finset.sum_range_succ, Nat.add_comm]

lemma batch_pos (K : ℕ) (v : ℝ) (j : ℕ) : 0 < batch K v j := by simp [batch]

lemma batch_cost (K : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    (calls (batch K v) K : ℝ) ≤ 2 * K * (1 + v) := by
  rw [calls_eq, Nat.cast_sum]
  have hs : ∀ j : ℕ, (batch K v j : ℝ) ≤ 2 + (v * Real.sqrt K) * (1 / Real.sqrt (j + 1)) := by
    intro j
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ v * Real.sqrt K / Real.sqrt (j + 1))
    unfold batch
    push_cast
    simp only [div_eq_mul_inv, one_mul] at *
    linarith
  calc
    _ ≤ ∑ j ∈ Finset.range K, (2 + v * Real.sqrt K * (1 / Real.sqrt (j + 1))) :=
      Finset.sum_le_sum fun j _ => hs j
    _ = 2 * K + v * Real.sqrt K * ∑ j ∈ Finset.range K, 1 / Real.sqrt (j + 1) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [mul_comm]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (inv_sqrt_sum K) (by positivity : 0 ≤ v * Real.sqrt K)
      have hsq := congrArg (fun t : ℝ => v * t) (Real.sq_sqrt (by positivity : 0 ≤ (K : ℝ)))
      change v * (Real.sqrt K) ^ 2 = v * K at hsq
      nlinarith


lemma batch_lower (K : ℕ) (v : ℝ) (j : ℕ) :
    v * Real.sqrt K / Real.sqrt (j + 1) ≤ (batch K v j : ℝ) := by
  unfold batch
  push_cast
  linarith [Nat.le_ceil (v * Real.sqrt K / Real.sqrt (j + 1))]

lemma batch_variance {K : ℕ} (hK : 0 < K) {v : ℝ} (hv : 0 < v) {j : ℕ} (hj : j < K) :
    1 / (batch K v j : ℝ) ≤ 1 / v ∧
      1 / (batch K v j : ℝ) / (j + 1) ≤
        (1 / (v * Real.sqrt K)) * (1 / Real.sqrt (j + 1)) := by
  have hB : 0 < (batch K v j : ℝ) := by exact_mod_cast batch_pos K v j
  have hR : 0 < Real.sqrt (K : ℝ) := by positivity
  have hr : 0 < Real.sqrt ((j : ℝ) + 1) := by positivity
  have hb := (div_le_iff₀ hr).mp (batch_lower K v j)
  have hrR := Real.sqrt_le_sqrt (show (j : ℝ) + 1 ≤ K by exact_mod_cast Nat.succ_le_of_lt hj)
  constructor
  · apply one_div_le_one_div_of_le hv
    nlinarith [mul_le_mul_of_nonneg_left hrR hv.le]
  · have hs := mul_le_mul_of_nonneg_right hb hr.le
    rw [mul_assoc (batch K v j : ℝ), Real.mul_self_sqrt (by positivity)] at hs
    rw [div_div, one_div_mul_one_div]
    exact one_div_le_one_div_of_le (by positivity) hs

end OracleTemplate.SublevelWeighted
