import LongTails.Algorithms.ContinuizedQuasar
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OracleTemplate.ContinuizedSimilarQuasar

open LongTails.Setups.ContinuizedSimilarQuasar

open scoped BigOperators

lemma theta_bounds (p : Params) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L)
    (hγ : 0 < p.γ) :
    0 < theta p ∧ theta p ≤ 1 ∧ theta p ^ 2 * p.L ≤ p.μ ∧
      512 * theta p * p.δ ^ 2 ≤ p.γ ^ 2 * p.μ ^ 2 := by
  let a := Real.sqrt (p.L / p.μ)
  let d := 512 * p.δ ^ 2 / (p.γ ^ 2 * p.μ ^ 2)
  have hκ : 1 ≤ p.L / p.μ := (le_div_iff₀ hμ).mpr (by simpa using hμL)
  have ha : 1 ≤ a := by simpa [a] using Real.sqrt_le_sqrt hκ
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hZ : 0 < a + d := by linarith
  have ht : theta p = 1 / (a + d) := rfl
  have htpos : 0 < theta p := by rw [ht]; positivity
  have hta : theta p * a ≤ 1 := by
    rw [ht, one_div, inv_mul_eq_div]
    exact (div_le_one hZ).mpr (by linarith)
  have htd : theta p * d ≤ 1 := by
    rw [ht, one_div, inv_mul_eq_div]
    exact (div_le_one hZ).mpr (by linarith)
  have ha2 : a ^ 2 = p.L / p.μ := Real.sq_sqrt (by linarith)
  have hta0 : 0 ≤ theta p * a := by positivity
  have hs : theta p ^ 2 * (p.L / p.μ) ≤ 1 := by nlinarith [sq_nonneg (1 - theta p * a)]
  have hstep : theta p ^ 2 * p.L ≤ p.μ := by
    have hh := mul_le_mul_of_nonneg_right hs hμ.le
    field_simp at hh
    nlinarith
  refine ⟨htpos, ?_, hstep, ?_⟩
  · rw [ht]
    exact (div_le_one hZ).mpr (by linarith)
  · dsimp [d] at htd
    have hh := mul_le_mul_of_nonneg_right htd (show 0 ≤ p.γ ^ 2 * p.μ ^ 2 by positivity)
    field_simp at hh
    nlinarith

lemma epochLength_bound (p : Params) (hμ : 0 < p.μ) (hμL : p.μ ≤ p.L)
    (hγ : 0 < p.γ) : 8 ≤ (epochLength p : ℝ) * (p.γ * theta p) := by
  have ht := (theta_bounds p hμ hμL hγ).1
  have hc : 0 < p.γ * theta p := mul_pos hγ ht
  have he : 8 / (p.γ * theta p) =
      8 * Real.sqrt (p.L / p.μ) / p.γ + 4096 * p.δ ^ 2 / (p.γ ^ 3 * p.μ ^ 2) := by
    unfold theta
    field_simp; ring
  apply (div_le_iff₀ hc).mp
  rw [he]
  exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 _))

lemma epochs_accuracy (p : Params) (hγ : 0 < p.γ) (hε : 0 < p.ε) :
    2 * p.Δ / p.γ ≤ (2 : ℝ) ^ epochs p * p.ε := by
  have hc : 2 * p.Δ / (p.γ * p.ε) ≤ (2 : ℝ) ^ epochs p := by
    calc
      _ ≤ 1 + 2 * p.Δ / (p.γ * p.ε) := by linarith
      _ ≤ (⌈1 + 2 * p.Δ / (p.γ * p.ε)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ ((2 ^ Nat.clog 2 ⌈1 + 2 * p.Δ / (p.γ * p.ε)⌉₊ : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) _
      _ ≤ (2 : ℝ) ^ epochs p := by
        norm_cast
        exact Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  have hh := (div_le_iff₀ (mul_pos hγ hε)).mp hc
  apply (div_le_iff₀ hγ).mpr
  nlinarith

lemma epoch_weights {c₀ b : ℝ} (hc₀ : 0 < c₀) (hc₁ : c₀ ≤ 1)
    (hb : 0 ≤ b) (hsmall : 64 * b ≤ c₀) (m : ℕ) (hm : 8 ≤ (m : ℝ) * c₀) :
    let q := 4 / (4 + c₀ - b)
    q ^ m ≤ 3 / 8 ∧ b * ∑ j ∈ Finset.range m, q ^ j ≤ 1 / 8 := by
  let c := c₀ - b
  let q := 4 / (4 + c)
  have hc : 0 < c := by dsimp [c]; linarith
  have hc1 : c ≤ 1 := by dsimp [c]; linarith
  have hd : 0 < 4 + c := by positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hmc : (63 : ℝ) ≤ 8 * (m : ℝ) * c := by
    have hh : 63 * c₀ ≤ 64 * c := by dsimp [c]; linarith
    have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    nlinarith
  have hprod : q * (1 + c / 4) = 1 := by dsimp [q]; field_simp
  have hp : q ^ m * (1 + c / 4) ^ m = 1 := by rw [← mul_pow, hprod, one_pow]
  have hbern := one_add_mul_le_pow (show -2 ≤ c / 4 by linarith) m
  have hbern' := mul_le_mul_of_nonneg_left hbern (pow_nonneg hq.le m)
  have hbase : (8 : ℝ) / 3 ≤ 1 + (m : ℝ) * (c / 4) := by nlinarith
  have hbase' := mul_le_mul_of_nonneg_left hbase (pow_nonneg hq.le m)
  have hpow : q ^ m ≤ 3 / 8 := by nlinarith
  have hgeom (k : ℕ) : (1 - q) * ∑ j ∈ Finset.range k, q ^ j = 1 - q ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, pow_succ]; nlinarith
  have hcoef : 8 * b ≤ 1 - q := by
    have he : 1 - q = c / (4 + c) := by dsimp [q]; field_simp; ring
    rw [he]
    apply (le_div_iff₀ hd).mpr
    have hh := mul_le_mul_of_nonneg_left hc1 (show 0 ≤ 8 * b by positivity)
    dsimp [c] at *
    nlinarith
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range m, q ^ j :=
    Finset.sum_nonneg (fun j _ => pow_nonneg hq.le j)
  have hh := mul_le_mul_of_nonneg_right hcoef hsum0
  have herr : b * ∑ j ∈ Finset.range m, q ^ j ≤ 1 / 8 := by
    nlinarith [hgeom m, pow_nonneg hq.le m]
  change (4 / (4 + c₀ - b)) ^ m ≤ _ ∧ _
  have he : 4 + c₀ - b = 4 + c := by dsimp [c]; ring
  simpa only [he] using And.intro hpow herr

end OracleTemplate.ContinuizedSimilarQuasar
