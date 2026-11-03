import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Convex.Function

open scoped BigOperators Topology

namespace LongTails.Proofs.FiniteSumNondualLowerGeometry

def deadZone (δ t : ℝ) : ℝ := max (|t| - δ) 0

lemma deadZone_nonneg (δ t : ℝ) : 0 ≤ deadZone δ t := le_max_right _ _

lemma abs_le_deadZone_add (δ t : ℝ) : |t| ≤ deadZone δ t + δ := by
  have h := le_max_left (|t| - δ) 0
  dsimp [deadZone]
  linarith

lemma deadZone_lipschitz (δ x y : ℝ) :
    |deadZone δ x - deadZone δ y| ≤ |x - y| := by
  have h := abs_max_sub_max_le_abs (|x| - δ) (|y| - δ) 0
  have he : |x| - δ - (|y| - δ) = |x| - |y| := by ring
  rw [he] at h
  exact h.trans (abs_abs_sub_abs_le x y)

def softThreshold (δ t : ℝ) : ℝ := max (t - δ) 0 - max (-t - δ) 0

lemma deadZone_quadratic_model (δ x y : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ deadZone δ y ^ 2 - deadZone δ x ^ 2 -
      2 * softThreshold δ x * (y - x) ∧
    deadZone δ y ^ 2 - deadZone δ x ^ 2 -
      2 * softThreshold δ x * (y - x) ≤ (y - x) ^ 2 := by
  simp only [deadZone, softThreshold, abs, max_def]
  split_ifs <;> constructor <;> nlinarith [sq_nonneg (y - x)]

lemma deadZone_sq_hasDerivAt (δ x : ℝ) (hδ : 0 ≤ δ) :
    HasDerivAt (fun y => deadZone δ y ^ 2) (2 * softThreshold δ x) x := by
  apply HasDerivAt.of_isLittleO
  have hb : (fun y => deadZone δ y ^ 2 - deadZone δ x ^ 2 -
      (y - x) • (2 * softThreshold δ x)) =O[nhds x] (fun y => ‖y - x‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [] with y
    have h := deadZone_quadratic_model δ x y hδ
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (y - x)), one_mul,
      smul_eq_mul, mul_comm (y - x), abs_of_nonneg h.1, sq_abs] using h.2
  exact hb.trans_isLittleO (Asymptotics.isLittleO_pow_sub_sub x (by norm_num : 1 < 2))

lemma deadZone_sq_convex (δ : ℝ) (hδ : 0 ≤ δ) :
    ConvexOn ℝ Set.univ (fun y => deadZone δ y ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hx := (deadZone_quadratic_model δ (a * x + b * y) x hδ).1
  have hy := (deadZone_quadratic_model δ (a * x + b * y) y hδ).1
  have he : a * (x - (a * x + b * y)) + b * (y - (a * x + b * y)) = 0 := by
    calc
      _ = (1 - (a + b)) * (a * x + b * y) := by ring
      _ = 0 := by rw [hab]; ring
  simp only [smul_eq_mul]
  have he' := congrArg (fun t => 2 * softThreshold δ (a * x + b * y) * t) he
  have hab' := congrArg (fun t => t * deadZone δ (a * x + b * y) ^ 2) hab
  nlinarith only [mul_nonneg ha hx, mul_nonneg hb hy, he', hab']

lemma softThreshold_lipschitz (δ x y : ℝ) (hδ : 0 ≤ δ) :
    |softThreshold δ x - softThreshold δ y| ≤ |x - y| := by
  simp only [softThreshold, abs, max_def]
  split_ifs <;> linarith

lemma deadZone_inactive (δ t : ℝ) (ht : |t| ≤ δ) :
    deadZone δ t = 0 ∧ softThreshold δ t = 0 := by
  have hp := le_abs_self t
  have hn := neg_le_abs t
  simp only [deadZone, softThreshold]
  rw [max_eq_right (by linarith : |t| - δ ≤ 0),
    max_eq_right (by linarith : t - δ ≤ 0),
    max_eq_right (by linarith : -t - δ ≤ 0)]
  simp

lemma large_coordinates {ι : Type*} [Fintype ι] (x : ι → ℝ) (δ R : ℝ)
    (hR : ∑ i, |x i| ≤ R) :
    ((Finset.univ.filter (fun i => δ < |x i|)).card : ℝ) * δ ≤ R := by
  classical
  let s := Finset.univ.filter (fun i => δ < |x i|)
  calc
    (s.card : ℝ) * δ = ∑ _ ∈ s, δ := by simp
    _ ≤ ∑ i ∈ s, |x i| := Finset.sum_le_sum fun i hi =>
      (Finset.mem_filter.mp hi).2.le
    _ ≤ ∑ i, |x i| := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun i _ _ => abs_nonneg (x i))
    _ ≤ R := hR

lemma chain_difference_energy (x : ℕ → ℝ) (m : ℕ) :
    x 0 ^ 2 + ∑ j ∈ Finset.range m, (x j - x (j + 1)) ^ 2 ≤
      4 * ∑ j ∈ Finset.range (m + 1), x j ^ 2 := by
  have hs : x 0 ^ 2 + (∑ j ∈ Finset.range m, (x j - x (j + 1)) ^ 2) +
      x 0 ^ 2 + 2 * x m ^ 2 ≤ 4 * ∑ j ∈ Finset.range (m + 1), x j ^ 2 := by
    induction m with
    | zero => simp; nlinarith [sq_nonneg (x 0)]
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ (fun j => x j ^ 2)]
      nlinarith [sq_nonneg (x m + x (m + 1))]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x m)]

lemma chain_difference_energy_fin (k : ℕ) (x : Fin (k + 1) → ℝ) :
    x 0 ^ 2 + ∑ j : Fin k, (x j.castSucc - x j.succ) ^ 2 ≤
      4 * ∑ j, x j ^ 2 := by
  have h : (∑ j : Fin k, (x j.castSucc - x j.succ) ^ 2) ≤
      ∑ j : Fin k, (2 * x j.castSucc ^ 2 + 2 * x j.succ ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    nlinarith [sq_nonneg (x j.castSucc + x j.succ)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h
  have h₁ := Fin.sum_univ_succ (fun j : Fin (k + 1) => x j ^ 2)
  have h₂ := Fin.sum_univ_castSucc (fun j : Fin (k + 1) => x j ^ 2)
  nlinarith [sq_nonneg (x 0), sq_nonneg (x (Fin.last k))]

lemma chain_telescope (δ a : ℝ) (x : ℕ → ℝ) (m : ℕ) :
    a - |x m| - (m : ℝ) * δ ≤
      |a - x 0| + ∑ j ∈ Finset.range m, deadZone δ (x j - x (j + 1)) := by
  induction m with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, sub_zero, Finset.range_zero, Finset.sum_empty,
      add_zero]
    have h₁ := le_abs_self (a - x 0)
    have h₂ := le_abs_self (x 0)
    linarith
  | succ m ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ]
    have h₁ : |x m| ≤ |x m - x (m + 1)| + |x (m + 1)| := by
      calc
        |x m| = |(x m - x (m + 1)) + x (m + 1)| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    have h₂ := abs_le_deadZone_add δ (x m - x (m + 1))
    linarith

lemma chain_energy (δ a : ℝ) (x : ℕ → ℝ) (m : ℕ)
    (h : 0 ≤ a - |x m| - (m : ℝ) * δ) :
    (a - |x m| - (m : ℝ) * δ) ^ 2 ≤
      ((m : ℝ) + 1) * ((a - x 0) ^ 2 +
        ∑ j ∈ Finset.range m, deadZone δ (x j - x (j + 1)) ^ 2) := by
  let w : ℕ → ℝ := fun i => if i = 0 then |a - x 0|
    else deadZone δ (x (i - 1) - x i)
  have hw : (∑ i ∈ Finset.range (m + 1), w i) =
      |a - x 0| + ∑ j ∈ Finset.range m, deadZone δ (x j - x (j + 1)) := by
    rw [Finset.sum_range_succ']
    simp [w, add_comm]
  have hw₂ : (∑ i ∈ Finset.range (m + 1), w i ^ 2) =
      (a - x 0) ^ 2 + ∑ j ∈ Finset.range m, deadZone δ (x j - x (j + 1)) ^ 2 := by
    rw [Finset.sum_range_succ']
    simp [w, sq_abs, add_comm]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (m + 1))
    (fun _ => (1 : ℝ)) w
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, Nat.cast_add, Nat.cast_one] at hc
  rw [hw, hw₂] at hc
  exact (pow_le_pow_left₀ h (chain_telescope δ a x m) 2).trans hc

lemma chain_gap (δ a : ℝ) (x : ℕ → ℝ) (m k : ℕ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hm : m < k)
    (hscale : (k : ℝ) * δ ≤ a / 8) (htail : |x m| ≤ δ / 4) :
    a ^ 2 ≤ 2 * (k : ℝ) * ((a - x 0) ^ 2 +
      ∑ j ∈ Finset.range m, deadZone δ (x j - x (j + 1)) ^ 2) := by
  have hmk : (m : ℝ) + 1 ≤ k := by exact_mod_cast hm
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hd : δ ≤ a / 8 := by nlinarith
  have hmδ : (m : ℝ) * δ ≤ (k : ℝ) * δ := by gcongr
  have ht : 3 * a / 4 ≤ a - |x m| - (m : ℝ) * δ := by linarith
  have ht₀ : 0 ≤ a - |x m| - (m : ℝ) * δ := by linarith
  have he := chain_energy δ a x m ht₀
  have hsq := pow_le_pow_left₀ (show 0 ≤ 3 * a / 4 by positivity) ht 2
  have hE : 0 ≤ (a - x 0) ^ 2 +
      ∑ j ∈ Finset.range m, deadZone δ (x j - x (j + 1)) ^ 2 := by positivity
  have hc := mul_le_mul_of_nonneg_right hmk hE
  nlinarith

lemma chain_gap_fin (δ a : ℝ) (k m : ℕ) (x : Fin (k + 1) → ℝ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hm : m ≤ k)
    (hscale : ((k : ℝ) + 1) * δ ≤ a / 8)
    (htail : |x ⟨m, by omega⟩| ≤ δ / 4) :
    a ^ 2 ≤ 2 * ((k : ℝ) + 1) * ((x 0 - a) ^ 2 +
      ∑ j : Fin k, deadZone δ (x j.castSucc - x j.succ) ^ 2) := by
  let X : ℕ → ℝ := fun j => if hj : j < k + 1 then x ⟨j, hj⟩ else 0
  have hm' : m < k + 1 := by omega
  have ht : |X m| ≤ δ / 4 := by simpa [X, hm] using htail
  have he := chain_gap δ a X m (k + 1) ha hδ hm'
    (by simpa using hscale) ht
  have hs : (∑ j ∈ Finset.range m, deadZone δ (X j - X (j + 1)) ^ 2) ≤
      ∑ j ∈ Finset.range k, deadZone δ (X j - X (j + 1)) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
      (fun j _ _ => sq_nonneg _)
  have hf : (∑ j ∈ Finset.range k, deadZone δ (X j - X (j + 1)) ^ 2) =
      ∑ j : Fin k, deadZone δ (x j.castSucc - x j.succ) ^ 2 := by
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro j _
    have hj : (j : ℕ) < k + 1 := by omega
    have hj' : (j : ℕ) + 1 < k + 1 := by omega
    simp only [X, dite_eq_left hj, dite_eq_left hj']
    rfl
  rw [hf] at hs
  have hz : (a - X 0) ^ 2 = (x 0 - a) ^ 2 := by
    simp [X]
    ring
  rw [hz] at he
  simp only [Nat.cast_add, Nat.cast_one] at he
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * ((k : ℝ) + 1))]

end LongTails.Proofs.FiniteSumNondualLowerGeometry
