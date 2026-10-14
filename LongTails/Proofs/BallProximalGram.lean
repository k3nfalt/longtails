import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.BallProximal

noncomputable section

lemma tail_square_sum (a : ℕ → ℝ) {i N : ℕ} (hi : i ≤ N) :
    (∑ j ∈ Finset.range N, if i ≤ j then a j ^ 2 - a (j + 1) ^ 2 else 0) =
      a i ^ 2 - a N ^ 2 := by
  induction N with
  | zero =>
      have hi0 : i = 0 := by omega
      simp [hi0]
  | succ N ih =>
      by_cases hiN : i ≤ N
      · rw [Finset.sum_range_succ, ih hiN, ite_eq_left hiN]
        ring
      · have hi' : i = N + 1 := by omega
        subst i
        have hz : ∀ j ∈ Finset.range (N + 1), ¬N + 1 ≤ j := by
          intro j hj
          have := Finset.mem_range.mp hj
          omega
        rw [sub_self]
        apply Finset.sum_eq_zero
        intro j hj
        exact ite_eq_right (hz j hj)

def markovVector (N : ℕ) (a : ℕ → ℝ) (i : ℕ) : EuclideanSpace ℝ (Fin N) :=
  WithLp.toLp 2 (fun j => if i ≤ j.val then Real.sqrt (a j.val ^ 2 - a (j.val + 1) ^ 2) else 0)

lemma markovVector_inner {N : ℕ} {a : ℕ → ℝ} (haN : a N = 0)
    (ha : ∀ j < N, a (j + 1) ^ 2 ≤ a j ^ 2) {i j : ℕ} (hi : i ≤ N) (hj : j ≤ N) :
    ⟪markovVector N a i, markovVector N a j⟫ = a (max i j) ^ 2 := by
  rw [PiLp.inner_apply]
  have he (k : Fin N) :
      ⟪markovVector N a i k, markovVector N a j k⟫ =
        if max i j ≤ k.val then a k.val ^ 2 - a (k.val + 1) ^ 2 else 0 := by
    simp only [markovVector, PiLp.toLp_apply, RCLike.inner_apply, conj_trivial]
    by_cases hi' : i ≤ k.val <;> by_cases hj' : j ≤ k.val
    · simp [hi', hj', Real.mul_self_sqrt (sub_nonneg.mpr (ha _ k.isLt))]
    · simp [hi', hj']
    · simp [hi', hj']
    · simp [hi', hj']
  simp_rw [he]
  rw [Fin.sum_univ_eq_sum_range (fun k => if max i j ≤ k then a k ^ 2 - a (k + 1) ^ 2 else 0),
    tail_square_sum a (max_le hi hj), haN]
  ring

lemma markovVector_norm {N : ℕ} {a : ℕ → ℝ} (haN : a N = 0)
    (ha : ∀ j < N, a (j + 1) ^ 2 ≤ a j ^ 2) {i : ℕ} (hi : i ≤ N) (hai : 0 ≤ a i) :
    ‖markovVector N a i‖ = a i := by
  have hh := markovVector_inner haN ha hi hi
  rw [max_self, real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg (markovVector N a i)]

def markovUnit (N : ℕ) (a : ℕ → ℝ) (i : ℕ) : EuclideanSpace ℝ (Fin N) :=
  (a i)⁻¹ • markovVector N a i

lemma markovUnit_inner {N : ℕ} {a : ℕ → ℝ} (haN : a N = 0)
    (ha : ∀ j < N, a (j + 1) ^ 2 ≤ a j ^ 2) {i j : ℕ}
    (hij : i ≤ j) (hj : j < N) (hai : 0 < a i) (haj : 0 < a j) :
    ⟪markovUnit N a i, markovUnit N a j⟫ = a j / a i := by
  simp only [markovUnit, real_inner_smul_left, real_inner_smul_right]
  rw [markovVector_inner haN ha (by omega) hj.le, max_eq_right hij]
  field_simp

lemma markovUnit_norm {N : ℕ} {a : ℕ → ℝ} (haN : a N = 0)
    (ha : ∀ j < N, a (j + 1) ^ 2 ≤ a j ^ 2) {i : ℕ} (hi : i < N) (hai : 0 < a i) :
    ‖markovUnit N a i‖ = 1 := by
  rw [markovUnit, norm_smul, markovVector_norm haN ha hi.le hai.le,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hai), inv_mul_cancel₀ (ne_of_gt hai)]


lemma exists_unit_gram {N : ℕ} {a : ℕ → ℝ}
    (hap : ∀ i < N, 0 < a i) (ham : ∀ i j, i ≤ j → j < N → a j ≤ a i) :
    ∃ u : ℕ → EuclideanSpace ℝ (Fin N),
      (∀ i < N, ‖u i‖ = 1) ∧
      ∀ i j, i ≤ j → j < N → ⟪u i, u j⟫ = a j / a i := by
  let b : ℕ → ℝ := fun i => if i < N then a i else 0
  have hbN : b N = 0 := by simp [b]
  have hba : ∀ j < N, b (j + 1) ^ 2 ≤ b j ^ 2 := by
    intro j hj
    by_cases hj' : j + 1 < N
    · simp only [b, ite_eq_left hj, ite_eq_left hj']
      exact pow_le_pow_left₀ (hap _ hj').le (ham j (j + 1) (by omega) hj') 2
    · simp [b, hj, hj', sq_nonneg]
  refine ⟨markovUnit N b, ?_, ?_⟩
  · intro i hi
    exact markovUnit_norm hbN hba hi (by simpa [b, hi] using hap i hi)
  · intro i j hij hj
    have hi : i < N := by omega
    simpa [b, hi, hj] using markovUnit_inner hbN hba hij hj
      (by simpa [b, hi] using hap i hi) (by simpa [b, hj] using hap j hj)

end

end OracleTemplate.BallProximal
