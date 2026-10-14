import LongTails.Proofs.ReshuffledHarmonicWeights

set_option autoImplicit false

open Finset

namespace OracleTemplate.ReshuffledWeighted

open ReshuffledHarmonic

lemma sum_range_blocks (n K : ℕ) (f : ℕ → ℝ) :
    (∑ t ∈ range (n * K), f t) = ∑ k ∈ range K, ∑ i ∈ range n, f (n * k + i) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

lemma triangular_sum (n : ℕ) (a b : ℕ → ℝ) :
    (∑ i ∈ range n, a i * ∑ j ∈ range i, b j) =
      ∑ j ∈ range n, b j * ∑ i ∈ Ico (j + 1) n, a i := by
  simp_rw [mul_sum]
  simpa only [Nat.Ico_zero_eq_range, mul_comm] using
    (sum_Ico_Ico_comm' 0 n (fun j i => b j * a i)).symm

lemma future_weights {c : ℝ} (hc : 0 ≤ c) {n b S j : ℕ}
    (hb : b + n ≤ S) (hj : j < n) :
    (∑ i ∈ Ico (j + 1) n, V c (S - (b + i))) ≤ n * H n * V c (S - (b + j)) := by
  have he : (∑ i ∈ Ico (j + 1) n, V c (S - (b + i))) =
      ∑ l ∈ range (n - 1 - j), V c (S + 1 - (b + n) + l) := by
    simp_rw [show ∀ i, S - (b + i) = (S - b) - i by omega]
    rw [sum_Ico_reflect _ _ (by omega), sum_Ico_eq_sum_range]
    apply sum_congr
    · congr 1; omega
    · intro l hl
      congr 1
      omega
  rw [he]
  have hz := sum_V_epoch_le (c := c) hc
    (q := S + 1 - (b + n)) (m := n - 1 - j) (n := n) (by omega) (by omega)
  convert hz using 1; congr 2; omega

lemma epoch_history {c : ℝ} (hc : 0 ≤ c) {n b S : ℕ}
    (hb : b + n ≤ S) (M : ℕ → ℝ) (hM : ∀ j, j < n → 0 ≤ M (b + j)) :
    (∑ i ∈ range n, V c (S - (b + i)) * ∑ j ∈ range i, M (b + j)) ≤
      n * H n * ∑ j ∈ range n, V c (S - (b + j)) * M (b + j) := by
  rw [triangular_sum]
  calc
    _ ≤ ∑ j ∈ range n, M (b + j) * (n * H n * V c (S - (b + j))) := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left (future_weights hc hb (mem_range.mp hj))
        (hM j (mem_range.mp hj))
    _ = _ := by simp only [mul_sum]; apply sum_congr rfl; intros; ring

noncomputable def history (n : ℕ) (M : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ j ∈ range (t % n), M (n * (t / n) + j)

lemma history_inner {n : ℕ} (hn : 0 < n) (M : ℕ → ℝ) (k i : ℕ) (hi : i < n) :
    history n M (n * k + i) = ∑ j ∈ range i, M (n * k + j) := by
  simp only [history, Nat.mul_add_div hn, Nat.div_eq_of_lt hi, add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hi]

lemma weighted_history {c : ℝ} (hc : 0 ≤ c) {n K S : ℕ} (hn : 0 < n)
    (hS : n * K ≤ S) (M : ℕ → ℝ) (hM : ∀ t, t < n * K → 0 ≤ M t) :
    (∑ t ∈ range (n * K), V c (S - t) * history n M t) ≤
      n * H n * ∑ t ∈ range (n * K), V c (S - t) * M t := by
  rw [sum_range_blocks, sum_range_blocks, mul_sum]
  apply sum_le_sum
  intro k hk
  have hk' := mem_range.mp hk
  have hb : n * k + n ≤ S := by nlinarith
  have he : (∑ i ∈ range n, V c (S - (n * k + i)) * history n M (n * k + i)) =
      ∑ i ∈ range n, V c (S - (n * k + i)) * ∑ j ∈ range i, M (n * k + j) := by
    apply sum_congr rfl
    intro i hi
    rw [history_inner hn M k i (mem_range.mp hi)]
  rw [he]
  exact epoch_history hc hb M (fun j hj => hM _ (by nlinarith))

lemma centered_absorption {η L H A R M V : ℝ}
    (hη : 0 ≤ η) (hL : 0 ≤ L) (hH : 1 ≤ H) (hA : 0 ≤ A)
    (hstep : η * L * H ≤ 1 / 40)
    (ha : A ≤ R + 2 * η * L * A + η * H * M)
    (hm : M ≤ 4 * L * A + 2 * V) : A ≤ 2 * R + 4 * η * H * V := by
  have hH0 : 0 ≤ H := by linarith
  have hηL : 0 ≤ η * L := mul_nonneg hη hL
  have hsmall : η * L ≤ 1 / 40 := by
    have hh := mul_le_mul_of_nonneg_left hH hηL
    nlinarith
  have hc : η * L * (2 + 4 * H) ≤ 1 / 2 := by nlinarith
  have hcA := mul_le_mul_of_nonneg_right hc hA
  have hm' := mul_le_mul_of_nonneg_left hm (mul_nonneg hη hH0)
  nlinarith

lemma bregman_absorption {η L H B M N : ℝ}
    (hη : 0 ≤ η) (hH : 1 ≤ H) (hB : 0 ≤ B)
    (hstep : η * L * H ≤ 1 / 40) (hm : M ≤ 4 * L * B + 2 * N) :
    10 * H * η ^ 2 * M - 2 * η * B ≤ 20 * H * η ^ 2 * N := by
  have hH0 : 0 ≤ H := by linarith
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 10 * H * η ^ 2 by positivity)
  have hs := mul_le_mul_of_nonneg_right hstep (show 0 ≤ 40 * η * B by positivity)
  nlinarith

lemma initialization_absorption {η L H D R w : ℝ}
    (hη : 0 ≤ η) (hL : 0 ≤ L) (hH : 1 ≤ H) (hw : 0 ≤ w)
    (hstep : η * L * H ≤ 1 / 40) (hR : R ≤ L * D ^ 2 / 2) :
    w * D ^ 2 / 2 + (1 + 132 * H) * η ^ 2 * L * w * R ≤ w * D ^ 2 := by
  have hH0 : 0 ≤ H := by linarith
  have hηL : 0 ≤ η * L := mul_nonneg hη hL
  have hsmall : η * L ≤ 1 / 40 := by
    have hh := mul_le_mul_of_nonneg_left hH hηL
    nlinarith
  have hs1 : (η * L) ^ 2 ≤ 1 / 1600 := by nlinarith
  have hs2 : η ^ 2 * L ^ 2 * H ≤ 1 / 1600 := by
    have hh := mul_le_mul hsmall hstep (mul_nonneg hηL hH0) (by norm_num : (0 : ℝ) ≤ 1 / 40)
    nlinarith
  have hc : (1 + 132 * H) * η ^ 2 * L ^ 2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hR
    (show 0 ≤ (1 + 132 * H) * η ^ 2 * L * w by positivity)
  have hc' := mul_le_mul_of_nonneg_right hc (show 0 ≤ w * D ^ 2 / 2 by positivity)
  nlinarith

lemma weighted_history_shifted {c : ℝ} (hc : 0 ≤ c) {n K : ℕ} (hn : 0 < n)
    (hK : 0 < K) (M : ℕ → ℝ) (hM : ∀ t, t < n * K → 0 ≤ M t) :
    let v := fun t => if t = 0 then V c (n * K) else V c (n * K + 1 - t)
    (∑ t ∈ range (n * K), v t * history n M t) ≤
      n * H n * ∑ t ∈ range (n * K), v t * M t := by
  dsimp only
  have he : (∑ t ∈ range (n * K),
      (if t = 0 then V c (n * K) else V c (n * K + 1 - t)) * history n M t) =
      ∑ t ∈ range (n * K), V c (n * K + 1 - t) * history n M t := by
    apply sum_congr rfl
    intro t ht
    by_cases hz : t = 0
    · subst t; simp [history]
    · simp [hz]
  rw [he]
  apply (weighted_history hc hn (Nat.le_succ (n * K)) M hM).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity [H_nonneg n])
  apply sum_le_sum
  intro t ht
  apply mul_le_mul_of_nonneg_right _ (hM t (mem_range.mp ht))
  by_cases hz : t = 0
  · subst t
    simpa using V_succ_le hc (Nat.mul_pos hn hK)
  · simp [hz]

lemma centered_weighted {n T : ℕ} (hn : 0 < n) (w A R M : ℕ → ℝ) {η L H V0 : ℝ}
    (hη : 0 ≤ η) (hL : 0 ≤ L) (hH : 1 ≤ H) (hstep : η * L * H ≤ 1 / 40)
    (hw : ∀ t, t < T → 0 ≤ w t) (hA : ∀ t, t < T → 0 ≤ A t)
    (ha : ∀ t, t < T → n * (A t - R t) ≤ 2 * n * η * L * A t + η * history n M t)
    (hm : ∀ t, t < T → M t ≤ 4 * L * A t + 2 * V0)
    (hh : (∑ t ∈ range T, w t * history n M t) ≤ n * H * ∑ t ∈ range T, w t * M t) :
    (∑ t ∈ range T, w t * A t) ≤
      2 * (∑ t ∈ range T, w t * R t) + 4 * η * H * V0 * ∑ t ∈ range T, w t := by
  have has := sum_le_sum (s := range T) (fun t ht =>
    show (n : ℝ) * (w t * A t) - n * (w t * R t) ≤
        (2 * n * η * L) * (w t * A t) + η * (w t * history n M t) by
      have hh := mul_le_mul_of_nonneg_left (ha t (mem_range.mp ht)) (hw t (mem_range.mp ht))
      nlinarith)
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum] at has
  have hms := sum_le_sum (s := range T) (fun t ht =>
    mul_le_mul_of_nonneg_left (hm t (mem_range.mp ht)) (hw t (mem_range.mp ht)))
  have hηh := mul_le_mul_of_nonneg_left hh hη
  have hnn : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ha' : (∑ t ∈ range T, w t * A t) ≤
      (∑ t ∈ range T, w t * R t) + 2 * η * L * (∑ t ∈ range T, w t * A t) +
        η * H * (∑ t ∈ range T, w t * M t) := by
    have hn' : n * (∑ t ∈ range T, w t * A t) ≤
        n * ((∑ t ∈ range T, w t * R t) + 2 * η * L * (∑ t ∈ range T, w t * A t) +
          η * H * (∑ t ∈ range T, w t * M t)) := by
      nlinarith
    exact le_of_mul_le_mul_left hn' hnn
  have hm' : (∑ t ∈ range T, w t * M t) ≤
      4 * L * (∑ t ∈ range T, w t * A t) + 2 * (V0 * ∑ t ∈ range T, w t) := by
    calc
      _ ≤ ∑ t ∈ range T, w t * (4 * L * A t + 2 * V0) := hms
      _ = _ := by
        simp only [mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intros
        ring
  have hres := centered_absorption hη hL hH
    (sum_nonneg fun t ht => mul_nonneg (hw t (mem_range.mp ht)) (hA t (mem_range.mp ht)))
    hstep ha' hm'
  nlinarith

end OracleTemplate.ReshuffledWeighted
