import LongTails.Proofs.NcConcaveHuber

open scoped BigOperators

namespace LongTails.Proofs.NcConcaveBlock

open LongTails.Proofs.NcConcaveHuber

variable {m : ℕ}

noncomputable def alpha (m : ℕ) : ℝ := 1 / Real.sqrt (m + 1)

lemma alpha_pos (m : ℕ) : 0 < alpha m := by
  unfold alpha; have : (0 : ℝ) < Real.sqrt (m + 1) := Real.sqrt_pos.mpr (by positivity); positivity

lemma alpha_sq (m : ℕ) : alpha m ^ 2 = 1 / (m + 1) := by
  unfold alpha; rw [div_pow, Real.sq_sqrt (by positivity)]; ring

lemma alpha_le_one (m : ℕ) : alpha m ≤ 1 := by
  unfold alpha
  rw [div_le_one (Real.sqrt_pos.mpr (by positivity))]
  simp

lemma alpha_mul_le (m : ℕ) : alpha m * m ≤ Real.sqrt (m + 1) := by
  have h := alpha_sq m
  have hp := alpha_pos m
  have hs : 0 < Real.sqrt (m + 1) := Real.sqrt_pos.mpr (by positivity)
  have hss := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m + 1)
  have : alpha m * Real.sqrt (m + 1) = 1 := by
    unfold alpha; field_simp
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

noncomputable def blockVal (τ a b : ℝ) (y : Fin (m + 1) → ℝ) : ℝ :=
  -(alpha m ^ 2 / 2) * y 0 ^ 2 - ∑ k : Fin m, huber τ (y k.castSucc - y k.succ) +
    alpha m * a * y 0 - alpha m / 2 * b * y (Fin.last m) - alpha m ^ 2 * m * b ^ 2 / 8

noncomputable def ystar (a b : ℝ) (k : Fin (m + 1)) : ℝ :=
  (a - b / 2) / alpha m - alpha m * b / 2 * k

lemma ystar_diff (a b : ℝ) (k : Fin m) :
    ystar (m := m) a b k.castSucc - ystar a b k.succ = alpha m * b / 2 := by
  simp only [ystar, Fin.val_castSucc, Fin.val_succ]; push_cast; ring

lemma telescope (w : Fin (m + 1) → ℝ) :
    ∑ k : Fin m, (w k.castSucc - w k.succ) = w 0 - w (Fin.last m) := by
  have h1 := Fin.sum_univ_castSucc w
  have h2 := Fin.sum_univ_succ w
  rw [Finset.sum_sub_distrib]; linarith

lemma block_value_star {τ : ℝ} (hτ : 0 < τ) (a b : ℝ) (hb : |alpha m * b / 2| ≤ τ) :
    blockVal (m := m) τ a b (ystar a b) = (a - b / 2) ^ 2 / 2 := by
  have hα := alpha_pos m
  unfold blockVal
  have hd (k : Fin m) : huber τ (ystar (m := m) a b k.castSucc - ystar a b k.succ) =
      (alpha m * b / 2) ^ 2 / 2 := by
    rw [ystar_diff, huber_of_abs_le hτ hb]
  simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hlast : ystar (m := m) a b (Fin.last m) = (a - b / 2) / alpha m - alpha m * b / 2 * m := by
    simp [ystar]
  have h0 : ystar (m := m) a b 0 = (a - b / 2) / alpha m := by simp [ystar]
  rw [hlast, h0]
  field_simp
  ring

lemma block_le {τ : ℝ} (hτ : 0 < τ) (a b : ℝ) (hb : |alpha m * b / 2| ≤ τ) (y : Fin (m + 1) → ℝ) :
    blockVal (m := m) τ a b y ≤ (a - b / 2) ^ 2 / 2 := by
  rw [← block_value_star hτ a b hb]
  have hα := alpha_pos m
  set ys := ystar (m := m) a b
  have hstar : dhuber τ (alpha m * b / 2) = alpha m * b / 2 := dhuber_of_abs_le hτ hb
  have hk (k : Fin m) : huber τ (ys k.castSucc - ys k.succ) + alpha m * b / 2 *
      ((y k.castSucc - y k.succ) - (ys k.castSucc - ys k.succ)) ≤ huber τ (y k.castSucc - y k.succ) := by
    have h := (huber_model hτ (ys k.castSucc - ys k.succ) (y k.castSucc - y k.succ)).1
    rw [ystar_diff] at h ⊢
    rw [hstar] at h
    linarith
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hk k)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have ht := telescope (fun k => y k - ys k)
  have ht' : ∑ k : Fin m, ((y k.castSucc - y k.succ) - (ys k.castSucc - ys k.succ)) =
      (y 0 - ys 0) - (y (Fin.last m) - ys (Fin.last m)) := by
    rw [← ht]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [ht'] at hsum
  have h0 : ys 0 = (a - b / 2) / alpha m := by simp [ys, ystar]
  have hq : alpha m ^ 2 / 2 * ys 0 ^ 2 + alpha m ^ 2 * ys 0 * (y 0 - ys 0) ≤
      alpha m ^ 2 / 2 * y 0 ^ 2 := by nlinarith [sq_nonneg (y 0 - ys 0), sq_nonneg (alpha m)]
  unfold blockVal
  have hαys : alpha m ^ 2 * ys 0 = alpha m * (a - b / 2) := by rw [h0]; field_simp
  have hq' : alpha m ^ 2 / 2 * ys 0 ^ 2 + alpha m * (a - b / 2) * (y 0 - ys 0) ≤
      alpha m ^ 2 / 2 * y 0 ^ 2 := by rw [← hαys]; exact hq
  linarith [hq', hsum]

lemma ystar_sq_le (a b : ℝ) :
    ∑ k : Fin (m + 1), ystar (m := m) a b k ^ 2 ≤ 2 * (m + 1) ^ 2 * (a ^ 2 + b ^ 2) := by
  have hα := alpha_pos m
  have hm := alpha_mul_le m
  have hs : 0 < Real.sqrt (m + 1) := Real.sqrt_pos.mpr (by positivity)
  have hss := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ m + 1)
  have hinv : 1 / alpha m = Real.sqrt (m + 1) := by unfold alpha; field_simp
  have hpt (k : Fin (m + 1)) : |ystar (m := m) a b k| ≤ (|a| + |b|) * Real.sqrt (m + 1) := by
    have hk : (k : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp k.isLt
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    unfold ystar
    have e1 : |(a - b / 2) / alpha m| ≤ (|a| + |b| / 2) * Real.sqrt (m + 1) := by
      rw [div_eq_mul_one_div, hinv, abs_mul, abs_of_pos hs]
      have : |a - b / 2| ≤ |a| + |b| / 2 := by
        calc |a - b / 2| ≤ |a| + |b / 2| := abs_sub _ _
          _ = |a| + |b| / 2 := by rw [abs_div]; norm_num
      nlinarith
    have e2 : |alpha m * b / 2 * k| ≤ |b| / 2 * Real.sqrt (m + 1) := by
      rw [show alpha m * b / 2 * (k : ℝ) = b / 2 * (alpha m * k) by ring, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ alpha m * (k : ℝ))]
      rw [abs_div]; norm_num
      have : alpha m * k ≤ Real.sqrt (m + 1) := le_trans (by nlinarith) hm
      nlinarith [abs_nonneg b]
    calc _ ≤ |(a - b / 2) / alpha m| + |alpha m * b / 2 * k| := abs_sub _ _
      _ ≤ _ := by linarith
  have hsq (k : Fin (m + 1)) : ystar (m := m) a b k ^ 2 ≤ (m + 1) * (2 * (a ^ 2 + b ^ 2)) := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (hpt k) 2
    rw [sq_abs, mul_pow, hss] at h
    nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]
  have := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hsq k)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  push_cast at this
  nlinarith

end LongTails.Proofs.NcConcaveBlock
