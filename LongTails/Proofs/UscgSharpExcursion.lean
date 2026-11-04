import Mathlib

namespace LongTails.Proofs.UscgSharpExcursion

lemma impulse_negative {α B L η : ℝ} {k t : ℕ}
    (ha : 0 < α) (ha1 : α < 1) (hB : 0 ≤ B) (hL : 0 < L) (he : 0 < η)
    (hk : 0 < k) (ht : t < k)
    (hshock : 2 * L * η * (k : ℝ) ^ 2 ≤ B * (1 - α) ^ k) :
    α * (-B * (1 - α) ^ t + L * η * ((t : ℝ) * (t + 1) / 2)) < 0 := by
  have hb : 0 ≤ 1 - α := by linarith
  have hp := pow_le_pow_of_le_one hb (show 1 - α ≤ 1 by linarith) ht.le
  have hm := mul_le_mul_of_nonneg_left hp hB
  have ht' : (t : ℝ) + 1 ≤ k := by exact_mod_cast ht
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have hprod : (t : ℝ) * (t + 1) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hprod (show 0 ≤ L * η by positivity)
  have hpos : 0 < L * η * (k : ℝ) ^ 2 := by positivity
  apply mul_neg_of_pos_of_neg ha
  nlinarith

lemma excursion {α B L η : ℝ} {k : ℕ} {x m : ℕ → ℝ}
    (ha : 0 < α) (ha1 : α < 1) (hB : 0 ≤ B) (hL : 0 < L) (he : 0 < η)
    (hk : 0 < k) (hx : x 0 = 0) (hm : m 0 = -α * B)
    (hupdate : ∀ t < k, m t < 0 → x (t + 1) = x t + η)
    (hmom : ∀ t < k, m (t + 1) = (1 - α) * m t + α * L * x (t + 1))
    (hshock : 2 * L * η * (k : ℝ) ^ 2 ≤ B * (1 - α) ^ k) :
    ∀ t ≤ k, x t = η * t ∧
      m t ≤ α * (-B * (1 - α) ^ t + L * η * ((t : ℝ) * (t + 1) / 2)) := by
  intro t
  induction t with
  | zero => simp [hx, hm]
  | succ t ih =>
    intro ht
    have htk : t < k := by omega
    obtain ⟨hxt, hmt⟩ := ih htk.le
    have hneg := lt_of_le_of_lt hmt (impulse_negative ha ha1 hB hL he hk htk hshock)
    have hxn : x (t + 1) = η * (t + 1) := by rw [hupdate t htk hneg, hxt]; ring
    refine ⟨by simpa using hxn, ?_⟩
    rw [hmom t htk, hxn]
    have hscaled := mul_le_mul_of_nonneg_left hmt (show 0 ≤ 1 - α by linarith)
    have hc : 0 ≤ α * α * L * η * ((t : ℝ) * (t + 1) / 2) := by positivity
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

lemma gradient_area {L η : ℝ} {k : ℕ} {x : ℕ → ℝ}
    (hL : 0 ≤ L) (he : 0 ≤ η) (hx : ∀ t ≤ k, x t = η * t) :
    L * η * (k : ℝ) ^ 2 / 2 ≤ ∑ t ∈ Finset.range (k + 1), |L * x t| := by
  have heq : ∑ t ∈ Finset.range (k + 1), |L * x t| =
      L * η * ((k : ℝ) * (k + 1) / 2) := by
    calc
      _ = ∑ t ∈ Finset.range (k + 1), L * η * (t : ℝ) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [hx t (by simpa using Finset.mem_range.mp ht), abs_of_nonneg (by positivity)]
        ring
      _ = _ := by
        rw [← Finset.mul_sum]
        have hs' : (∑ t ∈ Finset.range (k + 1), (t : ℝ)) = (k : ℝ) * (k + 1) / 2 := by
          have hn : (∑ t ∈ Finset.range (k + 1), t) * 2 = (k + 1) * k := by
            simpa using Finset.sum_range_id_mul_two (k + 1)
          have hr : (∑ t ∈ Finset.range (k + 1), (t : ℝ)) * 2 = (k + 1) * (k : ℝ) := by
            have hc := congrArg (fun n : ℕ => (n : ℝ)) hn
            push_cast at hc
            exact hc
          linarith
        rw [hs']
  rw [heq]
  have : 0 ≤ L * η * (k : ℝ) := by positivity
  nlinarith

end LongTails.Proofs.UscgSharpExcursion
