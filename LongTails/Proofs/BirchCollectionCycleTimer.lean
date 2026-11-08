import LongTails.Algorithms.BirchCollectionWorkerPools

namespace LongTails.Proofs.BirchCollectionCycleTimer

open LongTails.Algorithms.BirchCollectionWorkerPools

def waiting (T g k : ℕ) : ℕ :=
  if k % T ≤ g then g - k % T else T + g - k % T

def sinceLimit (T g k : ℕ) : ℕ := T - 1 - waiting T g k

lemma group_count (m s : ℕ) (hm : 0 < m) : cycleGroups m s = (m - 1) / s + 1 := by
  simp [cycleGroups, Nat.ne_of_gt hm]

lemma group_lt {m s : ℕ} (hm : 0 < m) (w : Fin m) :
    w.val / s < cycleGroups m s := by
  rw [group_count m s hm]
  have h : w.val ≤ m - 1 := by have := w.isLt; omega
  exact Nat.lt_succ_of_le (Nat.div_le_div_right h)

lemma cycle_group_mem {m s k : ℕ} (w : Fin m) :
    w ∈ cycleGroup m s k ↔ w.val / s = k % cycleGroups m s := by
  simp [cycleGroup]

lemma cycle_group_nonempty (m s k : ℕ) (hm : 0 < m) (hs : 0 < s) :
    ∃ w : Fin m, w ∈ cycleGroup m s k := by
  let T := cycleGroups m s
  let g := k % T
  have hT : 0 < T := by unfold T; rw [group_count m s hm]; exact Nat.zero_lt_succ _
  have hg : g < T := Nat.mod_lt _ hT
  have hg' : g ≤ (m - 1) / s := by rw [show T = (m - 1) / s + 1 from group_count m s hm] at hg; omega
  have hmul := (Nat.le_div_iff_mul_le hs).1 hg'
  have hlt : g * s < m := by omega
  refine ⟨⟨g * s, hlt⟩, (cycle_group_mem _).2 ?_⟩
  exact Nat.mul_div_cancel g hs

lemma waiting_lt {T g k : ℕ} (hT : 0 < T) (hg : g < T) : waiting T g k < T := by
  have hk := Nat.mod_lt k hT
  unfold waiting
  split_ifs <;> omega

lemma waiting_zero {T g k : ℕ} (hT : 0 < T) (_hg : g < T) :
    waiting T g k = 0 ↔ g = k % T := by
  have hk := Nat.mod_lt k hT
  unfold waiting
  split_ifs <;> omega

lemma phase_next {T k : ℕ} (hT : 0 < T) :
    (k + 1) % T = if k % T + 1 = T then 0 else k % T + 1 := by
  have hk := Nat.mod_lt k hT
  rw [← Nat.mod_add_mod k T 1]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

lemma since_selected {T g k : ℕ} (hT : 0 < T) (_hg : g < T)
    (h : g = k % T) : sinceLimit T g (k + 1) = 0 := by
  have hk := Nat.mod_lt k hT
  unfold sinceLimit waiting
  rw [phase_next hT]
  by_cases ht : k % T + 1 = T
  · rw [ite_eq_left ht, ite_eq_left (Nat.zero_le _)]
    omega
  · rw [ite_eq_right ht, ite_eq_right (by omega)]
    omega

lemma since_other {T g k : ℕ} (hT : 0 < T) (hg : g < T)
    (h : g ≠ k % T) : sinceLimit T g (k + 1) = sinceLimit T g k + 1 := by
  have hk := Nat.mod_lt k hT
  unfold sinceLimit waiting
  rw [phase_next hT]
  by_cases ht : k % T + 1 = T
  · rw [ite_eq_left ht, ite_eq_left (Nat.zero_le _), ite_eq_right (by omega)]
    omega
  · rw [ite_eq_right ht]
    split_ifs <;> omega

end LongTails.Proofs.BirchCollectionCycleTimer
