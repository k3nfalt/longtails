import LongTails.Proofs.DyadicHolderTrajectory

namespace OracleTemplate.DyadicHolder

lemma off_eq_sum (cfg : DyadicConfig) : ∀ n, off cfg n = ∑ k ∈ Finset.range n, cfg.batch k
  | 0 => rfl
  | n + 1 => by rw [off, off_eq_sum cfg n, Finset.sum_range_succ]

noncomputable def lvl (t : ℕ) : ℕ := if t = 0 then 0 else 2 ^ padicValNat 2 t

lemma lvl_even {s : ℕ} : lvl (2 * s) = 2 * lvl s := by
  unfold lvl
  by_cases hs : s = 0
  · simp [hs]
  · have h2 : 2 * s ≠ 0 := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_right_of_eq_false _ _ (eq_false hs),
      padicValNat.mul (by norm_num) hs, padicValNat.self (by norm_num), pow_add, pow_one]

lemma lvl_odd (s : ℕ) : lvl (2 * s + 1) = 1 := by
  unfold lvl
  have h : ¬ 2 ∣ 2 * s + 1 := by omega
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)), padicValNat.eq_zero_of_not_dvd h,
    pow_zero]

lemma sum_lvl_double (m : ℕ) :
    ∑ t ∈ Finset.range (2 * m), lvl t = m + 2 * ∑ s ∈ Finset.range m, lvl s := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ, lvl_odd, lvl_even]
      ring

lemma sum_lvl_block (J : ℕ) : 2 * ∑ t ∈ Finset.range (2 ^ J), lvl t = J * 2 ^ J := by
  induction J with
  | zero => simp [lvl]
  | succ J ih =>
      rw [pow_succ, mul_comm (2 ^ J) 2, sum_lvl_double, mul_add, ih]
      ring

lemma sum_mod_le (f : ℕ → ℕ) {n : ℕ} (hn : 0 < n) (N : ℕ) :
    ∑ k ∈ Finset.range N, f (k % n) ≤ (N / n + 1) * ∑ t ∈ Finset.range n, f t := by
  have hblock : ∀ q, ∑ k ∈ Finset.range (q * n), f (k % n) = q * ∑ t ∈ Finset.range n, f t := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        rw [show (q + 1) * n = q * n + n by ring, Finset.sum_range_add, ih]
        have : ∀ x ∈ Finset.range n, f ((q * n + x) % n) = f x := by
          intro x hx
          rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hx)]
        rw [Finset.sum_congr rfl this]
        ring
  have hN : N ≤ (N / n + 1) * n := by
    have := Nat.lt_div_mul_add hn (a := N)
    nlinarith [Nat.div_add_mod N n, Nat.mod_lt N hn]
  rw [← hblock]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN) fun _ _ _ => Nat.zero_le _

lemma DyadicConfig.lvl_pos (cfg : DyadicConfig) (k : ℕ) :
    lvl (cfg.pos k) = if cfg.pos k = 0 then 0 else 2 ^ cfg.level k := rfl

lemma anchor_count (cfg : DyadicConfig) (N : ℕ) :
    ∑ k ∈ Finset.range N, (if cfg.pos k = 0 then 1 else 0) ≤ N / 2 ^ cfg.J + 1 := by
  have h := sum_mod_le (fun t => if t = 0 then 1 else 0) (n := 2 ^ cfg.J) (by positivity) N
  have h1 : ∑ t ∈ Finset.range (2 ^ cfg.J), (if t = 0 then 1 else 0) = 1 := by
    rw [Finset.sum_ite_eq' (Finset.range (2 ^ cfg.J)) 0 (fun _ => 1)]
    simp
  rw [h1, mul_one] at h
  exact h

lemma level_count (cfg : DyadicConfig) (N : ℕ) :
    2 * ∑ k ∈ Finset.range N, lvl (cfg.pos k) ≤ (N / 2 ^ cfg.J + 1) * (cfg.J * 2 ^ cfg.J) := by
  have h := sum_mod_le lvl (n := 2 ^ cfg.J) (by positivity) N
  rw [← sum_lvl_block cfg.J]
  unfold DyadicConfig.pos
  nlinarith

end OracleTemplate.DyadicHolder
