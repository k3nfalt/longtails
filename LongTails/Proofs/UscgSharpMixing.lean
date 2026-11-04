import Mathlib

namespace LongTails.Proofs.UscgSharpMixing

lemma geometric_sum_le_inv {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (T : ℕ) :
    ∑ j ∈ Finset.range T, (1 - a) ^ j ≤ 1 / a := by
  have hid : a * (∑ j ∈ Finset.range T, (1 - a) ^ j) = 1 - (1 - a) ^ T := by
    induction T with
    | zero => simp
    | succ T ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring
  apply (le_div_iff₀ ha).mpr
  nlinarith [pow_nonneg (show 0 ≤ 1 - a by linarith) T]

lemma kernel_sum_cutoff {a C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (_hC : 0 ≤ C) (n : ℕ) (hcut : C * (1 - a) ^ n ≤ 1) (T : ℕ) :
    ∑ j ∈ Finset.range T, min 1 (C * (1 - a) ^ j) ≤ (n : ℝ) + 1 / a := by
  have hhead : ∀ k, (∑ j ∈ Finset.range k, min 1 (C * (1 - a) ^ j)) ≤ (k : ℝ) := by
    intro k
    calc
      _ ≤ ∑ j ∈ Finset.range k, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => min_le_left _ _)
      _ = _ := by simp
  by_cases hT : T ≤ n
  · have hh : (T : ℝ) ≤ n := by exact_mod_cast hT
    have hp : 0 ≤ 1 / a := by positivity
    linarith [hhead T]
  · have he : T = n + (T - n) := by omega
    rw [he, Finset.sum_range_add]
    have ht : (∑ j ∈ Finset.range (T - n), min 1 (C * (1 - a) ^ (n + j))) ≤ 1 / a := by
      calc
        _ ≤ ∑ j ∈ Finset.range (T - n), C * (1 - a) ^ (n + j) :=
          Finset.sum_le_sum (fun _ _ => min_le_right _ _)
        _ = (C * (1 - a) ^ n) * ∑ j ∈ Finset.range (T - n), (1 - a) ^ j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [pow_add]
          ring
        _ ≤ 1 * ∑ j ∈ Finset.range (T - n), (1 - a) ^ j := by
          gcongr
        _ ≤ _ := by simpa using geometric_sum_le_inv ha ha1 (T - n)
    linarith [hhead n]

lemma kernel_sum_log {a C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hC : 1 ≤ C) (T : ℕ) :
    ∑ j ∈ Finset.range T, min 1 (C * (1 - a) ^ j) ≤ (Real.log C + 2) / a := by
  let n : ℕ := ⌈Real.log C / a⌉₊
  have hn : Real.log C / a ≤ (n : ℝ) := Nat.le_ceil _
  have hnupper : (n : ℝ) ≤ Real.log C / a + 1 := by
    exact (Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg hC) ha.le)).le
  have hb : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
  have hp := pow_le_pow_left₀ (show 0 ≤ 1 - a by linarith) hb n
  have he : (Real.exp (-a)) ^ n = Real.exp (-a * n) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hp
  have hlog : Real.log C ≤ a * n := by nlinarith [(div_le_iff₀ ha).mp hn]
  have hcut : C * (1 - a) ^ n ≤ 1 := by
    calc
      _ ≤ C * Real.exp (-a * n) := mul_le_mul_of_nonneg_left hp (by linarith)
      _ ≤ C * Real.exp (-Real.log C) := by gcongr; linarith
      _ = 1 := by rw [Real.exp_neg, Real.exp_log (by linarith)]; field_simp
  have hh := kernel_sum_cutoff ha ha1 (show 0 ≤ C by linarith) n hcut T
  have hlast : (n : ℝ) + 1 / a ≤ (Real.log C + 2) / a := by
    apply (le_div_iff₀ ha).mpr
    have hu := (mul_le_mul_of_nonneg_right hnupper ha.le)
    have hid : (Real.log C / a + 1) * a = Real.log C + a := by field_simp
    rw [hid] at hu
    have hi : (1 / a) * a = 1 := by field_simp
    nlinarith
  exact hh.trans hlast

lemma shifted_kernel_sum (w : ℕ → ℝ) (j T : ℕ) :
    ∑ t ∈ Finset.range T, (if j ≤ t then w (t - j) else 0) =
      ∑ r ∈ Finset.range (T - j), w r := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hj : j ≤ T
    · have he : T + 1 - j = (T - j) + 1 := by omega
      simp [hj, he, Finset.sum_range_succ]
    · have hz : T - j = 0 := by omega
      have hz' : T + 1 - j = 0 := by omega
      simp [hj, hz, hz']

lemma occupation_sum_bound {I w y : ℕ → ℝ} {R : ℝ} {T : ℕ}
    (hI : ∀ j, 0 ≤ I j)
    (hkernel : ∀ n, ∑ r ∈ Finset.range n, w r ≤ R)
    (hpoint : ∀ t < T, y t ≤ ∑ j ∈ Finset.range T,
      I j * (if j ≤ t then w (t - j) else 0)) :
    ∑ t ∈ Finset.range T, y t ≤ R * ∑ j ∈ Finset.range T, I j := by
  calc
    _ ≤ ∑ t ∈ Finset.range T, ∑ j ∈ Finset.range T,
        I j * (if j ≤ t then w (t - j) else 0) :=
      Finset.sum_le_sum (fun t ht => hpoint t (Finset.mem_range.mp ht))
    _ = ∑ j ∈ Finset.range T, I j *
        (∑ t ∈ Finset.range T, if j ≤ t then w (t - j) else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
    _ = ∑ j ∈ Finset.range T, I j * (∑ r ∈ Finset.range (T - j), w r) := by
      simp_rw [shifted_kernel_sum]
    _ ≤ ∑ j ∈ Finset.range T, I j * R :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hkernel _) (hI j))
    _ = _ := by rw [← Finset.sum_mul]; ring

lemma min_one_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min 1 (a + b) ≤ min 1 a + min 1 b := by
  by_cases ha1 : a ≤ 1
  · by_cases hb1 : b ≤ 1
    · rw [min_eq_right ha1, min_eq_right hb1]
      exact min_le_right _ _
    · rw [min_eq_right ha1, min_eq_left (by linarith : 1 ≤ b)]
      exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_left (by linarith : 1 ≤ a)]
    have hh : 0 ≤ min 1 b := le_min (by norm_num) hb
    exact (min_le_left _ _).trans (by linarith)

lemma min_one_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    min 1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, min 1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (min_one_add (hf i (Finset.mem_insert_self _ _))
      (Finset.sum_nonneg (fun j hj => hf j (Finset.mem_insert_of_mem hj)))).trans
      (add_le_add le_rfl (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

lemma one_le_sum_min {ι : Type*} (s : Finset ι) {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hlarge : 1 ≤ ∑ i ∈ s, f i) :
    1 ≤ ∑ i ∈ s, min 1 (f i) := by
  simpa only [min_eq_left hlarge] using min_one_sum s hf

lemma binary_min_mul {I : ℕ} (hI : I ≤ 1) (v : ℝ) :
    min 1 ((I : ℝ) * v) = (I : ℝ) * min 1 v := by
  interval_cases I <;> simp

lemma positive_signal_occupation {ι : Type*} (s : Finset ι)
    {I : ι → ℕ} {w : ι → ℝ} {m mass : ℝ}
    (hI : ∀ j ∈ s, I j ≤ 1) (hw : ∀ j ∈ s, 0 ≤ w j)
    (hmass : 1 / 2 ≤ mass)
    (hsignal : m = -mass + (∑ j ∈ s, (I j : ℝ) * w j) / 2) :
    (if 0 ≤ m then (1 : ℝ) else 0) ≤ ∑ j ∈ s, (I j : ℝ) * min 1 (w j) := by
  by_cases hm : 0 ≤ m
  · rw [ite_eq_left hm]
    have hlarge : 1 ≤ ∑ j ∈ s, (I j : ℝ) * w j := by linarith
    have hh := one_le_sum_min s (fun j hj => mul_nonneg (Nat.cast_nonneg _) (hw j hj)) hlarge
    have he : (∑ j ∈ s, min 1 ((I j : ℝ) * w j)) =
        ∑ j ∈ s, (I j : ℝ) * min 1 (w j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact binary_min_mul (hI j hj) _
    rwa [he] at hh
  · rw [ite_eq_right hm]
    exact Finset.sum_nonneg (fun j hj => mul_nonneg (Nat.cast_nonneg _)
      (le_min (by norm_num) (hw j hj)))

lemma displacement_lower {x m v : ℕ → ℝ} {eta : ℝ} {T : ℕ}
    (heta : 0 ≤ eta) (hx : x 0 = 0)
    (hupdate : ∀ t < T, x (t + 1) = x t + eta * v t)
    (hv : ∀ t < T, -1 ≤ v t)
    (hnegative : ∀ t < T, m t < 0 → v t = 1) :
    ∀ n ≤ T, eta * ((n : ℝ) - 2 * ∑ t ∈ Finset.range n,
      if 0 ≤ m t then (1 : ℝ) else 0) ≤ x n := by
  intro n
  induction n with
  | zero => simp [hx]
  | succ n ih =>
    intro hn
    have hnT : n < T := by omega
    have hprev := ih hnT.le
    rw [hupdate n hnT, Finset.sum_range_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    by_cases hm : 0 ≤ m n
    · rw [ite_eq_left hm]
      nlinarith [hv n hnT]
    · rw [ite_eq_right hm, hnegative n hnT (lt_of_not_ge hm)]
      nlinarith

lemma occupation_from_signal {I : ℕ → ℕ} {m mass : ℕ → ℝ}
    {a C : ℝ} {T burn : ℕ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hC : 1 ≤ C)
    (hI : ∀ j, I j ≤ 1)
    (hzero : ∀ j < burn, j < T → I j = 0)
    (hmass : ∀ t < T, 0 < mass t)
    (hlate : ∀ t < T, burn ≤ t → 1 / 2 ≤ mass t)
    (hsignal : ∀ t < T, m t = -mass t +
      (∑ j ∈ Finset.range T, (I j : ℝ) *
        (if j ≤ t then C * (1 - a) ^ (t - j) else 0)) / 2) :
    ∑ t ∈ Finset.range T, (if 0 ≤ m t then (1 : ℝ) else 0) ≤
      ((Real.log C + 2) / a) * ∑ j ∈ Finset.range T, (I j : ℝ) := by
  apply occupation_sum_bound (fun _ => Nat.cast_nonneg _) (kernel_sum_log ha ha1 hC)
  intro t ht
  by_cases hb : burn ≤ t
  · have hh := positive_signal_occupation (Finset.range T) (fun j _ => hI j)
      (fun j _ => show 0 ≤ (if j ≤ t then C * (1 - a) ^ (t - j) else 0) by
        split_ifs <;> positivity)
      (hlate t ht hb) (hsignal t ht)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  · have hz : (∑ j ∈ Finset.range T, (I j : ℝ) *
        (if j ≤ t then C * (1 - a) ^ (t - j) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hjt : j ≤ t
      · rw [hzero j (by omega) (Finset.mem_range.mp hj)]
        simp
      · simp [hjt]
    have hm : m t < 0 := by rw [hsignal t ht, hz]; linarith [hmass t ht]
    rw [ite_eq_right (not_le_of_gt hm)]
    apply Finset.sum_nonneg
    intro j _
    apply mul_nonneg (Nat.cast_nonneg _)
    split_ifs <;> positivity

lemma early_zero_of_sparse {I : ℕ → ℕ} {R : ℝ} {burn T : ℕ}
    (hR : (burn : ℝ) ≤ R)
    (hsparse : ∀ n, 0 < n → n ≤ T →
      2 * R * ((∑ j ∈ Finset.range n, I j : ℕ) : ℝ) < n) :
    ∀ j < burn, j < T → I j = 0 := by
  intro j hj hjT
  have hs := hsparse (j + 1) (by omega) (by omega)
  have hsingle : I j ≤ ∑ i ∈ Finset.range (j + 1), I i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le _) (by simp)
  have hj' : ((j + 1 : ℕ) : ℝ) ≤ burn := by exact_mod_cast hj
  have hR0 : 0 ≤ R := le_trans (Nat.cast_nonneg _) hR
  by_contra hn
  have hi : 1 ≤ I j := by omega
  have hsum : (1 : ℝ) ≤ ((∑ i ∈ Finset.range (j + 1), I i : ℕ) : ℝ) := by
    exact_mod_cast hi.trans hsingle
  nlinarith

lemma positive_displacement {x m v : ℕ → ℝ} {eta R : ℝ} {I : ℕ → ℕ} {T : ℕ}
    (heta : 0 < eta) (hx : x 0 = 0)
    (hupdate : ∀ t < T, x (t + 1) = x t + eta * v t)
    (hv : ∀ t < T, -1 ≤ v t)
    (hnegative : ∀ t < T, m t < 0 → v t = 1)
    (hoccupancy : ∀ n ≤ T,
      (∑ t ∈ Finset.range n, if 0 ≤ m t then (1 : ℝ) else 0) ≤
        R * ((∑ j ∈ Finset.range n, I j : ℕ) : ℝ))
    (hsparse : ∀ n, 0 < n → n ≤ T →
      2 * R * ((∑ j ∈ Finset.range n, I j : ℕ) : ℝ) < n) :
    ∀ n, 0 < n → n ≤ T → 0 < x n := by
  intro n hn hnT
  have hd := displacement_lower heta.le hx hupdate hv hnegative n hnT
  have ho := hoccupancy n hnT
  have hs := hsparse n hn hnT
  have hp : 0 < (n : ℝ) - 2 * ∑ t ∈ Finset.range n,
      if 0 ≤ m t then (1 : ℝ) else 0 := by linarith
  exact lt_of_lt_of_le (mul_pos heta hp) hd

noncomputable def burnTime (a : ℝ) : ℕ := ⌈Real.log 2 / a⌉₊

lemma burn_le_radius {a C : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hC : 1 ≤ C) :
    (burnTime a : ℝ) ≤ (Real.log C + 2) / a := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hn : (burnTime a : ℝ) ≤ Real.log 2 / a + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (Real.log_nonneg (by norm_num)) ha.le)).le
  have hid : (Real.log 2 / a + 1) * a = Real.log 2 + a := by field_simp
  apply (le_div_iff₀ ha).mpr
  have hu := mul_le_mul_of_nonneg_right hn ha.le
  rw [hid] at hu
  linarith [Real.log_nonneg hC]

lemma forgetting_le_exp {a : ℝ} (_ha : 0 ≤ a) (ha1 : a ≤ 1) (t : ℕ) :
    (1 - a) ^ t ≤ Real.exp (-a * t) := by
  have hb : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
  have hh := pow_le_pow_left₀ (show 0 ≤ 1 - a by linarith) hb t
  have he : (Real.exp (-a)) ^ t = Real.exp (-a * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [he] at hh

lemma late_mass {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {t : ℕ}
    (ht : burnTime a ≤ t) : 1 / 2 ≤ 1 - (1 - a) ^ (t + 1) := by
  have hn : Real.log 2 / a ≤ (burnTime a : ℝ) := Nat.le_ceil _
  have ht' : (burnTime a : ℝ) ≤ t := by exact_mod_cast ht
  have hprod : Real.log 2 ≤ a * (t + 1) := by
    have hh := (div_le_iff₀ ha).mp (hn.trans ht')
    nlinarith
  have hp := forgetting_le_exp ha.le ha1 (t + 1)
  have hex : Real.exp (-a * (t + 1)) ≤ (1 / 2 : ℝ) := by
    calc
      _ ≤ Real.exp (-Real.log 2) := by apply Real.exp_le_exp.mpr; linarith
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  push_cast at hp
  linarith

end LongTails.Proofs.UscgSharpMixing
