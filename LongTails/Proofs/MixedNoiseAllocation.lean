import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace OracleTemplate.MixedNoise

lemma sum_two_pow (m : ℕ) : ∑ l ∈ Finset.range m, (2 : ℝ) ^ l = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

lemma sum_inv_two_pow (m : ℕ) :
    ∑ l ∈ Finset.range m, 1 / (2 : ℝ) ^ l = 2 - 2 / 2 ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    field_simp
    ring

lemma sum_inv_two_pow_le (m : ℕ) :
    ∑ l ∈ Finset.range m, 1 / (2 : ℝ) ^ l ≤ 2 := by
  rw [sum_inv_two_pow]
  have : 0 ≤ (2 : ℝ) / 2 ^ m := by positivity
  linarith

lemma relative_allocation {C r : ℝ} (hC : 0 < C) (b : ℕ → ℝ) (m : ℕ)
    (hb : ∀ l < m, 0 < b l) (halloc : ∀ l < m, C * r * 2 ^ l ≤ b l) :
    ∑ l ∈ Finset.range m, r / b l ≤ 2 / C := by
  have hterm : ∀ l < m, r / b l ≤ (1 / (2 : ℝ) ^ l) / C := by
    intro l hl
    rw [div_div]
    apply (div_le_div_iff₀ (hb l hl) (by positivity : 0 < (2 : ℝ) ^ l * C)).mpr
    nlinarith [halloc l hl]
  calc
    _ ≤ ∑ l ∈ Finset.range m, (1 / (2 : ℝ) ^ l) / C :=
      Finset.sum_le_sum fun l hl => hterm l (Finset.mem_range.mp hl)
    _ = (∑ l ∈ Finset.range m, 1 / (2 : ℝ) ^ l) / C := by rw [Finset.sum_div]
    _ ≤ 2 / C := div_le_div_of_nonneg_right (sum_inv_two_pow_le m) hC.le

lemma normalized_geometric_allocation (m : ℕ) :
    ∑ l ∈ Finset.range m, (2 : ℝ) ^ l / 2 ^ m ≤ 1 := by
  rw [← Finset.sum_div, sum_two_pow]
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ m)).mpr
  linarith

lemma geometric_weighted_allocation {C v : ℝ} (hC : 0 < C) (b : ℕ → ℝ) (m k : ℕ)
    (hb : ∀ l < m, 0 < b l)
    (halloc : ∀ l < m, C * v * 2 ^ m * ((2 : ℝ) ^ l) ^ k ≤ b l) :
    ∑ l ∈ Finset.range m, v * ((2 : ℝ) ^ l) ^ (k + 1) / b l ≤ 1 / C := by
  have hterm : ∀ l < m,
      v * ((2 : ℝ) ^ l) ^ (k + 1) / b l ≤ ((2 : ℝ) ^ l / 2 ^ m) / C := by
    intro l hl
    rw [div_div]
    apply (div_le_div_iff₀ (hb l hl) (by positivity : 0 < (2 : ℝ) ^ m * C)).mpr
    have hh := mul_le_mul_of_nonneg_left (halloc l hl)
      (by positivity : 0 ≤ (2 : ℝ) ^ l)
    rw [pow_succ]
    nlinarith
  calc
    _ ≤ ∑ l ∈ Finset.range m, ((2 : ℝ) ^ l / 2 ^ m) / C :=
      Finset.sum_le_sum fun l hl => hterm l (Finset.mem_range.mp hl)
    _ = (∑ l ∈ Finset.range m, (2 : ℝ) ^ l / 2 ^ m) / C := by rw [Finset.sum_div]
    _ ≤ 1 / C := div_le_div_of_nonneg_right (normalized_geometric_allocation m) hC.le

lemma sum_blocks (u : ℕ → ℝ) (n h : ℕ) :
    (∑ j ∈ Finset.range n, ∑ k ∈ Finset.range h, u (j * h + k)) =
      ∑ k ∈ Finset.range (n * h), u k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.succ_mul, Finset.sum_range_add, ih]

lemma previous_block_energy (u : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k) (n h : ℕ) (hh : 0 < h) :
    (∑ j ∈ Finset.range (n - 1), (h : ℝ) *
      ((∑ k ∈ Finset.range h, u (j * h + k)) / h)) ≤
      ∑ k ∈ Finset.range (n * h), u k := by
  have hhr : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
  have hcancel (a : ℝ) : (h : ℝ) * (a / h) = a := by field_simp
  simp only [hcancel]
  rw [sum_blocks]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.mul_le_mul_right h (Nat.sub_le n 1)))
  exact fun k _ _ => hu k

lemma held_previous_block_energy (u : ℕ → ℝ) (hu : ∀ k, 0 ≤ u k)
    (n h : ℕ) (hh : 0 < h) :
    (∑ t ∈ Finset.range (n * h),
      if t < h then 0 else (∑ k ∈ Finset.range h, u ((t / h - 1) * h + k)) / h) ≤
      ∑ t ∈ Finset.range (n * h), u t := by
  rw [← sum_blocks]
  have hblock (j : ℕ) :
      (∑ k ∈ Finset.range h,
        if j * h + k < h then 0 else
          (∑ a ∈ Finset.range h, u (((j * h + k) / h - 1) * h + a)) / h) =
      if j = 0 then 0 else (h : ℝ) * ((∑ k ∈ Finset.range h, u ((j - 1) * h + k)) / h) := by
    by_cases hj : j = 0
    · subst j
      simp only [zero_mul, zero_add, ↓reduceIte]
      apply Finset.sum_eq_zero
      intro k hk
      simp [Finset.mem_range.mp hk]
    · have hjpos : 1 ≤ j := by omega
      have he (k : ℕ) (hk : k ∈ Finset.range h) :
          (j * h + k) / h = j ∧ ¬ j * h + k < h := by
        have hk' := Finset.mem_range.mp hk
        constructor
        · rw [Nat.add_comm, Nat.add_mul_div_right k j hh, Nat.div_eq_of_lt hk', Nat.zero_add]
        · have := Nat.mul_le_mul_right h hjpos
          omega
      simp only [hj, ↓reduceIte]
      calc
        _ = ∑ _k ∈ Finset.range h, (∑ a ∈ Finset.range h, u ((j - 1) * h + a)) / h := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [(he k hk).1, (he k hk).2, ↓reduceIte]
        _ = _ := by simp [nsmul_eq_mul]
  simp_rw [hblock]
  have hshift (F : ℕ → ℝ) :
      (∑ j ∈ Finset.range n, if j = 0 then 0 else F (j - 1)) =
        ∑ j ∈ Finset.range (n - 1), F j := by
    cases n with
    | zero => simp
    | succ n => rw [Finset.sum_range_succ']; simp
  rw [hshift (fun j => (h : ℝ) * ((∑ k ∈ Finset.range h, u (j * h + k)) / h))]
  exact previous_block_energy u hu n h hh

lemma periodic_sum (w : ℕ → ℝ) (n h : ℕ) (hh : 0 < h) :
    (∑ t ∈ Finset.range (n * h), if t % h = 0 then w (t / h) else 0) =
      ∑ j ∈ Finset.range n, w j := by
  rw [← sum_blocks]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single 0]
  · simp [hh.ne']
  · intro k hk hk0
    have hk' := Finset.mem_range.mp hk
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod,
      Nat.zero_add, Nat.mod_eq_of_lt hk', hk0, ↓reduceIte]
  · intro hn
    exact False.elim (hn (Finset.mem_range.mpr hh))

lemma initial_segment_sum (T h : ℕ) (G : ℝ) :
    (∑ t ∈ Finset.range T, if t < h then G else 0) = (min T h : ℕ) * G := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases ht : T < h
    · simp only [ht, ↓reduceIte, min_eq_left ht.le, min_eq_left (by omega : T + 1 ≤ h),
        Nat.cast_add, Nat.cast_one]
      ring
    · simp only [ht, ↓reduceIte, add_zero, min_eq_right (by omega : h ≤ T),
        min_eq_right (by omega : h ≤ T + 1)]

lemma weighted_anchor_exposure (T h : ℕ) (u w : ℕ → ℝ) (G S a b : ℝ)
    (hu : ∀ t < T, 0 ≤ u t) (hG : 0 ≤ G) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hinit : ∀ t < T, t < h → u t = G)
    (hwinit : ∀ t < T, t < h → w t ≤ a)
    (hwregular : ∀ t < T, h ≤ t → w t ≤ b)
    (hregular : (∑ t ∈ Finset.range T, if t < h then 0 else u t) ≤ S) :
    (∑ t ∈ Finset.range T, w t * u t) ≤ a * h * G + b * S := by
  have hpoint (t : ℕ) (ht : t ∈ Finset.range T) :
      w t * u t ≤ a * (if t < h then G else 0) + b * (if t < h then 0 else u t) := by
    have ht' := Finset.mem_range.mp ht
    by_cases hth : t < h
    · simp only [hth, ↓reduceIte, mul_zero, add_zero, hinit t ht' hth]
      exact mul_le_mul_of_nonneg_right (hwinit t ht' hth) hG
    · simp only [hth, ↓reduceIte, mul_zero, zero_add]
      exact mul_le_mul_of_nonneg_right (hwregular t ht' (by omega)) (hu t ht')
  calc
    _ ≤ ∑ t ∈ Finset.range T,
        (a * (if t < h then G else 0) + b * (if t < h then 0 else u t)) :=
      Finset.sum_le_sum hpoint
    _ = a * ((min T h : ℕ) * G) + b *
        (∑ t ∈ Finset.range T, if t < h then 0 else u t) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, initial_segment_sum]
    _ ≤ a * ((h : ℝ) * G) + b * S := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ ha
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right T h) hG
      · exact mul_le_mul_of_nonneg_left hregular hb
    _ = _ := by ring

end OracleTemplate.MixedNoise
