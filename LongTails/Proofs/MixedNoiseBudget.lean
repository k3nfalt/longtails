import LongTails.Proofs.MixedNoiseSchedule
import LongTails.Proofs.MixedNoiseAllocation

namespace OracleTemplate.MixedNoise

lemma iteration_sizes (cfg : Config) (t : ℕ) :
    (cfg.iterationTasks t).map BatchTask.size = (cfg.levels t).map (fun l => max 1 (cfg.batch t l)) := by
  apply List.ext_getElem
  · simp [Config.iterationTasks]
  · intro i hi hi'
    simp [Config.iterationTasks]

lemma prefix_sizes (cfg : Config) (t : ℕ) :
    ((cfg.prefixTasks t).map BatchTask.size).sum =
      ∑ k ∈ Finset.range t, ((cfg.levels k).map (fun l => max 1 (cfg.batch k l))).sum := by
  induction t with
  | zero => simp [Config.prefixTasks]
  | succ t ih =>
    rw [prefixTasks_succ, List.map_append, List.sum_append, ih, iteration_sizes,
      Finset.sum_range_succ]

lemma calls_sum_levels (cfg : Config) :
    cfg.calls = 2 * ∑ t ∈ Finset.range cfg.T,
      ((cfg.levels t).map (fun l => max 1 (cfg.batch t l))).sum := by
  rw [Config.calls, Config.tasks, prefix_sizes]

lemma iteration_grid_bound (cfg : Config) (t : ℕ) :
    ((cfg.levels t).map (fun l => max 1 (cfg.batch t l))).sum ≤
      ∑ l ∈ Finset.range (cfg.m + 1), if t % 4 ^ l = 0 then max 1 (cfg.batch t l) else 0 := by
  rw [← List.sum_toFinset _ (levels_nodup cfg t)]
  by_cases ht : t = 0
  · subst t
    simpa [Config.levels] using
      (Finset.single_le_sum (f := fun l => max 1 (cfg.batch 0 l))
        (fun l hl => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_self cfg.m)))
  · simp [Config.levels, ht, List.toFinset_filter, List.toFinset_range, Finset.sum_filter]

lemma calls_grid_bound (cfg : Config) :
    cfg.calls ≤ 2 * ∑ l ∈ Finset.range (cfg.m + 1),
      ∑ t ∈ Finset.range cfg.T, if t % 4 ^ l = 0 then max 1 (cfg.batch t l) else 0 := by
  rw [calls_sum_levels]
  calc
    _ ≤ 2 * ∑ t ∈ Finset.range cfg.T,
        ∑ l ∈ Finset.range (cfg.m + 1), if t % 4 ^ l = 0 then max 1 (cfg.batch t l) else 0 :=
      Nat.mul_le_mul_left 2 (Finset.sum_le_sum (fun t ht => iteration_grid_bound cfg t))
    _ = _ := by rw [Finset.sum_comm]

lemma iterationTarget_bounds {L Δ ε : ℝ} (hL : 0 < L) (hΔ : 0 ≤ Δ) (hε : 0 < ε)
    (hlarge : ε ^ 2 < 2 * L * Δ) :
    16 * L * Δ / ε ^ 2 ≤ (iterationTarget L Δ ε : ℝ) ∧
      (iterationTarget L Δ ε : ℝ) ≤ 18 * L * Δ / ε ^ 2 ∧
      9 ≤ iterationTarget L Δ ε := by
  have hpos : 0 ≤ 16 * L * Δ / ε ^ 2 := by positivity
  have hlo := Nat.le_ceil (16 * L * Δ / ε ^ 2)
  have hhi := Nat.ceil_lt_add_one hpos
  have hD : (1 : ℝ) / 2 < L * Δ / ε ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hε)).mpr
    nlinarith
  change _ ≤ (⌈16 * L * Δ / ε ^ 2⌉₊ : ℝ) ∧
    (⌈16 * L * Δ / ε ^ 2⌉₊ : ℝ) ≤ _ ∧ 9 ≤ ⌈16 * L * Δ / ε ^ 2⌉₊
  refine ⟨hlo, ?_, ?_⟩
  · have he : 18 * L * Δ / ε ^ 2 = 16 * L * Δ / ε ^ 2 + 2 * (L * Δ / ε ^ 2) := by ring
    rw [he]
    linarith
  · have h8 : (8 : ℝ) < (⌈16 * L * Δ / ε ^ 2⌉₊ : ℝ) := by
      have he : 16 * L * Δ / ε ^ 2 = 16 * (L * Δ / ε ^ 2) := by ring
      apply lt_of_lt_of_le _ hlo
      rw [he]
      linarith
    exact_mod_cast h8

lemma rounded_multiple_bounds (N q : ℕ) (hq : 0 < q) (hqN : q ≤ N) :
    N ≤ q * ⌈(N : ℝ) / q⌉₊ ∧ q * ⌈(N : ℝ) / q⌉₊ ≤ 2 * N := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlo := Nat.le_ceil ((N : ℝ) / q)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ (N : ℝ) / q by positivity)
  have hlow := mul_le_mul_of_nonneg_left hlo hqR.le
  have hupp := mul_lt_mul_of_pos_left hhi hqR
  have he : (q : ℝ) * ((N : ℝ) / q) = N := by field_simp
  rw [he] at hlow
  rw [mul_add, he, mul_one] at hupp
  have hqNR : (q : ℝ) ≤ N := by exact_mod_cast hqN
  constructor
  · exact_mod_cast hlow
  · have h : (q : ℝ) * ⌈(N : ℝ) / q⌉₊ ≤ 2 * N := by linarith
    exact_mod_cast h

lemma lower_power_four (n : ℕ) (hn : 0 < n) :
    4 ^ Nat.log 4 n ≤ n ∧ n < 4 * 4 ^ Nat.log 4 n := by
  refine ⟨Nat.pow_log_le_self 4 hn.ne', ?_⟩
  simpa only [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 4) n

lemma hierarchy_power_le_target (L M σ Δ ε : ℝ)
    (hN : 0 < iterationTarget L Δ ε) :
    4 ^ hierarchyDepth L M σ Δ ε ≤ iterationTarget L Δ ε := by
  unfold hierarchyDepth
  split_ifs with hs hM
  · simp only [pow_zero]
    omega
  · exact Nat.pow_log_le_self 4 hN.ne'
  · have hm : 0 < min (iterationTarget L Δ ε) (max 1 ⌊2 * L * σ / (M * ε)⌋₊) :=
      lt_min hN (lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _))
    exact (Nat.pow_log_le_self 4 hm.ne').trans (min_le_left _ _)

lemma periodic_values (w : ℕ → ℝ) (n h : ℕ) (hh : 0 < h) :
    (∑ t ∈ Finset.range (n * h), if t % h = 0 then w t else 0) =
      ∑ j ∈ Finset.range n, w (j * h) := by
  calc
    _ = ∑ t ∈ Finset.range (n * h), if t % h = 0 then w ((t / h) * h) else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hm : t % h = 0
      · simp only [hm, ↓reduceIte, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hm)]
      · simp only [hm, ↓reduceIte]
    _ = _ := periodic_sum (fun j => w (j * h)) n h hh

lemma rounded_batch_lower (x : ℝ) : x ≤ ((max 1 ⌈x⌉₊ : ℕ) : ℝ) :=
  (Nat.le_ceil x).trans (by exact_mod_cast Nat.le_max_right 1 ⌈x⌉₊)

lemma rounded_batch_upper {x : ℝ} (hx : 0 ≤ x) : ((max 1 ⌈x⌉₊ : ℕ) : ℝ) ≤ x + 1 := by
  rw [Nat.cast_max, Nat.cast_one]
  exact max_le (by linarith) (Nat.ceil_lt_add_one hx).le

lemma periodic_prefix_bound (w : ℕ → ℝ) (n h k : ℕ) (hh : 0 < h)
    (b s : ℝ) (hs : 0 ≤ s)
    (hw : ∀ t < n * h, w t ≤ b + if t < k * h then s else 0) :
    (∑ t ∈ Finset.range (n * h), if t % h = 0 then w t else 0) ≤ n * b + k * s := by
  rw [periodic_values w n h hh]
  calc
    _ ≤ ∑ j ∈ Finset.range n, (b + if j < k then s else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j * h < n * h := Nat.mul_lt_mul_of_pos_right (Finset.mem_range.mp hj) hh
      simpa only [Nat.mul_lt_mul_right hh] using hw (j * h) hjn
    _ = n * b + (min n k : ℕ) * s := by
      rw [Finset.sum_add_distrib, initial_segment_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right (show ((min n k : ℕ) : ℝ) ≤ k by exact_mod_cast min_le_right n k) hs)

lemma sum_inv_four_pow_le (m : ℕ) : ∑ l ∈ Finset.range m, 1 / (4 : ℝ) ^ l ≤ 2 := by
  apply le_trans _ (sum_inv_two_pow_le m)
  apply Finset.sum_le_sum
  intro l hl
  apply one_div_le_one_div_of_le (by positivity)
  gcongr
  norm_num

lemma depth_le_power_four (m : ℕ) : m ≤ 4 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ]
    have hp : 0 < 4 ^ m := by positivity
    omega

lemma geometric_edge_cost {C r A T : ℝ} (m : ℕ)
    (hC : 1 ≤ C) (hr : 0 ≤ r) (hA : 0 ≤ A) (hT : (4 : ℝ) ^ m ≤ T) :
    (∑ l ∈ Finset.range m,
      (T / (4 : ℝ) ^ l * (1 + C * (r * 2 ^ l + A * 2 ^ m * ((2 : ℝ) ^ l) ^ 3)) +
        4 * (1 + C * r * 2 ^ m * (2 : ℝ) ^ l))) ≤
      6 * C * (1 + r) * T + C * A * (4 : ℝ) ^ m * T := by
  have hC0 : 0 ≤ C := by linarith
  have hT0 : 0 ≤ T := le_trans (by positivity) hT
  have hpow (l : ℕ) : (4 : ℝ) ^ l = ((2 : ℝ) ^ l) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have he (l : ℕ) :
      (T / (4 : ℝ) ^ l * (1 + C * (r * 2 ^ l + A * 2 ^ m * ((2 : ℝ) ^ l) ^ 3)) +
        4 * (1 + C * r * 2 ^ m * (2 : ℝ) ^ l)) =
      T * (1 / (4 : ℝ) ^ l) + C * r * T * (1 / (2 : ℝ) ^ l) +
        C * A * 2 ^ m * T * (2 : ℝ) ^ l + 4 + 4 * C * r * 2 ^ m * (2 : ℝ) ^ l := by
    rw [hpow]
    field_simp
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have h1 := mul_le_mul_of_nonneg_left (sum_inv_four_pow_le m) hT0
  have h2 := mul_le_mul_of_nonneg_left (sum_inv_two_pow_le m) (show 0 ≤ C * r * T by positivity)
  have hg : (∑ l ∈ Finset.range m, (2 : ℝ) ^ l) ≤ 2 ^ m := by rw [sum_two_pow]; linarith
  have h3 := mul_le_mul_of_nonneg_left hg (show 0 ≤ C * A * 2 ^ m * T by positivity)
  have h4 := mul_le_mul_of_nonneg_left hg (show 0 ≤ 4 * C * r * 2 ^ m by positivity)
  have hmq : (m : ℝ) ≤ (4 : ℝ) ^ m := by exact_mod_cast depth_le_power_four m
  have hm : (m : ℝ) ≤ T := hmq.trans hT
  have hrt := mul_le_mul_of_nonneg_left hT (show 0 ≤ C * r by positivity)
  have hct := mul_le_mul_of_nonneg_right hC hT0
  rw [hpow] at hT hrt ⊢
  nlinarith only [h1, h2, h3, h4, hm, hrt, hct]

lemma geometric_root_cost {C r Z T q : ℝ}
    (hC : 1 ≤ C) (hr : 0 ≤ r) (hq : 1 ≤ q) (hT : q ≤ T) :
    C * (r * q + Z) + 1 + T / q * (1 + C * (r + Z)) ≤
      2 * C * (1 + r) * T + C * Z * (1 + T / q) + 1 := by
  have hC0 : 0 ≤ C := by linarith
  have hq0 : 0 < q := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hdiv : T / q ≤ T := (div_le_iff₀ hq0).mpr (by nlinarith only [mul_nonneg hT0 (sub_nonneg.mpr hq)])
  have hrt := mul_le_mul_of_nonneg_left hT (show 0 ≤ C * r by positivity)
  have hrdiv := mul_le_mul_of_nonneg_left hdiv (show 0 ≤ C * r by positivity)
  have hct := mul_le_mul_of_nonneg_right hC hT0
  nlinarith only [hdiv, hrt, hrdiv, hct, hT0]

lemma geometric_total_cost {C r A Z T : ℝ} (m : ℕ)
    (hC : 1 ≤ C) (hr : 0 ≤ r) (hA : 0 ≤ A) (hT : (4 : ℝ) ^ m ≤ T) :
    2 * ((∑ l ∈ Finset.range m,
      (T / (4 : ℝ) ^ l * (1 + C * (r * 2 ^ l + A * 2 ^ m * ((2 : ℝ) ^ l) ^ 3)) +
        4 * (1 + C * r * 2 ^ m * (2 : ℝ) ^ l))) +
      (C * (r * (4 : ℝ) ^ m + Z) + 1 + T / (4 : ℝ) ^ m * (1 + C * (r + Z)))) ≤
    16 * C * (1 + r) * T + (if m = 0 then 0 else 2 * C * A * (4 : ℝ) ^ m * T) +
      2 * C * Z * (1 + T / (4 : ℝ) ^ m) + 2 := by
  have hq : (1 : ℝ) ≤ 4 ^ m := one_le_pow₀ (by norm_num)
  have hroot := geometric_root_cost (Z := Z) hC hr hq hT
  by_cases hm : m = 0
  · subst m
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, ↓reduceIte, add_zero, div_one] at hroot ⊢
    have hC0 : 0 ≤ C := by linarith
    have hT0 : 0 ≤ T := le_trans (by positivity) hT
    have hp : 0 ≤ C * (1 + r) * T := by positivity
    nlinarith only [hroot, hp]
  · rw [ite_eq_right_iff.mpr (fun h => (hm h).elim)]
    have he := geometric_edge_cost m hC hr hA hT
    linarith

lemma clamped_inverse_bound {N q : ℕ} {W : ℝ} (hN : 0 < N) (hq : 0 < q) (hW : 0 < W)
    (hclamp : min N (max 1 ⌊W⌋₊) < 4 * q) :
    1 / (q : ℝ) ≤ 4 / (N : ℝ) + 8 / W := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  rcases min_lt_iff.mp hclamp with hn | hf
  · have hn' : (N : ℝ) ≤ 4 * q := by exact_mod_cast hn.le
    have h : 1 / (q : ℝ) ≤ 4 / (N : ℝ) := by
      apply (div_le_div_iff₀ hqr hNr).mpr
      nlinarith only [hn']
    have hp : 0 ≤ 8 / W := by positivity
    linarith
  · have hf' : (⌊W⌋₊ : ℝ) < 4 * q := by
      exact_mod_cast (Nat.le_max_right 1 ⌊W⌋₊).trans_lt hf
    have hw := Nat.lt_floor_add_one W
    have h : 1 / (q : ℝ) ≤ 8 / W := by
      apply (div_le_div_iff₀ hqr hW).mpr
      nlinarith only [hf', hw, hq1]
    have hp : 0 ≤ 4 / (N : ℝ) := by positivity
    linarith

end OracleTemplate.MixedNoise
