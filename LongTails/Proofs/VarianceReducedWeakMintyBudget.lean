import LongTails.Proofs.VarianceReducedWeakMintyTuning

namespace OracleTemplate.VarianceReducedWeakMinty

lemma batch_cost_algebra {N r z B t q : ℝ}
    (hN : 0 ≤ N) (hr : 0 ≤ r) (hz : 0 ≤ z) (hB : 0 ≤ B) (ht : 1 / 2 ≤ t)
    (hq : 0 < q) (h1 : N / q ≤ z) (h2 : q * r ≤ 2 * r + z)
    (h3 : q ^ 2 * r ≤ 8 * r + 2 * N) :
    (N + 2147483648 * t * q ^ 2 * r) * (1 + 128 * B / q) ≤
      4398046511104 * t * (N + r + (z + r) * B) := by
  have ht0 : 0 ≤ t := by linarith
  have he : (N + 2147483648 * t * q ^ 2 * r) * (1 + 128 * B / q) =
      N + 128 * B * (N / q) + 2147483648 * t * (q ^ 2 * r) +
        274877906944 * t * B * (q * r) := by field_simp; ring
  rw [he]
  have ha := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 128 * B by positivity)
  have hb := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 2147483648 * t by positivity)
  have hc := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 274877906944 * t * B by positivity)
  have hn := mul_le_mul_of_nonneg_right ht hN
  have hbz := mul_le_mul_of_nonneg_right ht (mul_nonneg hB hz)
  have htr := mul_nonneg ht0 hr
  have htrb := mul_nonneg htr hB
  have htn := mul_nonneg ht0 hN
  have htzb := mul_nonneg (mul_nonneg ht0 hz) hB
  nlinarith only [ha, hb, hc, hn, hbz, htr, htrb, htn, htzb]

lemma exact_cost_algebra {N B g : ℝ} (hN : 0 ≤ N) (hB : 0 ≤ B) (hg : 1 / 2 ≤ g) :
    (4096 * N * g + N) * (1 + 64 * B) ≤
      4398046511104 * g * N * (1 + B) := by
  have hn := mul_le_mul_of_nonneg_right hg hN
  have hnb := mul_le_mul_of_nonneg_right hn hB
  have hgn := mul_nonneg (show 0 ≤ g by linarith) hN
  have hgnb := mul_nonneg hgn hB
  nlinarith only [hn, hnb, hgn, hgnb]

lemma epoch_scaling {N r : ℝ} (hN : 0 ≤ N) (hr : 0 < r) :
    let q := max 2 ⌈Real.sqrt N / r⌉₊
    N / (q : ℝ) ≤ Real.sqrt N * r ∧
      (q : ℝ) * r ^ 2 ≤ 2 * r ^ 2 + Real.sqrt N * r ∧
      (q : ℝ) ^ 2 * r ^ 2 ≤ 8 * r ^ 2 + 2 * N := by
  dsimp only
  let q := max 2 ⌈Real.sqrt N / r⌉₊
  have hq : (0 : ℝ) < q := by dsimp [q]; positivity
  have hlow : Real.sqrt N / r ≤ q :=
    (Nat.le_ceil _).trans (by exact_mod_cast Nat.le_max_right 2 ⌈Real.sqrt N / r⌉₊)
  have hhi : (q : ℝ) ≤ 2 + Real.sqrt N / r := by
    dsimp [q]
    rw [Nat.cast_max]
    apply max_le
    · have hh : 0 ≤ Real.sqrt N / r := by positivity
      linarith
    · have hh := Nat.ceil_lt_add_one (show 0 ≤ Real.sqrt N / r by positivity)
      linarith
  have hlo' := (div_le_iff₀ hr).mp hlow
  have hhi' := mul_le_mul_of_nonneg_right hhi hr.le
  have hcan : (2 + Real.sqrt N / r) * r = 2 * r + Real.sqrt N := by field_simp
  rw [hcan] at hhi'
  have hs := Real.sq_sqrt hN
  have hs0 := Real.sqrt_nonneg N
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ hq]
    have hh := mul_le_mul_of_nonneg_left hlo' hs0
    nlinarith only [hh, hs]
  · have hh := mul_le_mul_of_nonneg_right hhi' hr.le
    nlinarith only [hh]
  · have hh := mul_self_le_mul_self (by positivity : 0 ≤ (q : ℝ) * r) hhi'
    nlinarith [sq_nonneg (2 * r - Real.sqrt N)]

lemma exact_query_cost {n b J M : ℕ} {g B : ℝ} (hn : 0 < n)
    (hg : 1 / 2 ≤ g) (hB : 0 ≤ B) (hJ : (J : ℝ) + 1 ≤ 1024 * g)
    (hM : (M : ℝ) ≤ 1 + 64 * B) :
    (((stepCost true n b J * 2 + n) * M : ℕ) : ℝ) ≤
      4398046511104 * g * n * (1 + B) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hstep : (stepCost true n b J : ℝ) ≤ 2048 * n * g := by
    simp only [stepCost, estimatorCost, ↓reduceIte, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    have hh := mul_le_mul_of_nonneg_left hJ (show 0 ≤ 2 * (n : ℝ) by positivity)
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) - 1 by linarith) hJ0]
  have hh := mul_le_mul (show (stepCost true n b J : ℝ) * 2 + n ≤ 4096 * n * g + n by linarith)
    hM (Nat.cast_nonneg M) (by positivity : 0 ≤ 4096 * (n : ℝ) * g + n)
  push_cast
  exact hh.trans (exact_cost_algebra (Nat.cast_nonneg n) hB hg)

lemma batch_query_cost {n b J q M : ℕ} {g d r B : ℝ} (hn : 0 < n) (hb : 0 < b)
    (hq : 0 < q) (hg : 1 / 2 ≤ g) (hd : 1 ≤ d) (hr : 0 < r) (hB : 0 ≤ B)
    (hbatch : (b : ℝ) ≤ 524289 * q * r ^ 2 * d)
    (hJ : (J : ℝ) + 1 ≤ 1024 * g) (hM : (M : ℝ) ≤ 1 + 128 * B / q)
    (h1 : (n : ℝ) / q ≤ Real.sqrt n * r)
    (h2 : (q : ℝ) * r ^ 2 ≤ 2 * r ^ 2 + Real.sqrt n * r)
    (h3 : (q : ℝ) ^ 2 * r ^ 2 ≤ 8 * r ^ 2 + 2 * n) :
    (((stepCost false n b J * q + n) * M : ℕ) : ℝ) ≤
      4398046511104 * (g * d) * (n + r ^ 2 + (Real.sqrt n * r + r ^ 2) * B) := by
  have hg0 : 0 ≤ g := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hstep : (stepCost false n b J : ℝ) ≤ 2147483648 * g * d * q * r ^ 2 := by
    calc
      _ ≤ 3 * (b : ℝ) * ((J : ℝ) + 1) := by
        simp only [stepCost, estimatorCost, Bool.false_eq_true, ↓reduceIte, Nat.cast_add,
          Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
        nlinarith [mul_nonneg (show 0 ≤ (b : ℝ) - 1 by linarith) (Nat.cast_nonneg J)]
      _ ≤ 3 * (524289 * q * r ^ 2 * d) * (1024 * g) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hg0 hd0) hq'.le) (sq_nonneg r)]
  have hbase : (stepCost false n b J : ℝ) * q + n ≤
      n + 2147483648 * (g * d) * (q : ℝ) ^ 2 * r ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hstep hq'.le
    nlinarith only [hh]
  have hh := mul_le_mul hbase hM (Nat.cast_nonneg M) (by positivity)
  have ht : 1 / 2 ≤ g * d := by nlinarith
  push_cast
  exact hh.trans (batch_cost_algebra (Nat.cast_nonneg n) (sq_nonneg r)
    (mul_nonneg (Real.sqrt_nonneg _) hr.le) hB ht hq' h1 h2 h3)

open LongTails.Setups.FiniteSumWeakMintyInclusion

lemma ceil_epoch_bound {x : ℝ} (hx : 0 ≤ x) : (max 1 ⌈x⌉₊ : ℕ) ≤ x + 1 := by
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · linarith
  · exact (Nat.ceil_lt_add_one hx).le

lemma log_margin_lower {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 / 2 ≤ Real.log (2 / δ) / δ := by
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hlog2 : 1 / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  rw [le_div_iff₀ hδ, Real.log_div (by norm_num) hδ.ne']
  linarith

lemma exact_total_cost (p : Params) (hp : spec.valid p) (he : useExact p = true) :
    (((stepCost (useExact p) p.n (batchSize p) (innerLength p) * epochLength p + p.n) *
      epochCount p : ℕ) : ℝ) ≤
        4398046511104 * (Real.log (2 / margin p) / margin p) * exactWork p := by
  obtain ⟨hδ, hδ1⟩ := valid_margin p hp
  have hq : epochLength p = 2 := by simp only [epochLength, he, ↓reduceIte]
  have hM : (epochCount p : ℝ) ≤ 1 + 64 * (p.L ^ 2 * p.R ^ 2 / (margin p ^ 2 * p.ε ^ 2)) := by
    have hh := ceil_epoch_bound (show 0 ≤ 128 * p.L ^ 2 * p.R ^ 2 /
      (margin p ^ 2 * epochLength p * p.ε ^ 2) by positivity)
    change (epochCount p : ℝ) ≤ _ at hh
    rw [hq] at hh
    convert hh using 1
    push_cast
    ring
  rw [he, hq]
  have hh := exact_query_cost (b := batchSize p) hp.1 (log_margin_lower hδ hδ1)
    (show 0 ≤ p.L ^ 2 * p.R ^ 2 / (margin p ^ 2 * p.ε ^ 2) by positivity)
    (show (innerLength p : ℝ) + 1 ≤ 1024 * (Real.log (2 / margin p) / margin p) by
      simpa only [innerLength, mul_div_assoc] using inner_length_bound hδ hδ1) hM
  simpa only [exactWork, mul_assoc] using hh

lemma batch_total_cost (p : Params) (hp : spec.valid p) (he : useExact p = false) :
    (((stepCost (useExact p) p.n (batchSize p) (innerLength p) * epochLength p + p.n) *
      epochCount p : ℕ) : ℝ) ≤
        4398046511104 * (Real.log (2 / margin p) / margin p) * batchWork p := by
  obtain ⟨hδ, hδ1⟩ := valid_margin p hp
  have hL := hp.2.1
  have hΛ : 0 < p.Λ := lt_of_lt_of_le hL hp.2.2.1
  let r := p.Λ / p.L
  let d := (margin p ^ 3)⁻¹
  let B := p.L ^ 2 * p.R ^ 2 / (margin p ^ 2 * p.ε ^ 2)
  let g := Real.log (2 / margin p) / margin p
  have hr : 0 < r := div_pos hΛ hL
  have hr1 : 1 ≤ r := by dsimp [r]; rw [le_div_iff₀ hL]; simpa using hp.2.2.1
  have hd : 1 ≤ d := by
    dsimp [d]
    rw [← one_div, le_div_iff₀ (pow_pos hδ 3)]
    simpa using pow_le_one₀ hδ.le hδ1 (n := 3)
  have hq : epochLength p = max 2 ⌈Real.sqrt p.n / r⌉₊ := by
    simp only [epochLength, he, Bool.false_eq_true, ↓reduceIte, r, div_div_eq_mul_div]
  have hqpos : 0 < epochLength p := NeZero.pos _
  have hq' : (0 : ℝ) < epochLength p := by exact_mod_cast hqpos
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hg : 1 / 2 ≤ g := log_margin_lower hδ hδ1
  have hbr : batchSize p = ⌈524288 * epochLength p * r ^ 2 * d⌉₊ := by
    simp only [batchSize, he, Bool.false_eq_true, ↓reduceIte]
    congr 1
    dsimp [r, d]
    ring
  have hbatch : (batchSize p : ℝ) ≤ 524289 * epochLength p * r ^ 2 * d := by
    rw [hbr]
    have hbase : 1 ≤ (epochLength p : ℝ) * r ^ 2 * d := by
      have hq1 : (1 : ℝ) ≤ epochLength p := by exact_mod_cast hqpos
      have hr2 : 1 ≤ r ^ 2 := by nlinarith
      have hh := mul_le_mul hq1 hr2 (by norm_num : (0 : ℝ) ≤ 1) hq'.le
      have hh' := mul_le_mul hh hd (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
      norm_num at hh'
      exact hh'
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 524288 * epochLength p * r ^ 2 * d by positivity)
    nlinarith
  have hM : (epochCount p : ℝ) ≤ 1 + 128 * B / epochLength p := by
    have hh := ceil_epoch_bound (show 0 ≤ 128 * p.L ^ 2 * p.R ^ 2 /
      (margin p ^ 2 * epochLength p * p.ε ^ 2) by positivity)
    change (epochCount p : ℝ) ≤ _ at hh
    convert hh using 1
    dsimp [B]
    ring
  obtain ⟨h1, h2, h3⟩ := epoch_scaling (show (0 : ℝ) ≤ p.n by positivity) hr
  rw [← hq] at h1 h2 h3
  have hh := batch_query_cost hp.1 (batch_size_pos p hp) hqpos hg hd hr hB hbatch
    (show (innerLength p : ℝ) + 1 ≤ 1024 * g by
      simpa only [innerLength, g, mul_div_assoc] using inner_length_bound hδ hδ1) hM h1 h2 h3
  rw [he]
  refine hh.trans_eq ?_
  dsimp [g, d, r, B, batchWork]
  field_simp

lemma total_cost (p : Params) (hp : spec.valid p) :
    (stepCost (useExact p) p.n (batchSize p) (innerLength p) * epochLength p + p.n) * epochCount p ≤
      ⌈4398046511104 * (Real.log (2 / margin p) / margin p) * min (exactWork p) (batchWork p)⌉₊ := by
  have hh : (((stepCost (useExact p) p.n (batchSize p) (innerLength p) * epochLength p + p.n) *
      epochCount p : ℕ) : ℝ) ≤
        4398046511104 * (Real.log (2 / margin p) / margin p) * min (exactWork p) (batchWork p) := by
    by_cases he : exactWork p ≤ batchWork p
    · rw [min_eq_left he]
      exact exact_total_cost p hp (by simp [useExact, he])
    · rw [min_eq_right (le_of_not_ge he)]
      exact batch_total_cost p hp (by simp [useExact, he])
  exact_mod_cast hh.trans (Nat.le_ceil _)

end OracleTemplate.VarianceReducedWeakMinty
