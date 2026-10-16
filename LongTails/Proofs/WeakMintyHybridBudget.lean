import LongTails.Algorithms.WeakMintyHybrid

namespace OracleTemplate.WeakMintyHybrid

lemma innerCount_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) : 0 < innerCount δ := by
  apply Nat.ceil_pos.mpr
  apply mul_pos (div_pos (by norm_num) hδ)
  apply Real.log_pos
  rw [lt_div_iff₀ (sq_pos_of_pos hδ)]
  nlinarith

lemma innerCount_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (innerCount δ : ℝ) + 2 ≤ 46 * Real.log (2 / δ) / δ := by
  have hlogδ : Real.log δ ≤ 0 := Real.log_nonpos hδ.le hδ1
  have hlog2 : 1 / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlg : Real.log (2 / δ) = Real.log 2 - Real.log δ :=
    Real.log_div (by norm_num) hδ.ne'
  have hbig : Real.log (1024 / δ ^ 2) = 10 * Real.log 2 - 2 * Real.log δ := by
    rw [Real.log_div (by norm_num) (pow_ne_zero _ hδ.ne'), Real.log_pow]
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]
    norm_num
  have hpos : 0 ≤ (4 / δ) * Real.log (1024 / δ ^ 2) := by
    rw [hbig]
    exact mul_nonneg (by positivity) (by linarith)
  have hceil : (innerCount δ : ℝ) < (4 / δ) * Real.log (1024 / δ ^ 2) + 1 :=
    Nat.ceil_lt_add_one hpos
  have hc := mul_lt_mul_of_pos_left hceil hδ
  have he : δ * ((4 / δ) * Real.log (1024 / δ ^ 2) + 1) =
      4 * Real.log (1024 / δ ^ 2) + δ := by field_simp
  rw [he, hbig] at hc
  rw [le_div_iff₀ hδ, hlg]
  nlinarith

lemma total_budget {δ Q : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hQ : 0 ≤ Q) :
    (⌈16384 * Q / δ ^ 4⌉₊ + 1) * (innerCount δ + 2) ≤
      ⌈1048576 * (1 + Q) * Real.log (2 / δ) / δ ^ 5⌉₊ := by
  have hlog : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by
    rw [le_div_iff₀ hδ]
    linarith)
  have hN : ((⌈16384 * Q / δ ^ 4⌉₊ + 1 : ℕ) : ℝ) ≤ 16384 * Q / δ ^ 4 + 2 := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 16384 * Q / δ ^ 4 by positivity)
    push_cast
    linarith
  have hK : ((innerCount δ + 2 : ℕ) : ℝ) ≤ 46 * Real.log (2 / δ) / δ := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using innerCount_bound hδ hδ1
  have hp := mul_le_mul hN hK (by positivity)
    (show 0 ≤ 16384 * Q / δ ^ 4 + 2 by positivity)
  have heq : (16384 * Q / δ ^ 4 + 2) * (46 * Real.log (2 / δ) / δ) =
      (46 * (16384 * Q + 2 * δ ^ 4)) * Real.log (2 / δ) / δ ^ 5 := by
    field_simp
  rw [heq] at hp
  have hδ4 : δ ^ 4 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hcoef : 46 * (16384 * Q + 2 * δ ^ 4) ≤ 1048576 * (1 + Q) := by nlinarith
  have hbound := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hlog)
    (pow_nonneg hδ.le 5)
  have hreal := (hp.trans hbound).trans (Nat.le_ceil _)
  exact_mod_cast hreal

lemma iteration_sufficient {δ M R ε r : ℝ} (hδ : 0 < δ) (hM : 0 < M)
    (hε : 0 < ε) (hr : 0 ≤ r) (hR : r ≤ R) :
    r ^ 2 < (⌈16384 * (M * R ^ 2 / ε) / δ ^ 4⌉₊ + 1 : ℕ) *
      (δ ^ 4 * ε / (16384 * M)) := by
  have hN : 16384 * (M * R ^ 2 / ε) / δ ^ 4 <
      ((⌈16384 * (M * R ^ 2 / ε) / δ ^ 4⌉₊ + 1 : ℕ) : ℝ) := by
    have hh := Nat.le_ceil (16384 * (M * R ^ 2 / ε) / δ ^ 4)
    push_cast
    linarith
  have hh := mul_lt_mul_of_pos_right hN (by positivity : 0 < δ ^ 4 * ε / (16384 * M))
  have he : (16384 * (M * R ^ 2 / ε) / δ ^ 4) * (δ ^ 4 * ε / (16384 * M)) = R ^ 2 := by
    field_simp
  rw [he] at hh
  exact (pow_le_pow_left₀ hr hR 2).trans_lt hh

end OracleTemplate.WeakMintyHybrid
