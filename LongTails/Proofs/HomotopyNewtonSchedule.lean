import LongTails.Algorithms.HomotopyNewtonAEP

open scoped RealInnerProductSpace

namespace LongTails.Proofs.HomotopyNewtonSchedule

open LongTails.Setups.UnconstrainedLipschitzSecondDerivativeMonotone
open LongTails.Algorithms.HomotopyNewtonAEP

noncomputable section

variable {p : Params}

structure Valid (p : Params) : Prop where
  L : 0 < p.L
  D : 0 < p.D
  H : 0 ≤ p.H₀
  ε : 0 < p.ε

lemma outerCount_pos : 0 < outerCount p := by unfold outerCount; omega

lemma scale_pos (hp : Valid p) : 0 < scale p := by
  have := hp.D; have := hp.ε
  have hN : (0 : ℝ) < outerCount p := by exact_mod_cast outerCount_pos
  unfold scale; positivity

lemma step_pos (hp : Valid p) (k : ℕ) : 0 < step p k := by
  unfold step; have := scale_pos hp; positivity

lemma cumulative_succ (k : ℕ) : cumulative p (k + 1) = cumulative p k + step p k := by
  unfold cumulative step; push_cast; ring

lemma cumulative_nonneg (hp : Valid p) (k : ℕ) : 0 ≤ cumulative p k := by
  unfold cumulative; have := scale_pos hp; positivity

lemma cumulative_succ_pos (hp : Valid p) (k : ℕ) : 0 < cumulative p (k + 1) := by
  rw [cumulative_succ]; have := cumulative_nonneg hp k; have := step_pos hp k; linarith

lemma ratio_cumulative (hp : Valid p) (k : ℕ) :
    cumulative p (k + 1) / step p k = (k + 2) / 2 := by
  unfold cumulative step
  have := scale_pos hp
  field_simp
  push_cast; ring

lemma stiff_nonneg (hp : Valid p) : 0 ≤ stiff p := by
  unfold stiff; have := hp.H; have := hp.L.le; positivity

lemma one_le_denom (hp : Valid p) (k : ℕ) : 1 ≤ 1 + step p k * stiff p := by
  have := mul_nonneg (step_pos hp k).le (stiff_nonneg hp); linarith

lemma guess_pos (hp : Valid p) (k : ℕ) {g : ℝ} (hg : 0 < g) (j : ℕ) : 0 < guess p k g j := by
  unfold guess; have := one_le_denom hp k; positivity

lemma guess_succ (k : ℕ) (g : ℝ) (j : ℕ) : guess p k g (j + 1) = 2 * guess p k g j := by
  unfold guess; rw [pow_succ]; ring

lemma ratio_pos (hp : Valid p) (k : ℕ) {g : ℝ} (hg : 0 < g) (j : ℕ) : 0 < ratio p k g j := by
  unfold ratio
  have h1 := guess_pos hp k hg j
  have h2 : 0 < Real.sqrt (step p k * p.L) := Real.sqrt_pos.mpr (mul_pos (step_pos hp k) hp.L)
  exact lt_min one_pos (by positivity)

lemma ratio_le_one (k : ℕ) (g : ℝ) (j : ℕ) : ratio p k g j ≤ 1 := min_le_left _ _

lemma ratio_mul (hp : Valid p) (k : ℕ) {g : ℝ} (hg : 0 < g) (j : ℕ) :
    ratio p k g j * (50 * Real.sqrt (step p k * p.L) * guess p k g j) ≤ 1 := by
  have h1 := guess_pos hp k hg j
  have h2 : 0 < Real.sqrt (step p k * p.L) := Real.sqrt_pos.mpr (mul_pos (step_pos hp k) hp.L)
  have hq : 0 < 50 * Real.sqrt (step p k * p.L) * guess p k g j := by positivity
  calc ratio p k g j * (50 * Real.sqrt (step p k * p.L) * guess p k g j)
      ≤ 1 / (50 * Real.sqrt (step p k * p.L) * guess p k g j) *
          (50 * Real.sqrt (step p k * p.L) * guess p k g j) := by
        gcongr; exact min_le_right _ _
    _ = 1 := by field_simp

lemma ratio_inv_le (hp : Valid p) (k : ℕ) {g : ℝ} (hg : 0 < g) (j : ℕ) :
    1 / ratio p k g j ≤ 1 + 50 * Real.sqrt (step p k * p.L) * guess p k g j := by
  have h1 := guess_pos hp k hg j
  have h2 : 0 < Real.sqrt (step p k * p.L) := Real.sqrt_pos.mpr (mul_pos (step_pos hp k) hp.L)
  have hq : 0 < 50 * Real.sqrt (step p k * p.L) * guess p k g j := by positivity
  unfold ratio
  rcases le_total 1 (1 / (50 * Real.sqrt (step p k * p.L) * guess p k g j)) with h | h
  · rw [min_eq_left h]; norm_num; positivity
  · rw [min_eq_right h, one_div_one_div]; linarith

lemma start_pos (hp : Valid p) (k : ℕ) {g : ℝ} (hg : 0 < g) (j : ℕ) : 0 < start p k g j := by
  unfold start
  have h1 := ratio_pos hp k hg j
  have h2 := step_pos hp k
  have h3 := one_le_denom hp k
  exact lt_min h2 (by positivity)

lemma start_le (k : ℕ) (g : ℝ) (j : ℕ) : start p k g j ≤ step p k := min_le_left _ _

lemma start_scaled (hp : Valid p) (k : ℕ) {g : ℝ} (hg : 0 < g) (j : ℕ) :
    start p k g j / step p k * g ≤ ratio p k g j * guess p k g j := by
  have ha := step_pos hp k
  have hd := one_le_denom hp k
  have : start p k g j ≤ step p k * ratio p k g j * 2 ^ j / (1 + step p k * stiff p) :=
    min_le_right _ _
  calc start p k g j / step p k * g
      ≤ step p k * ratio p k g j * 2 ^ j / (1 + step p k * stiff p) / step p k * g := by gcongr
    _ = ratio p k g j * guess p k g j := by unfold guess; field_simp

lemma stageParam_pos (hp : Valid p) (k : ℕ) {g : ℝ} (hg : 0 < g) (j i : ℕ) :
    0 < stageParam p k g j i := by
  unfold stageParam
  have := start_pos hp k hg j
  have := ratio_pos hp k hg j
  exact lt_min (step_pos hp k) (by positivity)

lemma stageParam_le (k : ℕ) (g : ℝ) (j i : ℕ) : stageParam p k g j i ≤ step p k :=
  min_le_left _ _

lemma stageParam_zero (k : ℕ) (g : ℝ) (j : ℕ) : stageParam p k g j 0 = start p k g j := by
  unfold stageParam; rw [pow_zero, mul_one]; exact min_eq_right (start_le k g j)

lemma stageParam_mono (hp : Valid p) (k : ℕ) {g : ℝ} (hg : 0 < g) (j i : ℕ) :
    stageParam p k g j i ≤ stageParam p k g j (i + 1) := by
  unfold stageParam
  have := start_pos hp k hg j
  have := ratio_pos hp k hg j
  apply min_le_min le_rfl
  rw [pow_succ]
  have hp0 : 0 ≤ (1 + ratio p k g j) ^ i := pow_nonneg (by linarith) i
  have : (1 + ratio p k g j) ^ i ≤ (1 + ratio p k g j) ^ i * (1 + ratio p k g j) :=
    le_mul_of_one_le_right hp0 (by linarith)
  exact mul_le_mul_of_nonneg_left this (by linarith)

lemma stageParam_succ_le (hp : Valid p) (k : ℕ) {g : ℝ} (hg : 0 < g) (j i : ℕ) :
    stageParam p k g j (i + 1) ≤ (1 + ratio p k g j) * stageParam p k g j i := by
  unfold stageParam
  have := start_pos hp k hg j
  have hr := ratio_pos hp k hg j
  have ha := step_pos hp k
  rw [mul_min_of_nonneg _ _ (by linarith), pow_succ]
  apply min_le_min
  · nlinarith
  · linarith [show start p k g j * ((1 + ratio p k g j) ^ i * (1 + ratio p k g j)) =
      (1 + ratio p k g j) * (start p k g j * (1 + ratio p k g j) ^ i) by ring]

lemma stageParam_last (hp : Valid p) (k : ℕ) {g : ℝ} (hg : 0 < g) (j : ℕ) :
    stageParam p k g j (stages p k g j) = step p k := by
  unfold stageParam
  apply min_eq_left
  have hs := start_pos hp k hg j
  have hr := ratio_pos hp k hg j
  have ha := step_pos hp k
  have hlog : 0 < Real.log (1 + ratio p k g j) := Real.log_pos (by linarith)
  have hceil : Real.log (step p k / start p k g j) / Real.log (1 + ratio p k g j) ≤
      (stages p k g j : ℝ) := Nat.le_ceil _
  have hmul : Real.log (step p k / start p k g j) ≤
      (stages p k g j : ℝ) * Real.log (1 + ratio p k g j) := by
    rwa [div_le_iff₀ hlog] at hceil
  have hpow : step p k / start p k g j ≤ (1 + ratio p k g j) ^ stages p k g j := by
    rw [← Real.exp_log (by positivity : 0 < step p k / start p k g j),
      ← Real.exp_log (by positivity : 0 < (1 + ratio p k g j) ^ stages p k g j),
      Real.log_pow]
    exact Real.exp_le_exp.mpr hmul
  rw [div_le_iff₀ hs] at hpow
  linarith

lemma log_one_add_ge {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x / 2 ≤ Real.log (1 + x) := by
  have h := Real.le_log_one_add_of_nonneg hx0
  have : x / 2 ≤ 2 * x / (x + 2) := by
    rw [div_le_div_iff₀ (by norm_num) (by linarith)]; nlinarith
  linarith

end

end LongTails.Proofs.HomotopyNewtonSchedule
