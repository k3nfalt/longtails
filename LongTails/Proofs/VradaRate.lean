import LongTails.Proofs.VradaConvex
import Mathlib.Data.Nat.Log

namespace OracleTemplate.FiniteSum

open LongTails.Setups.FiniteSumSmoothAndConvex

noncomputable def vradaScale (m : ℕ) (L : ℝ) (k : ℕ) : ℝ :=
  2 * L * vradaWeight m L k / m

lemma vradaScale_pos {m : ℕ} {L : ℝ} (hL : 0 < L) (hm : 0 < m) (k : ℕ) :
    0 < vradaScale m L k := by
  have := vradaWeight_pos (m := m) hL k
  unfold vradaScale
  positivity

lemma vradaScale_zero {m : ℕ} {L : ℝ} (hL : 0 < L) :
    vradaScale m L 0 = 2 / m := by
  unfold vradaScale vradaWeight
  field_simp

lemma vradaScale_succ {m : ℕ} {L : ℝ} (hL : 0 < L) (hm : 0 < m) (k : ℕ) :
    vradaScale m L (k + 1) = vradaScale m L k + Real.sqrt (vradaScale m L k) := by
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have ha := vradaIncrement_pos hL hm k
  have hsq := vradaIncrement_sq (m := m) hL k
  have hb := vradaScale_pos hL hm k
  have hs := Real.sq_sqrt hb.le
  have he : 2 * L * vradaIncrement m L k / m = Real.sqrt (vradaScale m L k) := by
    have heq : (2 * L * vradaIncrement m L k / m) ^ 2 = vradaScale m L k := by
      unfold vradaScale
      field_simp
      nlinarith [hsq]
    have hn : 0 ≤ 2 * L * vradaIncrement m L k / m := by positivity
    nlinarith [Real.sqrt_nonneg (vradaScale m L k)]
  change 2 * L * (vradaWeight m L k + vradaIncrement m L k) / m = _
  rw [mul_add, add_div, he]
  rfl

lemma vradaScale_power {m : ℕ} {L : ℝ} (hL : 0 < L) (hm : 0 < m) (k : ℕ) :
    2 / (m : ℝ) ≤ vradaScale m L k ^ (2 ^ k) := by
  induction k with
  | zero => simp [vradaScale_zero hL]
  | succ k ih =>
    have hb := vradaScale_pos hL hm k
    have hs := Real.sq_sqrt hb.le
    have hstep : vradaScale m L k ≤ vradaScale m L (k + 1) ^ 2 := by
      rw [vradaScale_succ hL hm]
      nlinarith [Real.sqrt_nonneg (vradaScale m L k)]
    calc
      _ ≤ vradaScale m L k ^ (2 ^ k) := ih
      _ ≤ (vradaScale m L (k + 1) ^ 2) ^ (2 ^ k) :=
        pow_le_pow_left₀ hb.le hstep _
      _ = _ := by rw [← pow_mul, pow_succ]; congr 1; omega

lemma vradaScale_startup {m : ℕ} {L : ℝ} (hL : 0 < L) (hm : 0 < m) :
    1 / 2 ≤ vradaScale m L (Nat.clog 2 (Nat.clog 2 m)) := by
  let s := Nat.clog 2 (Nat.clog 2 m)
  have hpower := vradaScale_power hL hm s
  have hmreal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hnat : m ≤ 2 ^ (2 ^ s) := (Nat.le_pow_clog (by decide) m).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_pow_clog (by decide) (Nat.clog 2 m)))
  have hreal : (m : ℝ) ≤ (2 : ℝ) ^ (2 ^ s) := by exact_mod_cast hnat
  by_contra h
  have hlt : vradaScale m L s < 1 / 2 := lt_of_not_ge h
  have hle := pow_le_pow_left₀ (vradaScale_pos hL hm s).le hlt.le (2 ^ s)
  have hdiv : 2 / (m : ℝ) ≤ 1 / (2 : ℝ) ^ (2 ^ s) := by
    simpa only [div_pow, one_pow] using hpower.trans hle
  have hmul := (div_le_div_iff₀ hmreal (by positivity : (0 : ℝ) < 2 ^ (2 ^ s))).mp hdiv
  nlinarith [show (0 : ℝ) < 2 ^ (2 ^ s) by positivity]

lemma vradaScale_quadratic {m : ℕ} {L : ℝ} (hL : 0 < L) (hm : 0 < m)
    {s : ℕ} (hs : 1 / 2 ≤ vradaScale m L s) (t : ℕ) :
    ((t : ℝ) + 1) ^ 2 / 16 ≤ vradaScale m L (s + t) := by
  induction t with
  | zero => simp only [Nat.cast_zero, zero_add, one_pow, Nat.add_zero]; linarith
  | succ t ih =>
    have hb := vradaScale_pos hL hm (s + t)
    have hsq := Real.sq_sqrt hb.le
    have ht : 0 ≤ (t : ℝ) := Nat.cast_nonneg t
    have hsqrt : ((t : ℝ) + 1) / 4 ≤ Real.sqrt (vradaScale m L (s + t)) := by
      nlinarith [Real.sqrt_nonneg (vradaScale m L (s + t))]
    rw [show s + (t + 1) = (s + t) + 1 by omega, vradaScale_succ hL hm]
    push_cast
    nlinarith

lemma vradaWeight_tuning {m : ℕ} {L R ε : ℝ} (hL : 0 < L) (hm : 0 < m) (hε : 0 < ε) :
    let s := Nat.clog 2 (Nat.clog 2 m)
    let t := ⌈Real.sqrt (32 * L * R ^ 2 / ((m : ℝ) * ε))⌉₊
    R ^ 2 / vradaWeight m L (s + t) ≤ ε := by
  dsimp
  let s := Nat.clog 2 (Nat.clog 2 m)
  let t := ⌈Real.sqrt (32 * L * R ^ 2 / ((m : ℝ) * ε))⌉₊
  have hq := vradaScale_quadratic hL hm (vradaScale_startup hL hm) t
  have ht : Real.sqrt (32 * L * R ^ 2 / ((m : ℝ) * ε)) ≤ (t : ℝ) := Nat.le_ceil _
  have hs := Real.sq_sqrt (show 0 ≤ 32 * L * R ^ 2 / ((m : ℝ) * ε) by positivity)
  have hmreal : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hroot := Real.sqrt_nonneg (32 * L * R ^ 2 / ((m : ℝ) * ε))
  have htsq : 32 * L * R ^ 2 / ((m : ℝ) * ε) ≤ (t : ℝ) ^ 2 := by nlinarith
  have htsq' := (div_le_iff₀ (mul_pos hmreal hε)).mp htsq
  have hq' : (m : ℝ) * ((t : ℝ) + 1) ^ 2 ≤ 32 * L * vradaWeight m L (s + t) := by
    unfold vradaScale at hq
    have hh := (le_div_iff₀ hmreal).mp hq
    dsimp [s]
    nlinarith only [hh]
  apply (div_le_iff₀ (vradaWeight_pos hL _)).mpr
  have hmul := mul_le_mul_of_nonneg_right hq' hε.le
  nlinarith [mul_nonneg hmreal.le hε.le]

lemma vrada_coarse_accuracy {m : ℕ} {L R ε : ℝ} (hL : 0 < L) (hm : 0 < m)
    (hε : 0 < ε) (hcoarse : 2 * L ^ 2 * R ^ 4 ≤ (m : ℝ) * ε ^ 2) :
    R ^ 2 ≤ ε * vradaWeight m L 1 := by
  have ha := vradaIncrement_pos hL hm 0
  have hs := vradaIncrement_sq (m := m) hL 0
  have h0 : vradaWeight m L 0 = 1 / L := rfl
  rw [h0] at hs
  have he : 2 * L ^ 2 * vradaIncrement m L 0 ^ 2 = (m : ℝ) := by
    have hh := congrArg (fun x : ℝ => x * L) hs
    field_simp at hh
    nlinarith only [hh]
  have htarget : R ^ 2 ≤ ε * vradaIncrement m L 0 := by
    have he' := congrArg (fun x : ℝ => x * ε ^ 2) he
    have hp : 2 * L ^ 2 * (R ^ 2) ^ 2 ≤
        2 * L ^ 2 * (ε * vradaIncrement m L 0) ^ 2 := by
      nlinarith only [hcoarse, he']
    have hh : (R ^ 2) ^ 2 ≤ (ε * vradaIncrement m L 0) ^ 2 :=
      (mul_le_mul_iff_right₀ (show 0 < 2 * L ^ 2 by positivity)).mp hp
    nlinarith [mul_pos hε ha]
  change R ^ 2 ≤ ε * (vradaWeight m L 0 + vradaIncrement m L 0)
  have := vradaWeight_pos (m := m) hL 0
  nlinarith

end OracleTemplate.FiniteSum
