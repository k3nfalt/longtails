import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import LongTails.Proofs.TwoSidedPLBudget

namespace OracleTemplate.NonsmoothHidden

lemma local_numerator_bound {G r M s L : ℝ} (hG : 0 < G) (hr : 0 < r)
    (hM : 0 ≤ M) (hs : 1 ≤ s) (hL : 1 ≤ L) (hreg : 64 * M * r ≤ 1) :
    (G * s / r) * r ^ 2 / 2 + 28 * (G * s / r) * M * r ^ 3 +
      (96 * (G * s / r) * M * r ^ 3 + 16 * G * M * r ^ 2) * L +
      s ^ 2 * G ^ 2 / (2 * (G * s / r)) ≤ 16 * G * r * s * L := by
  have hspos : 0 < s := by linarith
  let a := G * r * s
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have he1 : (G * s / r) * r ^ 2 / 2 + s ^ 2 * G ^ 2 / (2 * (G * s / r)) = a := by
    dsimp [a]
    field_simp
    ring
  have he2 : (G * s / r) * M * r ^ 3 = a * (M * r) := by
    dsimp [a]
    field_simp
  have hq : 0 ≤ M * r := mul_nonneg hM hr.le
  have hsmall := mul_le_mul_of_nonneg_left hreg ha
  have h16 : 16 * G * M * r ^ 2 ≤ a := by
    have hbase : 16 * M * r ≤ 1 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hbase (mul_nonneg hG.le hr.le)
    have h2 := mul_le_mul_of_nonneg_left hs (mul_nonneg hG.le hr.le)
    dsimp [a]
    nlinarith
  have he3 : (G * s / r) * r ^ 2 / 2 + 28 * (G * s / r) * M * r ^ 3 +
      (96 * (G * s / r) * M * r ^ 3 + 16 * G * M * r ^ 2) * L +
      s ^ 2 * G ^ 2 / (2 * (G * s / r)) =
      a + 28 * a * (M * r) + (96 * a * (M * r) + 16 * G * M * r ^ 2) * L := by
    linear_combination he1 + (28 + 96 * L) * he2
  rw [he3]
  have h28 : 28 * a * (M * r) ≤ a := by nlinarith [mul_nonneg ha hq]
  have h96 : 96 * a * (M * r) ≤ 2 * a := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right (add_le_add h96 h16) (by linarith : 0 ≤ L)
  have haL := mul_le_mul_of_nonneg_left hL ha
  have he4 : 16 * G * r * s * L = 16 * a * L := by dsimp [a]; ring
  rw [he4]
  nlinarith

lemma log_sixteen_ge_one : 1 ≤ Real.log (16 : ℝ) := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4)
  have he : (16 : ℝ) = 4 ^ 2 := by norm_num
  rw [he, Real.log_pow]
  norm_num at h ⊢
  linarith

lemma local_count_log_bound {v : ℝ} (hv : 0 ≤ v)
    (N : ℕ) (hN : (N : ℝ) ≤ 4194304 * (1 + v) ^ 2 * (Real.log (16 * (1 + v))) ^ 2 + 1) :
    1 + Real.log ((N : ℝ) + 1) ≤ 13 * Real.log (16 * (1 + v)) := by
  let Q := 16 * (1 + v)
  have hQ : 16 ≤ Q := by dsimp [Q]; linarith
  have hQpos : 0 < Q := by linarith
  have hl : 1 ≤ Real.log Q := log_sixteen_ge_one.trans
    (Real.log_le_log (by norm_num) hQ)
  have hlQ : Real.log Q ≤ Q := by linarith [Real.log_le_sub_one_of_pos hQpos]
  have hw : 0 ≤ 1 + v := by linarith
  have hwQ : 1 + v ≤ Q := by dsimp [Q]; linarith
  have hc : (4194304 : ℝ) ≤ Q ^ 6 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hQ 6
    norm_num at hh
    linarith
  have hbig : 4194304 * (1 + v) ^ 2 * (Real.log Q) ^ 2 ≤ Q ^ 10 := by
    calc
      _ ≤ Q ^ 6 * Q ^ 2 * Q ^ 2 := by gcongr
      _ = _ := by ring
  have hten : (2 : ℝ) ≤ Q ^ 10 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) hQ 10
    norm_num at hh
    linarith
  have htwo : (2 : ℝ) ≤ Q ^ 2 := by nlinarith
  have hb : (N : ℝ) + 1 ≤ Q ^ 12 := by
    have h12 : 2 * Q ^ 10 ≤ Q ^ 12 := by
      calc _ ≤ Q ^ 2 * Q ^ 10 := mul_le_mul_of_nonneg_right htwo (by positivity)
           _ = _ := by ring
    change (N : ℝ) ≤ 4194304 * (1 + v) ^ 2 * (Real.log Q) ^ 2 + 1 at hN
    linarith
  have hh := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) + 1) hb
  rw [Real.log_pow] at hh
  norm_num at hh
  change _ ≤ 13 * Real.log Q
  linarith

lemma local_accuracy_tuning {v : ℝ} (hv : 0 ≤ v) (N : ℕ)
    (hlo : 4194304 * (1 + v) ^ 2 * (Real.log (16 * (1 + v))) ^ 2 ≤ (N : ℝ))
    (hhi : (N : ℝ) ≤ 4194304 * (1 + v) ^ 2 * (Real.log (16 * (1 + v))) ^ 2 + 1) :
    1 ≤ N ∧ 16 * v * (1 + Real.log ((N : ℝ) + 1)) / Real.sqrt (N : ℝ) ≤ 1 / 2 := by
  have hQ : (16 : ℝ) ≤ 16 * (1 + v) := by linarith
  have hl : 1 ≤ Real.log (16 * (1 + v)) := log_sixteen_ge_one.trans
    (Real.log_le_log (by norm_num) hQ)
  have hs : 2048 * (1 + v) * Real.log (16 * (1 + v)) ≤ Real.sqrt (N : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith [hlo]
  have hsone : 1 ≤ Real.sqrt (N : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2048 * (1 + v))
    linarith
  have hN : 1 ≤ N := by
    have hh := Real.sq_sqrt (Nat.cast_nonneg N)
    have hn : (1 : ℝ) ≤ N := by nlinarith
    exact_mod_cast hn
  refine ⟨hN, ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < Real.sqrt (N : ℝ))).2
  have hlog := local_count_log_bound hv N hhi
  have hm := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 16 * v)
  have hvl : 0 ≤ v * Real.log (16 * (1 + v)) := mul_nonneg hv (by linarith)
  nlinarith

lemma epoch_accuracy_tuning {A d : ℝ} (hA : 1 ≤ A) (hd : 0 ≤ d) (K : ℕ)
    (hK : 2 * A * Real.log (2 + 2 * d) ≤ (K : ℝ)) :
    (1 - 1 / (2 * A)) ^ K * d ≤ 1 / 2 := by
  have hC : 1 ≤ 2 * A := by linarith
  have hCp : 0 < 2 * A := by linarith
  have hx : 0 < 2 + 2 * d := by positivity
  have hp := TwoSidedPL.pow_le_exp_window hC K
  have hh : Real.log (2 + 2 * d) ≤ (K : ℝ) / (2 * A) :=
    (le_div_iff₀ hCp).2 (by nlinarith [hK])
  have he := Real.exp_le_exp.mpr (neg_le_neg hh)
  rw [Real.exp_neg (Real.log (2 + 2 * d)), Real.exp_log hx] at he
  have hf : (2 + 2 * d)⁻¹ * d ≤ 1 / 2 := by
    rw [inv_mul_eq_div, div_le_iff₀ hx]
    linarith
  exact (mul_le_mul_of_nonneg_right (hp.trans he) hd).trans hf

lemma total_count_bound {A B v d : ℝ} (hA : 1 ≤ A) (hB : 0 ≤ B) (hv : 0 ≤ v)
    (hd : 0 ≤ d) (hav : A * v ^ 2 ≤ 4 * B) (hdAB : 2 * d ≤ A + B)
    (N K : ℕ)
    (hN : (N : ℝ) ≤ 4194304 * (1 + v) ^ 2 * (Real.log (16 * (1 + v))) ^ 2 + 1)
    (hK : (K : ℝ) ≤ 2 * A * Real.log (2 + 2 * d) + 1) :
    (K : ℝ) * N ≤ 10000000000 * (A + B) *
      (Real.log (10000000000 * (2 + A + B))) ^ 3 := by
  let U := 10000000000 * (2 + A + B)
  let L := Real.log U
  have hA0 : 0 ≤ A := by linarith
  have hU : 16 ≤ U := by dsimp [U]; linarith
  have hL : 1 ≤ L := log_sixteen_ge_one.trans (Real.log_le_log (by norm_num) hU)
  have hv2 : v ^ 2 ≤ 4 * B := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sq_nonneg v)]
  have hvB : v ≤ 1 + 4 * B := by nlinarith [sq_nonneg (v - 1)]
  have hQ : 16 * (1 + v) ≤ U := by dsimp [U]; linarith
  have hlQ : 0 ≤ Real.log (16 * (1 + v)) := Real.log_nonneg (by linarith)
  have hlQL : Real.log (16 * (1 + v)) ≤ L := Real.log_le_log (by positivity) hQ
  have harg : 2 + 2 * d ≤ U := by dsimp [U]; linarith
  have hlog : Real.log (2 + 2 * d) ≤ L := Real.log_le_log (by positivity) harg
  have hAL : 1 ≤ A * L := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hL)]
  have hKb : (K : ℝ) ≤ 4 * A * L := by
    have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * A)
    linarith
  have hNs : 4194304 * (1 + v) ^ 2 * (Real.log (16 * (1 + v))) ^ 2 ≤
      4194304 * (1 + v) ^ 2 * L ^ 2 := by gcongr
  have hunit : 1 ≤ (1 + v) ^ 2 * L ^ 2 := by
    have hh : 1 ≤ (1 + v) ^ 2 := by nlinarith
    have hll : 1 ≤ L ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr hll)]
  have hNb : (N : ℝ) ≤ 4194305 * (1 + v) ^ 2 * L ^ 2 := by nlinarith
  have haw : A * (1 + v) ^ 2 ≤ 8 * (A + B) := by
    have hh := mul_nonneg hA0 (sq_nonneg (v - 1))
    nlinarith
  have hL0 : 0 ≤ L := by linarith
  calc
    _ ≤ (4 * A * L) * (4194305 * (1 + v) ^ 2 * L ^ 2) :=
      mul_le_mul hKb hNb (Nat.cast_nonneg N) (by positivity)
    _ = 16777220 * (A * (1 + v) ^ 2) * L ^ 3 := by ring
    _ ≤ 16777220 * (8 * (A + B)) * L ^ 3 := by gcongr
    _ ≤ 10000000000 * (A + B) * L ^ 3 := by nlinarith [mul_nonneg (by linarith : 0 ≤ A + B) (pow_nonneg hL0 3)]

end OracleTemplate.NonsmoothHidden
