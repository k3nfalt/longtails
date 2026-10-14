import LongTails.Algorithms.ConstantStepReshuffledGradient
import LongTails.Proofs.ReshuffledHarmonicWeights
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

open Finset

namespace OracleTemplate.ConstantStepReshuffledConvex

open LongTails.Setups.ConstantStepReshuffledSmoothConvex

lemma log_constant : Real.log (32770 : ℝ) < 11 := by
  have hm : Real.log (32770 : ℝ) < Real.log ((3 : ℝ) ^ 10) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at hm
  have h3 := Real.log_three_lt_d9
  norm_num at hm
  linarith

lemma horizon_log {n K : ℕ} (hn : 0 < n) (hK : 0 < K) {a : ℝ} (ha : 0 ≤ a)
    (hbound : (n * K : ℕ) ≤ 2 * (n : ℝ) + 32768 * (1 + Real.log n) * a *
      (1 + Real.log ((n : ℝ) + 2 + a))) :
    ReshuffledHarmonic.H (n * K) ≤ 12 * (1 + Real.log ((n : ℝ) + 2 + a)) := by
  let b : ℝ := n + 2 + a
  let l : ℝ := 1 + Real.log b
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb : 3 ≤ b := by dsimp [b]; linarith
  have hb0 : 0 < b := by linarith
  have hl : 1 ≤ l := by
    have hh := Real.log_nonneg (show 1 ≤ b by linarith)
    dsimp [l]
    linarith
  have hl0 : 0 < l := by linarith
  have hnlog : 1 + Real.log n ≤ l := by
    have hh := Real.log_le_log (Nat.cast_pos.mpr hn) (show (n : ℝ) ≤ b by dsimp [b]; linarith)
    dsimp [l]
    linarith
  have ha' : a ≤ b := by dsimp [b]; linarith
  have hn' : (n : ℝ) ≤ b := by dsimp [b]; linarith
  have hbig : (n * K : ℕ) ≤ 32770 * b * l ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hnlog (show 0 ≤ 32768 * a * l by positivity)
    have hba := mul_le_mul_of_nonneg_right ha' (show 0 ≤ 32768 * l ^ 2 by positivity)
    have hnl : 2 * (n : ℝ) ≤ 2 * b * l ^ 2 := by nlinarith [mul_nonneg hb0.le (sq_nonneg (l - 1))]
    change (n * K : ℕ) ≤ 2 * (n : ℝ) + 32768 * (1 + Real.log n) * a * l at hbound
    nlinarith
  have hT : (0 : ℝ) < (n * K : ℕ) := Nat.cast_pos.mpr (Nat.mul_pos hn hK)
  have hlog := Real.log_le_log hT hbig
  rw [Real.log_mul (by positivity : (32770 * b : ℝ) ≠ 0) (pow_ne_zero 2 hl0.ne'),
    Real.log_mul (by norm_num : (32770 : ℝ) ≠ 0) hb0.ne', Real.log_pow] at hlog
  have hll := Real.log_le_sub_one_of_pos hl0
  have hc := log_constant
  have hh := ReshuffledHarmonic.H_log (n * K)
  change ReshuffledHarmonic.H (n * K) ≤ 12 * l
  dsimp [l] at hl hlog hll ⊢
  nlinarith

lemma tuning {L σ D ε h l Hn HT T : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hh : 1 ≤ h) (hl : 1 ≤ l) (hHn : Hn ≤ h)
    (hHT0 : 0 ≤ HT) (hHT : HT ≤ 12 * l) (hT : 0 < T)
    (hcost : 32768 * h * l * (L * ε + σ ^ 2) * D ^ 2 / ε ^ 2 ≤ T) :
    let η := 1 / (12 * h * l * (536 * L + 132 * σ ^ 2 / ε))
    0 < η ∧ η * L * Hn * HT ≤ 1 / 536 ∧
      2 * D ^ 2 / (η * T) + 66 * η * Hn * HT * σ ^ 2 ≤ ε := by
  let η := 1 / (12 * h * l * (536 * L + 132 * σ ^ 2 / ε))
  have hh0 : 0 < h := by linarith
  have hl0 : 0 < l := by linarith
  have hden : 0 < 12 * h * l * (536 * L + 132 * σ ^ 2 / ε) := by positivity
  have hη : 0 < η := one_div_pos.mpr hden
  have hid : η * (12 * h * l * (536 * L + 132 * σ ^ 2 / ε)) = 1 := by
    dsimp [η]
    exact one_div_mul_cancel hden.ne'
  have hprod : Hn * HT ≤ h * (12 * l) := mul_le_mul hHn hHT hHT0 hh0.le
  have hcap0 : η * L * h * (12 * l) ≤ 1 / 536 := by
    have hnz : 0 ≤ η * 12 * h * l * (132 * σ ^ 2 / ε) := by positivity
    nlinarith
  have hcap := mul_le_mul_of_nonneg_left hprod (mul_nonneg hη.le hL.le)
  have hcap' : η * L * Hn * HT ≤ 1 / 536 := by nlinarith
  have hdenε : (536 * L + 132 * σ ^ 2 / ε) * ε = 536 * L * ε + 132 * σ ^ 2 := by
    field_simp [hε.ne']

  have hidε : η * 12 * h * l * (536 * L * ε + 132 * σ ^ 2) = ε := by
    calc
      _ = (η * (12 * h * l * (536 * L + 132 * σ ^ 2 / ε))) * ε := by rw [← hdenε]; ring
      _ = ε := by rw [hid, one_mul]
  have hnoise0 : 132 * η * h * (12 * l) * σ ^ 2 ≤ ε := by
    have hp : 0 ≤ η * 12 * h * l * (536 * L * ε) := by positivity
    nlinarith
  have hnoise1 := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 66 * η * σ ^ 2 by positivity)
  have hnoise : 66 * η * Hn * HT * σ ^ 2 ≤ ε / 2 := by nlinarith
  have hcost' : 32768 * h * l * (L * ε + σ ^ 2) * D ^ 2 ≤ T * ε ^ 2 :=
    (div_le_iff₀ (pow_pos hε 2)).mp hcost
  have hcostη := mul_le_mul_of_nonneg_left hcost' hη.le
  have hcoeff : 48 * (536 * L * ε + 132 * σ ^ 2) ≤ 32768 * (L * ε + σ ^ 2) := by
    nlinarith [sq_nonneg σ, mul_pos hL hε]
  have hcoeff' := mul_le_mul_of_nonneg_left hcoeff (show 0 ≤ η * h * l * D ^ 2 by positivity)
  have hinitid := congrArg (fun z : ℝ => 4 * D ^ 2 * z) hidε
  have hinitmul : (4 * D ^ 2) * ε ≤ (η * T * ε) * ε := by nlinarith
  have hinit : 4 * D ^ 2 ≤ η * T * ε := le_of_mul_le_mul_right hinitmul hε
  have hopt : 2 * D ^ 2 / (η * T) ≤ ε / 2 := by
    apply (div_le_iff₀ (mul_pos hη hT)).mpr
    nlinarith
  exact ⟨hη, hcap', by linarith⟩

lemma parameters (p : Params) (hp : spec.valid p) :
    0 < epochCount p ∧ 0 < stepSize p ∧
      stepSize p * p.Lmax * ReshuffledHarmonic.H p.n * ReshuffledHarmonic.H (p.n * epochCount p) ≤ 1 / 536 ∧
      2 * p.R ^ 2 / (stepSize p * (p.n * epochCount p : ℕ)) +
        66 * stepSize p * ReshuffledHarmonic.H p.n * ReshuffledHarmonic.H (p.n * epochCount p) * p.σ ^ 2 ≤ p.ε := by
  rcases hp with ⟨hLa, hLm, hR, hσ, hε⟩
  have hL : 0 < p.Lmax := hLa.trans_le hLm
  have hn := NeZero.pos p.n
  have hn0 : (0 : ℝ) < p.n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ p.n := by exact_mod_cast hn
  let a := scale p
  let h := 1 + Real.log p.n
  let l := 1 + Real.log ((p.n : ℝ) + 2 + a)
  have ha : 0 ≤ a := by dsimp [a, scale]; positivity
  have hh : 1 ≤ h := by have := Real.log_nonneg hn1; dsimp [h]; linarith
  have hl : 1 ≤ l := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (p.n : ℝ) + 2 + a by linarith)
    dsimp [l]
    linarith
  have hh0 : 0 < h := by linarith
  have hl0 : 0 < l := by linarith
  have harg : 0 ≤ 1 + 32768 * h * a * l / p.n := by positivity
  have hlo : 1 + 32768 * h * a * l / p.n ≤ (epochCount p : ℝ) := Nat.le_ceil _
  have hhi : (epochCount p : ℝ) < (1 + 32768 * h * a * l / p.n) + 1 :=
    Nat.ceil_lt_add_one harg
  have hK : 0 < epochCount p := by
    have hpositive : (0 : ℝ) < epochCount p := by
      have ha' : 0 ≤ 32768 * h * a * l / p.n := by positivity
      linarith
    exact Nat.cast_pos.mp hpositive
  have hdiv : (p.n : ℝ) * (32768 * h * a * l / p.n) = 32768 * h * a * l :=
    mul_div_cancel₀ _ hn0.ne'
  have hlo' := mul_le_mul_of_nonneg_left hlo hn0.le
  have hhi' := mul_lt_mul_of_pos_left hhi hn0
  have hcost0 : 32768 * h * a * l ≤ (p.n * epochCount p : ℕ) := by
    rw [Nat.cast_mul]
    nlinarith
  have hbound : (p.n * epochCount p : ℕ) ≤ 2 * (p.n : ℝ) + 32768 * h * a * l := by
    rw [Nat.cast_mul]
    nlinarith
  have hcost : 32768 * h * l * (p.Lmax * p.ε + p.σ ^ 2) * p.R ^ 2 / p.ε ^ 2 ≤
      (p.n * epochCount p : ℕ) := by
    calc
      _ = 32768 * h * a * l := by dsimp [a, scale]; ring
      _ ≤ _ := hcost0
  have hHT := horizon_log hn hK ha hbound
  have hHn := ReshuffledHarmonic.H_log p.n
  have htune := tuning hL hε hh hl hHn
    (ReshuffledHarmonic.H_nonneg (p.n * epochCount p)) hHT
    (Nat.cast_pos.mpr (Nat.mul_pos hn hK)) hcost
  exact ⟨hK, htune⟩

end OracleTemplate.ConstantStepReshuffledConvex
