import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
import LongTails.Setups.MinimizerRegularHessian

namespace OracleTemplate.SpectralGradient

open LongTails.Setups.MinimizerRegularHessian

noncomputable def curvatureFactor (p : Params) : ℝ :=
  4 * ((Module.finrank ℝ p.E : ℝ) + 1) ^ 2 *
    (4 * p.L ^ 2 / p.μ ^ 2) ^ Module.finrank ℝ p.E * p.M / p.μ ^ 2

noncomputable def warmupCount (p : Params) : ℕ :=
  ⌈(2 * p.L / p.μ) * Real.log (2 + 2 * curvatureFactor p * p.L * p.R)⌉₊

noncomputable def windowCount (p : Params) : ℕ :=
  ⌈Real.log (1 + Real.log (1 + (p.L * p.R) ^ 2 / (p.μ * p.ε))) / Real.log 2⌉₊

lemma expanded_cost (p : Params) : warmupCount p + windowCount p * (2 * Module.finrank ℝ p.E) =
    ⌈(2 * p.L / p.μ) * Real.log (2 + 8 * ((Module.finrank ℝ p.E : ℝ) + 1) ^ 2 * (4 * p.L ^ 2 / p.μ ^ 2) ^ Module.finrank ℝ p.E * p.M * p.L * p.R / p.μ ^ 2)⌉₊ + 2 * Module.finrank ℝ p.E * ⌈Real.log (1 + Real.log (1 + p.L ^ 2 * p.R ^ 2 / (p.μ * p.ε))) / Real.log 2⌉₊ := by
  have he : 2 + 2 * curvatureFactor p * p.L * p.R =
      2 + 8 * ((Module.finrank ℝ p.E : ℝ) + 1) ^ 2 *
        (4 * p.L ^ 2 / p.μ ^ 2) ^ Module.finrank ℝ p.E * p.M * p.L * p.R / p.μ ^ 2 := by
    unfold curvatureFactor
    ring
  unfold warmupCount windowCount
  rw [he]
  simp only [mul_pow]
  ac_rfl

lemma scalar_warmup {a H : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hH : 1 ≤ H) :
    (1 - a) ^ ⌈Real.log (2 * H) / a⌉₊ ≤ 1 / (2 * H) := by
  have hH0 : 0 < H := by linarith
  have hw := Nat.le_ceil (Real.log (2 * H) / a)
  have he : 1 - a ≤ Real.exp (-a) := by linarith [Real.add_one_le_exp (-a)]
  calc
    _ ≤ Real.exp (-a) ^ ⌈Real.log (2 * H) / a⌉₊ :=
      pow_le_pow_left₀ (sub_nonneg.mpr ha1) he _
    _ = Real.exp ((⌈Real.log (2 * H) / a⌉₊ : ℝ) * (-a)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (-Real.log (2 * H)) := by
      apply Real.exp_le_exp.mpr
      have hh := (div_le_iff₀ ha).mp hw
      nlinarith only [hh]
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; simp only [one_div]

lemma quadratic_sequence_bound (v : ℕ → ℝ) {B H c : ℝ}
    (hB : 0 < B) (hH : 0 < H) (hc : 0 ≤ c) (hcH : c * B ≤ H)
    (hv : ∀ n, 0 ≤ v n) (h0 : v 0 ≤ B / (2 * H))
    (hstep : ∀ n, v (n + 1) ≤ c * (v n) ^ 2) (n : ℕ) :
    v n ≤ (B / H) * Real.exp (-(2 : ℝ) ^ n * Real.log 2) := by
  have hcoef : c * (B / H) ^ 2 ≤ B / H := by
    calc
      _ = (c * B / H) * (B / H) := by ring
      _ ≤ 1 * (B / H) := mul_le_mul_of_nonneg_right ((div_le_one hH).mpr hcH) (by positivity)
      _ = _ := one_mul _
  induction n with
  | zero =>
    simpa [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), div_eq_mul_inv,
      mul_assoc, mul_comm, mul_left_comm] using h0
  | succ n ih =>
    have he : Real.exp (-(2 : ℝ) ^ (n + 1) * Real.log 2) =
        Real.exp (-(2 : ℝ) ^ n * Real.log 2) ^ 2 := by
      rw [pow_succ, pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    calc
      _ ≤ c * (v n) ^ 2 := hstep n
      _ ≤ c * ((B / H) * Real.exp (-(2 : ℝ) ^ n * Real.log 2)) ^ 2 := by
        gcongr
        exact hv n
      _ = (c * (B / H) ^ 2) * Real.exp (-(2 : ℝ) ^ n * Real.log 2) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

lemma window_count {s : ℝ} (hs : 0 < s) :
    1 + Real.log (1 + s) ≤ (2 : ℝ) ^ ⌈Real.log (1 + Real.log (1 + s)) / Real.log 2⌉₊ := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 0 < Real.log (1 + s) := Real.log_pos (by linarith)
  have hm := Nat.le_ceil (Real.log (1 + Real.log (1 + s)) / Real.log 2)
  have he := Real.exp_le_exp.mpr ((div_le_iff₀ h2).mp hm)
  rw [Real.exp_log (by linarith : 0 < 1 + Real.log (1 + s)), Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  exact he

lemma terminal_accuracy {B H μ ε v : ℝ} (hB : 0 < B) (hH : 1 ≤ H)
    (hμ : 0 < μ) (hε : 0 < ε) (hv0 : 0 ≤ v)
    (hv : v ≤ (B / H) * Real.exp (-(2 : ℝ) ^
      ⌈Real.log (1 + Real.log (1 + B ^ 2 / (μ * ε))) / Real.log 2⌉₊ * Real.log 2)) :
    v ^ 2 / (2 * μ) ≤ ε := by
  let s := B ^ 2 / (μ * ε)
  let m := ⌈Real.log (1 + Real.log (1 + s)) / Real.log 2⌉₊
  have hs : 0 < s := by dsimp [s]; positivity
  have hH0 : 0 < H := by linarith
  have hm : 1 + Real.log (1 + s) ≤ (2 : ℝ) ^ m := window_count hs
  have hlog : 1 ≤ 2 * Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    linarith
  have hpower : 0 ≤ (2 : ℝ) ^ m := by positivity
  have hexp : Real.exp (-(2 : ℝ) ^ m * Real.log 2) ^ 2 ≤ 1 / (1 + s) := by
    rw [pow_two, ← Real.exp_add]
    calc
      _ ≤ Real.exp (-Real.log (1 + s)) := by
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_right hlog hpower
        nlinarith only [hm, hh]
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by linarith)]; simp only [one_div]
  have hv' : v ≤ B * Real.exp (-(2 : ℝ) ^ m * Real.log 2) := by
    apply hv.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    exact div_le_self hB.le hH
  have hv2 : v ^ 2 ≤ B ^ 2 / (1 + s) := by
    calc
      _ ≤ (B * Real.exp (-(2 : ℝ) ^ m * Real.log 2)) ^ 2 := pow_le_pow_left₀ hv0 hv' _
      _ = B ^ 2 * Real.exp (-(2 : ℝ) ^ m * Real.log 2) ^ 2 := mul_pow _ _ _
      _ ≤ B ^ 2 * (1 / (1 + s)) := mul_le_mul_of_nonneg_left hexp (sq_nonneg B)
      _ = _ := by ring
  have hid : μ * ε * s = B ^ 2 := by dsimp [s]; field_simp
  have hb : B ^ 2 / (1 + s) ≤ μ * ε := by
    apply (div_le_iff₀ (by linarith : 0 < 1 + s)).mpr
    nlinarith [mul_pos hμ hε]
  apply (div_le_iff₀ (by positivity : 0 < 2 * μ)).mpr
  nlinarith only [hv2.trans hb, mul_pos hμ hε]

end OracleTemplate.SpectralGradient
