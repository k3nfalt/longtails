import LongTails.Algorithms.GapStrongGrowthAccelerated
import Mathlib.Tactic

namespace OracleTemplate.GapStrongGrowth

open LongTails.Setups.GapSmoothStrongGrowth

lemma confidence_ge_one (p : Params) : 1 ≤ confidence p := by
  unfold confidence
  linarith [abs_nonneg (Real.log p.δ)]

lemma confidence_pos (p : Params) : 0 < confidence p := lt_of_lt_of_le zero_lt_one (confidence_ge_one p)

noncomputable def geometryScale (p : Params) (A : ℝ) : ℝ :=
  1 + p.R * Real.sqrt p.H1 + Real.sqrt (p.H0 * A)

lemma geometry_scale_square (p : Params) (hR : 0 ≤ p.R) (h0 : 0 ≤ p.H0)
    (h1 : 0 ≤ p.H1) {A : ℝ} (hA : 0 ≤ A) :
    p.H0 * A + p.H1 * p.R ^ 2 ≤ geometryScale p A ^ 2 := by
  have hs0 := Real.sq_sqrt (mul_nonneg h0 hA)
  have hs1 : (p.R * Real.sqrt p.H1) ^ 2 = p.H1 * p.R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt h1]
    ring
  have hR1 := mul_nonneg hR (Real.sqrt_nonneg p.H1)
  have h0A := Real.sqrt_nonneg (p.H0 * A)
  unfold geometryScale
  nlinarith [mul_nonneg hR1 h0A]

lemma denominator_ge_one (p : Params) (hR : 0 ≤ p.R) (A : ℝ) :
    1 ≤ 1 + p.R * Real.sqrt p.H1 + Real.sqrt (p.H0 * A) := by
  linarith [mul_nonneg hR (Real.sqrt_nonneg p.H1), Real.sqrt_nonneg (p.H0 * A)]

lemma increment_scale (p : Params) (hR : 0 ≤ p.R) (A : ℝ) :
    32768 * confidence p * increment p A * geometryScale p A = A := by
  have hb := denominator_ge_one p hR A
  have hq := confidence_pos p
  unfold increment geometryScale
  field_simp

lemma geometry_scale_radius (p : Params) (A : ℝ) :
    p.R * Real.sqrt p.H1 ≤ geometryScale p A := by
  unfold geometryScale
  linarith [Real.sqrt_nonneg (p.H0 * A)]

lemma increment_pos (p : Params) (hR : 0 ≤ p.R) {A : ℝ} (hA : 0 < A) :
    0 < increment p A := by
  have hb := denominator_ge_one p hR A
  have hq := confidence_pos p
  unfold increment
  positivity

lemma increment_small (p : Params) (hR : 0 ≤ p.R) {A : ℝ} (hA : 0 ≤ A) :
    increment p A ≤ A / 32768 := by
  have hb := denominator_ge_one p hR A
  have hq := confidence_ge_one p
  exact div_le_div_of_nonneg_left hA (by norm_num) (by nlinarith :
    32768 ≤ 32768 * confidence p * (1 + p.R * Real.sqrt p.H1 + Real.sqrt (p.H0 * A)))

lemma weight_pos (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (n : ℕ) :
    0 < weight p n := by
  induction n with
  | zero => dsimp [weight]; positivity
  | succ n ih => exact add_pos ih (increment_pos p hR.le ih)

lemma log_step_lower {A a : ℝ} (hA : 0 < A) (ha : 0 < a) (haA : a ≤ A) :
    a / (2 * A) ≤ Real.log (A + a) - Real.log A := by
  have hAp : 0 < A + a := by positivity
  have hh := Real.one_sub_inv_le_log_of_pos (div_pos hAp hA)
  rw [Real.log_div hAp.ne' hA.ne'] at hh
  have he : 1 - ((A + a) / A)⁻¹ = a / (A + a) := by field_simp; ring
  rw [he] at hh
  exact (div_le_div_of_nonneg_left ha.le hAp (by linarith : A + a ≤ 2 * A)).trans hh

lemma sqrt_step_lower {A a : ℝ} (hA : 0 < A) (ha : 0 < a) (haA : a ≤ A) :
    a / (4 * Real.sqrt A) ≤ Real.sqrt (A + a) - Real.sqrt A := by
  have hs := Real.sq_sqrt hA.le
  have hs' := Real.sq_sqrt (show 0 ≤ A + a by positivity)
  have hsp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hh : Real.sqrt (A + a) ≤ 2 * Real.sqrt A := by
    nlinarith [Real.sqrt_nonneg (A + a)]
  have hd : 0 ≤ Real.sqrt (A + a) - Real.sqrt A := by
    exact sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.sqrt A)).mpr
  nlinarith [mul_nonneg hd (show 0 ≤ 3 * Real.sqrt A - Real.sqrt (A + a) by linarith)]

noncomputable def growthPotential (p : Params) (A : ℝ) : ℝ :=
  (1 + p.R * Real.sqrt p.H1) * Real.log A + 2 * Real.sqrt p.H0 * Real.sqrt A

lemma growth_potential_step (p : Params) (hR : 0 ≤ p.R) (h0 : 0 ≤ p.H0)
    {A : ℝ} (hA : 0 < A) :
    1 / (65536 * confidence p) ≤ growthPotential p (A + increment p A) - growthPotential p A := by
  let a := increment p A
  let C := 1 + p.R * Real.sqrt p.H1
  have ha : 0 < a := increment_pos p hR hA
  have haA : a ≤ A := by have := increment_small p hR hA.le; dsimp [a]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hl := mul_le_mul_of_nonneg_left (log_step_lower hA ha haA) hC
  have hs := mul_le_mul_of_nonneg_left (sqrt_step_lower hA ha haA)
    (show 0 ≤ 2 * Real.sqrt p.H0 by positivity)
  have hsp : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hsA := Real.sq_sqrt hA.le
  have hm : Real.sqrt (p.H0 * A) = Real.sqrt p.H0 * Real.sqrt A := Real.sqrt_mul h0 A
  have hb := denominator_ge_one p hR A
  have hq := confidence_pos p
  have he : C * (a / (2 * A)) + 2 * Real.sqrt p.H0 * (a / (4 * Real.sqrt A)) =
      1 / (65536 * confidence p) := by
    dsimp [a, increment, C]
    rw [hm]
    field_simp
    nlinarith
  unfold growthPotential
  change 1 / (65536 * confidence p) ≤ C * Real.log (A + a) + 2 * Real.sqrt p.H0 * Real.sqrt (A + a) -
    (C * Real.log A + 2 * Real.sqrt p.H0 * Real.sqrt A)
  linarith

lemma weight_growth (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ) (h0 : 0 ≤ p.H0)
    (n : ℕ) : (n : ℝ) / (65536 * confidence p) ≤ growthPotential p (weight p n) -
      growthPotential p (weight p 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := growth_potential_step p hR.le h0 (weight_pos p hR hΔ n)
    simp only [Nat.cast_add, Nat.cast_one, weight] at *
    have hq := confidence_pos p
    field_simp at *
    linarith

lemma log_sixteen_bound {r : ℝ} (hr : 1 ≤ r) :
    Real.log (16 * r) ≤ 4 * Real.log (1 + r) := by
  have hs : 4 * r ≤ (1 + r) ^ 2 := by nlinarith [sq_nonneg (r - 1)]
  have hs' := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * r) hs 2
  have hb : 16 * r ≤ (1 + r) ^ 4 := by nlinarith [sq_nonneg (r - 1)]
  have hh := Real.log_le_log (by positivity : 0 < 16 * r) hb
  simpa only [Real.log_pow, Nat.cast_ofNat] using hh

lemma growth_potential_upper (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (hε : 0 < p.ε) (hεΔ : p.ε ≤ p.Δ) (h0 : 0 ≤ p.H0)
    {A : ℝ} (hA : 0 < A) (hAb : A ≤ 16 * p.R ^ 2 / p.ε) :
    growthPotential p A - growthPotential p (weight p 0) ≤
      4 * (1 + p.R * Real.sqrt p.H1) * Real.log (1 + p.Δ / p.ε) +
        8 * p.R * Real.sqrt (p.H0 / p.ε) := by
  have hinit : 0 < p.R ^ 2 / p.Δ := by positivity
  have htarget : 0 < 16 * p.R ^ 2 / p.ε := by positivity
  have hC : 0 ≤ 1 + p.R * Real.sqrt p.H1 := by positivity
  have hratio : 1 ≤ p.Δ / p.ε := (one_le_div hε).mpr hεΔ
  have he : (16 * p.R ^ 2 / p.ε) / (p.R ^ 2 / p.Δ) = 16 * (p.Δ / p.ε) := by
    field_simp
  have hl : Real.log A - Real.log (p.R ^ 2 / p.Δ) ≤
      4 * Real.log (1 + p.Δ / p.ε) := by
    calc
      _ ≤ Real.log (16 * p.R ^ 2 / p.ε) - Real.log (p.R ^ 2 / p.Δ) :=
        sub_le_sub_right (Real.log_le_log hA hAb) _
      _ = Real.log (16 * (p.Δ / p.ε)) := by rw [← Real.log_div htarget.ne' hinit.ne', he]
      _ ≤ _ := log_sixteen_bound hratio
  have hs := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hAb) (Real.sqrt_nonneg p.H0)
  have hsimp : Real.sqrt p.H0 * Real.sqrt (16 * p.R ^ 2 / p.ε) =
      4 * p.R * Real.sqrt (p.H0 / p.ε) := by
    rw [Real.sqrt_div (by positivity : 0 ≤ 16 * p.R ^ 2),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16), Real.sqrt_sq hR.le,
      Real.sqrt_div h0]
    norm_num
    ring
  rw [hsimp] at hs
  have hl' := mul_le_mul_of_nonneg_left hl hC
  have hi : 0 ≤ Real.sqrt p.H0 * Real.sqrt (p.R ^ 2 / p.Δ) := by positivity
  simp only [growthPotential, weight]
  nlinarith only [hs, hl', hi]

lemma weight_reaches_accuracy (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    (hε : 0 < p.ε) (hεΔ : p.ε ≤ p.Δ) (h0 : 0 ≤ p.H0) {n : ℕ}
    (hn : 1048576 * confidence p * ((1 + p.R * Real.sqrt p.H1) * Real.log (1 + p.Δ / p.ε) +
      p.R * Real.sqrt (p.H0 / p.ε)) ≤ (n : ℝ)) :
    16 * p.R ^ 2 / p.ε ≤ weight p n := by
  by_contra! hb
  have hlo := weight_growth p hR hΔ h0 n
  have hhi := growth_potential_upper p hR hΔ hε hεΔ h0 (weight_pos p hR hΔ n) hb.le
  have hlog : 0 < Real.log (1 + p.Δ / p.ε) := Real.log_pos (by linarith [div_pos hΔ hε])
  have hC : 0 < 1 + p.R * Real.sqrt p.H1 := by positivity
  have hfirst := mul_pos hC hlog
  have hsecond : 0 ≤ p.R * Real.sqrt (p.H0 / p.ε) := by positivity
  have hq := confidence_pos p
  have hlo' := (div_le_iff₀ (show 0 < 65536 * confidence p by positivity)).mp hlo
  have hhi' := mul_le_mul_of_nonneg_right hhi hq.le
  have hfirst' := mul_pos hfirst hq
  have hsecond' := mul_nonneg hsecond hq.le
  nlinarith only [hlo', hhi', hn, hfirst', hsecond']

end OracleTemplate.GapStrongGrowth
