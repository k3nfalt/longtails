import LongTails.Proofs.CompositeGapTuning

namespace LongTails.Proofs.CompositeGapGrowth

open LongTails.Setups.CompositeGapSmooth
open OracleTemplate.CompositeGapAccelerated
open CompositeGapTuning

lemma active_mass (p : Params) {Δ A : ℝ} (hA : 0 < A) :
    A + weight p Δ A = min (target p Δ) (A / (1 - fraction p Δ)) := by
  rw [weight, ite_eq_right hA.ne', ← min_add_add_left]
  have hd : 0 < 1 - fraction p Δ := by linarith [fraction_le p Δ]
  congr 1
  · ring
  · field_simp
    ring

lemma capped_mass {T A θ : ℝ} (hT : 0 ≤ T) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hA : A ≤ T) :
    (if T ≤ A then A else min T (A / (1 - θ))) = min T (A / (1 - θ)) := by
  split_ifs with hh
  · have he : A = T := le_antisymm hA hh
    rw [he, min_eq_left]
    exact (le_div_iff₀ (by linarith)).mpr (by nlinarith)
  · rfl

lemma capped_recurrence {T a θ : ℝ} (ha : 0 ≤ a) (haT : a ≤ T)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (f : ℕ → ℝ) (hinit : f 0 = a)
    (hstep : ∀ n, f (n + 1) = min T (f n / (1 - θ))) (n : ℕ) :
    f n = min T (a / (1 - θ) ^ n) := by
  have hd : 0 < 1 - θ := by linarith
  have hT : 0 ≤ T := ha.trans haT
  induction n with
  | zero => simpa [hinit] using (min_eq_right haT).symm
  | succ n ih =>
    rw [hstep, ih, ← min_div_div_right hd.le, ← min_assoc]
    have hh : T ≤ T / (1 - θ) := (le_div_iff₀ hd).mpr (by nlinarith)
    rw [min_eq_left hh, pow_succ, div_div]

lemma exp_fraction (θ : ℝ) : (1 - θ) * Real.exp θ ≤ 1 := by
  have hh := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-θ)) (Real.exp_pos θ).le
  rw [← Real.exp_add] at hh
  simp only [neg_add_cancel, Real.exp_zero] at hh
  nlinarith only [hh]

lemma capped_reaches {T a θ : ℝ} (ha : 0 < a) (haT : a ≤ T)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (f : ℕ → ℝ) (hinit : f 0 = a)
    (hstep : ∀ n, f (n + 1) = min T (f n / (1 - θ))) (n : ℕ)
    (hn : Real.log (T / a) ≤ n * θ) : f n = T := by
  rw [capped_recurrence ha.le haT hθ hθ1 f hinit hstep n]
  apply min_eq_left
  have hd : 0 < 1 - θ := by linarith
  have hT : 0 < T := ha.trans_le haT
  have hex : T / a ≤ Real.exp (n * θ) := by
    rw [← Real.exp_log (show 0 < T / a by positivity)]
    exact Real.exp_le_exp.mpr hn
  have hp := pow_le_pow_left₀ (show 0 ≤ (1 - θ) * Real.exp θ by positivity) (exp_fraction θ) n
  rw [mul_pow, one_pow, ← Real.exp_nat_mul] at hp
  have ht := mul_le_mul_of_nonneg_left hex (show 0 ≤ (1 - θ) ^ n by positivity)
  apply (le_div_iff₀ (pow_pos hd n)).mpr
  have hh : T / a * (1 - θ) ^ n ≤ 1 := by nlinarith only [ht, hp]
  have hx := mul_le_mul_of_nonneg_right hh ha.le
  field_simp at hx
  nlinarith only [hx]

lemma iterations_suffice {D U n : ℝ} (hD : 1 ≤ D) (hDU : D ≤ U)
    (hn : 256 * (1 + Real.sqrt U) * Real.log (32 * U) ≤ n) :
    Real.log (16 * D) ≤ (n - 1) / (128 * (1 + Real.sqrt D)) := by
  have hU : 1 ≤ U := hD.trans hDU
  have hlog : 1 ≤ Real.log (32 * U) := by
    have hh := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 31 by norm_num)
    norm_num at hh
    have ht := Real.log_le_log (by norm_num : (0 : ℝ) < 32) (show 32 ≤ 32 * U by linarith)
    linarith
  have hlogD : Real.log (16 * D) ≤ Real.log (32 * U) :=
    Real.log_le_log (by positivity) (by linarith)
  have hs := Real.sqrt_le_sqrt hDU
  have hsU := Real.sqrt_nonneg U
  have hsD := Real.sqrt_nonneg D
  have hprod := mul_le_mul_of_nonneg_right hs (show 0 ≤ Real.log (32 * U) by linarith)
  have hprod1 := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1 + Real.sqrt U by positivity)
  have hprodD := mul_le_mul_of_nonneg_left hlogD (show 0 ≤ 128 * (1 + Real.sqrt D) by positivity)
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [hn, hprod, hprod1, hprodD, hsU]

lemma phase_iterations_suffice (p : Params) (h0 : 0 ≤ p.H0) (h1 : 0 ≤ p.H1)
    (hR : 0 < p.R) (hε : 0 < p.ε) {Δ : ℝ} (hεΔ : p.ε ≤ Δ) :
    0 < phaseIterations p ∧ Real.log (16 * scale p Δ) ≤
      ((phaseIterations p : ℝ) - 1) * fraction p Δ := by
  have hΔ : 0 < Δ := hε.trans_le hεΔ
  let U := 1 + 2 * p.H0 * p.R ^ 2 / p.ε + p.H1 * p.R ^ 2
  have hU : 1 ≤ U := by
    have hh : 0 ≤ 2 * p.H0 * p.R ^ 2 / p.ε := by positivity
    have ht : 0 ≤ p.H1 * p.R ^ 2 := by positivity
    dsimp [U]
    linarith
  have hD := scale_ge_one p h0 h1 hR hΔ
  have hDU : scale p Δ ≤ U := by
    rw [scale_formula p hR hΔ]
    have hh : p.H0 * p.R ^ 2 / Δ ≤ p.H0 * p.R ^ 2 / p.ε :=
      div_le_div_of_nonneg_left (by positivity) hε hεΔ
    have hn : 0 ≤ p.H0 * p.R ^ 2 / p.ε := by positivity
    dsimp [U]
    have he : 2 * p.H0 * p.R ^ 2 / p.ε = 2 * (p.H0 * p.R ^ 2 / p.ε) := by ring
    rw [he]
    linarith
  have hlog : 0 < Real.log (32 * U) := Real.log_pos (by linarith)
  have hpos : 0 < phaseIterations p := Nat.ceil_pos.mpr (by change 0 < 256 * (1 + Real.sqrt U) * Real.log (32 * U); positivity)
  refine ⟨hpos, ?_⟩
  have hh := iterations_suffice hD hDU
    (show 256 * (1 + Real.sqrt U) * Real.log (32 * U) ≤ (phaseIterations p : ℝ) from Nat.le_ceil _)
  simpa only [fraction, div_eq_mul_inv, one_div, one_mul] using hh

lemma stage_gap_gt (p : Params) (hΔ : 0 < p.Δ) (hε : 0 < p.ε)
    {k : ℕ} (hk : k < phases p) : p.ε < p.Δ / 2 ^ k := by
  have ht : (k : ℝ) < Real.log (p.Δ / p.ε) / Real.log 2 := Nat.lt_ceil.mp hk
  have hl : (k : ℝ) * Real.log 2 < Real.log (p.Δ / p.ε) :=
    (lt_div_iff₀ (Real.log_pos (by norm_num))).mp ht
  have he := Real.exp_lt_exp.mpr hl
  rw [Real.exp_log (show 0 < p.Δ / p.ε by positivity), Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  have hh := (lt_div_iff₀ hε).mp he
  apply (lt_div_iff₀ (by positivity)).mpr
  nlinarith only [hh]

lemma final_gap_le (p : Params) (hΔ : 0 < p.Δ) (hε : 0 < p.ε) :
    p.Δ / 2 ^ phases p ≤ p.ε := by
  have ht : Real.log (p.Δ / p.ε) / Real.log 2 ≤ (phases p : ℝ) := Nat.le_ceil _
  have hl := (div_le_iff₀ (Real.log_pos (by norm_num))).mp ht
  have he := Real.exp_le_exp.mpr hl
  rw [Real.exp_log (show 0 < p.Δ / p.ε by positivity), Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  have hh := (div_le_iff₀ hε).mp he
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hh]

end LongTails.Proofs.CompositeGapGrowth
