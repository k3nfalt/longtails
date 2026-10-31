import LongTails.Proofs.AdamHeavyTailedHistory
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import LongTails.Proofs.TerminalClippingEnergy

open MeasureTheory

namespace LongTails.Proofs.AdamLogMoments

lemma logarithmic_absorption {M Φ Z S c : ℝ} (hM : 1 ≤ M) (hΦ : 1 ≤ Φ)
    (hZ : 0 ≤ Z) (hc1 : c ≤ 1 / 64)
    (hlog : Real.log M ≤ Real.log Φ + 1 + 2 * c * Real.log M +
      c * Real.log (1 + 2 * Z) + S) :
    M ^ 16 ≤ (Real.exp 32 * Φ ^ 32) *
      (Real.exp (32 * S) * Real.sqrt (1 + 2 * Z)) := by
  have hm := Real.log_nonneg hM
  have hp := Real.log_nonneg hΦ
  have hz := Real.log_nonneg (show 1 ≤ 1 + 2 * Z by linarith)
  have hcm : 2 * c * Real.log M ≤ Real.log M / 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 4 - c by linarith) hm]
  have hcz : 32 * c * Real.log (1 + 2 * Z) ≤ Real.log (1 + 2 * Z) / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hc1) hz]
  have hfinal : 16 * Real.log M ≤ 32 * Real.log Φ + 32 +
      Real.log (1 + 2 * Z) / 2 + 32 * S := by linarith
  have he := Real.exp_le_exp.mpr hfinal
  have hm0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hp0 : 0 < Φ := lt_of_lt_of_le zero_lt_one hΦ
  have hleft : Real.exp (16 * Real.log M) = M ^ (16 : ℕ) := by
    rw [show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hm0]
  have hright : Real.exp (32 * Real.log Φ + 32 + Real.log (1 + 2 * Z) / 2 + 32 * S) =
      (Real.exp 32 * Φ ^ (32 : ℕ)) * (Real.exp (32 * S) * Real.sqrt (1 + 2 * Z)) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_half,
      Real.exp_log (by positivity : 0 < 1 + 2 * Z)]
    rw [show (32 : ℝ) = ((32 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hp0]
    ring
  rwa [hleft, hright] at he

lemma sixteenth_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {M Z S : Ω → ℝ} {Φ c : ℝ}
    (hMm : Measurable M) (hZm : Measurable Z) (hSm : Measurable S)
    (hM : ∀ ω, 1 ≤ M ω) (hΦ : 1 ≤ Φ) (hZ : ∀ ω, 0 ≤ Z ω)
    (hc1 : c ≤ 1 / 64)
    (hZi : Integrable Z P) (hZE : (∫ ω, Z ω ∂P) ≤ 1)
    (hSi : Integrable (fun ω => Real.exp (64 * S ω)) P)
    (hSE : (∫ ω, Real.exp (64 * S ω) ∂P) ≤ 3)
    (hlog : ∀ ω, Real.log (M ω) ≤ Real.log Φ + 1 + 2 * c * Real.log (M ω) +
      c * Real.log (1 + 2 * Z ω) + S ω) :
    Integrable (fun ω => (M ω) ^ 16) P ∧
      (∫ ω, (M ω) ^ 16 ∂P) ≤ 3 * Real.exp 32 * Φ ^ 32 := by
  have hF : Measurable (fun ω => Real.exp (32 * S ω)) := by fun_prop
  have hG : Measurable (fun ω => Real.sqrt (1 + 2 * Z ω)) := by fun_prop
  have hFe (ω) : (Real.exp (32 * S ω)) ^ 2 = Real.exp (64 * S ω) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hGe (ω) : (Real.sqrt (1 + 2 * Z ω)) ^ 2 = 1 + 2 * Z ω :=
    Real.sq_sqrt (by linarith [hZ ω])
  have hFi : Integrable (fun ω => (Real.exp (32 * S ω)) ^ 2) P := by
    simpa only [hFe] using hSi
  have hGi : Integrable (fun ω => (Real.sqrt (1 + 2 * Z ω)) ^ 2) P := by
    have hi : Integrable (fun ω => 1 + 2 * Z ω) P := (integrable_const 1).add (hZi.const_mul 2)
    simpa only [hGe] using hi
  have hh := AdamHeavyTailedHistory.integral_abs_product_bound P
    (show 0 ≤ Real.exp 32 * Φ ^ 32 by positivity) (hMm.pow_const 16) hF hG
    (fun ω => (Real.exp_pos _).le) (fun ω => Real.sqrt_nonneg _) hFi hGi (fun ω => by
      rw [abs_of_nonneg (by positivity : 0 ≤ (M ω) ^ 16)]
      exact logarithmic_absorption (hM ω) hΦ (hZ ω) hc1 (hlog ω))
  have hGE : (∫ ω, (Real.sqrt (1 + 2 * Z ω)) ^ 2 ∂P) ≤ 3 := by
    simp only [hGe]
    rw [integral_add (integrable_const 1) (hZi.const_mul 2), integral_const_mul]
    simp only [integral_const, probReal_univ, one_smul]
    linarith
  have hFE : (∫ ω, (Real.exp (32 * S ω)) ^ 2 ∂P) ≤ 3 := by simpa only [hFe] using hSE
  have hb : Real.sqrt (∫ ω, (Real.exp (32 * S ω)) ^ 2 ∂P) *
      Real.sqrt (∫ ω, (Real.sqrt (1 + 2 * Z ω)) ^ 2 ∂P) ≤ 3 := by
    have ht := mul_le_mul (Real.sqrt_le_sqrt hFE) (Real.sqrt_le_sqrt hGE)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg 3)
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  refine ⟨hh.1, ?_⟩
  have hhb := hh.2
  have habs (ω) : |(M ω) ^ 16| = (M ω) ^ 16 := abs_of_nonneg (by positivity)
  simp only [habs] at hhb
  have ht := mul_le_mul_of_nonneg_left hb (show 0 ≤ Real.exp 32 * Φ ^ 32 by positivity)
  exact hhb.trans (by nlinarith [ht])

lemma exponential_constant : 3 * Real.exp 32 ≤ (16 : ℝ) ^ 16 := by
  have hh := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 32
  have he : Real.exp 32 = (Real.exp 1) ^ (32 : ℕ) := by
    simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 32
  rw [he]
  norm_num at hh ⊢
  linarith

lemma half_power_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {M : Ω → ℝ} {C : ℝ} (hM : Measurable M) (hC : 0 ≤ C)
    (n : ℕ) (hi : Integrable (fun ω => (M ω) ^ (2 * n)) P)
    (hb : (∫ ω, (M ω) ^ (2 * n) ∂P) ≤ C ^ (2 * n)) :
    Integrable (fun ω => (M ω) ^ n) P ∧
      (∫ ω, (M ω) ^ n ∂P) ≤ C ^ n := by
  have he (x : ℝ) : (x ^ n) ^ 2 = x ^ (2 * n) := by rw [← pow_mul, Nat.mul_comm]
  have hs : Integrable (fun ω => |(M ω) ^ n| ^ 2) P := by
    simpa only [sq_abs, he] using hi
  have hs' : Integrable (fun ω => ((M ω) ^ n) ^ 2) P := by simpa only [he] using hi
  have hlp := (memLp_two_iff_integrable_sq (hM.pow_const n).aestronglyMeasurable).2 hs'
  have hint := hlp.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hh := OracleTemplate.TerminalClipping.mean_norm_bound hint
    (by simpa only [Real.norm_eq_abs] using hs) (show 0 ≤ C ^ n by positivity)
    (by simpa only [Real.norm_eq_abs, sq_abs, he] using hb)
  exact ⟨hint, (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hh)⟩

lemma accumulator_feedback {G N T v K M : ℝ} (hT : 0 < T) (hv : 1 ≤ v)
    (hN : 0 ≤ N) (hM : 1 ≤ M) (hG : G ≤ 2 * T * (K * M) ^ 2 + 2 * N) :
    1 + G / (T * v) ≤ (1 + 2 * K ^ 2) * M ^ 2 * (1 + 2 * (N / (T * v))) := by
  have hv0 : 0 < v := by linarith
  have hden : 0 < T * v := mul_pos hT hv0
  have hG' : G / (T * v) ≤ 2 * K ^ 2 * M ^ 2 + 2 * (N / (T * v)) := by
    apply (div_le_iff₀ hden).2
    have he : (2 * K ^ 2 * M ^ 2 + 2 * (N / (T * v))) * (T * v) =
        2 * T * v * K ^ 2 * M ^ 2 + 2 * N := by field_simp
    rw [he]
    have hp := mul_nonneg (sub_nonneg.2 hv) (mul_nonneg hT.le (sq_nonneg (K * M)))
    nlinarith
  have hz : 0 ≤ N / (T * v) := div_nonneg hN hden.le
  have hm : 0 ≤ M ^ 2 - 1 := by nlinarith
  have hp := mul_nonneg hz hm
  have hk := mul_nonneg (mul_nonneg (sq_nonneg K) (sq_nonneg M)) hz
  nlinarith

noncomputable def prefixMaximum (a : ℕ → ℝ) : ℕ → ℝ
  | 0 => a 0
  | n + 1 => max (prefixMaximum a n) (a (n + 1))

lemma prefixMaximum_attained (a : ℕ → ℝ) (n : ℕ) :
    ∃ k ≤ n, prefixMaximum a n = a k := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
      rcases le_total (prefixMaximum a n) (a (n + 1)) with h | h
      · exact ⟨n + 1, le_rfl, max_eq_right h⟩
      · obtain ⟨k, hk, he⟩ := ih
        exact ⟨k, Nat.le_trans hk (Nat.le_succ n), (max_eq_left h).trans he⟩

lemma le_prefixMaximum (a : ℕ → ℝ) {k n : ℕ} (hk : k ≤ n) : a k ≤ prefixMaximum a n := by
  induction n with
  | zero =>
      have he : k = 0 := by omega
      subst k
      exact le_rfl
  | succ n ih =>
      by_cases he : k = n + 1
      · subst k; exact le_max_right _ _
      · exact (ih (by omega)).trans (le_max_left _ _)

lemma measurable_prefixMaximum {Ω : Type*} [MeasurableSpace Ω] {a : Ω → ℕ → ℝ}
    (ha : ∀ n, Measurable (fun ω => a ω n)) (n : ℕ) :
    Measurable (fun ω => prefixMaximum (a ω) n) := by
  induction n with
  | zero => exact ha 0
  | succ n ih => exact ih.max (ha (n + 1))

lemma logarithmic_feedback {M Φ Z S c D B K : ℝ} (hM : 1 ≤ M) (hZ : 0 ≤ Z)
    (hB : 1 ≤ B) (hc : 0 ≤ c)
    (hfeedback : B ≤ (1 + 2 * K ^ 2) * M ^ 2 * (1 + 2 * Z))
    (hpath : Real.log M ≤ Real.log Φ + D + c * (2 + Real.log B) + S)
    (hconstant : D + c * (2 + Real.log (1 + 2 * K ^ 2)) ≤ 1) :
    Real.log M ≤ Real.log Φ + 1 + 2 * c * Real.log M + c * Real.log (1 + 2 * Z) + S := by
  have hm : 0 < M := by linarith
  have hk : 0 < 1 + 2 * K ^ 2 := by positivity
  have hz : 0 < 1 + 2 * Z := by positivity
  have hh := Real.log_le_log (by linarith : 0 < B) hfeedback
  rw [Real.log_mul (mul_pos hk (sq_pos_of_pos hm)).ne' hz.ne',
    Real.log_mul hk.ne' (sq_pos_of_pos hm).ne', Real.log_pow] at hh
  have hh' := mul_le_mul_of_nonneg_left hh hc
  norm_num at hh'
  nlinarith

lemma log_noise_fourth {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) (hZ0 : ∀ ω, 0 ≤ Z ω)
    (hi : Integrable Z P) (hE : (∫ ω, Z ω ∂P) ≤ 1) :
    Integrable (fun ω => Real.log (1 + 2 * Z ω) ^ 4) P ∧
      (∫ ω, Real.log (1 + 2 * Z ω) ^ 4 ∂P) ≤ 256 := by
  have hy (ω) : 0 < 1 + 2 * Z ω := by linarith [hZ0 ω]
  have hl (ω) : 0 ≤ Real.log (1 + 2 * Z ω) := Real.log_nonneg (by linarith [hZ0 ω])
  have hb (ω) : Real.log (1 + 2 * Z ω) ^ 4 ≤ 24 * (1 + 2 * Z ω) := by
    have hh := Real.pow_div_factorial_le_exp _ (hl ω) 4
    rw [Real.exp_log (hy ω)] at hh
    norm_num at hh
    linarith
  have hmi : Integrable (fun ω => 24 * (1 + 2 * Z ω)) P :=
    (integrable_const 1 |>.add (hi.const_mul 2)).const_mul 24
  have hm : Measurable (fun ω => Real.log (1 + 2 * Z ω) ^ 4) :=
    ((measurable_const.add (measurable_const.mul hZ)).log).pow_const 4
  have hint : Integrable (fun ω => Real.log (1 + 2 * Z ω) ^ 4) P := by
    apply hmi.mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hl ω) 4)]; exact hb ω)
  refine ⟨hint, ?_⟩
  have hh := integral_mono hint hmi hb
  rw [integral_const_mul, integral_add (integrable_const 1) (hi.const_mul 2), integral_const_mul] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
  linarith
lemma weighted_log_square {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {M R L : Ω → ℝ} {K C : ℝ}
    (hM : Measurable M) (hR : Measurable R) (hL : Measurable L)
    (hR0 : ∀ ω, 0 ≤ R ω)
    (hiM : Integrable (fun ω => M ω ^ 4) P) (hiL : Integrable (fun ω => L ω ^ 4) P)
    (hEM : (∫ ω, M ω ^ 4 ∂P) ≤ C ^ 4) (hEL : (∫ ω, L ω ^ 4 ∂P) ≤ 256)
    (hb : ∀ ω, R ω ≤ 8 * K * M ω + L ω) :
    Integrable (fun ω => (M ω * R ω) ^ 2) P ∧
      (∫ ω, (M ω * R ω) ^ 2 ∂P) ≤ 128 * K ^ 2 * C ^ 4 + 32 * C ^ 2 := by
  have hiM' : Integrable (fun ω => (M ω ^ 2) ^ 2) P := by simpa only [← pow_mul] using hiM
  have hiL' : Integrable (fun ω => (L ω ^ 2) ^ 2) P := by simpa only [← pow_mul] using hiL
  have hip : Integrable (fun ω => M ω ^ 2 * L ω ^ 2) P :=
    ((memLp_two_iff_integrable_sq (hM.pow_const 2).aestronglyMeasurable).2 hiM').integrable_mul
      ((memLp_two_iff_integrable_sq (hL.pow_const 2).aestronglyMeasurable).2 hiL')
  have hEp : (∫ ω, M ω ^ 2 * L ω ^ 2 ∂P) ≤ 16 * C ^ 2 := by
    have hh := AdamHeavyTailedHistory.integral_nonnegative_cauchy P
      (hM.pow_const 2) (hL.pow_const 2) (fun ω => sq_nonneg _) (fun ω => sq_nonneg _) hiM' hiL'
    have h1 : Real.sqrt (∫ ω, (M ω ^ 2) ^ 2 ∂P) ≤ C ^ 2 := by
      have ht := Real.sqrt_le_sqrt hEM
      rw [show C ^ 4 = (C ^ 2) ^ 2 by ring, Real.sqrt_sq (sq_nonneg C)] at ht
      simpa only [← pow_mul] using ht
    have h2 : Real.sqrt (∫ ω, (L ω ^ 2) ^ 2 ∂P) ≤ 16 := by
      have ht := Real.sqrt_le_sqrt hEL
      norm_num [← pow_mul] at ht ⊢
      exact ht
    have hp := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (sq_nonneg C)
    exact hh.trans (by nlinarith [hp])
  have hpoint (ω) : (M ω * R ω) ^ 2 ≤ 128 * K ^ 2 * M ω ^ 4 + 2 * (M ω ^ 2 * L ω ^ 2) := by
    have ht := pow_le_pow_left₀ (hR0 ω) (hb ω) 2
    have hp := mul_le_mul_of_nonneg_left ht (sq_nonneg (M ω))
    nlinarith [sq_nonneg (8 * K * M ω - L ω),
      mul_nonneg (sq_nonneg (M ω)) (sq_nonneg (8 * K * M ω - L ω))]
  have hiB := (hiM.const_mul (128 * K ^ 2)).add (hip.const_mul 2)
  have hint : Integrable (fun ω => (M ω * R ω) ^ 2) P := by
    apply hiB.mono' ((hM.mul hR).pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpoint ω)
  refine ⟨hint, ?_⟩
  have hh := integral_mono hint hiB hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add (hiM.const_mul _) (hip.const_mul _), integral_const_mul, integral_const_mul] at hh
  have hm := mul_le_mul_of_nonneg_left hEM (by positivity : 0 ≤ 128 * K ^ 2)
  linarith

lemma envelope_log_bound {B K M Z : ℝ} (hB : 1 ≤ B) (hK : 1 ≤ K) (hM : 1 ≤ M)
    (hZ : 0 ≤ Z) (hc : Real.log (1 + 2 * K ^ 2) ≤ 4 * K)
    (hb : B ≤ (1 + 2 * K ^ 2) * M ^ 2 * (1 + 2 * Z)) :
    2 + Real.log B ≤ 8 * K * M + Real.log (1 + 2 * Z) := by
  have hm : 0 < M := by linarith
  have hz : 0 < 1 + 2 * Z := by linarith
  have hk : 0 < 1 + 2 * K ^ 2 := by positivity
  have hh := Real.log_le_log (by linarith : 0 < B) hb
  rw [Real.log_mul (mul_pos hk (sq_pos_of_pos hm)).ne' hz.ne', Real.log_mul hk.ne' (sq_pos_of_pos hm).ne', Real.log_pow] at hh
  have hl := Real.log_le_sub_one_of_pos hm
  have hp := mul_nonneg (sub_nonneg.2 hK) (sub_nonneg.2 hM)
  norm_num at hh
  nlinarith

lemma nonnegative_four_sum_square {D A B C N : ℝ} (hD : 0 ≤ D)
    (hb : D ≤ A + B + C + N) : D ^ 2 ≤ 4 * (A ^ 2 + B ^ 2 + C ^ 2 + N ^ 2) := by
  have hh := pow_le_pow_left₀ hD hb 2
  nlinarith [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (A - N),
    sq_nonneg (B - C), sq_nonneg (B - N), sq_nonneg (C - N)]

lemma lower_height_moments {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {M : Ω → ℝ} {C : ℝ} (hM : Measurable M) (hC : 0 ≤ C)
    (hi : Integrable (fun ω => M ω ^ 16) P) (hb : (∫ ω, M ω ^ 16 ∂P) ≤ C ^ 16) :
    (Integrable (fun ω => M ω ^ 4) P ∧ (∫ ω, M ω ^ 4 ∂P) ≤ C ^ 4) ∧
    (Integrable (fun ω => M ω ^ 2) P ∧ (∫ ω, M ω ^ 2 ∂P) ≤ C ^ 2) := by
  have h8 := half_power_moment P hM hC 8 hi hb
  have h4 := half_power_moment P hM hC 4 h8.1 h8.2
  exact ⟨h4, half_power_moment P hM hC 2 h4.1 h4.2⟩

lemma signal_second_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {D M R N : Ω → ℝ} {Δ C B V : ℝ}
    (hD : Measurable D) (hD0 : ∀ ω, 0 ≤ D ω)
    (hiMR : Integrable (fun ω => (M ω * R ω) ^ 2) P)
    (hiM : Integrable (fun ω => M ω ^ 2) P) (hiN : Integrable (fun ω => N ω ^ 2) P)
    (hEMR : (∫ ω, (M ω * R ω) ^ 2 ∂P) ≤ B)
    (hEM : (∫ ω, M ω ^ 2 ∂P) ≤ C) (hEN : (∫ ω, N ω ^ 2 ∂P) ≤ V)
    (hb : ∀ ω, D ω ≤ Δ + M ω * R ω + M ω + N ω) :
    Integrable (fun ω => D ω ^ 2) P ∧
      (∫ ω, D ω ^ 2 ∂P) ≤ 4 * (Δ ^ 2 + B + C + V) := by
  have hip := (((integrable_const (Δ ^ 2)).add hiMR).add hiM).add hiN
  have hp (ω) := nonnegative_four_sum_square (hD0 ω) (hb ω)
  have hint : Integrable (fun ω => D ω ^ 2) P := by
    apply (hip.const_mul 4).mono' (hD.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hp ω)
  refine ⟨hint, ?_⟩
  have hh := integral_mono hint (hip.const_mul 4) hp
  simp only [Pi.add_apply] at hh
  have hiAB : Integrable (fun ω => Δ ^ 2 + (M ω * R ω) ^ 2) P := (integrable_const _).add hiMR
  have hiABC : Integrable (fun ω => Δ ^ 2 + (M ω * R ω) ^ 2 + M ω ^ 2) P := hiAB.add hiM
  rw [integral_const_mul, integral_add hiABC hiN, integral_add hiAB hiM,
    integral_add (integrable_const _) hiMR] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
  linarith

lemma denominator_square_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {X M Z : Ω → ℝ} {K v Φ : ℝ}
    (hK : 1 ≤ K) (hv : 1 ≤ v) (hΦ : 1 ≤ Φ) (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hiM : Integrable (fun ω => M ω ^ 2) P) (hiZ : Integrable Z P)
    (hEM : (∫ ω, M ω ^ 2 ∂P) ≤ 256 * Φ ^ 4) (hEZ : (∫ ω, Z ω ∂P) ≤ 1)
    (hb : ∀ ω, X ω ≤ v + 3 * K ^ 2 * M ω ^ 2 + 2 * v * Z ω) :
    Integrable (fun ω => (1 + Real.sqrt (X ω)) ^ 2) P ∧
      (∫ ω, (1 + Real.sqrt (X ω)) ^ 2 ∂P) ≤ (64 * K * Real.sqrt v * Φ ^ 2) ^ 2 := by
  have hv0 : 0 ≤ v := by linarith
  have hp (ω) : (1 + Real.sqrt (X ω)) ^ 2 ≤ 2 + 2 * v + 6 * K ^ 2 * M ω ^ 2 + 4 * v * Z ω := by
    have hs := Real.sq_sqrt (hX0 ω)
    nlinarith [sq_nonneg (Real.sqrt (X ω) - 1), hb ω]
  have hiA : Integrable (fun ω => 2 + 2 * v + 6 * K ^ 2 * M ω ^ 2) P :=
    (integrable_const _).add (hiM.const_mul _)
  have hiB : Integrable (fun ω => 2 + 2 * v + 6 * K ^ 2 * M ω ^ 2 + 4 * v * Z ω) P :=
    hiA.add (hiZ.const_mul _)
  have hm := ((Real.continuous_sqrt.measurable.comp hX).const_add 1).pow_const 2
  have hint : Integrable (fun ω => (1 + Real.sqrt (X ω)) ^ 2) P := by
    apply hiB.mono' hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hp ω)
  refine ⟨hint, ?_⟩
  have hh := integral_mono hint hiB hp
  rw [integral_add hiA (hiZ.const_mul _), integral_add (integrable_const _) (hiM.const_mul _),
    integral_const_mul, integral_const_mul] at hh
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hh
  have hm' := mul_le_mul_of_nonneg_left hEM (by positivity : 0 ≤ 6 * K ^ 2)
  have hz' := mul_le_mul_of_nonneg_left hEZ (by positivity : 0 ≤ 4 * v)
  have hk2 : 1 ≤ K ^ 2 := by nlinarith
  have hφ4 : 1 ≤ Φ ^ 4 := by nlinarith [sq_nonneg (Φ ^ 2 - 1), sq_nonneg (Φ - 1)]
  have hprod : 1 ≤ K ^ 2 * Φ ^ 4 := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hprod hv0
  have hvm := mul_nonneg (sub_nonneg.2 hv) (show 0 ≤ K ^ 2 * Φ ^ 4 by positivity)
  rw [show (64 * K * Real.sqrt v * Φ ^ 2) ^ 2 = 4096 * K ^ 2 * v * Φ ^ 4 by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hv0]; ring]
  nlinarith
end LongTails.Proofs.AdamLogMoments
