import LongTails.Proofs.ParameterFreeNsgdmGrid
import LongTails.Proofs.ParameterFreeNsgdmExecution
import Mathlib.Analysis.Complex.ExponentialBounds

namespace LongTails.Proofs.ParameterFreeNsgdmBudget

open LongTails.Algorithms.ParameterFreeNsgdm ParameterFreeNsgdmGrid ParameterFreeNsgdmExecution

noncomputable def mainThreshold (L Δ σ p ε : ℝ) : ℝ :=
  8000 * L * Δ / ε ^ 2 + L * Δ * σ ^ (p / (p - 1)) * (80 / ε) ^ ((3 * p - 2) / (p - 1)) +
    σ ^ ((5 * p - 2) / (2 * p - 2)) * (L * Δ) ^ (-(p / (2 * p - 2))) *
      (60 / ε) ^ ((3 * p - 2) / (2 * p - 2)) +
    (σ ^ 2 / (L * Δ)) ^ (p / (2 * p - 2)) + Real.sqrt (3 * L / Δ) + (Δ / (3 * L)) ^ ((1 : ℝ) / 3) +
    6 ^ ((1 : ℝ) / (p - 1)) * (5 * σ / ε) ^ (p / (p - 1)) + 1

noncomputable def countThreshold (σ p ε : ℝ) : ℝ :=
  (64 * (1 + 5 * σ / ε) ^ p *
    ((22 + 2 * p * Real.logb 2 (1 + 5 * σ / ε)) / (p - 1)) ^ 4) ^ ((1 : ℝ) / (p - 1))

noncomputable def levelA (σ p ε : ℝ) : ℝ := (6 + p * Real.logb 2 (1 + 5 * σ / ε)) / (p - 1)

lemma exp_half_le : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have h2 : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have he : Real.exp 1 ≤ 4 := by
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num) ?_
  rw [h2]
  linarith

lemma exp_quarter_le : Real.exp (1 / 4 : ℝ) ≤ 13 / 10 := by
  have h4 : Real.exp (1 / 4 : ℝ) ^ 4 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  have he : Real.exp 1 ≤ 272 / 100 := by
    have := Real.exp_one_lt_d9
    norm_num at this
    linarith
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by norm_num) ?_
  rw [h4]
  linarith

lemma log_two_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have := Real.log_le_log (Real.exp_pos _) exp_half_le
  rwa [Real.log_exp] at this

noncomputable def levelK (σ p ε : ℝ) : ℝ :=
  levelA σ p ε + 2 * (2 / (p - 1)) * Real.logb 2 (2 * levelA σ p ε + 4 * (2 / (p - 1)) + 2)

lemma log_count_lemma {a q x : ℝ} (ha : 0 ≤ a) (hq : 2 ≤ q)
    (hx : a + 2 * q * Real.logb 2 (2 * a + 4 * q + 2) ≤ x) :
    a + q * Real.logb 2 (x + 1) ≤ x := by
  set x₀ := a + 2 * q * Real.logb 2 (2 * a + 4 * q + 2) with hx₀
  have hY : (1 : ℝ) ≤ 2 * a + 4 * q + 2 := by linarith
  have hlogY : 0 ≤ Real.logb 2 (2 * a + 4 * q + 2) := Real.logb_nonneg (by norm_num) hY
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx₀a : a ≤ x₀ := by rw [hx₀]; nlinarith
  have hx₀1 : 0 < x₀ + 1 := by linarith
  have hlog3 : (3 : ℝ) ≤ Real.logb 2 (2 * a + 4 * q + 2) := by
    rw [show (3 : ℝ) = Real.logb 2 8 by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.logb_pow]; simp]
    exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by linarith)
  have hbig : q ≤ (x₀ + 1) * Real.log 2 := by
    have h1 : 6 * q ≤ x₀ := by rw [hx₀]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left log_two_half (by linarith : (0 : ℝ) ≤ x₀ + 1)]
  have hY0 : 0 < 2 * a + 4 * q + 2 := by linarith
  have h2Y : 2 * a + 4 * q + 2 ≤ (2 : ℝ) ^ (2 * a + 4 * q + 2) := by
    have hhalf : 1 + (2 * a + 4 * q + 2) / 4 ≤ (2 : ℝ) ^ ((2 * a + 4 * q + 2) / 2) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      have h := Real.add_one_le_exp (Real.log 2 * ((2 * a + 4 * q + 2) / 2))
      nlinarith [mul_nonneg (sub_nonneg.2 log_two_half) hY0.le]
    calc 2 * a + 4 * q + 2 ≤ (1 + (2 * a + 4 * q + 2) / 4) ^ 2 := by
          nlinarith [sq_nonneg ((2 * a + 4 * q + 2) / 4 - 1)]
      _ ≤ ((2 : ℝ) ^ ((2 * a + 4 * q + 2) / 2)) ^ 2 := by gcongr
      _ = (2 : ℝ) ^ (2 * a + 4 * q + 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          congr 1
          push_cast
          ring
  have hl : Real.logb 2 (2 * a + 4 * q + 2) ≤ 2 * a + 4 * q + 2 :=
    (Real.logb_le_iff_le_rpow (by norm_num) hY0).2 h2Y
  have hsq : x₀ + 1 ≤ (2 * a + 4 * q + 2) ^ 2 := by
    rw [hx₀]
    nlinarith [mul_le_mul_of_nonneg_left hl (by linarith : (0 : ℝ) ≤ 2 * q), mul_nonneg ha ha,
      mul_nonneg ha (by linarith : (0 : ℝ) ≤ q),
      mul_nonneg (by linarith : (0 : ℝ) ≤ q) (by linarith : (0 : ℝ) ≤ q)]
  have hstart : a + q * Real.logb 2 (x₀ + 1) ≤ x₀ := by
    have : Real.logb 2 (x₀ + 1) ≤ 2 * Real.logb 2 (2 * a + 4 * q + 2) := by
      calc Real.logb 2 (x₀ + 1) ≤ Real.logb 2 ((2 * a + 4 * q + 2) ^ 2) :=
            Real.logb_le_logb_of_le (by norm_num) hx₀1 hsq
        _ = 2 * Real.logb 2 (2 * a + 4 * q + 2) := by
            rw [Real.logb_pow]; push_cast; ring
    rw [hx₀]; nlinarith
  have hgrow : Real.logb 2 (x + 1) ≤ Real.logb 2 (x₀ + 1) + (x - x₀) / ((x₀ + 1) * Real.log 2) := by
    have hpos : 0 < x + 1 := by linarith
    have hratio : 0 < (x + 1) / (x₀ + 1) := by positivity
    have h1 : Real.log ((x + 1) / (x₀ + 1)) ≤ (x + 1) / (x₀ + 1) - 1 := Real.log_le_sub_one_of_pos hratio
    have h2 : Real.log ((x + 1) / (x₀ + 1)) = Real.log (x + 1) - Real.log (x₀ + 1) :=
      Real.log_div hpos.ne' hx₀1.ne'
    have h3 : (x + 1) / (x₀ + 1) - 1 = (x - x₀) / (x₀ + 1) := by
      rw [div_sub_one hx₀1.ne']
      congr 1
      ring
    rw [h2, h3] at h1
    unfold Real.logb
    rw [show (x - x₀) / ((x₀ + 1) * Real.log 2) =
      ((x - x₀) / (x₀ + 1)) / Real.log 2 by rw [div_div], ← add_div]
    apply div_le_div_of_nonneg_right _ hlog2.le
    linarith
  have hfrac : q * ((x - x₀) / ((x₀ + 1) * Real.log 2)) ≤ x - x₀ := by
    have hxx : 0 ≤ x - x₀ := by linarith
    have hden : 0 < (x₀ + 1) * Real.log 2 := by positivity
    rw [mul_div_assoc', div_le_iff₀ hden]
    nlinarith
  calc a + q * Real.logb 2 (x + 1)
      ≤ a + q * (Real.logb 2 (x₀ + 1) + (x - x₀) / ((x₀ + 1) * Real.log 2)) := by
        gcongr
    _ = (a + q * Real.logb 2 (x₀ + 1)) + q * ((x - x₀) / ((x₀ + 1) * Real.log 2)) := by ring
    _ ≤ x₀ + (x - x₀) := add_le_add hstart hfrac
    _ = x := by ring


lemma candidates_le (k : ℕ) : (candidates k : ℝ) ≤ 10 * ((k : ℝ) + 1) ^ 2 := by
  unfold candidates momentumCount stepCount
  push_cast
  nlinarith [sq_nonneg (k : ℝ), (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma phaseStart_le (K : ℕ) : (phaseStart (K + 1) : ℝ) ≤ 40 * ((K : ℝ) + 1) ^ 2 * 2 ^ K := by
  have hmono : ∀ j ≤ K, (candidates j : ℝ) ≤ candidates K := by
    intro j hj
    unfold candidates momentumCount stepCount
    push_cast
    have : (j : ℝ) ≤ K := by exact_mod_cast hj
    nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hsum : ∀ K, (phaseStart (K + 1) : ℝ) = ∑ j ∈ Finset.range (K + 1), 2 * ((candidates j : ℝ) * 2 ^ j) := by
    intro K
    induction K with
    | zero => simp [phaseStart, phaseCost, horizon]
    | succ K ih =>
        rw [phaseStart, Nat.cast_add, ih, Finset.sum_range_succ _ (K + 1)]
        simp [phaseCost, horizon]
  rw [hsum]
  calc ∑ j ∈ Finset.range (K + 1), 2 * ((candidates j : ℝ) * 2 ^ j)
      ≤ ∑ j ∈ Finset.range (K + 1), 2 * ((candidates K : ℝ) * 2 ^ j) := by
        apply Finset.sum_le_sum
        intro j hj
        have := hmono j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
        gcongr
    _ = 2 * (candidates K : ℝ) * ∑ j ∈ Finset.range (K + 1), (2 : ℝ) ^ j := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ ≤ 2 * (candidates K : ℝ) * (2 ^ (K + 1)) := by
        gcongr
        have := geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1) (K + 1)
        rw [this]
        have h2 : (0 : ℝ) ≤ 2 ^ (K + 1) - 1 := by
          have : (1 : ℝ) ≤ 2 ^ (K + 1) := one_le_pow₀ (by norm_num)
          linarith
        rw [div_le_iff₀ (by norm_num)]
        linarith
    _ ≤ 2 * (10 * ((K : ℝ) + 1) ^ 2) * (2 ^ (K + 1)) := by
        gcongr
        exact candidates_le K
    _ = 40 * ((K : ℝ) + 1) ^ 2 * 2 ^ K := by rw [pow_succ]; ring

lemma single_validation_bound {σ p ε T : ℝ} (hσ : 0 ≤ σ) (hp : 1 < p) (hε : 0 < ε) (hT : 0 < T)
    (hthr : 6 ^ ((1 : ℝ) / (p - 1)) * (5 * σ / ε) ^ (p / (p - 1)) ≤ T) :
    (6 * σ ^ p / T ^ (p - 1)) ^ (1 / p) ≤ ε / 5 := by
  have hp1 : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have hkey : 6 * σ ^ p ≤ T ^ (p - 1) * (ε / 5) ^ p := by
    have h1 : (6 ^ ((1 : ℝ) / (p - 1)) * (5 * σ / ε) ^ (p / (p - 1))) ^ (p - 1) ≤ T ^ (p - 1) :=
      Real.rpow_le_rpow (by positivity) hthr hp1.le
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by positivity), one_div_mul_cancel hp1.ne', div_mul_cancel₀ _ hp1.ne',
      Real.rpow_one] at h1
    have h2 : (5 * σ / ε) ^ p = 5 ^ p * σ ^ p / ε ^ p := by
      rw [Real.div_rpow (by positivity) hε.le, Real.mul_rpow (by norm_num) hσ]
    have h3 : (ε / 5) ^ p = ε ^ p / 5 ^ p := Real.div_rpow hε.le (by norm_num) p
    rw [h2] at h1
    rw [h3]
    have h5 : (0 : ℝ) < 5 ^ p := by positivity
    have hε' : (0 : ℝ) < ε ^ p := by positivity
    calc 6 * σ ^ p = 6 * (5 ^ p * σ ^ p / ε ^ p) * ε ^ p / 5 ^ p := by
          rw [mul_assoc 6, div_mul_cancel₀ _ hε'.ne', eq_div_iff h5.ne']
          ring
      _ ≤ T ^ (p - 1) * ε ^ p / 5 ^ p := by gcongr
      _ = T ^ (p - 1) * (ε ^ p / 5 ^ p) := by ring
  have hTp : 0 < T ^ (p - 1) := by positivity
  calc (6 * σ ^ p / T ^ (p - 1)) ^ (1 / p) ≤ ((ε / 5) ^ p) ^ (1 / p) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        rw [div_le_iff₀ hTp]; linarith
    _ = ε / 5 := by
        rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hp0.ne', Real.rpow_one]

lemma count_validation_bound {σ p ε : ℝ} (hσ : 0 ≤ σ) (hp : 1 < p) (hp2 : p ≤ 2) (hε : 0 < ε)
    {k : ℕ} (hk : levelK σ p ε ≤ k) :
    ((candidates k : ℝ) * (6 * σ ^ p / ((2 : ℝ) ^ k) ^ (p - 1))) ^ (1 / p) ≤ ε / 5 := by
  have hp1 : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have hq : (2 : ℝ) ≤ 2 / (p - 1) := by
    rw [le_div_iff₀ hp1]; linarith
  have hpos : 0 < 1 + 5 * σ / ε := by positivity
  have hlogσ : 0 ≤ Real.logb 2 (1 + 5 * σ / ε) := Real.logb_nonneg (by norm_num) (by
    have : 0 ≤ 5 * σ / ε := by positivity
    linarith)
  have ha : 0 ≤ levelA σ p ε := by unfold levelA; positivity
  have hcount := log_count_lemma ha hq (x := k) (by unfold levelK at hk; exact hk)
  have hcount' : 6 + p * Real.logb 2 (1 + 5 * σ / ε) + 2 * Real.logb 2 ((k : ℝ) + 1) ≤
      k * (p - 1) := by
    have h := mul_le_mul_of_nonneg_right hcount hp1.le
    have hinv1 : (p - 1) * (p - 1)⁻¹ = 1 := mul_inv_cancel₀ hp1.ne'
    have e : (levelA σ p ε + 2 / (p - 1) * Real.logb 2 ((k : ℝ) + 1)) * (p - 1) =
        6 + p * Real.logb 2 (1 + 5 * σ / ε) + 2 * Real.logb 2 ((k : ℝ) + 1) := by
      unfold levelA
      linear_combination
        (6 + p * Real.logb 2 (1 + 5 * σ / ε) + 2 * Real.logb 2 ((k : ℝ) + 1)) * hinv1
    rw [e] at h
    exact h
  have hkey : 60 * ((k : ℝ) + 1) ^ 2 * (5 * σ / ε) ^ p ≤ ((2 : ℝ) ^ k) ^ (p - 1) := by
    have hpk : ((2 : ℝ) ^ k) ^ (p - 1) = 2 ^ ((k : ℝ) * (p - 1)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    rw [hpk]
    have h60 : (60 : ℝ) ≤ 2 ^ (6 : ℝ) := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have hk1 : ((k : ℝ) + 1) ^ 2 = 2 ^ (2 * Real.logb 2 ((k : ℝ) + 1)) := by
      rw [mul_comm, Real.rpow_mul (by norm_num),
        Real.rpow_logb (by norm_num) (by norm_num) (by positivity), Real.rpow_two]
    have hσε : (5 * σ / ε) ^ p ≤ 2 ^ (p * Real.logb 2 (1 + 5 * σ / ε)) := by
      rw [mul_comm p, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hpos]
      exact Real.rpow_le_rpow (by positivity) (by linarith) hp0.le
    have hlhs : 60 * ((k : ℝ) + 1) ^ 2 * (5 * σ / ε) ^ p ≤
        2 ^ (6 + 2 * Real.logb 2 ((k : ℝ) + 1) + p * Real.logb 2 (1 + 5 * σ / ε)) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), hk1]
      gcongr
    refine hlhs.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_)
    linarith
  have hT : (0 : ℝ) < ((2 : ℝ) ^ k) ^ (p - 1) := by positivity
  have hcand := candidates_le k
  have hinner : (candidates k : ℝ) * (6 * σ ^ p / ((2 : ℝ) ^ k) ^ (p - 1)) ≤ (ε / 5) ^ p := by
    have h2 : (5 * σ / ε) ^ p = 5 ^ p * σ ^ p / ε ^ p := by
      rw [Real.div_rpow (by positivity) hε.le, Real.mul_rpow (by norm_num) hσ]
    have h3 : (ε / 5) ^ p = ε ^ p / 5 ^ p := Real.div_rpow hε.le (by norm_num) p
    have hσp : 0 ≤ σ ^ p := by positivity
    have hA : (candidates k : ℝ) * (6 * σ ^ p) ≤ 60 * ((k : ℝ) + 1) ^ 2 * σ ^ p := by
      nlinarith [mul_le_mul_of_nonneg_right hcand (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hσp)]
    have hB : 60 * ((k : ℝ) + 1) ^ 2 * σ ^ p ≤ ((2 : ℝ) ^ k) ^ (p - 1) * (ε / 5) ^ p := by
      rw [h2] at hkey
      rw [h3]
      have h5 : (0 : ℝ) < 5 ^ p := by positivity
      have hε' : (0 : ℝ) < ε ^ p := by positivity
      have hsplit : 60 * ((k : ℝ) + 1) ^ 2 * σ ^ p =
          (60 * ((k : ℝ) + 1) ^ 2 * (5 ^ p * σ ^ p / ε ^ p)) * (ε ^ p / 5 ^ p) := by
        field_simp
      rw [hsplit]
      exact mul_le_mul_of_nonneg_right hkey (by positivity)
    calc (candidates k : ℝ) * (6 * σ ^ p / ((2 : ℝ) ^ k) ^ (p - 1))
        = (candidates k : ℝ) * (6 * σ ^ p) / ((2 : ℝ) ^ k) ^ (p - 1) := by ring
      _ ≤ 60 * ((k : ℝ) + 1) ^ 2 * σ ^ p / ((2 : ℝ) ^ k) ^ (p - 1) :=
          div_le_div_of_nonneg_right hA hT.le
      _ ≤ (ε / 5) ^ p := by
          rw [div_le_iff₀ hT]
          linarith [hB]
  calc ((candidates k : ℝ) * (6 * σ ^ p / ((2 : ℝ) ^ k) ^ (p - 1))) ^ (1 / p)
      ≤ ((ε / 5) ^ p) ^ (1 / p) := Real.rpow_le_rpow (by positivity) hinner (by positivity)
    _ = ε / 5 := by rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hp0.ne', Real.rpow_one]


lemma sqrt_term_bound {L Δ ε T : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hε : 0 < ε) (hT : 0 < T)
    (h : 8000 * L * Δ / ε ^ 2 ≤ T) :
    Real.exp (1 / 2) * (2 * Real.sqrt (3 * L * Δ / T)) ≤ ε / 5 ∧
      12 * Real.exp (1 / 4) * Real.sqrt (L * Δ / T) ≤ ε / 5 := by
  have he2 := exp_half_le
  have he4 := exp_quarter_le
  have hs : Real.sqrt (L * Δ / T) ≤ ε / 80 := by
    rw [Real.sqrt_le_left (by positivity)]
    rw [div_le_iff₀ hT]
    have : L * Δ ≤ T * ε ^ 2 / 8000 := by
      rw [le_div_iff₀ (by norm_num)]
      have := h
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    calc L * Δ ≤ T * ε ^ 2 / 8000 := this
      _ ≤ (ε / 80) ^ 2 * T := by nlinarith [mul_nonneg (sq_nonneg ε) hT.le]
  have hs3 : Real.sqrt (3 * L * Δ / T) = Real.sqrt 3 * Real.sqrt (L * Δ / T) := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have hsqrt3 : Real.sqrt 3 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  constructor
  · rw [hs3]
    have h0 : 0 ≤ Real.sqrt (L * Δ / T) := Real.sqrt_nonneg _
    calc Real.exp (1 / 2) * (2 * (Real.sqrt 3 * Real.sqrt (L * Δ / T)))
        ≤ 2 * (2 * (2 * (ε / 80))) := by gcongr
      _ ≤ ε / 5 := by linarith
  · calc 12 * Real.exp (1 / 4) * Real.sqrt (L * Δ / T) ≤ 12 * (13 / 10) * (ε / 80) := by
          gcongr
      _ ≤ ε / 5 := by linarith


lemma step_range {L Δ σ p T : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hT : 1 ≤ T)
    (h1 : Real.sqrt (3 * L / Δ) ≤ T) (h2 : (Δ / (3 * L)) ^ ((1 : ℝ) / 3) ≤ T) :
    1 / T ^ 2 ≤ optStep L Δ σ p T ∧ optStep L Δ σ p T ≤ T := by
  have hT0 : 0 < T := by linarith
  have hα0 := optMomentum_pos (L := L) (Δ := Δ) (σ := σ) (p := p) hT0
  have hα1 := optMomentum_le_one (L := L) (Δ := Δ) (σ := σ) (p := p) (T := T)
  have hαT := inv_le_optMomentum (L := L) (Δ := Δ) (σ := σ) (p := p) hT
  set a := optMomentum L Δ σ p T with ha
  unfold optStep
  rw [← ha]
  constructor
  · rw [Real.le_sqrt (by positivity) (by positivity)]
    have hinv : 1 / T ≤ Real.sqrt (Δ / (3 * L)) := by
      have h3 : Real.sqrt (3 * L / Δ) * Real.sqrt (Δ / (3 * L)) = 1 := by
        rw [← Real.sqrt_mul (by positivity), show 3 * L / Δ * (Δ / (3 * L)) = 1 by field_simp]
        exact Real.sqrt_one
      rw [div_le_iff₀ hT0]
      calc (1 : ℝ) = Real.sqrt (3 * L / Δ) * Real.sqrt (Δ / (3 * L)) := h3.symm
        _ ≤ Real.sqrt (Δ / (3 * L)) * T := by
            rw [mul_comm]
            gcongr
    have hsq : (1 / T) ^ 2 ≤ Δ / (3 * L) := by
      calc (1 / T) ^ 2 ≤ Real.sqrt (Δ / (3 * L)) ^ 2 := by gcongr
        _ = Δ / (3 * L) := Real.sq_sqrt (by positivity)
    have hT2 : 0 < T ^ 2 := by positivity
    calc (1 / T ^ 2) ^ 2 = (1 / T) ^ 2 * (1 / T ^ 2) := by field_simp
      _ ≤ Δ / (3 * L) * (1 / T ^ 2) := by gcongr
      _ = Δ * (1 / T) / (3 * L * T) := by field_simp
      _ ≤ Δ * a / (3 * L * T) := by gcongr
  · have hcube : Δ / (3 * L) ≤ T ^ 3 := by
      calc Δ / (3 * L) = ((Δ / (3 * L)) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            norm_num
        _ ≤ T ^ 3 := by gcongr
    calc Real.sqrt (Δ * a / (3 * L * T)) ≤ Real.sqrt (T ^ 2) := by
          apply Real.sqrt_le_sqrt
          have : Δ * a / (3 * L * T) ≤ Δ / (3 * L * T) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            nlinarith
          refine this.trans ?_
          rw [div_le_iff₀ (by positivity)]
          have : Δ / (3 * L) * (3 * L) = Δ := by field_simp
          nlinarith [mul_le_mul_of_nonneg_right hcube (by positivity : (0 : ℝ) ≤ 3 * L)]
      _ = T := Real.sqrt_sq hT0.le


lemma tuned_bound {L Δ σ p ε T : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hp : 1 < p)
    (hε : 0 < ε) (hT : 1 ≤ T)
    (h1 : 8000 * L * Δ / ε ^ 2 ≤ T)
    (h2 : L * Δ * σ ^ (p / (p - 1)) * (80 / ε) ^ ((3 * p - 2) / (p - 1)) ≤ T)
    (h3 : σ ^ ((5 * p - 2) / (2 * p - 2)) * (L * Δ) ^ (-(p / (2 * p - 2))) *
      (60 / ε) ^ ((3 * p - 2) / (2 * p - 2)) ≤ T)
    (h4 : (σ ^ 2 / (L * Δ)) ^ (p / (2 * p - 2)) ≤ T) :
    tunedRate L Δ σ p T ≤ 3 * ε / 5 := by
  have hT0 : 0 < T := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have h3p : 0 < 3 * p - 2 := by linarith
  have h2p : 0 < 2 * p - 2 := by linarith
  have hr : 0 < p / (3 * p - 2) := by positivity
  have he4 : 1 ≤ Real.exp (1 / 4 : ℝ) := Real.one_le_exp (by norm_num)
  obtain ⟨hs1, hs2⟩ := sqrt_term_bound hL hΔ hε hT0 h1
  unfold tunedRate
  by_cases hσ0 : σ = 0
  · subst hσ0
    have hα : optMomentum L Δ 0 p T = 1 := by simp [optMomentum]
    rw [hα]
    simp only [one_mul, mul_zero, zero_mul, zero_div, add_zero]
    linarith
  have hσpos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hσ0)
  set c₀ := L * Δ / (σ ^ 2 * T) with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have hαdef : optMomentum L Δ σ p T = min 1 (max (1 / T) (c₀ ^ (p / (3 * p - 2)))) := by
    simp [optMomentum, hσ0, hc₀]
  by_cases hc1 : 1 ≤ c₀
  · have hα : optMomentum L Δ σ p T = 1 := by
      rw [hαdef]
      have h1' : 1 ≤ c₀ ^ (p / (3 * p - 2)) := Real.one_le_rpow hc1 hr.le
      rw [min_eq_left (le_max_of_le_right h1')]
    rw [hα, Real.one_rpow, one_mul, mul_one]
    have hσle : σ ≤ Real.sqrt (L * Δ / T) := by
      rw [Real.le_sqrt hσ (by positivity)]
      rw [hc₀, le_div_iff₀ (by positivity)] at hc1
      rw [le_div_iff₀ hT0]
      linarith
    have ht2 : 12 * Real.exp (1 / 4) * σ ≤ ε / 5 := by
      calc 12 * Real.exp (1 / 4) * σ ≤ 12 * Real.exp (1 / 4) * Real.sqrt (L * Δ / T) := by gcongr
        _ ≤ ε / 5 := hs2
    have ht3 : 12 * σ / T ≤ ε / 5 := by
      calc 12 * σ / T ≤ 12 * σ := by
            rw [div_le_iff₀ hT0]; nlinarith
        _ ≤ 12 * Real.exp (1 / 4) * σ := by nlinarith
        _ ≤ ε / 5 := ht2
    linarith
  · rw [not_le] at hc1
    have he2 := exp_half_le
    have he4 := exp_quarter_le
    set r := p / (3 * p - 2) with hr_def
    have hinv3 : (3 * p - 2) * (3 * p - 2)⁻¹ = 1 := mul_inv_cancel₀ h3p.ne'
    have hinvp : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
    have hinv1 : (p - 1) * (p - 1)⁻¹ = 1 := mul_inv_cancel₀ hp1.ne'
    have hinv2 : (2 * p - 2) * (2 * p - 2)⁻¹ = 1 := mul_inv_cancel₀ h2p.ne'
    have hr1 : r ≤ 1 := by rw [hr_def, div_le_one h3p]; linarith
    have h1r : 1 - r = (2 * p - 2) / (3 * p - 2) := by
      rw [hr_def]
      linear_combination (-1 : ℝ) * hinv3
    have hcr1 : c₀ ^ r ≤ 1 := Real.rpow_le_one hc₀pos.le hc1.le hr.le
    have hcrT : 1 / T ≤ c₀ ^ r := by
      have hq : σ ^ 2 / (L * Δ) ≤ T ^ ((2 * p - 2) / p) := by
        have := Real.rpow_le_rpow (by positivity) h4 (by positivity : (0 : ℝ) ≤ (2 * p - 2) / p)
        rwa [← Real.rpow_mul (by positivity),
          show p / (2 * p - 2) * ((2 * p - 2) / p) = 1 by field_simp, Real.rpow_one] at this
      have hcT : c₀ * T ^ ((3 * p - 2) / p) ≥ 1 := by
        rw [hc₀]
        have : L * Δ / (σ ^ 2 * T) * T ^ ((3 * p - 2) / p) = (L * Δ / σ ^ 2) * T ^ ((2 * p - 2) / p) := by
          have hTsplit : T ^ ((3 * p - 2) / p) = T * T ^ ((2 * p - 2) / p) := by
            rw [show (3 * p - 2) / p = 1 + (2 * p - 2) / p by field_simp; ring, Real.rpow_add hT0,
              Real.rpow_one]
          rw [hTsplit]; field_simp
        rw [this, ge_iff_le, ← div_le_iff₀' (by positivity)]
        rw [one_div, inv_div]
        exact hq
      have hpow : (c₀ * T ^ ((3 * p - 2) / p)) ^ r ≥ 1 := Real.one_le_rpow hcT hr.le
      rw [Real.mul_rpow hc₀pos.le (by positivity), ← Real.rpow_mul hT0.le,
        show (3 * p - 2) / p * r = 1 by rw [hr_def]; field_simp, Real.rpow_one] at hpow
      rw [div_le_iff₀ hT0]; linarith
    have hα : optMomentum L Δ σ p T = c₀ ^ r := by
      rw [hαdef, max_eq_right hcrT, min_eq_right hcr1]
    rw [hα]
    set w := c₀ ^ ((p - 1) / (3 * p - 2)) with hw
    have hw0 : 0 ≤ w := Real.rpow_nonneg hc₀pos.le _
    set M := σ * w with hM
    have hM0 : 0 ≤ M := mul_nonneg hσ hw0
    have hterm2 : (c₀ ^ r) ^ ((p - 1) / p) = w := by
      rw [hw, ← Real.rpow_mul hc₀pos.le, hr_def]
      congr 1
      linear_combination ((p - 1) / (3 * p - 2)) * hinvp
    have hM2 : M ^ 2 = σ ^ 2 * c₀ ^ (1 - r) := by
      rw [hM, mul_pow, hw, ← Real.rpow_natCast (c₀ ^ _), ← Real.rpow_mul hc₀pos.le, h1r]
      congr 2
      push_cast
      ring
    have hLΔ : L * Δ = c₀ * (σ ^ 2 * T) := by rw [hc₀]; field_simp
    have hval : 3 * L * Δ / (c₀ ^ r * T) = 3 * M ^ 2 := by
      rw [hM2, show 3 * L * Δ = 3 * (L * Δ) by ring, hLΔ, Real.rpow_sub hc₀pos, Real.rpow_one,
        div_eq_iff (by positivity)]
      have hcr : c₀ / c₀ ^ r * c₀ ^ r = c₀ := div_mul_cancel₀ _ (by positivity)
      linear_combination (-3 * σ ^ 2 * T) * hcr
    have hterm1 : Real.sqrt (3 * L * Δ / (c₀ ^ r * T)) = Real.sqrt 3 * M := by
      rw [hval, Real.sqrt_mul (by norm_num), Real.sqrt_sq hM0]
    have hMle : M ≤ ε / 80 := by
      have he_pos : 0 < (3 * p - 2) / (p - 1) := by positivity
      have hMpow : M ^ ((3 * p - 2) / (p - 1)) = σ ^ ((3 * p - 2) / (p - 1)) * c₀ := by
        rw [hM, Real.mul_rpow hσ hw0, hw, ← Real.rpow_mul hc₀pos.le, div_mul_div_comm,
          mul_comm (p - 1), div_self (by positivity), Real.rpow_one]
      have hσe : σ ^ ((3 * p - 2) / (p - 1)) = σ ^ (p / (p - 1)) * σ ^ 2 := by
        rw [← Real.rpow_two, ← Real.rpow_add hσpos]
        congr 1
        linear_combination 2 * hinv1
      have hε80 : (ε / 80) ^ ((3 * p - 2) / (p - 1)) =
          ((80 / ε) ^ ((3 * p - 2) / (p - 1)))⁻¹ := by
        rw [← Real.inv_rpow (by positivity), inv_div]
      have hu : L * Δ / (σ ^ 2 * T) * (σ ^ 2 * T) = L * Δ := div_mul_cancel₀ _ (by positivity)
      have hsplit : σ ^ (p / (p - 1)) * σ ^ 2 * (L * Δ / (σ ^ 2 * T)) *
          (80 / ε) ^ ((3 * p - 2) / (p - 1)) =
          (L * Δ * σ ^ (p / (p - 1)) * (80 / ε) ^ ((3 * p - 2) / (p - 1))) / T := by
        rw [eq_div_iff hT0.ne']
        linear_combination (σ ^ (p / (p - 1)) * (80 / ε) ^ ((3 * p - 2) / (p - 1))) * hu
      have hle : M ^ ((3 * p - 2) / (p - 1)) ≤ (ε / 80) ^ ((3 * p - 2) / (p - 1)) := by
        rw [hMpow, hσe, hε80, inv_eq_one_div, le_div_iff₀ (by positivity), hc₀, hsplit,
          div_le_one hT0]
        exact h2
      exact (Real.rpow_le_rpow_iff hM0 (by positivity) he_pos).1 hle
    have hIle : 12 * σ / (c₀ ^ r * T) ≤ ε / 5 := by
      have hbig : 60 * σ / ε ≤ c₀ ^ r * T := by
        have hT1r : (60 / ε) * σ ^ ((5 * p - 2) / (3 * p - 2)) * (L * Δ) ^ (-(p / (3 * p - 2))) ≤
            T ^ (1 - r) := by
          have := Real.rpow_le_rpow (by positivity) h3
            (by positivity : (0 : ℝ) ≤ (2 * p - 2) / (3 * p - 2))
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_mul hσ, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)] at this
          rw [h1r]
          have e1 : (5 * p - 2) / (2 * p - 2) * ((2 * p - 2) / (3 * p - 2)) =
              (5 * p - 2) / (3 * p - 2) := by
            linear_combination ((5 * p - 2) / (3 * p - 2)) * hinv2
          have e2 : -(p / (2 * p - 2)) * ((2 * p - 2) / (3 * p - 2)) = -(p / (3 * p - 2)) := by
            linear_combination (-(p / (3 * p - 2))) * hinv2
          have e3 : (3 * p - 2) / (2 * p - 2) * ((2 * p - 2) / (3 * p - 2)) = 1 := by
            linear_combination ((2 * p - 2) * (2 * p - 2)⁻¹) * hinv3 + hinv2
          rw [e1, e2, e3, Real.rpow_one] at this
          linarith [this]
        have hprod : c₀ ^ r * T = (L * Δ) ^ r * σ ^ (-(2 * r)) * T ^ (1 - r) := by
          rw [hc₀, Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) hT0.le,
            ← Real.rpow_natCast σ 2, ← Real.rpow_mul hσ, Real.rpow_sub hT0, Real.rpow_one]
          push_cast
          rw [Real.rpow_neg hσ]
          have : σ ^ ((2 : ℝ) * r) ≠ 0 := by positivity
          have : T ^ r ≠ 0 := by positivity
          field_simp
        rw [hprod]
        have hA : (L * Δ) ^ (p / (3 * p - 2)) * ((L * Δ) ^ (p / (3 * p - 2)))⁻¹ = 1 :=
          mul_inv_cancel₀ (by positivity)
        have hB : σ ^ (2 * (p / (3 * p - 2))) * (σ ^ (2 * (p / (3 * p - 2))))⁻¹ = 1 :=
          mul_inv_cancel₀ (by positivity)
        have hsplitσ : σ ^ ((5 * p - 2) / (3 * p - 2)) = σ * σ ^ (2 * (p / (3 * p - 2))) := by
          rw [show (5 * p - 2) / (3 * p - 2) = 1 + 2 * (p / (3 * p - 2)) by linear_combination hinv3,
            Real.rpow_add hσpos, Real.rpow_one]
        calc 60 * σ / ε = (L * Δ) ^ r * σ ^ (-(2 * r)) *
              ((60 / ε) * σ ^ ((5 * p - 2) / (3 * p - 2)) * (L * Δ) ^ (-(p / (3 * p - 2)))) := by
              rw [hr_def, Real.rpow_neg (by positivity : (0 : ℝ) ≤ L * Δ), Real.rpow_neg hσ, hsplitσ]
              linear_combination
                (-(60 * σ / ε) * (σ ^ (2 * (p / (3 * p - 2))) * (σ ^ (2 * (p / (3 * p - 2))))⁻¹)) * hA +
                (-(60 * σ / ε)) * hB
          _ ≤ (L * Δ) ^ r * σ ^ (-(2 * r)) * T ^ (1 - r) := by
              gcongr
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ hε] at hbig
      nlinarith
    rw [hterm1, hterm2]
    have hsqrt3 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have ht1 : Real.exp (1 / 2) * (2 * (Real.sqrt 3 * M)) ≤ ε / 5 := by
      calc Real.exp (1 / 2) * (2 * (Real.sqrt 3 * M)) ≤ 2 * (2 * (2 * (ε / 80))) := by gcongr
        _ ≤ ε / 5 := by linarith
    have ht2 : 12 * Real.exp (1 / 4) * σ * w ≤ ε / 5 := by
      calc 12 * Real.exp (1 / 4) * σ * w = 12 * Real.exp (1 / 4) * M := by rw [hM]; ring
        _ ≤ 12 * (13 / 10) * (ε / 80) := by gcongr
        _ ≤ ε / 5 := by linarith
    linarith


noncomputable def levelStar (L Δ σ p ε : ℝ) : ℕ :=
  ⌈max (Real.logb 2 (mainThreshold L Δ σ p ε)) (levelK σ p ε)⌉₊

lemma mainThreshold_pos {L Δ σ p ε : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hp : 1 < p)
    (hε : 0 < ε) : 1 ≤ mainThreshold L Δ σ p ε := by
  unfold mainThreshold
  have hp1 : 0 < p - 1 := by linarith
  have : 0 ≤ 8000 * L * Δ / ε ^ 2 + L * Δ * σ ^ (p / (p - 1)) * (80 / ε) ^ ((3 * p - 2) / (p - 1)) +
      σ ^ ((5 * p - 2) / (2 * p - 2)) * (L * Δ) ^ (-(p / (2 * p - 2))) *
        (60 / ε) ^ ((3 * p - 2) / (2 * p - 2)) +
      (σ ^ 2 / (L * Δ)) ^ (p / (2 * p - 2)) + Real.sqrt (3 * L / Δ) + (Δ / (3 * L)) ^ ((1 : ℝ) / 3) +
      6 ^ ((1 : ℝ) / (p - 1)) * (5 * σ / ε) ^ (p / (p - 1)) := by positivity
  linarith

lemma twoPow_ge_of_level {L Δ σ p ε : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hp : 1 < p)
    (hε : 0 < ε) {k : ℕ} (hk : levelStar L Δ σ p ε ≤ k) :
    mainThreshold L Δ σ p ε ≤ (2 : ℝ) ^ k ∧ levelK σ p ε ≤ k := by
  have hS := mainThreshold_pos hL hΔ hσ hp hε
  have hceil : max (Real.logb 2 (mainThreshold L Δ σ p ε)) (levelK σ p ε) ≤ k := by
    have h := Nat.le_ceil (max (Real.logb 2 (mainThreshold L Δ σ p ε)) (levelK σ p ε))
    have hk' : ((levelStar L Δ σ p ε : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    unfold levelStar at hk'
    linarith
  constructor
  · have hlog : Real.logb 2 (mainThreshold L Δ σ p ε) ≤ k := le_trans (le_max_left _ _) hceil
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hlog
    rw [Real.rpow_logb (by norm_num) (by norm_num) (by linarith), Real.rpow_natCast] at this
    exact this
  · exact le_trans (le_max_right _ _) hceil

lemma twoPow_levelK_le {σ p ε : ℝ} (hσ : 0 ≤ σ) (hp : 1 < p) (hp2 : p ≤ 2) (hε : 0 < ε) :
    (2 : ℝ) ^ (levelK σ p ε) ≤ countThreshold σ p ε := by
  have hp1 : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have hpos : 0 < 1 + 5 * σ / ε := by positivity
  have hlogσ : 0 ≤ Real.logb 2 (1 + 5 * σ / ε) := Real.logb_nonneg (by norm_num) (by
    have : 0 ≤ 5 * σ / ε := by positivity
    linarith)
  set ℓ := Real.logb 2 (1 + 5 * σ / ε) with hℓ
  set q := 2 / (p - 1) with hq
  have hA : levelA σ p ε = (6 + p * ℓ) / (p - 1) := rfl
  have hx1 : 1 ≤ (p - 1)⁻¹ := (one_le_inv₀ hp1).2 (by linarith)
  have hY : 2 * levelA σ p ε + 4 * q + 2 ≤ (22 + 2 * p * ℓ) / (p - 1) := by
    rw [hA, hq]
    simp only [div_eq_mul_inv]
    nlinarith [hx1]
  have hYpos : 0 < 2 * levelA σ p ε + 4 * q + 2 := by rw [hA]; positivity
  unfold levelK countThreshold
  rw [← hq, Real.rpow_add (by norm_num), Real.mul_rpow (by positivity) (by positivity)]
  have hfirst : (2 : ℝ) ^ (levelA σ p ε) = (64 * (1 + 5 * σ / ε) ^ p) ^ ((1 : ℝ) / (p - 1)) := by
    rw [hA, Real.mul_rpow (by norm_num) (by positivity),
      show (64 : ℝ) = 2 ^ (6 : ℝ) by
        rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num,
      ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hpos.le,
      show (1 + 5 * σ / ε) = 2 ^ ℓ by rw [hℓ, Real.rpow_logb (by norm_num) (by norm_num) hpos],
      ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hsecond : (2 : ℝ) ^ (2 * q * Real.logb 2 (2 * levelA σ p ε + 4 * q + 2)) ≤
      (((22 + 2 * p * ℓ) / (p - 1)) ^ 4) ^ ((1 : ℝ) / (p - 1)) := by
    rw [show 2 * q * Real.logb 2 (2 * levelA σ p ε + 4 * q + 2) =
      Real.logb 2 (2 * levelA σ p ε + 4 * q + 2) * (2 * q) by ring, Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hYpos, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    have hexp : ((4 : ℕ) : ℝ) * ((1 : ℝ) / (p - 1)) = 2 * q := by rw [hq]; push_cast; ring
    rw [hexp]
    exact Real.rpow_le_rpow hYpos.le hY (by positivity)
  rw [hfirst]
  exact mul_le_mul_of_nonneg_left hsecond (by positivity)

noncomputable def budgetReal (L Δ σ p ε : ℝ) : ℝ :=
  80 * (2 + Real.logb 2 (mainThreshold L Δ σ p ε + countThreshold σ p ε)) ^ 2 *
    (mainThreshold L Δ σ p ε + countThreshold σ p ε)

lemma phaseStart_le_budget {L Δ σ p ε : ℝ} (hL : 0 < L) (hΔ : 0 < Δ) (hσ : 0 ≤ σ) (hp : 1 < p)
    (hp2 : p ≤ 2) (hε : 0 < ε) :
    (phaseStart (levelStar L Δ σ p ε + 1) : ℝ) ≤ budgetReal L Δ σ p ε := by
  set K := levelStar L Δ σ p ε with hK
  set S := mainThreshold L Δ σ p ε with hS
  set V := countThreshold σ p ε with hV
  have hS1 := mainThreshold_pos hL hΔ hσ hp hε
  have hV0 : 0 ≤ V := by rw [hV]; unfold countThreshold; positivity
  have hlogS : 0 ≤ Real.logb 2 S := Real.logb_nonneg (by norm_num) hS1
  have hlevelK0 : 0 ≤ levelK σ p ε := by
    unfold levelK levelA
    have hp1 : 0 < p - 1 := by linarith
    have hp0 : 0 < p := by linarith
    have : 0 ≤ Real.logb 2 (1 + 5 * σ / ε) := Real.logb_nonneg (by norm_num) (by
      have : 0 ≤ 5 * σ / ε := by positivity
      linarith)
    have h2 : 0 ≤ Real.logb 2 (2 * ((6 + p * Real.logb 2 (1 + 5 * σ / ε)) / (p - 1)) +
        4 * (2 / (p - 1)) + 2) :=
      Real.logb_nonneg (by norm_num) (by
        have : 0 ≤ 2 * ((6 + p * Real.logb 2 (1 + 5 * σ / ε)) / (p - 1)) + 4 * (2 / (p - 1)) := by
          positivity
        linarith)
    positivity
  have hKle : (K : ℝ) ≤ max (Real.logb 2 S) (levelK σ p ε) + 1 := by
    rw [hK]; unfold levelStar
    have := Nat.ceil_lt_add_one (le_max_of_le_left hlogS : 0 ≤ max (Real.logb 2 S) (levelK σ p ε))
    exact this.le
  have h2K : (2 : ℝ) ^ K ≤ 2 * (S + V) := by
    have : (2 : ℝ) ^ K = 2 ^ (K : ℝ) := by rw [Real.rpow_natCast]
    rw [this]
    calc (2 : ℝ) ^ (K : ℝ) ≤ 2 ^ (max (Real.logb 2 S) (levelK σ p ε) + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hKle
      _ = 2 * 2 ^ (max (Real.logb 2 S) (levelK σ p ε)) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
      _ ≤ 2 * (S + V) := by
          gcongr
          rcases le_total (Real.logb 2 S) (levelK σ p ε) with h | h
          · rw [max_eq_right h]
            exact (twoPow_levelK_le hσ hp hp2 hε).trans (by linarith)
          · rw [max_eq_left h, Real.rpow_logb (by norm_num) (by norm_num) (by linarith)]
            linarith
  have hK1 : (K : ℝ) + 1 ≤ 2 + Real.logb 2 (S + V) := by
    have hlogV : levelK σ p ε ≤ Real.logb 2 V := by
      have := twoPow_levelK_le hσ hp hp2 hε
      have hVpos : 0 < V := lt_of_lt_of_le (by positivity) this
      calc levelK σ p ε = Real.logb 2 (2 ^ levelK σ p ε) := by
            rw [Real.logb_rpow (by norm_num) (by norm_num)]
        _ ≤ Real.logb 2 V := Real.logb_le_logb_of_le (by norm_num) (by positivity) this
    have hmax : max (Real.logb 2 S) (levelK σ p ε) ≤ Real.logb 2 (S + V) := by
      apply max_le
      · exact Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
      · exact hlogV.trans (Real.logb_le_logb_of_le (by norm_num)
          (lt_of_lt_of_le (by positivity) (twoPow_levelK_le hσ hp hp2 hε)) (by linarith))
    linarith
  have hlogSV : 0 ≤ Real.logb 2 (S + V) := Real.logb_nonneg (by norm_num) (by linarith)
  calc (phaseStart (K + 1) : ℝ) ≤ 40 * ((K : ℝ) + 1) ^ 2 * 2 ^ K := phaseStart_le K
    _ ≤ 40 * (2 + Real.logb 2 (S + V)) ^ 2 * (2 * (S + V)) := by gcongr
    _ = budgetReal L Δ σ p ε := by rw [budgetReal, ← hS, ← hV]; ring

end LongTails.Proofs.ParameterFreeNsgdmBudget
