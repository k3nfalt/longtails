import LongTails.Proofs.FullRangeEstimator
import LongTails.Algorithms.FullRangeProgram
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory
open scoped BigOperators ENNReal

namespace LongTails.Proofs.FullRangeSeed

open LongTails.Algorithms.FullRangeMlmc LongTails.Algorithms.FullRangeProgram
open LongTails.Proofs.FullRangeEstimator

lemma exp_le_one_add_two {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1 + 2 * x := by
  have hc := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ 1) (show 0 ≤ 1 - x by linarith) h0
    (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, Real.exp_zero] at hc
  have he : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  nlinarith

lemma level_exp_bound (top : ℕ) :
    (∫ l, Real.exp ((2 : ℝ) ^ ((l : Fin (top + 1)) : ℕ) / (2 : ℝ) ^ top) ∂levelLaw top) ≤
      Real.exp (2 * (top + 1) / (2 : ℝ) ^ top) := by
  rw [integral_levelLaw]
  have hpt (l : Fin (top + 1)) : Real.exp ((2 : ℝ) ^ (l : ℕ) / (2 : ℝ) ^ top) ≤
      1 + 2 * ((2 : ℝ) ^ (l : ℕ) / (2 : ℝ) ^ top) := by
    apply exp_le_one_add_two (by positivity)
    rw [div_le_one (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hw (l : Fin (top + 1)) := (levelWeight_pos top l).le
  calc ∑ l : Fin (top + 1), levelWeight top (l : ℕ) • Real.exp ((2 : ℝ) ^ (l : ℕ) / (2 : ℝ) ^ top)
      ≤ ∑ l : Fin (top + 1), levelWeight top (l : ℕ) * (1 + 2 * ((2 : ℝ) ^ (l : ℕ) / (2 : ℝ) ^ top)) :=
        Finset.sum_le_sum fun l _ => by rw [smul_eq_mul]; exact mul_le_mul_of_nonneg_left (hpt l) (hw l)
    _ = 1 + 2 / (2 : ℝ) ^ top * ∑ l : Fin (top + 1), levelWeight top (l : ℕ) * (2 : ℝ) ^ (l : ℕ) := by
        rw [Finset.mul_sum]
        simp only [mul_add, mul_one, Finset.sum_add_distrib, levelWeight_sum]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
    _ ≤ 1 + 2 * (top + 1) / (2 : ℝ) ^ top := by
        have hsum : ∑ l : Fin (top + 1), levelWeight top (l : ℕ) * (2 : ℝ) ^ (l : ℕ) ≤ top + 1 := by
          have hb (l : Fin (top + 1)) : levelWeight top (l : ℕ) * (2 : ℝ) ^ (l : ℕ) ≤ 1 := by
            unfold levelWeight
            split_ifs with h
            · rw [h, pow_zero, mul_one, div_le_one (by positivity)]
              exact one_le_pow₀ (by norm_num)
            · rw [one_div, inv_mul_cancel₀ (by positivity)]
          calc _ ≤ ∑ _l : Fin (top + 1), (1 : ℝ) := Finset.sum_le_sum fun l _ => hb l
            _ = top + 1 := by simp
        have := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2 / (2 : ℝ) ^ top by positivity)
        have e : 2 / (2 : ℝ) ^ top * (top + 1) = 2 * (top + 1) / (2 : ℝ) ^ top := by ring
        linarith
    _ ≤ _ := by
        have := Real.add_one_le_exp (2 * (top + 1) / (2 : ℝ) ^ top)
        linarith

theorem seed_tail (K top n0 : ℕ) {d : ℝ} (hd : 0 < d) :
    (Measure.pi fun _ : Fin K => levelLaw top) {ℓ | 2 * n0 * (2 * K * (top + 1) +
      2 ^ top * (⌈Real.log (1 / d)⌉₊ + 1)) < seedCost n0 ℓ} ≤ ENNReal.ofReal d := by
  let μ := Measure.pi fun _ : Fin K => levelLaw top
  let M : ℝ := (2 : ℝ) ^ top
  have hM : 0 < M := by positivity
  let X : (Fin K → Fin (top + 1)) → ℝ := fun ℓ => ∑ i, (2 : ℝ) ^ ((ℓ i : ℕ)) / M
  let Nd : ℝ := (⌈Real.log (1 / d)⌉₊ : ℝ) + 1
  let t : ℝ := 2 * K * (top + 1) / M + Nd
  have hsub : {ℓ : Fin K → Fin (top + 1) | 2 * n0 * (2 * K * (top + 1) +
      2 ^ top * (⌈Real.log (1 / d)⌉₊ + 1)) < seedCost n0 ℓ} ⊆ {ℓ | Real.exp t ≤ Real.exp (X ℓ)} := by
    intro ℓ hℓ
    simp only [Set.mem_ofPred_eq] at hℓ ⊢
    apply Real.exp_le_exp.mpr
    unfold seedCost levelCost levelTime at hℓ
    have hn0 : 0 < n0 := by
      rcases Nat.eq_zero_or_pos n0 with h | h
      · subst h
        simp at hℓ
      · exact h
    have hc : ((2 * n0 * (2 * K * (top + 1) + 2 ^ top * (⌈Real.log (1 / d)⌉₊ + 1)) : ℕ) : ℝ) <
        ((∑ i, 2 * (n0 * 2 ^ ((ℓ i : ℕ))) : ℕ) : ℝ) := by exact_mod_cast hℓ
    push_cast at hc
    have hsum : (∑ i : Fin K, 2 * ((n0 : ℝ) * (2 : ℝ) ^ ((ℓ i : ℕ)))) =
        2 * n0 * ∑ i : Fin K, (2 : ℝ) ^ ((ℓ i : ℕ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hsum] at hc
    have hpos : (0 : ℝ) < 2 * n0 := by positivity
    have hc2 : 2 * K * (top + 1) + (2 : ℝ) ^ top * Nd < ∑ i : Fin K, (2 : ℝ) ^ ((ℓ i : ℕ)) := by
      have := lt_of_mul_lt_mul_left hc hpos.le
      simpa only [Nd] using this
    have hX : X ℓ = (∑ i : Fin K, (2 : ℝ) ^ ((ℓ i : ℕ))) / M := by
      simp only [X, Finset.sum_div]
    rw [hX]
    have : t = (2 * K * (top + 1) + M * Nd) / M := by
      simp only [t]
      field_simp
    rw [this]
    exact (div_le_div_iff_of_pos_right hM).mpr hc2.le
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ) (Filter.Eventually.of_forall fun ℓ =>
    (Real.exp_pos (X ℓ)).le) Integrable.of_finite (Real.exp t)
  have hprod : (∫ ℓ, Real.exp (X ℓ) ∂μ) =
      ∏ _i : Fin K, ∫ l, Real.exp ((2 : ℝ) ^ ((l : Fin (top + 1)) : ℕ) / M) ∂levelLaw top := by
    have : (fun ℓ : Fin K → Fin (top + 1) => Real.exp (X ℓ)) =
        fun ℓ => ∏ i, Real.exp ((2 : ℝ) ^ ((ℓ i : ℕ)) / M) := by
      funext ℓ
      simp only [X, Real.exp_sum]
    rw [this]
    exact integral_fintype_prod_eq_prod (fun _ l => Real.exp ((2 : ℝ) ^ ((l : Fin (top + 1)) : ℕ) / M))
  have hlev := level_exp_bound top
  have hnn : 0 ≤ ∫ l, Real.exp ((2 : ℝ) ^ ((l : Fin (top + 1)) : ℕ) / M) ∂levelLaw top :=
    integral_nonneg fun _ => (Real.exp_pos _).le
  have hpow : (∫ ℓ, Real.exp (X ℓ) ∂μ) ≤ Real.exp (2 * (top + 1) / M) ^ K := by
    rw [hprod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ hnn hlev K
  have hreal : μ.real {ℓ | Real.exp t ≤ Real.exp (X ℓ)} ≤ d := by
    have h1 : Real.exp t * μ.real {ℓ | Real.exp t ≤ Real.exp (X ℓ)} ≤ Real.exp (2 * (top + 1) / M) ^ K :=
      hmk.trans hpow
    have h2 : Real.exp (2 * (top + 1) / M) ^ K = Real.exp (2 * K * (top + 1) / M) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [h2] at h1
    have h3 : Real.exp (2 * K * (top + 1) / M) = Real.exp t * Real.exp (-Nd) := by
      rw [← Real.exp_add]
      congr 1
      simp only [t]
      ring
    rw [h3] at h1
    have h4 := le_of_mul_le_mul_left h1 (Real.exp_pos t)
    have h5 : Real.exp (-Nd) ≤ d := by
      have hl : Real.log (1 / d) ≤ Nd := by
        have := Nat.le_ceil (Real.log (1 / d))
        simp only [Nd]
        linarith
      have : Real.exp (-Nd) ≤ Real.exp (-Real.log (1 / d)) := Real.exp_le_exp.mpr (by linarith)
      rwa [Real.log_div (by norm_num) hd.ne', Real.log_one, zero_sub, neg_neg, Real.exp_log hd] at this
    linarith
  calc μ _ ≤ μ {ℓ | Real.exp t ≤ Real.exp (X ℓ)} := measure_mono hsub
    _ = ENNReal.ofReal (μ.real {ℓ | Real.exp t ≤ Real.exp (X ℓ)}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal d := ENNReal.ofReal_le_ofReal hreal

end LongTails.Proofs.FullRangeSeed
