import LongTails.Proofs.AdditiveFixedPointBlocks
import LongTails.Proofs.AdditiveFixedPointLowerBudget

open MeasureTheory
open scoped ENNReal

namespace LongTails.Proofs.AdditiveFixedPointHardness

open AdditiveFixedPointBlocks AdditiveFixedPointTesting AdditiveFixedPointProcess
open AdditiveFixedPointFamily AdditiveFixedPointNoise AdditiveFixedPointLowerBudget
open LongTails.Setups.AdditiveCubeFixedPoint

variable {p : Params} {S : Type*} [MeasurableSpace S]

lemma short_chain (π : ProbabilityMeasure S) {query output : S → Cube p} {update : S → Point p → S}
    (hq : Measurable query) (ho : Measurable output) (hu : Measurable update.uncurry)
    (he : 0 < p.ε) {b : ℕ} (hb : b < capacity p) :
    ∃ t : ℕ → Bool, risk π (law (variance p) 0)
      (step query update (by positivity : 0 ≤ 8 * p.ε) t 1)
      (test (fun x => guess 0 1 (output x) 0) (t 0)) b ≤ 3 / 4 := by
  let s : ℕ → Bool := fun _ => false
  let g := fun x => guess 0 1 (output x) 0
  have hg : Measurable g := (measurable_pi_apply 0).comp ((guess_measurable 0 1).comp ho)
  have hh : 0 ≤ 8 * p.ε := by positivity
  let v := variance p
  let base := step query update hh s 0
  obtain ⟨w, hw⟩ := rare_word hg (n := 1) (fun _ => stateLaw π (law v 0) base b)
  have hw' : risk π (law v 0) base (test g w) b ≤ 1 / 2 := by simpa [risk] using hw
  let t : ℕ → Bool := fun _ => w
  refine ⟨t, ?_⟩
  let next := step query update hh t 1
  change risk π (law v 0) next (test g w) b ≤ 3 / 4
  have ht := test_measurable hg w
  have hbase := step_measurable hq hu hh s 0
  have hnext := step_measurable hq hu hh t 1
  by_cases h0 : b = 0
  · subst b
    rw [risk, stateLaw_integral π _ hnext ht]
    rw [risk, stateLaw_integral π _ hbase ht] at hw'
    simp only [AdditiveFixedPointProcess.average_zero] at *
    exact hw'.trans (by apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp; norm_num)
  obtain ⟨hv, hen⟩ := capacity_energy p he (by omega) hb.le
  let B := (16 * p.ε)^2 / (v : ℝ)
  have hsame : map (p := p) hh t 0 = map hh s 0 := map_congr hh (by simp)
  have hgap (x : S) : ∑ i, ((map hh t 1 (query x)).val i -
      (map hh s 0 (query x)).val i)^2 / (v : ℝ) ≤ B := by
    rw [← hsame]
    simpa [B, show 2 * (8 * p.ε) = 16 * p.ε by ring] using
      block_energy hh t (show 0 ≤ 1 by decide) (query x)
        (show 0 < (v : ℝ) by exact_mod_cast pos_iff_ne_zero.mpr hv)
  have hsq := integrated_compare π hv (mean_measurable hq hh s 0) (mean_measurable hq hh t 1)
    hu ht (test_sq g w) hgap b
  have hr : risk π (law v 0) next (test g w) b ^ 2 ≤ ENNReal.ofReal (Real.exp B) ^ b *
      risk π (law v 0) base (test g w) b := by
    unfold risk
    rw [stateLaw_integral π _ hnext ht, stateLaw_integral π _ hbase ht]
    exact hsq
  have hex : Real.exp ((b : ℝ) * B) ≤ 9 / 8 := (Real.exp_le_exp.mpr hen).trans
    ((Real.exp_bound_div_one_sub_of_interval (by norm_num : (0:ℝ) ≤ 1/16) (by norm_num)).trans (by norm_num))
  have hfac : ENNReal.ofReal (Real.exp B) ^ b ≤ 9 / 8 := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos B).le, ← Real.exp_nat_mul]
    simpa [ENNReal.ofReal_div_of_pos] using ENNReal.ofReal_le_ofReal hex
  have hfin : risk π (law v 0) next (test g w) b ^ 2 ≤ (3 / 4 : ℝ≥0∞)^2 :=
    hr.trans ((mul_le_mul' hfac hw').trans (by apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp; norm_num))
  simpa only [AdditiveFixedPointGaussian.half_pow_square] using
    ENNReal.rpow_le_rpow hfin (by norm_num : (0 : ℝ) ≤ 1 / 2)

lemma hidden_output (π : ProbabilityMeasure S) {query output : S → Cube p} {update : S → Point p → S}
    (hq : Measurable query) (ho : Measurable output) (hu : Measurable update.uncurry)
    (hd : 0 < p.d) (he : 0 < p.ε) (hs : 0 ≤ p.σ) (hr : 128 * p.ε ≤ p.R)
    (hdim : ⌈p.R / p.ε⌉₊ ≤ p.d) {b : ℕ}
    (hb : b ≤ ⌊(1 + (p.σ / p.ε) ^ 2 / (2 + Real.log p.d)) *
      max 1 ((p.R / p.ε) / (1 + Real.log (2 + ((p.R : ℝ) + p.σ) / p.ε))) / 67108864⌋₊) :
    ∃ (L : ℕ) (t : ℕ → Bool), L + 1 ≤ p.d ∧ ((L + 1 : ℕ) : ℝ) * (6 * p.ε) < p.R ∧
      risk π (law (variance p) 0) (step query update (by positivity : 0 ≤ 8 * p.ε) t (L + 1))
        (test (fun x => guess L 1 (output x) 0) (t L)) b ≤ 3 / 4 := by
  by_cases hc : b < capacity p
  · obtain ⟨t, ht⟩ := short_chain π hq ho hu he hc
    exact ⟨0, t, hd, by push_cast; linarith, ht⟩
  let bs := chunks b (capacity p)
  let L := bs.length * width b
  have hdlog := Real.log_nonneg (show (1 : ℝ) ≤ p.d by exact_mod_cast hd)
  let H := 1 + Real.log (2 + ((p.R : ℝ) + p.σ) / p.ε)
  let J := 1 + (p.σ / p.ε) ^ 2 / (2 + Real.log p.d)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hbig : 1 ≤ (p.R / p.ε) / H := by
    by_contra! hsmall
    change b ≤ ⌊J * max 1 ((p.R / p.ε) / H) / 67108864⌋₊ at hb
    rw [max_eq_left hsmall.le, mul_one] at hb
    have hb' : (b : ℝ) ≤ J / 67108864 := (Nat.cast_le.mpr hb).trans (Nat.floor_le (by positivity))
    have hcap : (capacity p : ℝ) ≤ b := by exact_mod_cast le_of_not_gt hc
    have hpos : 0 < (capacity p : ℝ) := by exact_mod_cast capacity_pos p
    have hcap' : J ≤ 32769 * (capacity p : ℝ) := capacity_lower p hd he
    linarith
  change b ≤ ⌊J * max 1 ((p.R / p.ε) / H) / 67108864⌋₊ at hb
  rw [max_eq_right hbig] at hb
  have hL : (L : ℝ) ≤ p.R / p.ε / 8 := by
    apply chain_size p hd he hs hr (by omega)
    convert hb using 2
    change (p.R / p.ε) * J / (67108864 * H) = J * (p.R / p.ε / H) / 67108864
    rw [div_mul_eq_div_div]
    ring
  have hL' : (L : ℝ) * p.ε ≤ p.R / 8 := by
    apply (le_div_iff₀ he).mp
    convert hL using 1
    ring
  have hrad : ((L + 1 : ℕ) : ℝ) * (6 * p.ε) < p.R := by push_cast; linarith
  have hdim' : L + 1 ≤ p.d := by
    apply le_trans _ hdim
    apply (Nat.cast_le (α := ℝ)).mp
    apply le_trans _ (Nat.le_ceil _)
    rw [le_div_iff₀ he]
    push_cast
    linarith
  have hh : 0 ≤ 8 * p.ε := by positivity
  obtain ⟨t, _, ht⟩ := choose_signs π hq ho hu hh (fun _ => false) 0 (width b) (variance p)
    (tolerance b) bs (fun _ hn => phase_condition p he (by omega) hn)
  simp only [zero_add] at ht
  rw [show bs.sum = b from chunks_sum _ _] at ht
  refine ⟨L, t, hdim', hrad, ht.trans ?_⟩
  have htol : (b : ℝ≥0∞) * tolerance b ≤ 1 / 8 := by
    have h' : (b : ℝ) * (1 / (8 * ((b : ℝ) + 1))) ≤ 1 / 8 := by
      field_simp
      linarith
    simpa [tolerance, ENNReal.ofReal_mul, ENNReal.ofReal_div_of_pos] using ENNReal.ofReal_le_ofReal h'
  exact (add_le_add (le_refl (1/2 : ℝ≥0∞)) htol).trans (by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num)

end LongTails.Proofs.AdditiveFixedPointHardness
