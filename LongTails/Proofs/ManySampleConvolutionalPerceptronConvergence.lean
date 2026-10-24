import LongTails.Proofs.ManySampleConvolutionalPerceptronExecution
import LongTails.Proofs.ManySampleConvolutionalPerceptronBudget

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronConvergence

open LongTails.Setups.ManySampleConvolutionalPerceptron
open LongTails.Algorithms.ManySampleConvolutionalPerceptron
open ManySampleConvolutionalPerceptronParameters
open ManySampleConvolutionalPerceptronGeometry
open ManySampleConvolutionalPerceptronTrajectory
open ManySampleConvolutionalPerceptronExecution

noncomputable def tuning (p : Params) (hp : spec.valid p) : Tuning where
  ρ := p.lower / (4 * p.upper)
  δ := (p.contrast / (4 * p.upper)) ^ 2
  κ := p.derivativeMargin
  rho_pos := by
    have hg : 0 < p.lower := hp.2.2.1
    have : 0 < p.upper := hg.trans_le hp.2.2.2.1
    positivity
  rho_le := by
    have h := hp.2.2
    have hR : 0 < p.upper := h.1.trans_le h.2.1
    apply (div_le_iff₀ (by positivity : 0 < 4 * p.upper)).mpr
    linarith [h.2.1]
  delta_pos := by
    have h := hp.2.2
    have : 0 < p.upper := h.1.trans_le h.2.1
    have : 0 < p.contrast := h.2.2.1
    positivity
  delta_le := hp.2.2.2.2.2.2.2.1
  kappa_pos := hp.2.2.2.2.2.1
  kappa_le := hp.2.2.2.2.2.2.1
  small_cubic := hp.2.2.2.2.2.2.2.2.1
  small_quadratic := hp.2.2.2.2.2.2.2.2.2

lemma tuned_iterate (p : Params) (hp : spec.valid p) {D : Data p.dimension p.samples}
    (G : Geometry D p.lower p.upper p.contrast p.derivativeMargin)
    {Q : ℕ} (hQ : ((tuning p hp).negatives + 1) *
      (p.samples + 1 + (tuning p hp).referenceLength) ≤ Q) :
    Separates D (((step D (1 / (4 * p.upper)) ((p.contrast / (4 * p.upper)) ^ 4))^[Q]
      ⟨((Real.sqrt 2, 0), 0), 0⟩).point) := by
  have hg : 0 < p.lower := hp.2.2.1
  have hR : 0 < p.upper := hg.trans_le hp.2.2.2.1
  have hη : 0 < 1 / (4 * p.upper) := by positivity
  apply iterate_separates G (tuning p hp) hp.1 hg hη
    (by simp only [gains, tuning]; ring)
    (by simp only [gains, tuning]; ring)
    (plus_norm G) (minus_norm G) G.derivative_margin ?_ ?_ hQ
  · intro j
    cases j with
    | none =>
      change p.lower / (4 * p.upper) ≤ 1 / (4 * p.upper) * G.referenceScale
      have := mul_le_mul_of_nonneg_left G.reference_lower hη.le
      simpa only [one_div_mul_eq_div] using this
    | some i =>
      change p.lower / (4 * p.upper) ≤ 1 / (4 * p.upper) * G.background i
      have := mul_le_mul_of_nonneg_left (G.background_lower i) hη.le
      simpa only [one_div_mul_eq_div] using this
  · intro j
    have hu : 1 / (4 * p.upper) * p.upper = 1 / 4 := by field_simp
    cases j with
    | none =>
      change 1 / (4 * p.upper) * G.referenceScale ≤ 1 / 2
      have := mul_le_mul_of_nonneg_left G.reference_upper hη.le
      linarith
    | some i =>
      change 1 / (4 * p.upper) * G.background i ≤ 1 / 2
      have := mul_le_mul_of_nonneg_left (G.background_upper i) hη.le
      linarith

lemma public_budget_suffices (p : Params) (hp : spec.valid p) :
    ((tuning p hp).negatives + 1) * (p.samples + 1 + (tuning p hp).referenceLength) ≤
      ⌈34359738368 * (p.upper / p.lower) ^ 4 *
        (Real.log (16 * p.upper ^ 2 / p.contrast ^ 2)) ^ 2 *
        (p.samples + 1 + (p.upper / p.lower) * Real.log (16 * p.upper ^ 2 / p.contrast ^ 2)) /
        p.derivativeMargin ^ 2⌉₊ := by
  have hg : 0 < p.lower := hp.2.2.1
  have hR : 0 < p.upper := hg.trans_le hp.2.2.2.1
  have hb := ManySampleConvolutionalPerceptronBudget.scaled_block_budget
    (tuning p hp) (p.samples + 1) hg hR hp.2.2.2.2.1 rfl rfl
  simp only [Nat.cast_add, Nat.cast_one] at hb
  apply Nat.le_of_lt_succ
  have hceil := Nat.le_ceil (34359738368 * (p.upper / p.lower) ^ 4 *
    (Real.log (16 * p.upper ^ 2 / p.contrast ^ 2)) ^ 2 *
    (p.samples + 1 + (p.upper / p.lower) * Real.log (16 * p.upper ^ 2 / p.contrast ^ 2)) /
    p.derivativeMargin ^ 2)
  have hh : (((tuning p hp).negatives + 1) *
      (p.samples + 1 + (tuning p hp).referenceLength) : ℝ) ≤ _ := hb.trans hceil
  exact_mod_cast lt_of_le_of_lt hh (lt_add_one _)

end LongTails.Proofs.ManySampleConvolutionalPerceptronConvergence
