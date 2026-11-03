import LongTails.Proofs.DerivativePerceptronExecution

namespace LongTails.Proofs.DerivativeConvolutionalPerceptronConvergence

open LongTails.Setups.DerivativeConvolutionalPerceptron
open LongTails.Algorithms.DerivativeConvolutionalPerceptron
open DerivativePerceptronGeometry DerivativePerceptronExecution

lemma upper_pos (p : Params) (hp : spec.valid p) : 0 < p.upper := hp.2.1.trans_le hp.2.2.1

noncomputable def tuning (p : Params) (hp : spec.valid p) : DerivativePerceptronParameters.Tuning where
  κ := p.derivativeMargin
  r := p.lower / p.upper
  x := p.contrast / p.upper
  margin_pos := hp.2.2.2.2.1
  margin_le := hp.2.2.2.2.2.1
  ratio_pos := div_pos hp.2.1 (upper_pos p hp)
  ratio_le := (div_le_one (upper_pos p hp)).mpr hp.2.2.1
  contrast_pos := div_pos hp.2.2.2.1 (upper_pos p hp)
  contrast_le := hp.2.2.2.2.2.2

lemma stepSize_eq (p : Params) (hp : spec.valid p) :
    stepSize p = (tuning p hp).stepScale / p.upper := by
  unfold stepSize DerivativePerceptronParameters.Tuning.stepScale tuning
  field_simp

lemma stepSize_pos (p : Params) (hp : spec.valid p) : 0 < stepSize p := by
  rw [stepSize_eq p hp]
  exact div_pos (tuning p hp).stepScale_pos (upper_pos p hp)

lemma residualScale_eq (p : Params) (hp : spec.valid p) :
    (tuning p hp).residualScale = (stepSize p * p.contrast) ^ 2 := by
  rw [stepSize_eq p hp]
  change (tuning p hp).stepScale ^ 2 * (p.contrast / p.upper) ^ 2 = _
  ring

lemma backgroundScale_eq (p : Params) (hp : spec.valid p) :
    (tuning p hp).backgroundScale = stepSize p * p.lower := by
  rw [stepSize_eq p hp]
  change p.lower / p.upper * (tuning p hp).stepScale = _
  ring

lemma stepScale_eq (p : Params) (hp : spec.valid p) :
    (tuning p hp).stepScale = stepSize p * p.upper := by
  rw [stepSize_eq p hp, div_mul_cancel₀ _ (ne_of_gt (upper_pos p hp))]

set_option maxRecDepth 4096 in
lemma budget_eq (p : Params) (hp : spec.valid p) :
    (tuning p hp).iterations =
      ⌈2 ^ 140 * p.upper ^ 10 / (p.derivativeMargin ^ 8 * p.lower ^ 10) *
        (1 + Real.log (p.upper / p.contrast))⌉₊ := by
  change ⌈2 ^ 140 / (p.derivativeMargin ^ 8 * (p.lower / p.upper) ^ 10) *
    (1 + Real.log (1 / (p.contrast / p.upper)))⌉₊ = _
  congr 1
  rw [one_div_div]
  congr 1
  field_simp

lemma output_eq_iterate (p : Params) (D : Data p.dimension p.samples)
    (O : OracleTemplate.Oracle (Query p.dimension p.samples) (Reply p.dimension))
    (hlaw : ∀ history query seed, O.answer history query seed = answer D query.2)
    (K : ℕ) (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    output p O K seed ξ =
      (((step D (stepSize p))^[K] ((algorithm p).initial seed)).point) := by
  unfold output
  rw [OracleTemplate.execute_eq_of_answer_eq O (answer D) (fun h q s => hlaw h (0, q) s),
    OracleTemplate.execute_iterate]
  rfl

lemma initial_eq (p : Params) (seed : (algorithm p).Seed) :
    initial (stepSize p * p.contrast) = (algorithm p).initial seed := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have he : (1 + 1 : ℝ) / Real.sqrt 2 = Real.sqrt 2 := by
    apply (div_eq_iff hs).mpr
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  simp [initial, ManySampleConvolutionalPerceptronGeometry.decode, algorithm, he]

lemma tuned_iterate (p : Params) (hp : spec.valid p) {D : Data p.dimension p.samples}
    (G : Geometry D p.lower p.upper p.contrast p.derivativeMargin) (seed : (algorithm p).Seed) :
    Separates D ((step D (stepSize p))^[(p.samples + 1) * ((tuning p hp).iterations + 1)]
      ((algorithm p).initial seed)).point := by
  have hη := stepSize_pos p hp
  have hs := iterate_separates G hp.1 hη (residualScale_eq p hp) (tuning p hp).iterations
    (fun tr => Nat.le_of_lt (tr.length_bound (tuning p hp) G.separator G.separator_norm
      (plus_norm G) (minus_norm G) (derivative_margin G)
      (fun i => by
        rw [backgroundScale_eq p hp, abs_mul, abs_of_pos hη]
        exact mul_le_mul_of_nonneg_left (G.background_lower i) hη.le)
      (fun i => by
        rw [stepScale_eq p hp, abs_mul, abs_of_pos hη]
        exact mul_le_mul_of_nonneg_left (G.background_upper i) hη.le)))
  rw [initial_eq p seed] at hs
  exact hs

lemma output_separates (p : Params) (hp : spec.valid p) {D : Data p.dimension p.samples}
    (G : Geometry D p.lower p.upper p.contrast p.derivativeMargin)
    (O : OracleTemplate.Oracle (Query p.dimension p.samples) (Reply p.dimension))
    (hlaw : ∀ history query seed, O.answer history query seed = answer D query.2)
    (seed : (algorithm p).Seed) (ξ : (k : ℕ) → O.Seed k) :
    Separates D (output p O ((p.samples + 1) *
      (⌈2 ^ 140 * p.upper ^ 10 / (p.derivativeMargin ^ 8 * p.lower ^ 10) *
        (1 + Real.log (p.upper / p.contrast))⌉₊ + 1)) seed ξ) := by
  rw [output_eq_iterate p D O hlaw, ← budget_eq p hp]
  exact tuned_iterate p hp G seed

end LongTails.Proofs.DerivativeConvolutionalPerceptronConvergence
