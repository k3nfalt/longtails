import LongTails.Proofs.GapStrongGrowthLocalStep
import LongTails.Proofs.GapStrongGrowthIteration
import LongTails.Proofs.IIDBlocks

open MeasureTheory Set
open OracleTemplate.ContinuizedSimilarQuasar

namespace OracleTemplate.GapStrongGrowth

open LongTails.Setups.GapSmoothStrongGrowth

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

noncomputable def freeze (V : S → ℝ) (c : ℝ) (advance : S → Ω → S) (s : S) (ω : Ω) : S :=
  if V s < c then advance s ω else s

lemma freeze_measurable {V : S → ℝ} (hV : Measurable V) (c : ℝ)
    {advance : S → Ω → S} (ha : Measurable (fun t : S × Ω => advance t.1 t.2)) :
    Measurable (fun t : S × Ω => freeze V c advance t.1 t.2) := by
  exact Measurable.ite (measurableSet_lt (hV.comp measurable_fst) measurable_const) ha measurable_fst

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma frozen_constant (V : S → ℝ) (c : ℝ) (advance : S → Ω → S)
    (s : S) (hs : c ≤ V s) (n : ℕ) (ξ : Fin n → Ω) :
    iterateSamples (freeze V c advance) n s ξ = s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterateSamples, freeze, not_lt.mpr hs, ite_false]
    exact ih _

omit [MeasurableSpace S] [MeasurableSpace Ω] in
lemma frozen_compare (V : S → ℝ) (c : ℝ) (advance : S → Ω → S)
    (n : ℕ) (s : S) (ξ : Fin n → Ω) :
    iterateSamples advance n s ξ = iterateSamples (freeze V c advance) n s ξ ∨
      c ≤ V (iterateSamples (freeze V c advance) n s ξ) := by
  induction n generalizing s with
  | zero => exact Or.inl rfl
  | succ n ih =>
    by_cases hs : V s < c
    · simpa only [iterateSamples, freeze, hs, ite_true] using ih (advance s (ξ 0)) (fun i => ξ i.succ)
    · right
      rw [frozen_constant V c advance s (le_of_not_gt hs)]
      exact le_of_not_gt hs

lemma frozen_exponential_integral {V : S → ℝ} (hV : Measurable V)
    {c t : ℝ} {advance : S → Ω → S}
    (ha : Measurable (fun z : S × Ω => advance z.1 z.2))
    (P : ProbabilityMeasure Ω)
    (hstep : ∀ s, V s < c →
      Integrable (fun ω => Real.exp (t * V (advance s ω))) (P : Measure Ω) ∧
      (∫ ω, Real.exp (t * V (advance s ω)) ∂(P : Measure Ω)) ≤ Real.exp (t * V s))
    (n : ℕ) (s : S) :
    Integrable (fun ξ => Real.exp (t * V (iterateSamples (freeze V c advance) n s ξ)))
      (Measure.pi fun _ : Fin n => (P : Measure Ω)) ∧
    (∫ ξ, Real.exp (t * V (iterateSamples (freeze V c advance) n s ξ))
      ∂Measure.pi (fun _ : Fin n => (P : Measure Ω))) ≤ Real.exp (t * V s) := by
  have hs (s : S) : Integrable (fun ω => Real.exp (t * V (freeze V c advance s ω))) (P : Measure Ω) ∧
      (∫ ω, Real.exp (t * V (freeze V c advance s ω)) ∂(P : Measure Ω)) ≤
        1 * Real.exp (t * V s) + 0 := by
    by_cases hh : V s < c
    · simpa only [freeze, hh, ite_true, one_mul, add_zero] using hstep s hh
    · simp only [freeze, hh, ite_false]
      exact ⟨integrable_const _, by simp⟩
  simpa only [one_pow, one_mul, zero_mul, add_zero] using
    iterateSamples_measurable_integral (freeze_measurable hV c ha) P
      (fun s => Real.exp (t * V s)) (Real.measurable_exp.comp (hV.const_mul t))
      (fun _ => (Real.exp_pos _).le) (by norm_num : (0 : ℝ) ≤ 1)
       hs n s

lemma indicator_integral_exponential {X : Ω → ℝ} {Bad : Ω → Prop} [DecidablePred Bad]
    (hBad : MeasurableSet {ω | Bad ω}) (P : Measure Ω) [IsProbabilityMeasure P]
    {t c C : ℝ} (ht : 0 ≤ t)
    (hi : Integrable (fun ω => Real.exp (t * X ω)) P)
    (hb : (∫ ω, Real.exp (t * X ω) ∂P) ≤ C)
    (hcross : ∀ ω, Bad ω → c ≤ X ω) :
    (∫ ω, (if Bad ω then (1 : ℝ) else 0) ∂P) ≤ Real.exp (-t * c) * C := by
  classical
  have hm : Measurable (fun ω => if Bad ω then (1 : ℝ) else 0) :=
    Measurable.ite hBad measurable_const measurable_const
  have hbi : Integrable (fun ω => if Bad ω then (1 : ℝ) else 0) P :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by split_ifs <;> norm_num)
  have hpoint (ω) : (if Bad ω then (1 : ℝ) else 0) ≤
      Real.exp (-t * c) * Real.exp (t * X ω) := by
    split_ifs with h
    · rw [← Real.exp_add]
      calc
        1 = Real.exp 0 := by simp
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left (hcross ω h) ht])
    · positivity
  have hh := integral_mono hbi (hi.const_mul (Real.exp (-t * c))) hpoint
  rw [integral_const_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)

lemma confidence_tail (p : Params) (hδ : 0 < p.δ) (hδ1 : p.δ < 1) :
    Real.exp (-13 * confidence p / 128) ≤ p.δ := by
  have hlog : Real.log p.δ ≤ 0 := Real.log_nonpos hδ.le hδ1.le
  rw [← Real.exp_log hδ]
  apply Real.exp_le_exp.mpr
  unfold confidence
  rw [abs_of_nonpos hlog]
  nlinarith only [hlog]

lemma initial_energy_bound (p : Params) (hR : 0 < p.R) (hΔ : 0 < p.Δ)
    {f : p.E → ℝ} {u : p.E} (hr : ‖p.x0 - u‖ ≤ p.R)
    (hgap : f p.x0 - f u ≤ p.Δ) :
    energy p f u 0 (p.x0, p.x0) ≤ 3 * p.R ^ 2 / 2 := by
  have hs := pow_le_pow_left₀ (norm_nonneg _) hr 2
  have hg := mul_le_mul_of_nonneg_left hgap (show 0 ≤ p.R ^ 2 / p.Δ by positivity)
  have he : p.R ^ 2 / p.Δ * p.Δ = p.R ^ 2 := by field_simp
  rw [he] at hg
  dsimp [energy, weight]
  linarith

end OracleTemplate.GapStrongGrowth
