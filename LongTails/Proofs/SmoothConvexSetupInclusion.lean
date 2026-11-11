import LongTails.Setups.SmoothAndConvex
import LongTails.Setups.SmoothAndConvexExpected

open OracleTemplate MeasureTheory

namespace LongTails.Proofs.SmoothConvexSetupInclusion

open LongTails.Setups

lemma valid_original (q : SmoothAndConvexExpected.Params)
    (h : SmoothAndConvexExpected.spec.valid q) :
    SmoothAndConvex.spec.valid q.toSmoothAndConvex :=
  ⟨h.1, h.2.1.le, h.2.2.1⟩

lemma admissible_iff (q : SmoothAndConvexExpected.Params)
    (f : EuclideanSpace ℝ (Fin q.d) → ℝ)
    (O : Oracle (EuclideanSpace ℝ (Fin q.d)) (EuclideanSpace ℝ (Fin q.d))) :
    SmoothAndConvexExpected.spec.admissible q f O ↔
      SmoothAndConvex.spec.admissible q.toSmoothAndConvex f O := Iff.rfl

lemma successful_expected_of_ae (q : SmoothAndConvexExpected.Params)
    (f : EuclideanSpace ℝ (Fin q.d) → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (output : Ω → EuclideanSpace ℝ (Fin q.d)) (P : ProbabilityMeasure Ω)
    (hmeas : AEMeasurable (fun ω => f (output ω)) (P : Measure Ω))
    (h : SmoothAndConvex.spec.successful q.toSmoothAndConvex f output P) :
    SmoothAndConvexExpected.spec.successful q f output P := by
  obtain ⟨xstar, hmin, hbound⟩ := h
  change EuclideanSpace ℝ (Fin q.d) at xstar
  have hint : Integrable (fun ω => f (output ω) - f xstar) (P : Measure Ω) := by
    apply (integrable_const q.ε).mono' ((hmeas.sub_const (f xstar)).aestronglyMeasurable)
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmin (Set.mem_univ (output ω))))]
    exact hω
  refine ⟨xstar, hmin, hint, ?_⟩
  have hi := integral_mono_ae hint (integrable_const q.ε) hbound
  simpa only [integral_const, probReal_univ, one_smul] using hi

end LongTails.Proofs.SmoothConvexSetupInclusion
