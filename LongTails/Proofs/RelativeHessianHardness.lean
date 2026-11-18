import LongTails.TemplateLowerBound
import LongTails.Proofs.RelativeHessianLowerBound
import LongTails.Proofs.RelativeHessianTuning

namespace LongTails.Proofs.RelativeHessianHardness

open OracleTemplate MeasureTheory RelativeHessianTuning RelativeHessianInstance RelativeHessianScaling
open LongTails.Setups.PointwiseHessianStationarity

lemma hard (p : Params) (hp : spec.valid p)
    (A : Algorithm (Point p) (Reply p) (Point p)) (b : Fin 1 → ℕ)
    (hb : b 0 ≤ limit p) :
    ∃ (f : Point p → ℝ) (O : Oracle (Point p) (Reply p)), spec.admissible p f O ∧
      ¬ spec.successful p f (fun ω : A.Seed × ((k : ℕ) → O.Seed k) => execute O A b ω.1 ω.2)
        ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  have heq : b = fun _ => b 0 := funext (fun i => congrArg b (Subsingleton.elim i 0))
  obtain ⟨hD, hd, hsize⟩ := dimension_budget hp hb
  have hT : b 0 < edges (b 0) := by unfold edges; omega
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  obtain ⟨w, hw⟩ := RelativeHessianLowerBound.exists_failure p (amplitude_pos hp.1).le
    (frequency_pos hp.1).le A P (b 0) hT ((p.d : ℝ) / 2) hD hd hsize (by
      rw [product hp.1]
      linarith [hp.1.2.2.2.2.2])
  let π := FiniteSumNondualLowerAveraging.coordinateEmbedding w
  refine ⟨scaled (amplitude p) (frequency p) π, oracle (amplitude p) (frequency p) π, ?_, ?_⟩
  · exact admissible p (amplitude_pos hp.1).le (frequency_pos hp.1).le hp.1.1 hp.1.2.1
      hp.1.2.2.2.2.2 (absolute_scale hp.1).le (relative_scale hp.1) (gap_budget hp hb)
      (by rw [product hp.1]; exact hp.2.1) π
  · have hout : (fun ω : A.Seed × (ℕ → Unit) => execute (oracle (amplitude p) (frequency p) π) A b ω.1 ω.2) =
        (fun ω : A.Seed × (ℕ → Unit) => execute (oracle (amplitude p) (frequency p) π) A (fun _ => b 0) ω.1 ω.2) := by
      funext ω
      exact congrArg (fun c => execute (oracle (amplitude p) (frequency p) π) A c ω.1 ω.2) heq
    change ¬ broadSpec.successful p (scaled (amplitude p) (frequency p) π) _ P
    erw [hout]
    exact hw

end LongTails.Proofs.RelativeHessianHardness
