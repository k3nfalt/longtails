import LongTails.Algorithms.Extragradient
import LongTails.Proofs.ZerothOrderSmoothing

open MeasureTheory Metric

namespace LongTails.Algorithms.NondualSelector

open OracleTemplate.ZerothOrder

noncomputable def center {d : ℕ} [NeZero d]
    (K : Set (EuclideanSpace ℝ (Fin d))) (r : ℝ) : EuclideanSpace ℝ (Fin d) :=
  ∫ v : ℝ × sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
    OracleTemplate.SaddlePoint.project K (r • ballOffset v)
      ∂(radialLaw d (NeZero.pos d) : Measure ℝ).prod
        (sphereLaw (EuclideanSpace ℝ (Fin d)) : Measure _)

end LongTails.Algorithms.NondualSelector
