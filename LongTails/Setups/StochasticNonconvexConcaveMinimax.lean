import LongTails.Template
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open MeasureTheory

namespace LongTails.Setups.StochasticNonconvexConcaveMinimax

open OracleTemplate

structure Params where
  d : ℕ
  L : ℝ
  Δ : ℝ
  D : ℝ
  σ : ℝ
  ε : ℝ

abbrev Prim (d : ℕ) := EuclideanSpace ℝ (Fin 2 × Fin d)

abbrev Dual (d : ℕ) := EuclideanSpace ℝ (Fin d)

noncomputable def blockSq {d : ℕ} (x : Prim d) (b : Fin 2) : ℝ := ∑ i, x (b, i) ^ 2

noncomputable def radiusU (q : Params) : ℝ := 2 ^ 7 * Real.sqrt (q.Δ / q.L)

noncomputable def radiusAB (q : Params) : ℝ := 2 ^ 33 * q.ε / q.L

def primalSet (q : Params) : Set (Prim q.d) :=
  {x | blockSq x 0 ≤ radiusU q ^ 2 ∧ blockSq x 1 ≤ radiusAB q ^ 2}

def dualSet (q : Params) : Set (Dual q.d) := Metric.closedBall 0 (q.D / 2)

noncomputable def value {q : Params} (f : Prim q.d → Dual q.d → ℝ) (x : Prim q.d) : ℝ :=
  sSup (f x '' dualSet q)

def proxSet {q : Params} (f : Prim q.d → Dual q.d → ℝ) (x : Prim q.d) : Set (Prim q.d) :=
  {p | p ∈ primalSet q ∧ ∀ z ∈ primalSet q,
    value f p + q.L * ‖p - x‖ ^ 2 ≤ value f z + q.L * ‖z - x‖ ^ 2}

noncomputable def stationarity {q : Params} (f : Prim q.d → Dual q.d → ℝ) (x : Prim q.d) : ℝ :=
  2 * q.L * Metric.infDist x (proxSet f x)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := Prim q.d → Dual q.d → ℝ
  Query q := {z : Prim q.d × Dual q.d // z.1 ∈ primalSet q ∧ z.2 ∈ dualSet q}
  Reply q := Prim q.d × Dual q.d
  Output q := Prim q.d
  publicInput q := q
  valid q := 0 < q.L ∧ 0 < q.Δ ∧ 0 < q.D ∧ 0 ≤ q.σ ∧ 0 < q.ε ∧
    2 ^ 67 * q.ε ^ 2 ≤ q.L * q.Δ ∧ 2 ^ 36 * q.ε ≤ q.L * q.D ∧
    2 ^ 180 * (q.L * q.Δ / q.ε ^ 2) ^ 9 * (q.L * q.D / q.ε) ^ 7 *
      (1 + q.σ ^ 2 * q.L * q.D / q.ε ^ 3) ≤ q.d
  admissible q f O :=
    ∃ (gx : Prim q.d → Dual q.d → Prim q.d) (gy : Prim q.d → Dual q.d → Dual q.d)
      (μ : ProbabilityMeasure ℝ) (P : ProbabilityMeasure (ℕ → ℝ))
      (G : Prim q.d → Dual q.d → ℝ → Prim q.d × Dual q.d),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ω : ℕ → ℝ) => ω k) (μ : Measure ℝ) (P : Measure (ℕ → ℝ)) ∧
      O = { Seed := fun _ => ℝ
            law := P
            answer := fun _ (_, z) ω => G z.1.1 z.1.2 ω } ∧
      (∀ x y, HasGradientAt (fun x' => f x' y) (gx x y) x ∧ HasGradientAt (f x) (gy x y) y) ∧
      (∀ x ∈ primalSet q, ∀ x' ∈ primalSet q, ∀ y ∈ dualSet q, ∀ y' ∈ dualSet q,
        ‖gx x y - gx x' y'‖ ^ 2 + ‖gy x y - gy x' y'‖ ^ 2 ≤ q.L ^ 2 * (‖x - x'‖ ^ 2 + ‖y - y'‖ ^ 2)) ∧
      (∀ x ∈ primalSet q, ConcaveOn ℝ (dualSet q) (f x)) ∧
      value f 0 - sInf ((fun x => f x 0) '' primalSet q) ≤ q.Δ ∧
      Measurable (fun w : (Prim q.d × Dual q.d) × ℝ => G w.1.1 w.1.2 w.2) ∧
      (∀ x ∈ primalSet q, ∀ y ∈ dualSet q,
        Integrable (G x y) μ ∧ ∫ ω, G x y ω ∂μ = (gx x y, gy x y) ∧
        Integrable (fun ω => ‖(G x y ω).1 - gx x y‖ ^ 2 + ‖(G x y ω).2 - gy x y‖ ^ 2) μ ∧
        ∫ ω, (‖(G x y ω).1 - gx x y‖ ^ 2 + ‖(G x y ω).2 - gy x y‖ ^ 2) ∂μ ≤ q.σ ^ 2)
  successful q f output P :=
    Measurable output ∧ Integrable (fun ω => stationarity f (output ω)) (P : Measure _) ∧
      ∫ ω, stationarity f (output ω) ∂(P : Measure _) ≤ q.ε

end LongTails.Setups.StochasticNonconvexConcaveMinimax
