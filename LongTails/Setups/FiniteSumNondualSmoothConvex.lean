import LongTails.Setups.FiniteSumSmoothAndConvex
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory

namespace LongTails.Setups.FiniteSumNondualSmoothConvex

open OracleTemplate

structure Params where
  d : ℕ
  n : ℕ
  [nonzero : NeZero n]
  L : ℝ
  R : ℝ
  hR : 0 ≤ R
  ε : ℝ

attribute [instance] Params.nonzero

abbrev Point (p : Params) := EuclideanSpace ℝ (Fin p.d)

instance pointMeasurableSpace (d : ℕ) : MeasurableSpace (EuclideanSpace ℝ (Fin d)) :=
  borel _

instance pointBorelSpace (d : ℕ) : BorelSpace (EuclideanSpace ℝ (Fin d)) := ⟨rfl⟩

def domain (p : Params) : Set (Point p) := {x | ∑ i, |x i| ≤ p.R}

abbrev Feasible (p : Params) := {x : Point p // x ∈ domain p}

noncomputable abbrev objective {p : Params} (f : Fin p.n → Point p → ℝ) :=
  LongTails.Setups.FiniteSumSmoothAndConvex.objective f

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance p := Fin p.n → Point p → ℝ
  Query p := Fin p.n × Feasible p
  Reply p := Point p
  Output p := Feasible p
  publicInput p := p
  valid p := 0 < p.d ∧ 0 < p.n ∧ 0 < p.L ∧ 0 < p.R ∧ 0 < p.ε
  admissible p f oracle :=
    (∀ i, ConvexOn ℝ Set.univ (f i)) ∧
    (∀ i x, HasGradientAt (f i) (gradient (f i) x) x) ∧
    (∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L * ‖x - y‖) ∧
    (∀ history seed i x,
      oracle.answer history (0, (i, x)) seed = gradient (f i) x.val)
  successful p f output P :=
    Measurable output ∧
    ∃ xstar : Feasible p, IsMinOn (objective f) (domain p) xstar.val ∧
      Integrable (fun ω => objective f (output ω).val - objective f xstar.val)
        (P : Measure _) ∧
      (∫ ω, objective f (output ω).val - objective f xstar.val ∂(P : Measure _)) ≤ p.ε

end LongTails.Setups.FiniteSumNondualSmoothConvex
