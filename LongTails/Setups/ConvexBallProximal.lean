import LongTails.Algorithms.BallProximal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set MeasureTheory

namespace LongTails.Setups.ConvexBallProximal

open OracleTemplate OracleTemplate.BallProximal

structure Public where
  E : Type
  [normedE : NormedAddCommGroup E]
  [innerE : InnerProductSpace ℝ E]
  [finiteE : FiniteDimensional ℝ E]
  t : ℝ
  R : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : E

attribute [instance] Public.normedE Public.innerE Public.finiteE

structure Instance (p : Public) where
  C : Set p.E
  f : p.E → ℝ

abbrev spec : Setup where
  Params := Public
  Public := Public
  Instance := Instance
  Query p := p.E
  Reply p := p.E
  Output p := p.E
  publicInput p := p
  valid p := 0 < p.t ∧ 0 ≤ p.R ∧ 0 < p.Δ ∧ 0 < p.ε
  admissible p I O :=
    ConvexOn ℝ I.C I.f ∧
    IsClosed {q : p.E × ℝ | q.1 ∈ I.C ∧ I.f q.1 ≤ q.2} ∧
    p.x0 ∈ I.C ∧
    (∀ k seed x, x ∈ I.C →
      let y := O.answer k (0, x) seed
      y ∈ I.C ∧ ‖y - x‖ ≤ p.t ∧
        ∀ z ∈ I.C, ‖z - x‖ ≤ p.t → I.f y ≤ I.f z) ∧
    (∃ xstar ∈ I.C, IsMinOn I.f I.C xstar ∧
      ‖p.x0 - xstar‖ ≤ p.R ∧ I.f p.x0 - I.f xstar ≤ p.Δ)
  successful p I output P :=
    ∃ xstar ∈ I.C, IsMinOn I.f I.C xstar ∧
      ∀ᵐ ω ∂(P : Measure _), output ω ∈ I.C ∧ I.f (output ω) - I.f xstar ≤ p.ε
  allowedAlgorithm p A := A = algorithm p.x0

end LongTails.Setups.ConvexBallProximal
