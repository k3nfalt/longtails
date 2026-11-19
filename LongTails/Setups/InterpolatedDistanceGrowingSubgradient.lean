import LongTails.Setups.DistanceGrowingSubgradient
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Gradient.Basic

open scoped ContDiff
open MeasureTheory OracleTemplate
open LongTails.Setups.TerminalClippingConvex

namespace LongTails.Setups.InterpolatedDistanceGrowingSubgradient

def Interpolates (p : Public) (I : Instance p) (O : Oracle (Query p) (Vector p.d) 1) : Prop :=
  I.domain = Set.univ ∧
  ∃ (u g₀ : Vector p.d) (loss : (k : ℕ) → O.Seed k → Vector p.d → ℝ),
    ‖p.x0 - u‖ ≤ p.R ∧
    (∀ k z, ConvexOn ℝ Set.univ (loss k z) ∧ ContDiff ℝ ∞ (loss k z) ∧
      IsMinOn (loss k z) Set.univ u) ∧
    (∀ k z, gradient (loss k z) p.x0 = g₀) ∧
    (∀ h x z, O.answer h (0, .subgradient x) z = gradient (loss h.length z) x) ∧
    ∀ k x, Integrable (fun ξ : (i : ℕ) → O.Seed i => loss k (ξ k) x) (O.law : Measure _) ∧
      I.f x = ∫ (ξ : (i : ℕ) → O.Seed i), loss k (ξ k) x ∂(O.law : Measure _)

abbrev spec : Setup :=
  { DistanceGrowingSubgradient.spec with
    valid := fun p => 2 ≤ p.d ∧ 0 ≤ p.B ∧ 0 < p.G ∧ 0 < p.R ∧ 0 < p.ε ∧
      65536 * p.ε ≤ p.G * p.R ∧ 0 < p.δ ∧ p.δ ≤ 1 / 8
    admissible := fun p I O => DistanceGrowingSubgradient.spec.admissible p I O ∧
      Interpolates p I O }

end LongTails.Setups.InterpolatedDistanceGrowingSubgradient
