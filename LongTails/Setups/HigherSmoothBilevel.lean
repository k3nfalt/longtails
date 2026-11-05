import Mathlib.Analysis.InnerProductSpace.Calculus
import LongTails.Template
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option maxSynthPendingDepth 3

namespace LongTails.Setups.HigherSmoothBilevel

open OracleTemplate MeasureTheory

structure Params where
  X : Type
  [normedX : NormedAddCommGroup X]
  [innerX : InnerProductSpace ℝ X]
  [finiteX : FiniteDimensional ℝ X]
  Y : Type
  [normedY : NormedAddCommGroup Y]
  [innerY : InnerProductSpace ℝ Y]
  [finiteY : FiniteDimensional ℝ Y]
  x0 : X
  y0 : Y
  L : ℝ
  μ : ℝ
  Δ : ℝ
  G : ℝ
  ε : ℝ

attribute [instance] Params.normedX Params.innerX Params.finiteX
  Params.normedY Params.innerY Params.finiteY

structure Instance (p : Params) where
  f : p.X × p.Y → ℝ
  g : p.X × p.Y → ℝ

noncomputable def lowerSolution {p : Params} (I : Instance p) (x : p.X) : p.Y :=
by
  classical
  exact if h : ∃ y : p.Y, ∀ z, I.g (x, y) ≤ I.g (x, z) then Classical.choose h else 0

noncomputable def hyperObjective {p : Params} (I : Instance p) (x : p.X) : ℝ :=
  I.f (x, lowerSolution I x)

abbrev Reply (p : Params) :=
  ℝ × ℝ × ((p.X × p.Y) →L[ℝ] ℝ) × ((p.X × p.Y) →L[ℝ] ℝ)

noncomputable def firstOrderReply {p : Params} (I : Instance p) (z : p.X × p.Y) : Reply p :=
  (I.f z, I.g z, fderiv ℝ I.f z, fderiv ℝ I.g z)

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance := Instance
  Query p := p.X × p.Y
  Reply := Reply
  Output p := p.X
  publicInput p := p
  valid p := 0 < p.μ ∧ p.μ ≤ p.L ∧ 0 < p.Δ ∧ 0 ≤ p.G ∧ 0 < p.ε
  admissible p I O :=
    ContDiff ℝ 2 I.f ∧
    ContDiff ℝ 3 I.g ∧
    (∀ z, ‖fderiv ℝ I.f z‖ ≤ p.L) ∧
    (∀ z w, ‖fderiv ℝ I.f z - fderiv ℝ I.f w‖ ≤ p.L * ‖z - w‖) ∧
    (∀ z w, ‖fderiv ℝ (fderiv ℝ I.f) z - fderiv ℝ (fderiv ℝ I.f) w‖ ≤ p.L * ‖z - w‖) ∧
    (∀ z w, ‖fderiv ℝ I.g z - fderiv ℝ I.g w‖ ≤ p.L * ‖z - w‖) ∧
    (∀ z w, ‖fderiv ℝ (fderiv ℝ I.g) z - fderiv ℝ (fderiv ℝ I.g) w‖ ≤ p.L * ‖z - w‖) ∧
    (∀ z w, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) z -
      fderiv ℝ (fderiv ℝ (fderiv ℝ I.g)) w‖ ≤ p.L * ‖z - w‖) ∧
    (∀ x y z, I.g (x, y) + fderiv ℝ I.g (x, y) (0, z - y) +
      p.μ / 2 * ‖z - y‖ ^ 2 ≤ I.g (x, z)) ∧
    (∀ x, hyperObjective I p.x0 - hyperObjective I x ≤ p.Δ) ∧
    ‖gradient (fun y => I.g (p.x0, y)) p.y0‖ ≤ p.G ∧
    (∀ history z seed, O.answer history (0, z) seed = firstOrderReply I z)
  successful p I output P := ∀ᵐ ω ∂(P : Measure _),
    DifferentiableAt ℝ (hyperObjective I) (output ω) ∧
      ‖gradient (hyperObjective I) (output ω)‖ ≤ p.ε

end LongTails.Setups.HigherSmoothBilevel
