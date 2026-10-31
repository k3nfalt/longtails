import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Distributions.Uniform
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

namespace OracleTemplate.Adam

abbrev Point (d : ℕ) := EuclideanSpace ℝ (Fin d)

structure State (d : ℕ) where
  selected : ℕ
  time : ℕ
  point : Point d
  momentum : Point d
  secondMoment : Point d
  saved : Point d

noncomputable def secondMomentStep {d : ℕ} (ρ : ℝ) (v g : Point d) : Point d :=
  WithLp.toLp 2 fun i => (1 - ρ) * v i + ρ * (g i) ^ 2

noncomputable def direction {d : ℕ} (τ : ℝ) (m v : Point d) : Point d :=
  WithLp.toLp 2 fun i => m i / (Real.sqrt (v i) + τ)

noncomputable def update {d : ℕ} (q ρ η τ : ℝ) (s : State d) (g : Point d) : State d :=
  let m := q • s.momentum + (1 - q) • g
  let v := secondMomentStep ρ s.secondMoment g
  { selected := s.selected
    time := s.time + 1
    point := s.point - η • direction τ m v
    momentum := m
    secondMoment := v
    saved := if s.time = s.selected then s.point else s.saved }

noncomputable def method {d : ℕ} (q ρ η τ : ℝ) (n : ℕ) (x0 : Point d) :
    Algorithm (Point d) (Point d) (Point d) where
  Seed := Fin (n + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (n + 1))).toMeasure, inferInstance⟩
  State := State d
  initial k := ⟨k.val, 0, x0, 0, 0, x0⟩
  query s := (0, s.point)
  update := update q ρ η τ
  output s := s.saved

noncomputable def output {d : ℕ} (O : Oracle (Point d) (Point d))
    (q ρ η τ : ℝ) (n : ℕ) (x0 : Point d) (selected : Fin (n + 1))
    (ξ : (k : ℕ) → O.Seed k) : Point d :=
  execute O (method q ρ η τ n x0) (fun _ => n + 1) selected ξ

end OracleTemplate.Adam

open MeasureTheory

namespace LongTails.Setups.HeavyTailedAdam

open OracleTemplate

structure Params where
  d : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  σ : ℝ
  α : ℝ
  Δ : ℝ
  ε : ℝ
  x0 : Adam.Point d

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := Adam.Point q.d → ℝ
  Query q := Adam.Point q.d
  Reply q := Adam.Point q.d
  Output q := Adam.Point q.d
  publicInput q := q
  valid q := 0 < q.L ∧ 0 ≤ q.σ ∧ 1 < q.α ∧ q.α ≤ 2 ∧ 0 ≤ q.Δ ∧ 0 < q.ε
  admissible q f O :=
    ∃ (g : Adam.Point q.d → q.Ω → Adam.Point q.d)
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
      (∀ x, f q.x0 - f x ≤ q.Δ) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) p) ∧
      (∀ x, ∫ ω, g x ω ∂p = gradient f x) ∧
      (∀ x, Integrable (fun ω => ∑ i, |(g x ω - gradient f x) i| ^ q.α) p) ∧
      (∀ x, ∫ ω, ∑ i, |(g x ω - gradient f x) i| ^ q.α ∂p ≤ q.σ ^ q.α)
  successful q f output P :=
    Measurable output ∧
      Integrable (fun ω => ‖gradient f (output ω)‖) (P : Measure _) ∧
      ∫ ω, ‖gradient f (output ω)‖ ∂(P : Measure _) ≤ q.ε
  allowedAlgorithm q A :=
    ∃ (β ρ η τ : ℝ) (n : ℕ), 0 ≤ β ∧ β < 1 ∧ 0 < ρ ∧ ρ ≤ 1 ∧
      0 < η ∧ 0 < τ ∧ A = Adam.method β ρ η τ n q.x0

end LongTails.Setups.HeavyTailedAdam
