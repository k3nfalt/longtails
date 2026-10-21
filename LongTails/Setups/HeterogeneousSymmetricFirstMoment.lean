import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Distributions.Uniform
import LongTails.Setups.StochasticGeneralizedSmoothAndConvex
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace LongTails.Algorithms.HeterogeneousAdam

open OracleTemplate MeasureTheory

abbrev Point (b h : ℕ) := EuclideanSpace ℝ (Fin b ⊕ Fin h)

structure Config where
  lastIndex : ℕ
  α : ℝ
  β : ℝ
  δ : ℝ
  r₀ : ℝ
  bodyStep : ℕ → ℝ
  headStep : ℕ → ℝ

structure State (b h : ℕ) where
  clock : ℕ
  target : ℕ
  point : Point b h
  momentum : Point b h
  accumulator : Point b h
  selected : Point b h

noncomputable def initial (cfg : Config) (x₀ : Point b h)
    (seed : Fin (cfg.lastIndex + 1)) : State b h where
  clock := 0
  target := seed.val
  point := x₀
  momentum := 0
  accumulator := WithLp.toLp 2 fun i => Sum.casesOn i (fun _ => 0) (fun _ => cfg.r₀ ^ 2)
  selected := x₀

noncomputable def nextMomentum (cfg : Config) (s : State b h) (g : Point b h) : Point b h :=
  WithLp.toLp 2 fun i => Sum.casesOn i
    (fun j => cfg.α * s.momentum (.inl j) + (1 - cfg.α) * g (.inl j))
    (fun j => g (.inr j))

noncomputable def nextAccumulator (cfg : Config) (s : State b h) (g : Point b h) : Point b h :=
  WithLp.toLp 2 fun i => Sum.casesOn i
    (fun j => cfg.β * s.accumulator (.inl j) + (1 - cfg.β) * g (.inl j) ^ 2)
    (fun j => s.accumulator (.inr j) + g (.inr j) ^ 2)

noncomputable def nextPoint (cfg : Config) (s : State b h) (g : Point b h) : Point b h :=
  let m := nextMomentum cfg s g
  let v := nextAccumulator cfg s g
  WithLp.toLp 2 fun i => s.point i - Sum.casesOn i
    (fun j => cfg.bodyStep s.clock * (m (.inl j) / (1 - cfg.α ^ (s.clock + 1))) /
      (cfg.δ + Real.sqrt (v (.inl j) / (1 - cfg.β ^ (s.clock + 1)))))
    (fun j => cfg.headStep s.clock * g (.inr j) / Real.sqrt (v (.inr j)))

noncomputable def update (cfg : Config) (s : State b h) (g : Point b h) : State b h where
  clock := s.clock + 1
  target := s.target
  point := nextPoint cfg s g
  momentum := nextMomentum cfg s g
  accumulator := nextAccumulator cfg s g
  selected := if s.clock + 1 = s.target then nextPoint cfg s g else s.selected

def output (s : State b h) : Point b h := s.selected

noncomputable def method (cfg : Config) (x₀ : Point b h) :
    Algorithm (Point b h) (Point b h) (Point b h) where
  Seed := Fin (cfg.lastIndex + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (cfg.lastIndex + 1))).toMeasure, inferInstance⟩
  State := State b h
  initial := initial cfg x₀
  query := fun s => (0, s.point)
  update := update cfg
  output := output

noncomputable def run (cfg : Config) (x₀ : Point b h)
    (seed : Fin (cfg.lastIndex + 1)) (g : ℕ → Point b h → Point b h) : ℕ → State b h
  | 0 => initial cfg x₀ seed
  | n + 1 => update cfg (run cfg x₀ seed g n) (g n (run cfg x₀ seed g n).point)

noncomputable def trajectory (cfg : Config) (x₀ : Point b h)
    (g : ℕ → Point b h → Point b h) (n : ℕ) : Point b h :=
  (run cfg x₀ 0 g n).point



noncomputable def tunedConfig (b h T : ℕ) (L Δ σ δ : ℝ) : Config where
  lastIndex := T-1
  α := 9/10
  β := 999/1000
  δ := δ
  r₀ := 1+2*L*Δ+h*σ^2
  bodyStep := fun _ => Real.sqrt (Δ/(L*((b : ℝ)+h)))/Real.sqrt T
  headStep := fun _ => Real.sqrt (Δ/(L*((b : ℝ)+h)))


end LongTails.Algorithms.HeterogeneousAdam

open MeasureTheory

namespace LongTails.Setups.HeterogeneousSymmetricFirstMoment

open OracleTemplate LongTails.Algorithms.HeterogeneousAdam

structure Params where
  bodyDim : ℕ
  headDim : ℕ
  Ω : Type
  [measurableΩ : MeasurableSpace Ω]
  L : ℝ
  M : ℝ
  σBody : ℝ
  σHead : ℝ
  Δ : ℝ
  ε : ℝ
  δ : ℝ
  x₀ : Point bodyDim headDim

attribute [instance] Params.measurableΩ

abbrev spec : Setup where
  Params := Params
  Public := Params
  Instance q := Point q.bodyDim q.headDim → ℝ
  Query q := Point q.bodyDim q.headDim
  Reply q := Point q.bodyDim q.headDim
  Output q := Point q.bodyDim q.headDim
  publicInput q := q
  valid q := 0 < q.bodyDim + q.headDim ∧ 0 < q.L ∧ 0 ≤ q.M ∧
    0 ≤ q.σBody ∧ 0 ≤ q.σHead ∧ 0 < q.Δ ∧ 0 < q.ε ∧ 0 < q.δ
  admissible q f O :=
    ∃ (g : Point q.bodyDim q.headDim → q.Ω → Point q.bodyDim q.headDim)
      (p : ProbabilityMeasure q.Ω) (P : ProbabilityMeasure (ℕ → q.Ω)) (K : q.Ω → ℝ),
      LongTails.Setups.StochasticGeneralizedSmoothAndConvex.IID
        (fun k (ξ : ℕ → q.Ω) => ξ k) (p : Measure _) (P : Measure _) ∧
      O = { Seed := fun _ => q.Ω
            law := P
            answer := fun _ (_, x) ω => g x ω } ∧
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      (∀ x y, ‖gradient f x - gradient f y‖ ≤ q.L * ‖x - y‖) ∧
      (∀ x, f q.x₀ - f x ≤ q.Δ) ∧
      Measurable (Function.uncurry g) ∧
      (∀ x, Integrable (g x) p) ∧
      (∀ x, ∫ ω, g x ω ∂p = gradient f x) ∧
      (∀ x, ∫ ω, ∑ i : Fin q.bodyDim,
        |(g x ω - gradient f x) (.inl i)| ∂p ≤ q.σBody) ∧
      (∀ x, Integrable (fun ω => ∑ i : Fin q.headDim,
        ((g x ω - gradient f x) (.inr i)) ^ 2) p) ∧
      (∀ x, ∫ ω, ∑ i : Fin q.headDim,
        ((g x ω - gradient f x) (.inr i)) ^ 2 ∂p ≤ q.σHead ^ 2) ∧
      (∀ x (i : Fin q.bodyDim),
        (p : Measure _).map (fun ω => (g x ω - gradient f x) (.inl i)) =
        (p : Measure _).map (fun ω => -(g x ω - gradient f x) (.inl i))) ∧
      Measurable K ∧ Integrable K p ∧ (∫ ω, K ω ∂p) ≤ q.M ∧
      (∀ᵐ ω ∂(p : Measure _), 0 ≤ K ω ∧ ∀ x y (i : Fin q.bodyDim),
        |(g x ω - gradient f x) (.inl i) - (g y ω - gradient f y) (.inl i)| ≤
          K ω * ‖x - y‖)
  successful q f out P :=
    Measurable out ∧ Integrable (fun ω => ‖gradient f (out ω)‖) (P : Measure _) ∧
      (∫ ω, ‖gradient f (out ω)‖ ∂(P : Measure _)) ≤ q.ε
  allowedAlgorithm q A := ∃ cfg : Config,
    cfg.α = 9 / 10 ∧ cfg.β = 999 / 1000 ∧ cfg.δ = q.δ ∧ 0 < cfg.r₀ ∧
    (∀ t, 0 < cfg.bodyStep t) ∧ (∀ t, 0 < cfg.headStep t) ∧ A = method cfg q.x₀

end LongTails.Setups.HeterogeneousSymmetricFirstMoment
