import LongTails.Template
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Distributions.Uniform

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
