import LongTails.Setups.StochasticSurjectiveInequalities
import LongTails.Algorithms.Clipping
import Mathlib.Probability.Distributions.Uniform

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Algorithms.SurjectiveProxLinear

open OracleTemplate LongTails.Setups.StochasticSurjectiveInequalities

noncomputable def rho (p : Params) : ℝ := 4 * p.H * (p.H + 1)
noncomputable def gamma (p : Params) : ℝ := 1 + p.H + rho p * p.m * p.H
noncomputable def eta (p : Params) : ℝ := 1 / (4 * gamma p)
noncomputable def sensitivity (p : Params) : ℝ := 1024 * p.m ^ 2 * p.H ^ 12
noncomputable def radius (p : Params) : ℝ := p.ε / (64 * p.m * p.H ^ 3)
noncomputable def ridge (p : Params) : ℝ := p.ε / (524288 * p.m ^ 2 * p.H ^ 9)
noncomputable def certificateError (p : Params) : ℝ := p.ε / (16384 * p.m ^ 2 * p.H ^ 9)
noncomputable def beta (p : Params) : ℝ := 1 / (1 + 32768 * sensitivity p * p.σ ^ 2 / radius p ^ 2)
noncomputable def relaxation (p : Params) : ℝ := 1 / (512 * p.m * p.H ^ 7 * (1 + 524288 * p.m ^ 2 * p.H ^ 9 * p.σ / p.ε))
noncomputable def initialBatch (p : Params) : ℕ := ⌈1024 * sensitivity p * p.σ ^ 2 / radius p ^ 2⌉₊ + 1
noncomputable def certificateBatch (p : Params) : ℕ := ⌈8 * p.σ ^ 2 / certificateError p ^ 2⌉₊ + 1
noncomputable def iterations (p : Params) : ℕ := ⌈1024 * p.Δ / (gamma p * relaxation p * radius p ^ 2) + 64 / beta p⌉₊

def dualBox (p : Params) : Set (Constraint p) :=
  {ℓ | ∀ i, 0 ≤ ℓ i ∧ ℓ i ≤ rho p}

noncomputable def dualObjective (p : Params) (v : Primitive p) (ℓ : Constraint p) : ℝ :=
  eta p / 2 * ‖clip p.H v.1 + transposeAction p (clip p.H v.2.2) ℓ‖ ^ 2 -
    ⟪v.2.1, ℓ⟫ + ridge p / 2 * ‖ℓ‖ ^ 2

noncomputable def dualPoint (p : Params) (v : Primitive p) : Constraint p := by
  classical
  exact if h : ∃ ℓ ∈ dualBox p, ∀ z ∈ dualBox p, dualObjective p v ℓ ≤ dualObjective p v z
    then Classical.choose h else 0

noncomputable def modelStep (p : Params) (v : Primitive p) : p.E :=
  -eta p • (clip p.H v.1 + transposeAction p (clip p.H v.2.2) (dualPoint p v))

structure State (p : Params) where
  target : ℕ
  clock : ℕ
  x : p.E
  estimate : Primitive p
  certificate : Primitive p

noncomputable def query (p : Params) (s : State p) : p.E × p.E :=
  if initialBatch p ≤ s.clock ∧ s.clock < initialBatch p + s.target then
    (s.x + relaxation p • modelStep p s.estimate, s.x)
  else (s.x, s.x)

noncomputable def update (p : Params) (s : State p) (r : Primitive p × Primitive p) : State p :=
  if s.clock < initialBatch p then
    { s with clock := s.clock + 1
             estimate := s.estimate + (1 / ((s.clock : ℝ) + 1)) • (r.1 - s.estimate) }
  else if s.clock < initialBatch p + s.target then
    { s with clock := s.clock + 1
             x := s.x + relaxation p • modelStep p s.estimate
             estimate := r.1 + (1 - beta p) • (s.estimate - r.2) }
  else if s.clock < initialBatch p + s.target + certificateBatch p then
    { s with clock := s.clock + 1
             certificate := s.certificate +
               (1 / (((s.clock - (initialBatch p + s.target) : ℕ) : ℝ) + 1)) •
                 (r.1 - s.certificate) }
  else s

noncomputable def output (p : Params) (s : State p) : p.E × Constraint p :=
  (s.x, dualPoint p s.certificate)

noncomputable def algorithm (p : Params) :
    Algorithm (p.E × p.E) (Primitive p × Primitive p) (p.E × Constraint p) where
  Seed := Fin (iterations p + 1)
  law := ⟨(PMF.uniformOfFintype (Fin (iterations p + 1))).toMeasure, inferInstance⟩
  State := State p
  initial t := ⟨t.val, 0, p.x0, 0, 0⟩
  query s := (0, query p s)
  update := update p
  output := output p

end LongTails.Algorithms.SurjectiveProxLinear
