import LongTails.Setups.FiniteScaleConvolutionalSgd

open OracleTemplate
open LongTails.Setups.FiniteScaleConvolutionalSgd

namespace LongTails.Algorithms.FiniteScaleConvolutionalSgd

noncomputable def algorithm (p : Public) (η scale : ℝ) (period : ℕ+) :
    Algorithm (Query p) (Reply p.dimension) (Space p.dimension) where
  Seed := p.sampling.Ω
  law := p.sampling.law
  State := ScanState p
  initial := initial p scale
  query s := (0, scanQuery p s)
  update := scanUpdate p η scale period
  output s := s.point

noncomputable def output (p : Public) (η scale : ℝ) (period : ℕ+)
    (oracle : Oracle (Query p) (Reply p.dimension)) (calls : ℕ)
    (ω : p.sampling.Ω) (ξ : (k : ℕ) → oracle.Seed k) : Space p.dimension :=
  execute oracle (algorithm p η scale period) (fun _ => calls) ω ξ

noncomputable def stepSize (p : Public) : ℝ := p.derivativeMargin / (1000 * p.upper)

noncomputable def perturbation (p : Public) : ℝ := (stepSize p * p.contrast) ^ 2

noncomputable def backgroundStep (p : Public) : ℝ := stepSize p * p.lower

noncomputable def burnSteps (p : Public) : ℕ :=
  ⌈48 * (p.count : ℝ) / backgroundStep p ^ 2 * Real.log (24 / perturbation p)⌉₊

noncomputable def radius (p : Public) : ℝ :=
  10000 * (p.count : ℝ) / backgroundStep p ^ 2 * Real.log (24 / perturbation p)

noncomputable def runSteps (p : Public) : ℕ :=
  burnSteps p + ⌈96 * (p.count : ℝ) * radius p / p.derivativeMargin⌉₊

noncomputable def period (p : Public) : ℕ+ := ⟨runSteps p + 1, Nat.succ_pos _⟩

noncomputable def scale (p : Public) : ℝ :=
  Real.sqrt ((period p : ℝ) * (stepSize p + ‖p.initialReadout‖ ^ 2) / perturbation p)

noncomputable def tunedAlgorithm (p : Public) :
    Algorithm (Query p) (Reply p.dimension) (Space p.dimension) :=
  algorithm p (stepSize p) (scale p) (period p)

noncomputable def tunedOutput (p : Public) (oracle : Oracle (Query p) (Reply p.dimension))
    (calls : ℕ) (ω : p.sampling.Ω) (ξ : (k : ℕ) → oracle.Seed k) : Space p.dimension :=
  output p (stepSize p) (scale p) (period p) oracle calls ω ξ

end LongTails.Algorithms.FiniteScaleConvolutionalSgd
