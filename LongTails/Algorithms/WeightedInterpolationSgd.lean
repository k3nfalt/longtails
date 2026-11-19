import LongTails.Algorithms.WeakInterpolationDesign
import LongTails.Algorithms.DistributedReplyTransform
import LongTails.Algorithms.DistributedBatchedSgd
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LongTails.Algorithms.WeightedInterpolationSgd

open DistributedTemplate LongTails.Setups.DistributedWeakInterpolation WeakInterpolationDesign

noncomputable def period (p : Params) : ℕ := max 1 ⌈4 * smoothness p / information p⌉₊

noncomputable def phase (p : Params) : ℕ :=
  period p * (1 + ⌈Real.log (64 * (1 + p.R ^ 2 / p.ε))⌉₊)

noncomputable def rounds (p : Params) : ℕ := 2 * phase p + 1

noncomputable def stepSize (p : Params) (k : ℕ) : ℝ :=
  if k < phase p then 2 / (information p * period p)
  else 4 / (information p * (2 * period p + (k - phase p : ℕ)))

noncomputable def batchTime (p : Params) : Time :=
  max (Finset.univ.sup p.h) (256 * p.σ ^ 2 / (information p * p.ε * phase p)).toNNReal

noncomputable def batch (p : Params) (i : Fin p.n) : ℕ :=
  max 1 ⌈(batchTime p : ℝ) / (p.h i : ℝ)⌉₊

noncomputable def fraction (p : Params) (i : Fin p.n) : ℝ :=
  (batch p i : ℝ) / (∑ j, batch p j : ℕ)

noncomputable def scale (p : Params) : ℝ :=
  p.R + (rounds p : ℝ) * (8 * noiseRadius p + 8 * Real.sqrt p.ε)

noncomputable def tolerance (p : Params) : ℝ := p.ε / (4096 * rounds p * scale p)

noncomputable def guardRadius (p : Params) : ℝ :=
  p.R + Real.sqrt p.ε + noiseRadius p ^ 2 / tolerance p

noncomputable def width (p : Params) : ℕ+ :=
  ⟨Nat.size ⌈64 * (1 + Real.sqrt p.d) * (guardRadius p + scale p) / tolerance p⌉₊ + 1, by omega⟩

noncomputable def transport (p : Params) : LongTails.Setups.DistributedSmoothNonconvex.Params where
  d := p.d
  n := p.n
  Ω := ℕ × p.Ω
  h := p.h
  l := p.l
  b := p.b
  L := 1
  Δ := guardRadius p ^ 2 / 2
  ε := p.ε
  σ := 0
  x0 := p.x0

noncomputable def config (p : Params) (T : Time) : DistributedBatchedSgd.Config (transport p) :=
  let cfg : DistributedBatchedSgd.Config (transport p) :=
    { iterations := ⟨rounds p, by unfold rounds; omega⟩, batch := batch p, width := width p }
  { cfg with slack := T - DistributedBatchedSgd.timeBudget (transport p) cfg }

noncomputable def factor (p : Params) (i : Fin p.n) (j : ℕ) : ℝ :=
  stepSize p (j / batch p i) * weights p i / fraction p i

noncomputable def algorithm (p : Params) (T : Time) :=
  DistributedReplyTransform.algorithm (DistributedBatchedSgd.algorithm (transport p) (config p T))
    ⟨2 * phase p, by change 2 * phase p < 2 * phase p + 1; omega⟩
    (fun v j _ (g : Point p) => Fin.cases 0 (fun i => factor p i j • g) v)

abbrev LocalOracle (p : Params) := Fin p.n → Point p → p.Ω → Point p

noncomputable def rawParams (p : Params) : LongTails.Setups.DistributedSmoothNonconvex.Params :=
  { transport p with Ω := p.Ω, measurableΩ := p.measurableΩ }

noncomputable def rawConfig (p : Params) (T : Time) : DistributedBatchedSgd.Config (rawParams p) where
  iterations := (config p T).iterations
  batch := batch p
  width := width p
  slack := (config p T).slack

noncomputable def scaled (p : Params) (g : LocalOracle p) (k : ℕ) : LocalOracle p :=
  fun i x ω => (stepSize p k * weights p i / fraction p i) • g i x ω

noncomputable def iterate (p : Params) (T : Time) (g : LocalOracle p) (s : Samples p) : ℕ → Point p
  | 0 => p.x0
  | k + 1 =>
    let x := iterate p T g s k
    let v : Point p := DistributedBatchedSgd.estimate (rawParams p) (rawConfig p T) (scaled p g k) x k s
    x - v

noncomputable def output (p : Params) (T : Time) (g : LocalOracle p) (s : Samples p) : Point p :=
  iterate p T g s (2 * phase p)

end LongTails.Algorithms.WeightedInterpolationSgd
