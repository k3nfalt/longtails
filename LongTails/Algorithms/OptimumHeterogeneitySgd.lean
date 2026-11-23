import LongTails.Algorithms.OptimumHeterogeneityDesign
import LongTails.Algorithms.DistributedBatchedSgd
import LongTails.Algorithms.DistributedReplyTransform

namespace LongTails.Algorithms.OptimumHeterogeneitySgd

open DistributedTemplate LongTails.Setups.DistributedOptimumHeterogeneity OptimumHeterogeneityDesign

noncomputable def capacity (p : Params) (v : Fin p.n → ℝ) :=
  2 * (∑ i, (p.h i : ℝ)⁻¹) * Finset.univ.sup' Finset.univ_nonempty (fun i => (p.h i : ℝ) * weights p i * v i)

noncomputable def period (p : Params) := max 8 ⌈16 * capacity p p.L⌉₊

noncomputable def phase (p : Params) :=
  period p * (1 + ⌈Real.log (64 * (1 + (p.R / p.ε) ^ 2))⌉₊)

noncomputable def rounds (p : Params) := 2 * phase p + 1

noncomputable def stepSize (p : Params) (k : ℕ) : ℝ :=
  if k < phase p then 4 / period p else 8 / (2 * (period p : ℝ) + (k - phase p : ℕ))

noncomputable def batchTime (p : Params) : Time :=
  max (Finset.univ.sup p.h) (4096 * p.σ ^ 2 * cost p (weights p) / (p.ε ^ 2 * phase p)).toNNReal

noncomputable def batch (p : Params) (i : Fin p.n) := max 1 ⌈(batchTime p : ℝ) / (p.h i : ℝ)⌉₊

noncomputable def fraction (p : Params) (i : Fin p.n) : ℝ := (batch p i : ℝ) / (∑ j, batch p j : ℕ)

noncomputable def noiseRadius (p : Params) :=
  4 * capacity p (fun _ => 1) * (p.σ + Real.sqrt p.n * p.ζ) / period p

noncomputable def scale (p : Params) := p.R + 64 * rounds p * (noiseRadius p + p.ε)

noncomputable def tolerance (p : Params) := p.ε ^ 2 / (4096 * rounds p * scale p)

noncomputable def guardRadius (p : Params) :=
  p.R + p.ε + noiseRadius p + noiseRadius p ^ 2 / tolerance p

noncomputable def width (p : Params) : ℕ+ :=
  ⟨Nat.size ⌈64 * (1 + Real.sqrt p.d) * (guardRadius p + scale p) / tolerance p⌉₊ + 1, by omega⟩

noncomputable def transport (p : Params) : LongTails.Setups.DistributedSmoothNonconvex.Params where
  d := p.d
  n := p.n
  h := p.h
  l := p.l
  b := p.b
  Ω := p.Ω
  L := 1
  Δ := guardRadius p ^ 2 / 2
  ε := p.ε ^ 2
  σ := 0
  x0 := p.x0

noncomputable def config (p : Params) (T : Time) : DistributedBatchedSgd.Config (transport p) :=
  let c : DistributedBatchedSgd.Config (transport p) :=
    { iterations := ⟨rounds p, by unfold rounds; omega⟩, batch := batch p, width := width p }
  { c with slack := T - DistributedBatchedSgd.timeBudget (transport p) c }

abbrev LocalOracle (p : Params) := Fin p.n → Point p → p.Ω → Point p

noncomputable def multiplier (p : Params) (i : Fin p.n) (k : ℕ) :=
  stepSize p k * weights p i / fraction p i

noncomputable def scaled (p : Params) (g : LocalOracle p) (k : ℕ) : LocalOracle p :=
  fun i x s => multiplier p i k • g i x s

noncomputable def tagParams (p : Params) : LongTails.Setups.DistributedSmoothNonconvex.Params :=
  { transport p with Ω := ℕ × p.Ω, measurableΩ := inferInstance }

noncomputable def tagConfig (p : Params) (T : Time) : DistributedBatchedSgd.Config (tagParams p) where
  iterations := (config p T).iterations
  batch := batch p
  width := width p
  slack := (config p T).slack

noncomputable def algorithm (p : Params) (T : Time) :=
  DistributedReplyTransform.algorithm (DistributedBatchedSgd.algorithm (tagParams p) (tagConfig p T))
    ⟨2 * phase p, by change 2 * phase p < 2 * phase p + 1; omega⟩
    (fun v j _ (g : Point p) => Fin.cases 0 (fun i => multiplier p i (j / batch p i) • g) v)

noncomputable def iterate (p : Params) (T : Time) (g : LocalOracle p) (s : Samples p) : ℕ → Point p
  | 0 => p.x0
  | k + 1 =>
    let x := iterate p T g s k
    let v : Point p := DistributedBatchedSgd.estimate (transport p) (config p T) (scaled p g k) x k s
    x - v

noncomputable def output (p : Params) (T : Time) (g : LocalOracle p) (s : Samples p) :=
  iterate p T g s (2 * phase p)

end LongTails.Algorithms.OptimumHeterogeneitySgd
