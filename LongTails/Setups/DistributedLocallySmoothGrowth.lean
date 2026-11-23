import LongTails.Setups.DistributedMeanStrongGrowth

open DistributedTemplate

namespace LongTails.Setups.DistributedLocallySmoothGrowth

structure Params extends DistributedWeakInterpolation.Params where
  ρ : ℝ

noncomputable abbrev aggregate (p : Params) : DistributedMeanStrongGrowth.Params where
  d := p.d
  n := p.n
  Ω := p.Ω
  h := p.h
  l := p.l
  b := p.b
  L := max p.μ (Finset.univ.sup' Finset.univ_nonempty p.L)
  μ := p.μ
  ρ := p.ρ
  R := p.R
  σ := p.σ
  ε := p.ε
  x0 := p.x0

abbrev Point (p : Params) := DistributedMeanStrongGrowth.Point (aggregate p)
abbrev Functions (p : Params) := DistributedMeanStrongGrowth.Functions (aggregate p)
abbrev Samples (p : Params) := DistributedMeanStrongGrowth.Samples (aggregate p)

noncomputable def spec : Setup where
  Params := Params
  Public := Params
  publicInput := id
  numWorkers p := p.n + 1
  Instance := Functions
  ComputeQuery p := DistributedMeanStrongGrowth.spec.ComputeQuery (aggregate p)
  ComputeReply p := DistributedMeanStrongGrowth.spec.ComputeReply (aggregate p)
  CommReply p := DistributedMeanStrongGrowth.spec.CommReply (aggregate p)
  Output := Point
  valid p := DistributedMeanStrongGrowth.spec.valid (aggregate p) ∧ ∀ i, 0 ≤ p.L i
  admissible p f O := DistributedMeanStrongGrowth.spec.admissible (aggregate p) f O ∧
    ∀ i x y, ‖gradient (f i) x - gradient (f i) y‖ ≤ p.L i * ‖x-y‖
  successful p := DistributedMeanStrongGrowth.spec.successful (aggregate p)

end LongTails.Setups.DistributedLocallySmoothGrowth
