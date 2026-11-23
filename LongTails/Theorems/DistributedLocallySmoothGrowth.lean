import LongTails.Setups.DistributedLocallySmoothGrowth
import LongTails.Proofs.LocallySmoothGrowth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Theorems.DistributedLocallySmoothGrowth

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedLocallySmoothGrowth
open LongTails.Algorithms.LocallySmoothGrowthSgd
open LongTails.Proofs

noncomputable def budget (p : Params) : Time := by
  classical
  let v (t : ℝ) (i : Fin p.n) := (p.h i : ℝ) / ((1-t)*p.h i+t)
  let u (t : ℝ) (i : Fin p.n) := p.n * v t i / ∑ j, v t j
  let t := if h : ∃ t : ℝ, 0 ≤ t ∧ min (1-t) (p.n*p.ρ - ∑ i, u t i^2) = 0
    then h.choose else 0
  let a (i : Fin p.n) := p.μ * u t i
  let I := ∑ i, (a i)^2 / p.h i
  let M := Finset.univ.sup' Finset.univ_nonempty (fun i => a i * max (a i) (p.L i))
  let A := 2 * (∑ i, (p.h i : ℝ)⁻¹) * M / I
  let w := 1 + 2 * Real.log (4 + p.d + A +
    (p.R^2 + (p.σ * Finset.univ.sup' Finset.univ_nonempty a / M)^2)/p.ε)
  exact (2048 * (p.σ^2 / (I * p.ε) + A * (1 + Real.log (1 + p.R^2 / p.ε)) *
    (((Finset.univ.sup p.h : Time) : ℝ) + p.l + p.b * (64 + 1024 * (p.d : ℝ) * w)))).toNNReal

theorem result : TimedConvergence LongTails.Setups.DistributedLocallySmoothGrowth.spec budget := by
  refine ⟨fun p => algorithm p (budget p), ?_⟩
  intro p hp
  change Params at p
  refine ⟨trivial, ?_⟩
  intro f O hO
  obtain ⟨⟨hf, hF, hρ, ⟨z, hz, hR, hq⟩, g, ν, P, rfl, hw, hi⟩, hL⟩ := hO
  have G : DistributedGrowthGeometry.Geometry (aggregate p) f :=
    ⟨hp.1, fun i => (hf i).1, fun i => (hf i).2, hF, hρ⟩
  have D := LocallySmoothGrowth.bounds hp G hL hz hR hq hw hi
  exact GradientDiversityConvergence.executed_of_bounds G (budget p)
    (LocallySmoothGrowth.runtime hp (budget p) (Real.le_coe_toNNReal _)) D

end LongTails.Theorems.DistributedLocallySmoothGrowth
