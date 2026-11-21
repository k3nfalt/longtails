import LongTails.Setups.DistributedRelativeGrowth
import LongTails.Proofs.RelativeGrowthRuntime

namespace LongTails.Theorems.DistributedRelativeGrowth

open DistributedTemplate
open LongTails.Setups.DistributedRelativeGrowth
open LongTails.Algorithms.RelativeGrowthBatches

noncomputable def budget (p : Params) : Time := by
  classical
  let r (t : ℝ) (i : Fin p.n) := (p.h i : ℝ) / (1-t+t*p.h i)
  let u (t : ℝ) (i : Fin p.n) := (p.n : ℝ) * r t i / ∑ j, r t j
  let t := if ht : ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ ∑ i, u s i ^ 2 = (p.n : ℝ)*p.ρ then ht.choose else 0
  let a (i : Fin p.n) := p.μ * u t i
  let I := ∑ i, a i ^ 2 / (p.h i : ℝ)
  let M := Finset.univ.sup' Finset.univ_nonempty (fun i => a i * max (a i) (p.L i))
  let κ := 2 * (∑ i, (p.h i : ℝ)⁻¹) * M / I
  let w := 1 + 2 * Real.log (4 + p.d + κ + (p.R^2 + (p.σ * Finset.univ.sup' Finset.univ_nonempty a / M)^2) / p.ε)
  exact (2048 * (p.σ^2 / (I*p.ε) + κ*(1+Real.log (1+p.R^2/p.ε)) *
    (((Finset.univ.sup p.h : Time) : ℝ) + p.l + p.b*(64+1024*(p.d : ℝ)*w)))).toNNReal

theorem result : TimedConvergence LongTails.Setups.DistributedRelativeGrowth.spec budget := by
  refine ⟨fun p => algorithm p (budget p), ?_⟩
  intro p hp
  refine ⟨trivial, fun f O hO => ?_⟩
  exact Proofs.RelativeGrowthRuntime.successful hp (budget p) f O hO
    (Proofs.RelativeGrowthRuntime.enough hp (budget p) (Real.le_coe_toNNReal _))

end LongTails.Theorems.DistributedRelativeGrowth
