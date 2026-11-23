import LongTails.Setups.DistributedMeanStrongGrowth
import LongTails.Proofs.GradientDiversityConvergence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Theorems.DistributedGradientDiversity

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedMeanStrongGrowth
open LongTails.Algorithms.GradientDiversitySgd
open LongTails.Proofs

noncomputable def budget (p : Params) : Time := by
  classical
  let v (t : ℝ) (i : Fin p.n) := (p.h i : ℝ) / ((1-t)*p.h i+t)
  let u (t : ℝ) (i : Fin p.n) := p.n * v t i / ∑ j, v t j
  let t := if h : ∃ t : ℝ, 0 ≤ t ∧ min (1-t) (p.n*p.ρ - ∑ i, u t i^2) = 0
    then h.choose else 0
  let a (i : Fin p.n) := p.μ * u t i
  let I := ∑ i, (a i)^2 / p.h i
  let S := ∑ i, (p.h i : ℝ)⁻¹
  let U := Finset.univ.sup' Finset.univ_nonempty a
  let M := p.L * max (U * min (p.n : ℝ) (1 + Real.sqrt (p.n * (p.ρ-1))))
    (p.n * Finset.univ.sup' Finset.univ_nonempty (fun i => a i / (p.h i : ℝ)) / S)
  let A := 2 * S * M / I
  let w := Nat.size ⌈2 + p.d + A + (p.R^2 + (p.σ * U / M)^2)/p.ε⌉₊
  exact (2048 * (p.σ^2 / (I * p.ε) + A * (1 + Real.log (1 + p.R^2 / p.ε)) *
    (((Finset.univ.sup p.h : Time) : ℝ) + p.l + p.b * (64 + 1024 * (p.d : ℝ) * w)))).toNNReal

theorem result : TimedConvergence LongTails.Setups.DistributedMeanStrongGrowth.spec budget := by
  refine ⟨fun p => algorithm p (budget p), ?_⟩
  intro p hp
  change Params at p
  refine ⟨trivial, GradientDiversityConvergence.success hp (budget p) ?_⟩
  apply GradientDiversityConvergence.runtime hp
  have he : scale p = p.L * max (largest p * spread p)
      (p.n * Finset.univ.sup' Finset.univ_nonempty (gain p) / speed p) := by
    unfold scale
    rw [GradientDiversityConvergence.peak_eq]
  dsimp only
  rw [he]
  exact Real.le_coe_toNNReal _

end LongTails.Theorems.DistributedGradientDiversity
