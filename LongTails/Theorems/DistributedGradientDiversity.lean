import LongTails.Setups.DistributedGradientDiversity
import LongTails.Proofs.GradientDiversityConvergence

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Theorems.DistributedGradientDiversity

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedGradientDiversity
open LongTails.Algorithms.GradientDiversitySgd
open LongTails.Proofs

noncomputable def budget (p : Params) : Time := by
  classical
  let r (t : ℝ) (i : Fin p.n) := (p.h i : ℝ) / (1 - t + t * (p.h i : ℝ))
  let a (t : ℝ) (i : Fin p.n) := (p.n : ℝ) * r t i / ∑ j, r t j
  let t : ℝ := if h : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∑ i, (a t i)^2 = (p.n : ℝ)*p.ρ
    then h.choose else 0
  let u (i : Fin p.n) := p.μ / 2 * a t i
  let I := ∑ i, (u i)^2 / p.h i
  let S := ∑ i, (p.h i : ℝ)⁻¹
  let U := Finset.univ.sup' Finset.univ_nonempty u
  let M := p.L * max (U * min (p.n : ℝ) (1 + Real.sqrt (p.n * (p.ρ-1))))
    (p.n * Finset.univ.sup' Finset.univ_nonempty (fun i => u i / (p.h i : ℝ)) / S)
  let A := 2 * S * M / I
  let w := Nat.size ⌈2 + p.d + A + (p.R^2 + (p.σ * U / M)^2)/p.ε⌉₊
  exact (2048 * (p.σ^2 / (I * p.ε) + A * (1 + Real.log (1 + p.R^2 / p.ε)) *
    (((Finset.univ.sup p.h : Time) : ℝ) + p.l + p.b * (64 + 1024 * (p.d : ℝ) * w)))).toNNReal

theorem result : TimedConvergence LongTails.Setups.DistributedGradientDiversity.spec budget := by
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
