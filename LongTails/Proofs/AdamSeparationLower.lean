import LongTails.Proofs.AdamFiniteLower
import LongTails.Proofs.AdamFiniteLaw

namespace LongTails.Proofs.AdamSeparationLower

open OracleTemplate MeasureTheory
open LongTails.Algorithms.MatrixPolar
open LongTails.Setups.SpectralSmoothAdamComparison
open LongTails.Proofs.AdamScalarProcess LongTails.Proofs.AdamFinitePaths
open LongTails.Proofs.AdamSeparationModel LongTails.Proofs.AdamMatrixGeometry

lemma adam_lower {p : Public} (hp : spec.valid p) : AdamLower p := by
  intro a ha B T hB A hA
  refine ⟨hardObjective p, hardOracle p, hard_admissible hp, ?_⟩
  intro hsuccess
  obtain ⟨draw, hdraw, hlaw, hA⟩ := hA
  obtain ⟨_, _, hacc⟩ := hsuccess
  have hr : 1 < p.r := by have := hp.1; omega
  have hL := hp.2.1
  have hε := hp.2.2.2.1
  let ℓ := p.L / 2
  let c := 4 * p.ε / ((p.r : ℝ) - 1)
  let w := 8 * p.ε / p.L
  let D := p.Δ / (4 * p.ε)
  have hw : 0 < w := by dsimp [w]; positivity
  let z := fun (ω : Fin (T + 1) → Fin B → Bool) =>
    trajectory a p.r ℓ c w D (pathNoise p.ε B (T + 1) ω)
  let F := fun (j : Fin (T + 1)) (ω : Fin (T + 1) → Fin B → Bool) =>
    ℓ * |(z ω j).stiff| + ((p.r : ℝ) - 1) *
      |c * SeparationInstance.valleySlope w D (z ω j).quiet|
  have hexec (seed : A.Seed) (ξ : ℕ → Bool) :
      execute (hardOracle p) A (fun _ => B * (T + 1)) seed ξ =
        p.x0 + mixedProjection p.r
          (z (AdamFiniteLaw.blockPrefix B (T + 1) ξ) (draw seed)).stiff
          (z (AdamFiniteLaw.blockPrefix B (T + 1) ξ) (draw seed)).quiet := by
    have he := AdamSampledExecution.execute_eq_trajectory hr hB a ℓ c w D p.ε hw p.x0 draw hA seed ξ
    simpa only [z, AdamFiniteLaw.trajectory_blockPrefix a p.r ℓ c w D p.ε B (T + 1)
      (draw seed) (by omega) ξ, hardOracle, hardObjective, ℓ, c, w, D] using he
  have hvalue (seed : A.Seed) (ξ : ℕ → Bool) :
      nuclearNorm (gradient (hardObjective p)
        (execute (hardOracle p) A (fun _ => B * (T + 1)) seed ξ)) =
          F (draw seed) (AdamFiniteLaw.blockPrefix B (T + 1) ξ) := by
    rw [hexec]
    change nuclearNorm (gradient (AdamSeparationInstance.objective ℓ c w D p.x0) _) = _
    rw [AdamSeparationInstance.nuclear_gradient_mixed hr ℓ c D hw]
    simp only [F, abs_mul, abs_of_nonneg (show 0 ≤ ℓ by dsimp [ℓ]; positivity)]
  have hi := AdamFiniteLaw.output_integral (A.law : Measure _) B (T + 1) draw hdraw hlaw F
  change (∫ z : A.Seed × (ℕ → Bool), nuclearNorm (gradient (hardObjective p)
    (execute (hardOracle p) A (fun _ => B * (T + 1)) z.1 z.2))
    ∂(A.law : Measure _).prod (signStream : Measure _)) ≤ p.ε at hacc
  have hacc' : ((T + 1 : ℕ) * (Fintype.card (Fin (T + 1) → Fin B → Bool) : ℝ))⁻¹ *
      (∑ j, ∑ ω, F j ω) ≤ p.ε := by
    rw [← hi]
    simpa only [← hvalue] using hacc
  have hden : 0 < ((T + 1 : ℕ) * (Fintype.card (Fin (T + 1) → Fin B → Bool) : ℝ)) := by positivity
  have hsum : (∑ j, ∑ ω, F j ω) ≤
      (T + 1 : ℕ) * (Fintype.card (Fin (T + 1) → Fin B → Bool) : ℝ) * p.ε := by
    rw [← div_eq_inv_mul, div_le_iff₀ hden] at hacc'
    nlinarith
  exact AdamFiniteLower.finite_cost p hp a ha hB hsum

end LongTails.Proofs.AdamSeparationLower
