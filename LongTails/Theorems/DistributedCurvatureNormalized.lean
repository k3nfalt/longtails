import LongTails.Setups.DistributedHessianLipschitzNonconvex
import LongTails.Proofs.DistributedNormalizedAccuracy
import LongTails.Proofs.DistributedNormalizedExecution
import LongTails.Proofs.DistributedNormalizedRuntime
import LongTails.Proofs.DistributedNormalizedZeroDim

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Theorems.DistributedCurvatureNormalized

open MeasureTheory DistributedTemplate
open LongTails.Setups.DistributedHessianLipschitzNonconvex
open LongTails.Algorithms.DistributedNormalizedTuning

noncomputable def budget (p : Params) : Time := Real.toNNReal (33554432 * (1 + p.L * p.Δ / p.ε ^ 2) * ((p.l : ℝ) + (max ((Finset.univ.sup p.h : DistributedTemplate.Time) : ℝ) (max ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 66 : ℕ)) (max ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)⌉₊ + 66 : ℕ)) (max (p.d * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 66 : ℕ)) / p.n) (max (p.d * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)⌉₊ + 66 : ℕ)) / Real.sqrt p.n) (max (((p.d : ℝ) ^ 3 * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 66 : ℕ)) * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)⌉₊ + 66 : ℕ)) ^ 2 / p.n) ^ (1 / 3 : ℝ)) (max (p.σ ^ 2 * ((Finset.univ.sup p.h : DistributedTemplate.Time) : ℝ) / (p.n * p.ε ^ 2)) (max (Real.sqrt (p.d * p.σ ^ 2 * ((Finset.univ.sup p.h : DistributedTemplate.Time) : ℝ) * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + ((p.d : ℝ) ^ 2 * (1 + p.L * p.Δ / p.ε ^ 2) + p.d * min (p.σ ^ 2 / p.ε ^ 2) (p.n : ℝ)) / Real.sqrt p.n)⌉₊ + 66 : ℕ)) / (p.n * p.ε ^ 2))) (p.d * ((p.b : ℝ) * (Nat.size ⌈1048576 * (1 + (1 + p.L * p.Δ / p.ε ^ 2) * Real.sqrt p.d)⌉₊ + 66 : ℕ)) * min 1 (Real.sqrt (p.Q * p.ε) / p.L))))))))))))

theorem result : DistributedTemplate.TimedConvergence LongTails.Setups.DistributedHessianLipschitzNonconvex.spec budget := by
  refine ⟨fun p => LongTails.Algorithms.DistributedNormalizedTraining.algorithm p (budget p), ?_⟩
  intro p hp
  change Params at p
  obtain ⟨⟨hh, hL, hΔ, _, hε⟩, hQ⟩ := hp
  refine ⟨trivial, ?_⟩
  intro f O hO
  change Point p → ℝ at f
  obtain ⟨⟨hg, hlip, ⟨lower, hlower, hgap⟩, g, μ, P, rfl, hworkers, horacle⟩, hdiff, hH⟩ := hO
  change (∀ᵐ seed ∂(law (LongTails.Setups.DistributedSmoothNonconvex.system p.toParams g P)
      (LongTails.Algorithms.DistributedNormalizedTraining.algorithm p (budget p)) : Measure _),
      FiniteEvents (LongTails.Setups.DistributedSmoothNonconvex.system p.toParams g P)
        (LongTails.Algorithms.DistributedNormalizedTraining.algorithm p (budget p)) (budget p) seed) ∧
    spec.successful p f (fun seed =>
      execute (LongTails.Setups.DistributedSmoothNonconvex.system p.toParams g P)
        (LongTails.Algorithms.DistributedNormalizedTraining.algorithm p (budget p)) (budget p) seed.1 seed.2)
      (law (LongTails.Setups.DistributedSmoothNonconvex.system p.toParams g P)
        (LongTails.Algorithms.DistributedNormalizedTraining.algorithm p (budget p)))
  by_cases hd : 0 < p.d
  · let : Nonempty (Fin p.d) := ⟨⟨0, hd⟩⟩
    have halg : LongTails.Algorithms.DistributedNormalizedTraining.algorithm p (budget p) =
        LongTails.Algorithms.DistributedNormalizedProtocol.algorithm p (config p) (budget p) := by
      unfold LongTails.Algorithms.DistributedNormalizedTraining.algorithm
      exact dite_eq_left hd
    rw [halg]
    have hbudget : LongTails.Algorithms.DistributedNormalizedProtocol.executionTime p (config p) ≤ budget p :=
      LongTails.Proofs.DistributedNormalizedRuntime.execution_time_explicit p hd hL.le hΔ hε hh
    refine ⟨Filter.Eventually.of_forall (fun seed => ?_), ?_⟩
    · exact LongTails.Proofs.DistributedNormalizedExecution.finiteEvents p (config p) (budget p)
        g P seed.1.2 seed.2 seed.1.1
    · have he : (fun seed : LongTails.Algorithms.DistributedNormalizedDownlink.Seed p (config p) ×
          LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams =>
          execute (LongTails.Setups.DistributedSmoothNonconvex.system p.toParams g P)
            (LongTails.Algorithms.DistributedNormalizedProtocol.algorithm p (config p) (budget p))
            (budget p) seed.1 seed.2) =
          fun seed => LongTails.Algorithms.DistributedNormalizedDownlink.output p (config p)
            seed.1.2 g seed.2 seed.1.1 := by
        funext seed
        exact LongTails.Proofs.DistributedNormalizedExecution.execute_output p (config p) (budget p)
          g P seed.1.2 seed.2 seed.1.1 hbudget
      have hacc := LongTails.Proofs.DistributedNormalizedAccuracy.output_accuracy p hd hL hΔ hε hQ hh
        f hg hlip hdiff hH lower hlower hgap g μ (fun i => (horacle i).2) P hworkers
        (fun i => (horacle i).1)
      change Measurable _ ∧ Integrable _ _ ∧ _ ≤ p.ε
      change Measurable _ ∧ Integrable _
        ((LongTails.Algorithms.DistributedNormalizedDownlink.seedLaw p (config p) : Measure (LongTails.Algorithms.DistributedNormalizedDownlink.Seed p (config p))).prod
          (P : Measure (LongTails.Setups.DistributedSmoothNonconvex.Samples p.toParams))) ∧ _ ≤ p.ε
      erw [he]
      exact hacc
  · have halg : LongTails.Algorithms.DistributedNormalizedTraining.algorithm p (budget p) =
        LongTails.Algorithms.DistributedBatchedSgd.algorithm p.toParams
          (LongTails.Algorithms.DistributedNormalizedTraining.zeroConfig p (budget p)) := by
      unfold LongTails.Algorithms.DistributedNormalizedTraining.algorithm
      exact dite_eq_right hd
    rw [halg]
    refine ⟨Filter.Eventually.of_forall (fun seed => ?_), ?_⟩
    · exact LongTails.Proofs.DistributedNormalizedZeroDim.finiteEvents p (budget p) g P seed.1 seed.2
    · exact LongTails.Proofs.DistributedNormalizedZeroDim.successful p (Nat.eq_zero_of_not_pos hd)
        hε.le f _ _

end LongTails.Theorems.DistributedCurvatureNormalized
