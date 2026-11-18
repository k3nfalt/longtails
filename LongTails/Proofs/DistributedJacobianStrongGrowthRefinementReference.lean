import LongTails.Proofs.DistributedJacobianStrongGrowthWorkerReference
import LongTails.Proofs.DistributedJacobianStrongGrowthPayloadAggregation
import LongTails.Algorithms.DistributedLocalExtragradientProcess

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementReference

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientProcess
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart
open LongTails.Algorithms.LocalExtragradientQuantization
open LongTails.Algorithms.DistributedQuantization
open DistributedJacobianStrongGrowthWorkerReference
open DistributedJacobianStrongGrowthPayloadAggregation

noncomputable def refinementPoint (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (epoch : ℕ) : Point p :=
  refineRun p (warmCount p (localDepth p)) (localDepth p) (clipRadius p (localDepth p))
    (refinementWidth p (localDepth p)) (refinementSpacing p (localDepth p)) (radius p (localDepth p)) g
    (warmCenter p (warmCount p (localDepth p)) (warmWidth p (localDepth p))
      (warmSpacing p (localDepth p)) g samples) samples epoch

noncomputable def refinementSamples (p : Params) (samples : ℕ → p.Ω) (epoch : ℕ) (i : Fin p.n) : ℕ → p.Ω :=
  fun k => samples (p.n * (warmCount p (localDepth p) + 2 * localDepth p * epoch) + (p.n * k + i.val))

noncomputable def refinementCodes (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (epoch : ℕ) (i : Fin p.n) :
    Grid p.d (refinementWidth p (localDepth p)) :=
  quantize p.d (refinementWidth p (localDepth p)) (refinementSpacing p (localDepth p))
    (OracleTemplate.clip (clipRadius p (localDepth p))
      (LongTails.Algorithms.LocalNonlinearExtragradient.run (1 / (4 * p.L)) (g i)
        (refinementPoint p g samples epoch) (refinementSamples p samples epoch i) (localDepth p) -
          refinementPoint p g samples epoch))

noncomputable def refinementValues (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (epoch : ℕ) : Fin p.n → Fin p.d → ℕ :=
  fun i j => (refinementCodes p g samples epoch i j).val

lemma refinementPoint_zero (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) :
    refinementPoint p g samples 0 = warmCenter p (warmCount p (localDepth p))
      (warmWidth p (localDepth p)) (warmSpacing p (localDepth p)) g samples := rfl

lemma refinementPoint_final (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) :
    refinementPoint p g samples (refinementCount p (localDepth p)) = output p (localDepth p) g samples := rfl

lemma refinementValues_fits (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (epoch : ℕ) :
    ∀ i j, refinementValues p g samples epoch i j < 2 ^ refinementWidth p (localDepth p) := by
  intro i j
  exact (refinementCodes p g samples epoch i j).isLt

lemma refinementSubtree_fits (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (epoch : ℕ) (v : Fin p.n) :
    ∀ j, subtreeValues p v (refinementValues p g samples epoch) j <
      2 ^ (refinementWidth p (localDepth p) + LongTails.Algorithms.DistributedLocalExtragradientMedianSearch.countWidth p.n) :=
  subtreeValues_grid_fits p v _ _ (refinementValues_fits p g samples epoch)

lemma refinement_finishLocal_own (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (i : Fin p.n) (s : State p) (epoch : ℕ) (hs : s.phase = .refinement epoch)
    (hx : s.current = refinementPoint p g samples epoch) :
    (finishLocal p s (LongTails.Algorithms.LocalNonlinearExtragradient.run (1 / (4 * p.L)) (g i)
      (refinementPoint p g samples epoch) (refinementSamples p samples epoch i) (localDepth p))).own =
        refinementValues p g samples epoch i := by
  funext j
  simp only [finishLocal, hs, hx, refinementValues, refinementCodes]

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementReference
