import LongTails.Proofs.DistributedJacobianStrongGrowthRefinementState

namespace LongTails.Proofs.DistributedJacobianStrongGrowthRefinementBroadcast

open LongTails.Setups.DistributedJacobianStrongGrowth
open LongTails.Algorithms.DistributedLocalExtragradientProtocol
open LongTails.Algorithms.DistributedLocalExtragradientTuning
open LongTails.Algorithms.DistributedLocalExtragradientWarmStart
open LongTails.Algorithms.DistributedLocalExtragradientProcess
open LongTails.Algorithms.LocalExtragradientQuantization
open DistributedJacobianStrongGrowthRefinementReference
open DistributedJacobianStrongGrowthRefinementState
open DistributedJacobianStrongGrowthPayloadAggregation

lemma refinement_root_total (p : Params) (hp : valid p)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (epoch : ℕ) :
    subtreeValues p p.root (refinementValues p g samples epoch) =
      aggregateCodes (refinementCodes p g samples epoch) := by
  funext j
  simp [subtreeValues, DistributedJacobianStrongGrowthTree.subtree_root p hp,
    refinementValues, aggregateCodes]

lemma refinement_broadcast_point (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω)
    (s : State p) (epoch : ℕ) (hs : s.phase = .refinement epoch)
    (hx : s.current = refinementPoint p g samples epoch)
    (ha : s.anchor = warmCenter p (warmCount p (localDepth p)) (warmWidth p (localDepth p))
      (warmSpacing p (localDepth p)) g samples) :
    (finishBroadcast p s (aggregateCodes (refinementCodes p g samples epoch))).current =
      refinementPoint p g samples (epoch + 1) := by
  have h := DistributedJacobianStrongGrowthProtocol.refinement_broadcast_reference p s epoch
    (p.n * (warmCount p (localDepth p) + 2 * localDepth p * epoch)) hs g samples
  dsimp only at h
  rw [hx, ha] at h
  exact h

lemma refinementState_broadcast (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (i : Fin p.n)
    (s : State p) (epoch : ℕ) (hs : s.phase = .refinement epoch)
    (hb : epoch < refinementCount p (localDepth p))
    (h : RefinementState p g samples i s)
    (ha : s.anchor = warmCenter p (warmCount p (localDepth p)) (warmWidth p (localDepth p))
      (warmSpacing p (localDepth p)) g samples) :
    RefinementState p g samples i
      (finishBroadcast p s (aggregateCodes (refinementCodes p g samples epoch))) := by
  have hx := refinement_broadcast_point p g samples s epoch hs (h.1 epoch hs).1 ha
  simp only [finishBroadcast, hs, DistributedJacobianStrongGrowthProtocol.startRefinement_current] at hx
  simp only [finishBroadcast, hs]
  exact refinementState_start p g samples i _ (epoch + 1) (by omega) hx

lemma refinementState_final_median (p : Params)
    (g : Fin p.n → Point p → p.Ω → Point p) (samples : ℕ → p.Ω) (i : Fin p.n)
    (s : State p) (values : Fin p.d → ℕ) (hs : s.phase = .median 1)
    (hx : (finishBroadcast p s values).current = refinementPoint p g samples 0) :
    RefinementState p g samples i (finishBroadcast p s values) := by
  have hr : ¬ 1 < (1 : ℕ) := by omega
  simp only [finishBroadcast, hs, ite_eq_right hr,
    DistributedJacobianStrongGrowthProtocol.startRefinement_current] at hx
  simp only [finishBroadcast, hs, ite_eq_right hr]
  exact refinementState_start p g samples i _ 0 (Nat.zero_le _) hx

end LongTails.Proofs.DistributedJacobianStrongGrowthRefinementBroadcast
