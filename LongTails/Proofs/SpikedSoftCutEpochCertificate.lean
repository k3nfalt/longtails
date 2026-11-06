import LongTails.Proofs.SpikedSoftCutEpochProcess
import LongTails.Proofs.SpikedSoftCutCertificate
import LongTails.Proofs.SpikedSoftCutPrimal
import LongTails.Proofs.SpikedSoftCutFreshness

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SpikedSoftCutEpochCertificate

open LongTails.Setups.SpikedSubGaussianConvex
open LongTails.Algorithms.SpikedSoftCut
open LongTails.Algorithms.SpikedSoftCutMethod
open SpikedSoftCutEpochProcess

lemma seeded_inner_points (q : Params) (c : Config) (hb : 0 < c.b) (a : ℝ)
    (g : Space q → q.Ω → Space q) (ξ : ℕ → q.Ω) (i : Fin c.T) :
    innerPoints q c.α c.T c.b (fun j => tail q (innerSeedReplies q c a g ξ j)) i =
      innerSeedPoint q c a g i ξ := by
  exact (innerSeedPoint_generator q c hb a g ξ i).symm

lemma seeded_inner_errors (q : Params) (c : Config) (hb : 0 < c.b) (a : ℝ)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q) (ξ : ℕ → q.Ω) (i : Fin c.T) :
    innerEstimates q c.α c.T c.b (fun j => tail q (innerSeedReplies q c a g ξ j)) i -
      tail q (v (join q a (innerPoints q c.α c.T c.b (fun j => tail q (innerSeedReplies q c a g ξ j)) i))) =
      SoftCutPredictableBatches.batchError (innerParams q c.α) c.α (2/c.α) c.b
        (innerOracle q a g) (fun x => tail q (v (join q a x))) i ξ := by
  rw [seeded_inner_points q c hb]
  exact (SoftCutBatchConcentration.batchError_eq_estimate_error (innerParams q c.α)
    c.α (2/c.α) c.b hb (innerOracle q a g) (fun x => tail q (v (join q a x))) i ξ).symm

lemma seeded_true_certificate (q : Params) (c : Config) (a M V W r : ℝ)
    (g : Space q → q.Ω → Space q) (v : Space q → Space q) (ξ : ℕ → q.Ω)
    (hα : 0 < c.α) (hR : 0 < q.R) (hG : 0 ≤ q.G) (hT : 0 < c.T) (hb : 0 < c.b) (hn : 0 < c.n)
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hM : q.G+Real.sqrt V ≤ M)
    (hr : 0 < r) (hrR : r ≤ q.R)
    (hlog : (q.m : ℝ)*Real.log (q.R/r) ≤ (c.T : ℝ)/48) (hrM : 2*r*M ≤ c.α/96)
    (hgrad : ∀ x, ‖v x‖ ≤ q.G)
    (hgrid : (c.α/2+2*q.R*M)*c.T/c.n ≤ c.α*c.T/32)
    (hoperator : ‖innerErrorMatrix q c a g v ξ‖^2 ≤ V)
    (hintercept : ‖innerErrorIntercept q c a g v ξ‖^2 ≤ W)
    (hnoise : 2*(q.R^2*V+W)*c.T ≤ (c.α*c.T/32)^2) :
    ∀ y, ‖y‖ ≤ q.R →
      ∑ i : Fin c.T, weights q c (innerSeedReplies q c a g ξ) i *
        ⟪tail q (v (join q a (supportPoints q c (innerSeedReplies q c a g ξ) i))),
          supportPoints q c (innerSeedReplies q c a g ξ) i-y⟫ ≤ c.α/2 := by
  let replies := fun j => tail q (innerSeedReplies q c a g ξ j)
  let gradients := fun i : Fin c.T => tail q (v (join q a (innerPoints q c.α c.T c.b replies i)))
  have he (i : Fin c.T) := seeded_inner_errors q c hb a g v ξ i
  have hop : ∀ u : Fin c.T → ℝ,
      ‖∑ i, u i • (innerEstimates q c.α c.T c.b replies i-gradients i)‖^2 ≤ V*∑ i, u i^2 := by
    intro u
    simp_rw [show ∀ i, innerEstimates q c.α c.T c.b replies i-gradients i =
      SoftCutPredictableBatches.batchError (innerParams q c.α) c.α (2/c.α) c.b
        (innerOracle q a g) (fun x => tail q (v (join q a x))) i ξ from he]
    exact SubGaussianNetProbability.columnOperator_square_bound _ V hoperator u
  have hint : ∑ i, ⟪innerEstimates q c.α c.T c.b replies i-gradients i,
      innerPoints q c.α c.T c.b replies i⟫^2 ≤ W := by
    simp_rw [show ∀ i, innerEstimates q c.α c.T c.b replies i-gradients i =
      SoftCutPredictableBatches.batchError (innerParams q c.α) c.α (2/c.α) c.b
        (innerOracle q a g) (fun x => tail q (v (join q a x))) i ξ from he]
    have hp (i : Fin c.T) : innerPoints q c.α c.T c.b replies i = innerSeedPoint q c a g i ξ :=
      seeded_inner_points q c hb a g ξ i
    simp_rw [hp]
    have hh := hintercept
    rw [innerErrorIntercept, EuclideanSpace.real_norm_sq_eq] at hh
    convert! hh using 1
  exact SpikedSoftCutCertificate.generator_true_certificate q c.α M V W r c.T c.b c.n replies gradients
    hα hR hG hT hn hV hW hM hr hrR hlog hrM
    (fun i => (SpikedSoftCutCoordinates.norm_tail_le q _).trans (hgrad _)) hgrid hop hint hnoise

lemma epoch_primal_certificate (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (k : ℕ) (state : OuterState q) (g : Space q → q.Ω → Space q) (v : Space q → Space q)
    (f : Space q → ℝ) (ξ : ℕ → q.Ω) (xstar : Space q) (hxstar : ‖xstar‖ ≤ q.R)
    (δ : ℝ) (hconvex : ConvexOn ℝ Set.univ f)
    (hsupport : ∀ x y, ⟪v x,y-x⟫ ≤ f y-f x)
    (hcert : ∀ y, ‖y‖ ≤ q.R →
      ∑ i : Fin c.T, weights q c (innerSeedReplies q c (center q state) g ξ) i *
        ⟪tail q (v (join q (center q state) (supportPoints q c (innerSeedReplies q c (center q state) g ξ) i))),
          supportPoints q c (innerSeedReplies q c (center q state) g ξ) i-y⟫ ≤ δ) :
    f (primalOutput q c state (epochReplies q c k state g ξ))-f xstar +
      SpikedSoftCutFreshness.headSlope q c (center q state) v (innerSeedReplies q c (center q state) g ξ) *
        (head q xstar-center q state) ≤ δ := by
  let r := innerSeedReplies q c (center q state) g ξ
  have hw (i : Fin c.T) : 0 ≤ weights q c r i :=
    SpikedSoftCutSelection.certificateWeights_nonneg q c.α c.T c.n hn _ _ i
  have hs : ∑ i, weights q c r i = 1 :=
    SpikedSoftCutSelection.certificateWeights_sum q c.α c.T c.n hT _ _
  have hh := SpikedSoftCutPrimal.weighted_primal_certificate q f v hconvex hsupport
    (weights q c r) hw hs (center q state) (head q xstar) δ (supportPoints q c r) (tail q xstar)
    (hcert _ ((SpikedSoftCutCoordinates.norm_tail_le q xstar).trans hxstar))
  rw [SpikedSoftCutCoordinates.join_head_tail] at hh
  rw [SpikedSoftCutMethodExecution.primalOutput_prefix q c state (epochReplies q c k state g ξ) r
    (epochReplies_inner_prefix q c k state g ξ)]
  exact hh

lemma epoch_head_bound (q : Params) (c : Config) (hT : 0 < c.T) (hn : 0 < c.n)
    (a : ℝ) (g : Space q → q.Ω → Space q) (v : Space q → Space q) (ξ : ℕ → q.Ω)
    (hgrad : ∀ x, ‖v x‖ ≤ q.G) :
    |SpikedSoftCutFreshness.headSlope q c a v (innerSeedReplies q c a g ξ)| ≤ q.G := by
  let r := innerSeedReplies q c a g ξ
  have hw (i : Fin c.T) : 0 ≤ weights q c r i :=
    SpikedSoftCutSelection.certificateWeights_nonneg q c.α c.T c.n hn _ _ i
  have hs : ∑ i, weights q c r i = 1 :=
    SpikedSoftCutSelection.certificateWeights_sum q c.α c.T c.n hT _ _
  exact SpikedSoftCutPrimal.weighted_head_bound q (weights q c r) hw hs
    (fun i => v (join q a (supportPoints q c r i))) (fun i => hgrad _)

end LongTails.Proofs.SpikedSoftCutEpochCertificate
