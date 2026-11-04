import LongTails.Algorithms.NestedAnchoredInexactJacobian
import LongTails.Proofs.InexactJacobianPhase

open scoped RealInnerProductSpace

namespace LongTails.Proofs.InexactJacobianModel

open LongTails.Setups.InexactJacobianMonotone
open LongTails.Algorithms.NestedAnchoredInexactJacobian
open InexactJacobianGeometry

variable {p : Params}

lemma scale_pos (hR : 0 < p.R) (hε : 0 < p.ε) : 0 < scale p := by
  unfold scale outerCount
  positivity

lemma outerStep_pos (hR : 0 < p.R) (hε : 0 < p.ε) (k : ℕ) : 0 < outerStep p k := by
  unfold outerStep
  exact mul_pos (scale_pos hR hε) (by positivity)

lemma cumulative_succ (k : ℕ) : cumulative p (k + 1) = cumulative p k + outerStep p k := by
  unfold cumulative outerStep
  push_cast
  ring

lemma cumulative_nonneg (hR : 0 < p.R) (hε : 0 < p.ε) (k : ℕ) : 0 ≤ cumulative p k := by
  unfold cumulative
  have := scale_pos hR hε
  positivity

lemma guess_pos (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (k j : ℕ) : 0 < guess p k j := by
  unfold guess
  have := outerStep_pos hR hε k
  positivity

lemma innerStep_pos (hM : 0 < p.M) (hδ : 0 ≤ p.δ) (hR : 0 < p.R) (hε : 0 < p.ε)
    (k j : ℕ) : 0 < innerStep p k j := by
  unfold innerStep
  have := guess_pos hM hδ hR hε k j
  positivity

lemma innerCount_pos (k j : ℕ) : 0 < innerCount p k j := by unfold innerCount; omega

lemma innerCount_sufficient (hM : 0 < p.M) (hδ : 0 ≤ p.δ)
    (hR : 0 < p.R) (hε : 0 < p.ε) (k j : ℕ) :
    8 ≤ ((innerCount p k j : ℝ) * innerStep p k j) * (1 / outerStep p k) := by
  have ha := outerStep_pos hR hε k
  have ht := innerStep_pos hM hδ hR hε k j
  have hceil : 8 * outerStep p k / innerStep p k j ≤ (innerCount p k j : ℝ) := by
    unfold innerCount
    exact (Nat.le_ceil _).trans (by push_cast; linarith)
  have h := (div_le_iff₀ ht).1 hceil
  have he : ((innerCount p k j : ℝ) * innerStep p k j) * (1 / outerStep p k) =
      ((innerCount p k j : ℝ) * innerStep p k j) / outerStep p k := by ring
  rw [he, le_div_iff₀ ha]
  exact h

lemma trial_equation (s : State p) (Fc : p.E) (J D : p.E →L[ℝ] p.E)
    (ha : 0 < outerStep p s.k) (ht : 0 < innerStep p s.k s.j)
    (hD : ∀ v, 0 ≤ ⟪D v, v⟫) (herr : ‖J - D‖ ≤ p.δ) :
    s.trial Fc J + innerStep p s.k s.j •
      (s.regularizedValue s.innerCenter Fc +
        (J + (1 / outerStep p s.k + p.δ) • ContinuousLinearMap.id ℝ p.E)
          (s.trial Fc J - s.innerCenter)) = s.innerAnchor := by
  let μ := 1 / outerStep p s.k
  let t := innerStep p s.k s.j
  let B := J + (μ + p.δ) • ContinuousLinearMap.id ℝ p.E
  have hμ : 0 < μ := one_div_pos.mpr ha
  have hB : ∀ v, 0 ≤ ⟪B v, v⟫ := by
    intro v
    have h := shifted_monotone hD herr v
    dsimp only [B]
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply,
      inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h ⊢
    nlinarith [sq_nonneg ‖v‖]
  have hs := FrozenJacobianSplitting.op_surjective B hB (β := 1) (τ := t) one_pos ht.le
  have hop : (1 + t * (μ + p.δ)) • ContinuousLinearMap.id ℝ p.E + t • J =
      (1 : ℝ) • ContinuousLinearMap.id ℝ p.E + t • B := by
    ext v
    simp only [B, add_apply, smul_apply, ContinuousLinearMap.id_apply]
    module
  have hsurj : Function.Surjective
      ((1 + t * (μ + p.δ)) • ContinuousLinearMap.id ℝ p.E + t • J) := by rw [hop]; exact hs
  have h := Function.rightInverse_invFun hsurj
    (s.innerAnchor - t • s.regularizedValue s.innerCenter Fc +
      t • (J s.innerCenter + (μ + p.δ) • s.innerCenter))
  change ((1 + t * (μ + p.δ)) • ContinuousLinearMap.id ℝ p.E + t • J) (s.trial Fc J) = _ at h
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply] at h
  change s.trial Fc J + t • (s.regularizedValue s.innerCenter Fc + B (s.trial Fc J - s.innerCenter)) = _
  dsimp only [B]
  simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, map_sub]
  linear_combination (norm := module) h

end LongTails.Proofs.InexactJacobianModel
