import LongTails.Proofs.InterpolatedFiniteSumChains
import LongTails.Proofs.InterpolatedFiniteSumShield

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators RealInnerProductSpace
open Classical

namespace LongTails.Proofs.InterpolatedFiniteSumChainLocality

open InterpolatedFiniteSumChains InterpolatedFiniteSumProfiles FiniteSumNondualLowerComponents

noncomputable def selection {d k : ℕ} (π : Fin (k + 1) → Fin d) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun j => x (π j))
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }

lemma selection_apply {d k : ℕ} (π : Fin (k + 1) → Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin (k + 1)) : selection π x j = x (π j) := rfl

noncomputable def edges {d k : ℕ} (π : Fin (k + 1) → Fin d) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (k + 1)) :=
  (tailMap k).comp (selection π)

lemma edges_last {d k : ℕ} (π : Fin (k + 1) → Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    edges π x (Fin.last k) = x (π (Fin.last k)) := by
  exact tailMap_apply_last k (selection π x)

lemma edges_castSucc {d k : ℕ} (π : Fin (k + 1) → Fin d)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin k) :
    edges π x j.castSucc = x (π j.castSucc) - x (π j.succ) := by
  exact tailMap_apply_castSucc k (selection π x) j

lemma edges_prefix {d k : ℕ} (π ρ : Fin (k + 1) → Fin d) (r : ℕ)
    (h : ∀ i : Fin (k + 1), i.val < r + 1 → π i = ρ i)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin (k + 1)) (hj : j.val < r) :
    edges π x j = edges ρ x j := by
  revert hj
  refine Fin.lastCases ?_ (fun i => ?_) j
  · intro hj
    rw [edges_last, edges_last, h (Fin.last k) (by simpa using Nat.lt_succ_of_lt hj)]
  · intro hj
    rw [edges_castSucc, edges_castSucc, h i.castSucc (by omega), h i.succ (by simp only [Fin.val_succ, Fin.val_castSucc] at hj ⊢; omega)]

noncomputable def partialValue {d k : ℕ} (π : Fin (k + 1) → Fin d) (r : ℕ) (c σ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  -(c / σ) * x (π 0) + ∑ j : Fin (k + 1),
    if j.val < r then c * profile (edges π x j / σ) else 0

noncomputable def partialSlope {d k : ℕ} (π : Fin (k + 1) → Fin d) (r : ℕ) (σ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin (k + 1)) :=
  WithLp.toLp 2 (fun j => if j.val < r then profileSlope (edges π x j / σ) else 0)

noncomputable def partialField {d k : ℕ} (π : Fin (k + 1) → Fin d) (r : ℕ) (c σ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  c • (σ⁻¹ • edges π).adjoint (partialSlope π r σ x) - PiLp.single 2 (π 0) (c / σ)

lemma partialValue_prefix {d k : ℕ} (π ρ : Fin (k + 1) → Fin d) (r : ℕ) (c σ : ℝ)
    (h : ∀ i : Fin (k + 1), i.val < r + 1 → π i = ρ i)
    (x : EuclideanSpace ℝ (Fin d)) : partialValue π r c σ x = partialValue ρ r c σ x := by
  unfold partialValue
  rw [h 0 (by simp)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < r
  · rw [ite_eq_left hj, ite_eq_left hj, edges_prefix π ρ r h x j hj]
  · simp only [ite_eq_right hj]

lemma partialField_prefix {d k : ℕ} (π ρ : Fin (k + 1) → Fin d) (r : ℕ) (c σ : ℝ)
    (h : ∀ i : Fin (k + 1), i.val < r + 1 → π i = ρ i)
    (x : EuclideanSpace ℝ (Fin d)) : partialField π r c σ x = partialField ρ r c σ x := by
  unfold partialField
  rw [h 0 (by simp)]
  congr 2
  apply ext_inner_right ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, RCLike.inner_apply, partialSlope]
  apply Finset.sum_congr rfl
  intro j _
  change (σ⁻¹ * edges π v j) *
      (if j.val < r then profileSlope (edges π x j / σ) else 0) =
    (σ⁻¹ * edges ρ v j) *
      (if j.val < r then profileSlope (edges ρ x j / σ) else 0)
  by_cases hj : j.val < r
  · rw [ite_eq_left hj, ite_eq_left hj, edges_prefix π ρ r h x j hj,
      edges_prefix π ρ r h v j hj]
  · simp only [ite_eq_right hj, mul_zero]

lemma unseen_edge_bound {d k : ℕ} (π : Fin (k + 1) → Fin d) (r : ℕ) (σ : ℝ)
    (hσ : 0 < σ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ i : Fin (k + 1), r ≤ i.val → |x (π i)| ≤ σ / 8)
    (j : Fin (k + 1)) (hj : r ≤ j.val) : |edges π x j / σ| ≤ 1 / 4 := by
  rw [abs_div, abs_of_pos hσ, div_le_iff₀ hσ]
  revert hj
  refine Fin.lastCases ?_ (fun i => ?_) j
  · intro hj
    rw [edges_last]
    have hh := h (Fin.last k) hj
    linarith
  · intro hj
    rw [edges_castSucc]
    have h₁ := h i.castSucc hj
    have h₂ := h i.succ (by simp only [Fin.val_succ, Fin.val_castSucc] at hj ⊢; omega)
    have ha := abs_sub (x (π i.castSucc)) (x (π i.succ))
    linarith

lemma partialValue_full {d k : ℕ} (π : Fin (k + 1) → Fin d) (r : ℕ) (c σ : ℝ)
    (hσ : 0 < σ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ i : Fin (k + 1), r ≤ i.val → |x (π i)| ≤ σ / 8) :
    partialValue π r c σ x = partialValue π (k + 1) c σ x := by
  unfold partialValue
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [ite_eq_left j.isLt]
  by_cases hj : j.val < r
  · rw [ite_eq_left hj]
  · rw [ite_eq_right hj, (profile_flat _ (unseen_edge_bound π r σ hσ x h j (by omega))).1,
      mul_zero]

lemma partialField_full {d k : ℕ} (π : Fin (k + 1) → Fin d) (r : ℕ) (c σ : ℝ)
    (hσ : 0 < σ) (x : EuclideanSpace ℝ (Fin d))
    (h : ∀ i : Fin (k + 1), r ≤ i.val → |x (π i)| ≤ σ / 8) :
    partialField π r c σ x = partialField π (k + 1) c σ x := by
  have he : partialSlope π r σ x = partialSlope π (k + 1) σ x := by
    ext j
    change (if j.val < r then profileSlope (edges π x j / σ) else 0) =
      if j.val < k + 1 then profileSlope (edges π x j / σ) else 0
    rw [ite_eq_left j.isLt]
    by_cases hj : j.val < r
    · rw [ite_eq_left hj]
    · rw [ite_eq_right hj, (profile_flat _ (unseen_edge_bound π r σ hσ x h j (by omega))).2]
  simp only [partialField, he]

lemma partialValue_raw {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : partialValue π (k + 1) c σ x = rawChain π c σ x := by
  have he : edges (π : Fin (k + 1) → Fin d) = selectedTail π := rfl
  simp only [partialValue, rawChain, chainValue, energy, separableEnergy,
    smul_apply, PiLp.smul_apply, smul_eq_mul, ← div_eq_inv_mul, EuclideanSpace.inner_single_left,
    starRingEnd_apply, star_trivial, he]
  simp only [Fin.is_lt, ite_true, ← Finset.mul_sum]
  ring

lemma partialField_raw {d k : ℕ} (π : Fin (k + 1) ↪ Fin d) (c σ : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : partialField π (k + 1) c σ x = rawField π c σ x := by
  have he : edges (π : Fin (k + 1) → Fin d) = selectedTail π := rfl
  have hs : partialSlope π (k + 1) σ x = field ((σ⁻¹ • selectedTail π) x) := by
    ext j
    change (if j.val < k + 1 then profileSlope (edges π x j / σ) else 0) =
      profileSlope (σ⁻¹ * selectedTail π x j)
    rw [ite_eq_left j.isLt, he, div_eq_inv_mul]
  simp only [partialField, rawField, chainField, he, hs]

end LongTails.Proofs.InterpolatedFiniteSumChainLocality
