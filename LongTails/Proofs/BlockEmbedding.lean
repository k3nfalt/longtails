import LongTails.Proofs.BlockSgdRate
import LongTails.Template

open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.BlockEmbedding

open LongTails.Setups.BlockHeterogeneousNonconvex LongTails.Proofs.BlockSgdRate

variable {d B : ℕ} (blk : Fin d → Fin B)

abbrev blockSize (j : Fin B) : ℕ := Fintype.card {i // blk i = j}

noncomputable def blockEquiv (j : Fin B) : Fin (blockSize blk j) ≃ {i // blk i = j} :=
  (Fintype.equivFin _).symm

noncomputable def restrict (j : Fin B) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin (blockSize blk j)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun k => x (blockEquiv blk j k).1)
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }

noncomputable def extend (j : Fin B) :
    EuclideanSpace ℝ (Fin (blockSize blk j)) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2
        (fun i => if h : blk i = j then y ((blockEquiv blk j).symm ⟨i, h⟩) else 0)
      map_add' := by
        intro x y
        ext i
        by_cases h : blk i = j <;> simp [h]
      map_smul' := by
        intro a x
        ext i
        by_cases h : blk i = j <;> simp [h] }

lemma restrict_apply (j : Fin B) (x : EuclideanSpace ℝ (Fin d)) (k : Fin (blockSize blk j)) :
    restrict blk j x k = x (blockEquiv blk j k).1 := rfl

lemma extend_apply (j : Fin B) (y : EuclideanSpace ℝ (Fin (blockSize blk j))) (i : Fin d) :
    extend blk j y i = if h : blk i = j then y ((blockEquiv blk j).symm ⟨i, h⟩) else 0 := rfl

lemma restrict_extend (j : Fin B) (y : EuclideanSpace ℝ (Fin (blockSize blk j))) :
    restrict blk j (extend blk j y) = y := by
  ext k
  rw [restrict_apply, extend_apply, dite_eq_left (blockEquiv blk j k).2]
  simp

lemma restrict_extend_ne {j k : Fin B} (hjk : j ≠ k)
    (y : EuclideanSpace ℝ (Fin (blockSize blk k))) :
    restrict blk j (extend blk k y) = 0 := by
  ext m
  rw [restrict_apply, extend_apply]
  have h : blk (blockEquiv blk j m).1 ≠ k := by rw [(blockEquiv blk j m).2]; exact hjk
  rw [dite_eq_right h]
  rfl

lemma blockProj_extend_self (j : Fin B) (y : EuclideanSpace ℝ (Fin (blockSize blk j))) :
    blockProj blk j (extend blk j y) = extend blk j y := by
  ext i
  rw [blockProj_apply]
  split_ifs with h
  · rfl
  · rw [extend_apply, dite_eq_right h]

lemma blockProj_extend_ne {j k : Fin B} (hjk : j ≠ k)
    (y : EuclideanSpace ℝ (Fin (blockSize blk k))) :
    blockProj blk j (extend blk k y) = 0 := by
  ext i
  rw [blockProj_apply]
  split_ifs with h
  · rw [extend_apply]
    have : blk i ≠ k := by rw [h]; exact hjk
    rw [dite_eq_right this]
    rfl
  · rfl

lemma sum_subtype_eq (j : Fin B) (F : Fin d → ℝ) (hF : ∀ i, blk i ≠ j → F i = 0) :
    ∑ i, F i = ∑ k : Fin (blockSize blk j), F (blockEquiv blk j k).1 := by
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i => blk i = j) F]
  have h0 : ∑ i : {i // ¬ blk i = j}, F i = 0 :=
    Finset.sum_eq_zero (fun i _ => hF i i.2)
  rw [h0, add_zero]
  exact (Equiv.sum_comp (blockEquiv blk j) (fun s => F s.1)).symm

lemma inner_restrict (j : Fin B) (x : EuclideanSpace ℝ (Fin d))
    (y : EuclideanSpace ℝ (Fin (blockSize blk j))) :
    ⟪restrict blk j x, y⟫ = ⟪x, extend blk j y⟫ := by
  simp only [PiLp.inner_apply]
  symm
  rw [sum_subtype_eq blk j]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [extend_apply, dite_eq_left (blockEquiv blk j k).2, restrict_apply]
    simp
  · intro i hi
    rw [extend_apply, dite_eq_right hi]
    simp

lemma norm_extend (j : Fin B) (y : EuclideanSpace ℝ (Fin (blockSize blk j))) :
    ‖extend blk j y‖ = ‖y‖ := by
  have h : ‖extend blk j y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← inner_restrict,
      restrict_extend]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

lemma extend_restrict (j : Fin B) (x : EuclideanSpace ℝ (Fin d)) :
    extend blk j (restrict blk j x) = blockProj blk j x := by
  ext i
  rw [extend_apply, blockProj_apply]
  split_ifs with h
  · rw [restrict_apply]
    simp
  · rfl

lemma norm_restrict (j : Fin B) (x : EuclideanSpace ℝ (Fin d)) :
    ‖restrict blk j x‖ = ‖blockProj blk j x‖ := by
  rw [← extend_restrict, norm_extend]

lemma restrict_blockProj (j : Fin B) (x : EuclideanSpace ℝ (Fin d)) :
    restrict blk j (blockProj blk j x) = restrict blk j x := by
  rw [← extend_restrict, restrict_extend]

end LongTails.Proofs.BlockEmbedding
