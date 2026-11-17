import LongTails.Proofs.FrontierChainNoise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.FrontierChainPrefix

open FrontierChain FrontierChainProfiles FrontierChainMask FrontierChainNoise

variable {d k : ℕ}

lemma residual_decomposition (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    field π x - noiseField π x =
      (1 - mask π x 0) • blockNoise π x 0 +
      ∑ i : Fin k, (edgeField (π i.castSucc) (π i.succ) x -
        mask π x i.succ.val • blockNoise π x i.succ) := by
  unfold field noiseField
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero]
  rw [Finset.sum_sub_distrib]
  simp only [blockNoise, Fin.cases_zero]
  module

lemma residual_edge_boundary (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (i : Fin k) (hx : ∀ j : Fin (k + 1), i.succ.val ≤ j.val → |x (π j)| ≤ 1 / 4) :
    edgeField (π i.castSucc) (π i.succ) x - mask π x i.succ.val • blockNoise π x i.succ =
      edgeLeft (x (π i.castSucc)) 0 • EuclideanSpace.single (π i.castSucc) (1 : ℝ) := by
  rw [mask_one π x i.succ.val hx, one_smul]
  dsimp [edgeField, blockNoise]
  module

lemma residual_edge_flat (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (i : Fin k) (hx : |x (π i.castSucc)| ≤ 1 / 2) :
    edgeField (π i.castSucc) (π i.succ) x - mask π x i.succ.val • blockNoise π x i.succ = 0 := by
  rw [blockNoise_succ_zero π x i hx, smul_zero, sub_zero]
  have he := edge_flat (v := x (π i.succ)) hx
  simp [edgeField, he.2.1, he.2.2]

lemma residual_prefix (π π' : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) (r : ℕ)
    (hπ : ∀ j : Fin (k + 1), j.val < r → π j = π' j)
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4)
    (hx' : ∀ j : Fin (k + 1), r ≤ j.val → |x (π' j)| ≤ 1 / 4) :
    field π x - noiseField π x = field π' x - noiseField π' x := by
  classical
  rw [residual_decomposition, residual_decomposition]
  congr 1
  · by_cases hr : r = 0
    · subst r
      rw [mask_one π x 0 hx, mask_one π' x 0 hx']
      simp
    · rw [mask_prefix π π' x 0 r hπ hx hx']
      simp only [blockNoise, Fin.cases_zero, hπ 0 (by simpa using Nat.pos_of_ne_zero hr)]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.succ.val < r
    · rw [mask_prefix π π' x i.succ.val r hπ hx hx']
      have hprev := hπ i.castSucc (by simp only [Fin.val_succ, Fin.val_castSucc] at hi ⊢; omega)
      have hnext := hπ i.succ hi
      simp only [blockNoise, Fin.cases_succ, edgeField, hprev, hnext]
    · by_cases he : i.succ.val = r
      · rw [residual_edge_boundary π x i (by simpa only [he] using hx),
          residual_edge_boundary π' x i (by simpa only [he] using hx')]
        rw [hπ i.castSucc (by simp only [Fin.val_succ, Fin.val_castSucc] at he ⊢; omega)]
      · have hp : r ≤ i.castSucc.val := by simp only [Fin.val_succ, Fin.val_castSucc] at hi he ⊢; omega
        rw [residual_edge_flat π x i (by linarith [hx i.castSucc hp]),
          residual_edge_flat π' x i (by linarith [hx' i.castSucc hp])]

lemma field_prefix (π π' : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) (r : ℕ)
    (hπ : ∀ j : Fin (k + 1), j.val ≤ r → π j = π' j)
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4)
    (hx' : ∀ j : Fin (k + 1), r ≤ j.val → |x (π' j)| ≤ 1 / 4) :
    field π x = field π' x := by
  classical
  unfold field
  rw [hπ 0 (by simp)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.succ.val ≤ r
  · rw [edgeField, edgeField, hπ i.succ hi,
      hπ i.castSucc (by simp only [Fin.val_succ, Fin.val_castSucc] at hi ⊢; omega)]
  · have hp : r ≤ i.castSucc.val := by simp only [Fin.val_succ, Fin.val_castSucc] at hi ⊢; omega
    have hf := edge_flat (v := x (π i.succ)) (show |x (π i.castSucc)| ≤ 1 / 2 by linarith [hx i.castSucc hp])
    have hf' := edge_flat (v := x (π' i.succ)) (show |x (π' i.castSucc)| ≤ 1 / 2 by linarith [hx' i.castSucc hp])
    simp [edgeField, hf.2.1, hf.2.2, hf'.2.1, hf'.2.2]

lemma noise_prefix (π π' : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) (r : ℕ)
    (hπ : ∀ j : Fin (k + 1), j.val ≤ r → π j = π' j)
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4)
    (hx' : ∀ j : Fin (k + 1), r ≤ j.val → |x (π' j)| ≤ 1 / 4) :
    noiseField π x = noiseField π' x := by
  classical
  unfold noiseField
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val ≤ r
  · rw [mask_prefix π π' x i.val (r + 1) (fun j hj => hπ j (by omega))
      (fun j hj => hx j (by omega)) (fun j hj => hx' j (by omega))]
    congr 1
    refine Fin.cases ?_ (fun j hj => ?_) i hi
    · intro _
      simp only [blockNoise, Fin.cases_zero, hπ 0 (by simp)]
    · simp only [blockNoise, Fin.cases_succ, hπ j.succ hj,
        hπ j.castSucc (by simp only [Fin.val_succ, Fin.val_castSucc] at hj ⊢; omega)]
  · have hi0 : i ≠ 0 := by intro he; subst i; simp at hi
    let j := i.pred hi0
    have he : j.succ = i := Fin.succ_pred i hi0
    have hp : r ≤ j.castSucc.val := by rw [← he] at hi; simp only [Fin.val_succ, Fin.val_castSucc] at hi ⊢; omega
    rw [← he, blockNoise_succ_zero π x j (by linarith [hx j.castSucc hp]),
      blockNoise_succ_zero π' x j (by linarith [hx' j.castSucc hp])]
    simp

lemma mask_point (π : Fin (k + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d)) (r i : ℕ)
    (hc : ∀ j : Fin (k + 1), j.val < r → x (π j) = y (π j))
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4)
    (hy : ∀ j : Fin (k + 1), r ≤ j.val → |y (π j)| ≤ 1 / 4) :
    mask π x i = mask π y i := by
  unfold mask
  congr 1
  funext j
  split_ifs
  · by_cases hj : j.val < r
    · rw [hc j hj]
    · rw [cutoff_one (hx j (by omega)), cutoff_one (hy j (by omega))]
  · rfl

lemma residual_point (π : Fin (k + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d)) (r : ℕ)
    (hc : ∀ j : Fin (k + 1), j.val < r → x (π j) = y (π j))
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4)
    (hy : ∀ j : Fin (k + 1), r ≤ j.val → |y (π j)| ≤ 1 / 4) :
    field π x - noiseField π x = field π y - noiseField π y := by
  classical
  rw [residual_decomposition, residual_decomposition]
  congr 1
  · by_cases hr : r = 0
    · subst r
      rw [mask_one π x 0 hx, mask_one π y 0 hy]
      simp
    · rw [mask_point π x y r 0 hc hx hy]
      simp only [blockNoise, Fin.cases_zero, hc 0 (by simpa using Nat.pos_of_ne_zero hr)]
  · apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i.succ.val < r
    · rw [mask_point π x y r i.succ.val hc hx hy]
      have hprev := hc i.castSucc (by simp only [Fin.val_succ, Fin.val_castSucc] at hi ⊢; omega)
      have hnext := hc i.succ hi
      simp only [blockNoise, Fin.cases_succ, edgeField, hprev, hnext]
    · by_cases he : i.succ.val = r
      · rw [residual_edge_boundary π x i (by simpa only [he] using hx),
          residual_edge_boundary π y i (by simpa only [he] using hy)]
        rw [hc i.castSucc (by simp only [Fin.val_succ, Fin.val_castSucc] at he ⊢; omega)]
      · have hp : r ≤ i.castSucc.val := by simp only [Fin.val_succ, Fin.val_castSucc] at hi he ⊢; omega
        rw [residual_edge_flat π x i (by linarith [hx i.castSucc hp]),
          residual_edge_flat π y i (by linarith [hy i.castSucc hp])]

lemma field_point (π : Fin (k + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d)) (r : ℕ)
    (hc : ∀ j : Fin (k + 1), j.val ≤ r → x (π j) = y (π j))
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4)
    (hy : ∀ j : Fin (k + 1), r ≤ j.val → |y (π j)| ≤ 1 / 4) :
    field π x = field π y := by
  classical
  unfold field
  rw [hc 0 (by simp)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.succ.val ≤ r
  · simp only [edgeField, hc i.succ hi,
      hc i.castSucc (by simp only [Fin.val_succ, Fin.val_castSucc] at hi ⊢; omega)]
  · have hp : r ≤ i.castSucc.val := by simp only [Fin.val_succ, Fin.val_castSucc] at hi ⊢; omega
    have hf := edge_flat (v := x (π i.succ)) (show |x (π i.castSucc)| ≤ 1 / 2 by linarith [hx i.castSucc hp])
    have hf' := edge_flat (v := y (π i.succ)) (show |y (π i.castSucc)| ≤ 1 / 2 by linarith [hy i.castSucc hp])
    simp [edgeField, hf.2.1, hf.2.2, hf'.2.1, hf'.2.2]

lemma noise_point (π : Fin (k + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d)) (r : ℕ)
    (hc : ∀ j : Fin (k + 1), j.val ≤ r → x (π j) = y (π j))
    (hx : ∀ j : Fin (k + 1), r ≤ j.val → |x (π j)| ≤ 1 / 4)
    (hy : ∀ j : Fin (k + 1), r ≤ j.val → |y (π j)| ≤ 1 / 4) :
    noiseField π x = noiseField π y := by
  have hr := residual_point π x y (r + 1) (fun j hj => hc j (by omega))
    (fun j hj => hx j (by omega)) (fun j hj => hy j (by omega))
  rw [field_point π x y r hc hx hy] at hr
  have he := congrArg (fun v => field π y - v) hr
  simpa only [sub_sub_cancel] using he

end LongTails.Proofs.FrontierChainPrefix
