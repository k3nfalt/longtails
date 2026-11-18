import LongTails.Proofs.FrontierChainMask

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace LongTails.Proofs.FrontierChainNoise

open FrontierChain FrontierChainProfiles FrontierChainMask FrontierChainGeometry Classical

variable {d k : ℕ}

noncomputable def progress (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) : ℕ :=
  Finset.univ.sup (fun j : Fin (k + 1) => if 1 / 2 < |x (π j)| then j.val + 1 else 0)

lemma progress_le (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    progress π x ≤ k + 1 := by
  apply Finset.sup_le
  intro j _
  split_ifs <;> omega

lemma large_before_progress (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (j : Fin (k + 1)) (h : 1 / 2 < |x (π j)|) : j.val + 1 ≤ progress π x := by
  have he := Finset.le_sup
    (f := fun j : Fin (k + 1) => if 1 / 2 < |x (π j)| then j.val + 1 else 0)
    (Finset.mem_univ j)
  simpa only [progress, ite_eq_left h] using he

lemma small_after_progress (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (j : Fin (k + 1)) (h : progress π x ≤ j.val) : |x (π j)| ≤ 1 / 2 := by
  by_contra hj
  have := large_before_progress π x j (lt_of_not_ge hj)
  omega

lemma progress_witness (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (h : 0 < progress π x) :
    ∃ j : Fin (k + 1), 1 / 2 < |x (π j)| ∧ j.val + 1 = progress π x := by
  obtain ⟨j, _, he⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (fun j : Fin (k + 1) => if 1 / 2 < |x (π j)| then j.val + 1 else 0)
  change progress π x = _ at he
  split_ifs at he with hj
  · exact ⟨j, hj, he.symm⟩
  · omega

noncomputable def blockNoise (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    Fin (k + 1) → EuclideanSpace ℝ (Fin d) :=
  Fin.cases (-(potentialSlope (x (π 0)) • EuclideanSpace.single (π 0) (1 : ℝ)))
    (fun i => (edgeLeft (x (π i.castSucc)) (x (π i.succ)) - edgeLeft (x (π i.castSucc)) 0) •
      EuclideanSpace.single (π i.castSucc) (1 : ℝ) +
      edgeRight (x (π i.castSucc)) (x (π i.succ)) • EuclideanSpace.single (π i.succ) (1 : ℝ))

noncomputable def noiseField (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) := ∑ i : Fin (k + 1), mask π x i.val • blockNoise π x i

lemma blockNoise_succ_zero (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (i : Fin k) (h : |x (π i.castSucc)| ≤ 1 / 2) : blockNoise π x i.succ = 0 := by
  have h1 := edge_flat (v := x (π i.succ)) h
  have h0 := edge_flat (v := 0) h
  simp [blockNoise, h1.2.1, h1.2.2, h0.2.1]

lemma masked_block_zero (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (i : Fin (k + 1)) (hi : i.val ≠ progress π x) : mask π x i.val • blockNoise π x i = 0 := by
  by_cases hil : i.val < progress π x
  · obtain ⟨j, hj, he⟩ := progress_witness π x (by omega)
    rw [mask_zero π x i.val j (by omega) hj.le, zero_smul]
  · have hir : progress π x < i.val := by omega
    by_cases hi0 : i = 0
    · simp [hi0] at hir
    · let j := i.pred hi0
      have he : j.succ = i := Fin.succ_pred i hi0
      have hj : progress π x ≤ j.castSucc.val := by
        rw [← he] at hir
        simp only [Fin.val_succ] at hir
        simpa using (Nat.le_of_lt_succ hir)
      rw [← he, blockNoise_succ_zero π x j (small_after_progress π x j.castSucc hj), smul_zero]

lemma blockNoise_norm (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (i : Fin (k + 1)) : ‖blockNoise π x i‖ ≤ 33 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have h := (potentialSlope_bounds (x (π 0))).2
    simp [blockNoise, norm_smul, abs_of_nonneg (potentialSlope_bounds (x (π 0))).1]
    linarith
  · have hl1 : |edgeLeft (x (π j.castSucc)) (x (π j.succ))| ≤ 16 :=
      abs_le.mpr ⟨(edgeLeft_bounds _ _).1, (edgeLeft_bounds _ _).2.trans (by norm_num)⟩
    have hl0 : |edgeLeft (x (π j.castSucc)) 0| ≤ 16 :=
      abs_le.mpr ⟨(edgeLeft_bounds _ _).1, (edgeLeft_bounds _ _).2.trans (by norm_num)⟩
    have hr : |edgeRight (x (π j.castSucc)) (x (π j.succ))| ≤ 1 :=
      abs_le.mpr ⟨(edgeRight_bounds _ _).1, (edgeRight_bounds _ _).2.trans (by norm_num)⟩
    have hl := abs_sub (edgeLeft (x (π j.castSucc)) (x (π j.succ))) (edgeLeft (x (π j.castSucc)) 0)
    dsimp only [blockNoise, Fin.cases_succ]
    apply (norm_add_le _ _).trans
    simp only [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    linarith

lemma noiseField_norm (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    ‖noiseField π x‖ ≤ 33 := by
  by_cases hp : progress π x < k + 1
  · let i : Fin (k + 1) := ⟨progress π x, hp⟩
    have he : noiseField π x = mask π x i.val • blockNoise π x i := by
      unfold noiseField
      apply Finset.sum_eq_single i
      · intro j _ hj
        exact masked_block_zero π x j (fun he => hj (Fin.ext he))
      · simp
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mask_bounds π x i.val).1]
    have h := mul_le_mul (mask_bounds π x i.val).2 (blockNoise_norm π x i)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h
  · have he : noiseField π x = 0 := Finset.sum_eq_zero fun i _ =>
      masked_block_zero π x i (by omega)
    rw [he, norm_zero]
    norm_num

lemma correction_lipschitz (u v u' v' : ℝ) :
    |(edgeLeft u v - edgeLeft u 0) - (edgeLeft u' v' - edgeLeft u' 0)| ≤
      512 * (|u - u'| + |v - v'|) := by
  have h1 := edgeLeft_lipschitz u v u' v'
  have h0 := edgeLeft_lipschitz u 0 u' 0
  simp only [sub_self, abs_zero, add_zero] at h0
  have ht := abs_sub (edgeLeft u v - edgeLeft u' v') (edgeLeft u 0 - edgeLeft u' 0)
  rw [show (edgeLeft u v - edgeLeft u 0) - (edgeLeft u' v' - edgeLeft u' 0) =
    (edgeLeft u v - edgeLeft u' v') - (edgeLeft u 0 - edgeLeft u' 0) by ring]
  linarith [abs_nonneg (v - v')]

lemma blockNoise_lipschitz (π : Fin (k + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d))
    (i : Fin (k + 1)) : ‖blockNoise π x i - blockNoise π y i‖ ≤ 1040 * ‖x - y‖ := by
  have hc (j : Fin (k + 1)) : |x (π j) - y (π j)| ≤ ‖x - y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x - y) (π j)
  refine Fin.cases ?_ (fun j => ?_) i
  · have he : blockNoise π x 0 - blockNoise π y 0 =
        -(potentialSlope (x (π 0)) - potentialSlope (y (π 0))) •
          EuclideanSpace.single (π 0) (1 : ℝ) := by dsimp [blockNoise]; module
    rw [he]
    simp only [norm_smul, PiLp.norm_single, norm_one, mul_one, norm_neg, Real.norm_eq_abs]
    have hp := potentialSlope_lipschitz (x (π 0)) (y (π 0))
    linarith [hc 0, norm_nonneg (x - y)]
  · have he : blockNoise π x j.succ - blockNoise π y j.succ =
        ((edgeLeft (x (π j.castSucc)) (x (π j.succ)) - edgeLeft (x (π j.castSucc)) 0) -
          (edgeLeft (y (π j.castSucc)) (y (π j.succ)) - edgeLeft (y (π j.castSucc)) 0)) •
            EuclideanSpace.single (π j.castSucc) (1 : ℝ) +
        (edgeRight (x (π j.castSucc)) (x (π j.succ)) -
          edgeRight (y (π j.castSucc)) (y (π j.succ))) • EuclideanSpace.single (π j.succ) (1 : ℝ) := by
      dsimp [blockNoise]
      module
    rw [he]
    apply (norm_add_le _ _).trans
    simp only [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
    have hl := correction_lipschitz (x (π j.castSucc)) (x (π j.succ))
      (y (π j.castSucc)) (y (π j.succ))
    have hr := edgeRight_lipschitz (x (π j.castSucc)) (x (π j.succ))
      (y (π j.castSucc)) (y (π j.succ))
    linarith [hc j.castSucc, hc j.succ]

lemma masked_block_lipschitz (π : Fin (k + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d))
    (i : Fin (k + 1)) :
    ‖mask π x i.val • blockNoise π x i - mask π y i.val • blockNoise π y i‖ ≤
      1280 * ‖x - y‖ := by
  have he : mask π x i.val • blockNoise π x i - mask π y i.val • blockNoise π y i =
      (mask π x i.val - mask π y i.val) • blockNoise π x i +
        mask π y i.val • (blockNoise π x i - blockNoise π y i) := by module
  rw [he]
  calc _ ≤ ‖(mask π x i.val - mask π y i.val) • blockNoise π x i‖ +
      ‖mask π y i.val • (blockNoise π x i - blockNoise π y i)‖ := norm_add_le _ _
    _ ≤ (4 * ‖x - y‖) * 33 + 1 * (1040 * ‖x - y‖) := by
      simp only [norm_smul, Real.norm_eq_abs]
      apply add_le_add
      · exact mul_le_mul (mask_lipschitz π x y i.val) (blockNoise_norm π x i)
          (norm_nonneg _) (by positivity)
      · exact mul_le_mul (by rw [abs_of_nonneg (mask_bounds π y i.val).1]; exact (mask_bounds π y i.val).2)
          (blockNoise_lipschitz π x y i) (norm_nonneg _) (by norm_num)
    _ ≤ _ := by nlinarith [norm_nonneg (x - y)]

noncomputable def extendedBlock (π : Fin (k + 1) ↪ Fin d) (i : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  if hi : i < k + 1 then mask π x i • blockNoise π x ⟨i, hi⟩ else 0

lemma extendedBlock_zero (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d))
    (i : ℕ) (hi : i ≠ progress π x) : extendedBlock π i x = 0 := by
  unfold extendedBlock
  split_ifs with h
  · exact masked_block_zero π x ⟨i, h⟩ hi
  · rfl

lemma extendedBlock_lipschitz (π : Fin (k + 1) ↪ Fin d) (i : ℕ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    ‖extendedBlock π i x - extendedBlock π i y‖ ≤ 1280 * ‖x - y‖ := by
  unfold extendedBlock
  split_ifs with h
  · exact masked_block_lipschitz π x y ⟨i, h⟩
  · simp

set_option maxHeartbeats 800000 in
lemma noiseField_eq_extended (π : Fin (k + 1) ↪ Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    noiseField π x = extendedBlock π (progress π x) x := by
  unfold extendedBlock
  split_ifs with hp
  · let i : Fin (k + 1) := ⟨progress π x, hp⟩
    change noiseField π x = mask π x i.val • blockNoise π x i
    unfold noiseField
    apply Finset.sum_eq_single i
    · intro j _ hj
      exact masked_block_zero π x j (fun he => hj (Fin.ext he))
    · simp
  · exact Finset.sum_eq_zero fun i _ => masked_block_zero π x i (by omega)

lemma noiseField_lipschitz (π : Fin (k + 1) ↪ Fin d) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖noiseField π x - noiseField π y‖ ≤ 2560 * ‖x - y‖ := by
  rw [noiseField_eq_extended, noiseField_eq_extended]
  by_cases he : progress π x = progress π y
  · rw [he]
    exact (extendedBlock_lipschitz π (progress π y) x y).trans (by nlinarith [norm_nonneg (x - y)])
  · have hx0 := extendedBlock_zero π x (progress π y) (Ne.symm he)
    have hy0 := extendedBlock_zero π y (progress π x) he
    have hid : extendedBlock π (progress π x) x - extendedBlock π (progress π y) y =
        (extendedBlock π (progress π x) x - extendedBlock π (progress π x) y) +
          (extendedBlock π (progress π y) x - extendedBlock π (progress π y) y) := by
      rw [hx0, hy0]
      abel
    rw [hid]
    exact (norm_add_le _ _).trans ((add_le_add (extendedBlock_lipschitz π (progress π x) x y)
      (extendedBlock_lipschitz π (progress π y) x y)).trans_eq (by ring))

end LongTails.Proofs.FrontierChainNoise
