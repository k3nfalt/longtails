import LongTails.Algorithms.RandomReshuffling
import LongTails.Proofs.ReshufflingProductBounds
import LongTails.Proofs.ReshufflingPermutationMoments

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.Reshuffling

variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def epochLinear (A : I → E →L[ℝ] E) (η : ℝ) (w : List I) : E →L[ℝ] E :=
  (w.reverse.map (fun i => 1 + (-η) • A i)).prod

noncomputable def epochNoise (A : I → E →L[ℝ] E) (b : I → E) (η : ℝ) : List I → E
  | [] => 0
  | i :: w => epochLinear A η w (b i) + epochNoise A b η w

noncomputable def prefixCorrection (A : I → E →L[ℝ] E) (b : I → E) (η : ℝ) : List I → E → E
  | [], _ => 0
  | i :: w, v => epochLinear A η w (A i v) + prefixCorrection A b η w (v + b i)

lemma epochLinear_nil (A : I → E →L[ℝ] E) (η : ℝ) : epochLinear A η [] = 1 := by
  simp [epochLinear]

lemma epochLinear_cons (A : I → E →L[ℝ] E) (η : ℝ) (i : I) (w : List I) :
    epochLinear A η (i :: w) = epochLinear A η w * (1 + (-η) • A i) := by
  simp [epochLinear, List.prod_append]

lemma epochLinear_cons_apply (A : I → E →L[ℝ] E) (η : ℝ) (i : I) (w : List I) (x : E) :
    epochLinear A η (i :: w) x = epochLinear A η w (x - η • A i x) := by
  rw [epochLinear_cons]
  simp [mul_apply_eq_comp, sub_eq_add_neg]

lemma affine_pass (A : I → E →L[ℝ] E) (b : I → E) (η : ℝ) (w : List I) (x : E) :
    RandomReshuffling.pass (fun i y => A i y + b i) η w x =
      epochLinear A η w x - η • epochNoise A b η w := by
  induction w generalizing x with
  | nil => simp [RandomReshuffling.pass, epochLinear_nil, epochNoise]
  | cons i w ih =>
    rw [RandomReshuffling.pass, ih, epochLinear_cons_apply]
    simp only [epochNoise, smul_add, map_sub, map_add, map_smul]
    abel

lemma noise_prefix_identity (A : I → E →L[ℝ] E) (b : I → E) (η : ℝ)
    (w : List I) (v : E) :
    epochNoise A b η w + epochLinear A η w v =
      v + (w.map b).sum - η • prefixCorrection A b η w v := by
  induction w generalizing v with
  | nil => simp [epochNoise, epochLinear_nil, prefixCorrection]
  | cons i w ih =>
    rw [epochNoise, epochLinear_cons_apply, prefixCorrection]
    simp only [map_sub, map_smul, List.map_cons, List.sum_cons, smul_add]
    have h := ih (v + b i)
    rw [map_add] at h
    convert congrArg (fun z : E => z - η • epochLinear A η w (A i v)) h using 1 <;> abel

lemma centered_noise_identity (A : I → E →L[ℝ] E) (b : I → E) (η : ℝ)
    (w : List I) (hb : (w.map b).sum = 0) :
    epochNoise A b η w = -η • prefixCorrection A b η w 0 := by
  have h := noise_prefix_identity A b η w 0
  simpa only [map_zero, add_zero, zero_add, hb, zero_sub, neg_smul] using h

lemma epochNoise_eq_sum (A : I → E →L[ℝ] E) (b : I → E) (η : ℝ) (w : List I) :
    epochNoise A b η w = ∑ j : Fin w.length,
      epochLinear A η (w.drop (j.val + 1)) (b (w.get j)) := by
  induction w with
  | nil => simp [epochNoise]
  | cons i w ih =>
    rw [epochNoise, ih]
    change _ = ∑ j : Fin (w.length + 1),
      epochLinear A η ((i :: w).drop (j.val + 1)) (b ((i :: w).get j))
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, zero_add, List.drop_succ_cons, List.drop_zero,
      List.get_cons_zero, Fin.val_succ]
    congr 1

lemma prefixCorrection_eq_sum (A : I → E →L[ℝ] E) (b : I → E) (η : ℝ)
    (w : List I) (v : E) :
    prefixCorrection A b η w v = ∑ j : Fin w.length,
      epochLinear A η (w.drop (j.val + 1))
        (A (w.get j) (v + ((w.take j.val).map b).sum)) := by
  induction w generalizing v with
  | nil => simp [prefixCorrection]
  | cons i w ih =>
    rw [prefixCorrection, ih]
    change _ = ∑ j : Fin (w.length + 1), epochLinear A η ((i :: w).drop (j.val + 1))
      (A ((i :: w).get j) (v + (((i :: w).take j.val).map b).sum))
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, zero_add, List.drop_succ_cons, List.drop_zero,
      List.get_cons_zero, Fin.val_succ, List.take_zero,
      List.take_succ_cons, List.map_nil, List.sum_nil, add_zero, List.map_cons, List.sum_cons,
      add_assoc]
    congr 1

lemma epochLinear_norm_le_two (A : I → E →L[ℝ] E) {L η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hA : ∀ i, ‖A i‖ ≤ L)
    (w : List I) (hstep : (w.length : ℝ) * (η * L) ≤ 1 / 2) :
    ‖epochLinear A η w‖ ≤ 2 := by
  exact step_product_norm A hL hη hA w.reverse (by simpa only [List.length_reverse] using hstep)

omit [InnerProductSpace ℝ E] in
lemma full_list_sum [Fintype I] [DecidableEq I] (v : I → E)
    (w : List I) (hw : w.Nodup) (hlen : w.length = Fintype.card I) :
    (w.map v).sum = ∑ i, v i := by
  have he : w.toFinset = Finset.univ := Finset.eq_univ_of_card w.toFinset
    ((List.toFinset_card_of_nodup hw).trans hlen)
  rw [← List.sum_toFinset _ hw, he]

lemma epoch_noise_second_moment {n : ℕ}
    (A : Fin n → E →L[ℝ] E) (b : Fin n → E) {L G η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hA : ∀ i, ‖A i‖ ≤ L) (hb : ∑ i, b i = 0) (hbound : ∀ i, ‖b i‖ ≤ G)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n)
    (hstep : η * n * L ≤ 1 / 32) :
    (∑ π : Equiv.Perm (Fin n),
      ‖epochNoise (fun i => A (π i)) (fun i => b (π i)) η w‖ ^ 2) ≤
      4 * (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * η ^ 2 * (n : ℝ) ^ 3 * L ^ 2 * G ^ 2 := by
  classical
  let B := fun (π : Equiv.Perm (Fin n)) (j : Fin w.length) =>
    epochLinear (fun i => A (π i)) η (w.drop (j.val + 1)) * A (π (w.get j))
  have hB : ∀ π j, ‖B π j‖ ≤ 2 * L := by
    intro π j
    have hd : (w.drop (j.val + 1)).length ≤ n := by simp only [List.length_drop, hlen]; omega
    have hdr : ((w.drop (j.val + 1)).length : ℝ) ≤ n := by exact_mod_cast hd
    have hm := mul_le_mul_of_nonneg_right hdr (mul_nonneg hη hL)
    have hP := epochLinear_norm_le_two (fun i => A (π i)) hL hη (fun i => hA _)
      (w.drop (j.val + 1)) (by nlinarith)
    exact (norm_mul_le _ _).trans (mul_le_mul hP (hA _) (norm_nonneg _) (by norm_num))
  have hmoment := permutation_weighted_prefix_moment b hb
    hbound w hw B hB
  have hcenter : ∀ π : Equiv.Perm (Fin n), (w.map (fun i => b (π i))).sum = 0 := by
    intro π
    rw [full_list_sum _ w hw (by simpa only [Fintype.card_fin] using hlen), Equiv.sum_comp, hb]
  have he : ∀ π : Equiv.Perm (Fin n),
      ‖epochNoise (fun i => A (π i)) (fun i => b (π i)) η w‖ ^ 2 =
      η ^ 2 * ‖∑ j : Fin w.length, B π j (((w.take j.val).map (fun i => b (π i))).sum)‖ ^ 2 := by
    intro π
    rw [centered_noise_identity _ _ _ _ (hcenter π), norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_nonneg hη, mul_pow, prefixCorrection_eq_sum]
    simp only [zero_add, B, mul_apply_eq_comp]
  simp_rw [he]
  rw [← Finset.mul_sum]
  calc
    _ ≤ η ^ 2 * ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (w.length : ℝ) ^ 3 *
        (2 * L) ^ 2 * G ^ 2) := mul_le_mul_of_nonneg_left hmoment (sq_nonneg _)
    _ = _ := by rw [hlen]; ring

noncomputable def epochCrossOperator (A : I → E →L[ℝ] E) (η : ℝ)
    (w : List I) (j : ℕ) : E →L[ℝ] E :=
  ((w ++ (w.drop (j + 1)).reverse).map (fun i => 1 + (-η) • A i)).prod

lemma epochCrossOperator_swap {n : ℕ}
    (A : Fin n → E →L[ℝ] E) {L η : ℝ} (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hA : ∀ i, ‖A i‖ ≤ L) (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n)
    (hstep : η * n * L ≤ 1 / 32) (j : ℕ) (a b : Fin n) :
    ‖epochCrossOperator A η w j - epochCrossOperator (fun i => A (Equiv.swap a b i)) η w j‖ ≤
      16 * η * L := by
  have hlen' : (w ++ (w.drop (j + 1)).reverse).length ≤ 2 * n := by
    simp only [List.length_append, List.length_reverse, List.length_drop, hlen]
    omega
  have hlenR : ((w ++ (w.drop (j + 1)).reverse).length : ℝ) ≤ 2 * n := by exact_mod_cast hlen'
  have hmul := mul_le_mul_of_nonneg_right hlenR (mul_nonneg hη hL)
  have hcount : (w ++ (w.drop (j + 1)).reverse).count a +
      (w ++ (w.drop (j + 1)).reverse).count b ≤ 4 := by
    have hwa := List.nodup_iff_count_le_one.mp hw a
    have hwb := List.nodup_iff_count_le_one.mp hw b
    have hd' : (w.drop (j + 1)).Nodup := hw.drop
    have hd : ((w.drop (j + 1)).reverse).Nodup := List.nodup_reverse.mpr hd'
    have hva := List.nodup_iff_count_le_one.mp hd a
    have hvb := List.nodup_iff_count_le_one.mp hd b
    simp only [List.count_append]
    omega
  exact swap_product_difference A hL hη hA a b _ (by nlinarith) hcount

lemma epoch_cross_vector_bound {n : ℕ}
    (A : Fin n → E →L[ℝ] E) (b : Fin n → E) {L G η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hA : ∀ i, ‖A i‖ ≤ L) (hb : ∑ i, b i = 0) (hbound : ∀ i, ‖b i‖ ≤ G)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n)
    (hstep : η * n * L ≤ 1 / 32) :
    ‖∑ π : Equiv.Perm (Fin n), ∑ j : Fin w.length,
      epochCrossOperator (fun i => A (π i)) η w j.val (b (π (w.get j)))‖ ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * 16 * η * n * L * G := by
  classical
  have hj : ∀ j : Fin w.length,
      ‖∑ π : Equiv.Perm (Fin n), epochCrossOperator (fun i => A (π i)) η w j.val (b (π (w.get j)))‖ ≤
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (16 * η * L) * G := by
    intro j
    apply permutation_swap_centering_bound b hb _ (w.get j) (by positivity) hbound
    intro π k
    simpa only [Equiv.Perm.mul_apply] using epochCrossOperator_swap (fun i => A (π i))
      hL hη (fun i => hA _) w hw hlen hstep j.val (w.get j) k
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j : Fin w.length,
        ‖∑ π : Equiv.Perm (Fin n), epochCrossOperator (fun i => A (π i)) η w j.val (b (π (w.get j)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin w.length, (Fintype.card (Equiv.Perm (Fin n)) : ℝ) * (16 * η * L) * G :=
      Finset.sum_le_sum (fun j _ => hj j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hlen, nsmul_eq_mul]; ring

lemma epoch_cross_inner (A : I → E →L[ℝ] E)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric) (η : ℝ) (w : List I) (j : ℕ) (x y : E) :
    ⟪epochLinear A η w x, epochLinear A η (w.drop (j + 1)) y⟫ =
      ⟪x, epochCrossOperator A η w j y⟫ := by
  have hB : ∀ i, (1 + (-η) • A i).toLinearMap.IsSymmetric := by
    intro i u v
    change ⟪u + (-η) • A i u, v⟫ = ⟪u, v + (-η) • A i v⟫
    rw [inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right]
    have he : ⟪A i u, v⟫ = ⟪u, A i v⟫ := hs i u v
    rw [he]
  unfold epochCrossOperator
  rw [List.map_append, List.prod_append, mul_apply_eq_comp]
  exact (reverse_word_inner _ hB w x (epochLinear A η (w.drop (j + 1)) y)).symm

lemma epoch_cross_inner_bound {n : ℕ}
    (A : Fin n → E →L[ℝ] E) (b : Fin n → E) {L G η : ℝ}
    (hL : 0 ≤ L) (hη : 0 ≤ η)
    (hs : ∀ i, (A i).toLinearMap.IsSymmetric)
    (hA : ∀ i, ‖A i‖ ≤ L) (hb : ∑ i, b i = 0) (hbound : ∀ i, ‖b i‖ ≤ G)
    (w : List (Fin n)) (hw : w.Nodup) (hlen : w.length = n)
    (hstep : η * n * L ≤ 1 / 32) (x : E) :
    |∑ π : Equiv.Perm (Fin n),
      ⟪epochLinear (fun i => A (π i)) η w x,
        epochNoise (fun i => A (π i)) (fun i => b (π i)) η w⟫| ≤
      ‖x‖ * ((Fintype.card (Equiv.Perm (Fin n)) : ℝ) * 16 * η * n * L * G) := by
  classical
  simp_rw [epochNoise_eq_sum, inner_sum,
    epoch_cross_inner _ (fun i => hs _) η w]
  simp_rw [← inner_sum]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (epoch_cross_vector_bound A b hL hη hA hb hbound w hw hlen hstep)
      (norm_nonneg _))

end OracleTemplate.Reshuffling
