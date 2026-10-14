import LongTails.Proofs.ReshufflingWordEnergy

open scoped BigOperators RealInnerProductSpace

namespace OracleTemplate.Reshuffling

variable {I E : Type*} [Fintype I] [DecidableEq I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma permutation_pair_exchange (F : I → I → ℝ) (i j k : I)
    (hij : i ≠ j) (hik : i ≠ k) :
    (∑ π : Equiv.Perm I, F (π i) (π j)) = ∑ π : Equiv.Perm I, F (π i) (π k) := by
  classical
  apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap j k))
  intro π
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hij hik]

lemma permutation_cross_nonpos (b : I → E) (hb : ∑ i, b i = 0)
    (i j : I) (hij : i ≠ j) :
    (∑ π : Equiv.Perm I, ⟪b (π i), b (π j)⟫) ≤ 0 := by
  classical
  let c := fun k => ∑ π : Equiv.Perm I, ⟪b (π i), b (π k)⟫
  have hsum : ∑ k, c k = 0 := by
    dsimp [c]
    rw [Finset.sum_comm]
    have hz : ∀ π : Equiv.Perm I, (∑ k, ⟪b (π i), b (π k)⟫) = 0 := by
      intro π
      rw [← inner_sum, Equiv.sum_comp, hb, inner_zero_right]
    simp only [hz, Finset.sum_const_zero]
  have heq : ∑ k ∈ Finset.univ.erase i, c k =
      ((Finset.univ.erase i).card : ℝ) * c j := by
    calc
      _ = ∑ _k ∈ Finset.univ.erase i, c j := by
        apply Finset.sum_congr rfl
        intro k hk
        exact permutation_pair_exchange (fun a z => ⟪b a, b z⟫) i k j
          (Finset.mem_erase.mp hk).1.symm hij
      _ = _ := by simp
  have hdecomp := Finset.sum_erase_add (s := Finset.univ) c (Finset.mem_univ i)
  rw [heq, hsum] at hdecomp
  have hd : 0 ≤ c i := Finset.sum_nonneg (fun π _ => real_inner_self_nonneg)
  have hp : (0 : ℝ) < (Finset.univ.erase i).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨j, by simp [hij.symm]⟩
  change c j ≤ 0
  nlinarith

lemma permutation_subset_second_moment (b : I → E) (hb : ∑ i, b i = 0)
    {G : ℝ} (hbound : ∀ i, ‖b i‖ ≤ G) (s : Finset I) :
    (∑ π : Equiv.Perm I, ‖∑ i ∈ s, b (π i)‖ ^ 2) ≤
      (Fintype.card (Equiv.Perm I) : ℝ) * s.card * G ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hd : (∑ π : Equiv.Perm I, ‖b (π i)‖ ^ 2) ≤
        (Fintype.card (Equiv.Perm I) : ℝ) * G ^ 2 := by
      calc
        _ ≤ ∑ _π : Equiv.Perm I, G ^ 2 := Finset.sum_le_sum (fun π _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hbound _) 2)
        _ = _ := by simp
    have hc : (∑ π : Equiv.Perm I, ⟪b (π i), ∑ j ∈ s, b (π j)⟫) ≤ 0 := by
      simp_rw [inner_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_nonpos
      intro j hj
      exact permutation_cross_nonpos b hb i j (fun hij => hi (hij ▸ hj))
    have he : (∑ π : Equiv.Perm I, ‖∑ j ∈ insert i s, b (π j)‖ ^ 2) =
        (∑ π : Equiv.Perm I, ‖b (π i)‖ ^ 2) +
        (∑ π : Equiv.Perm I, ‖∑ j ∈ s, b (π j)‖ ^ 2) +
        2 * (∑ π : Equiv.Perm I, ⟪b (π i), ∑ j ∈ s, b (π j)⟫) := by
      simp only [Finset.sum_insert hi, norm_add_sq_real, Finset.sum_add_distrib, Finset.mul_sum]
      ring
    rw [he, Finset.card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma permutation_swap_centering (b : I → E) (hb : ∑ i, b i = 0)
    (H : Equiv.Perm I → E →L[ℝ] E) (i : I) :
    (Fintype.card I : ℝ) • (∑ π : Equiv.Perm I, H π (b (π i))) =
      ∑ j : I, ∑ π : Equiv.Perm I,
        (H π - H (π * Equiv.swap i j)) (b (π i)) := by
  classical
  have he : ∀ j, (∑ π : Equiv.Perm I, H (π * Equiv.swap i j) (b (π i))) =
      ∑ π : Equiv.Perm I, H π (b (π j)) := by
    intro j
    apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j))
    intro π
    simp [Equiv.Perm.mul_apply]
  simp only [sub_apply, Finset.sum_sub_distrib]
  simp_rw [he]
  have hz : (∑ j : I, ∑ π : Equiv.Perm I, H π (b (π j))) = 0 := by
    rw [Finset.sum_comm]
    have hzπ : ∀ π : Equiv.Perm I, (∑ j : I, H π (b (π j))) = 0 := by
      intro π
      rw [← map_sum, Equiv.sum_comp, hb, map_zero]
    simp only [hzπ, Finset.sum_const_zero]
  rw [hz, sub_zero]
  simp only [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

lemma permutation_swap_centering_bound (b : I → E) (hb : ∑ i, b i = 0)
    (H : Equiv.Perm I → E →L[ℝ] E) (i : I) {M G : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ j, ‖b j‖ ≤ G)
    (hH : ∀ π j, ‖H π - H (π * Equiv.swap i j)‖ ≤ M) :
    ‖∑ π : Equiv.Perm I, H π (b (π i))‖ ≤
      (Fintype.card (Equiv.Perm I) : ℝ) * M * G := by
  classical
  have hn : (0 : ℝ) < Fintype.card I := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
  apply (mul_le_mul_iff_right₀ hn).mp
  calc
    _ = ‖(Fintype.card I : ℝ) • (∑ π : Equiv.Perm I, H π (b (π i)))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hn.le]
    _ = _ := congrArg norm (permutation_swap_centering b hb H i)
    _ ≤ ∑ j : I, ‖∑ π : Equiv.Perm I, (H π - H (π * Equiv.swap i j)) (b (π i))‖ := norm_sum_le _ _
    _ ≤ ∑ j : I, ∑ π : Equiv.Perm I, ‖(H π - H (π * Equiv.swap i j)) (b (π i))‖ :=
      Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
    _ ≤ ∑ _j : I, ∑ _π : Equiv.Perm I, M * G := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro π hπ
      exact ((H π - H (π * Equiv.swap i j)).le_opNorm _).trans
        (mul_le_mul (hH π j) (hbound _) (norm_nonneg _) hM)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

lemma permutation_list_second_moment (b : I → E) (hb : ∑ i, b i = 0)
    {G : ℝ} (hbound : ∀ i, ‖b i‖ ≤ G)
    (w : List I) (hw : w.Nodup) :
    (∑ π : Equiv.Perm I, ‖(w.map (fun i => b (π i))).sum‖ ^ 2) ≤
      (Fintype.card (Equiv.Perm I) : ℝ) * w.length * G ^ 2 := by
  classical
  have he : ∀ π : Equiv.Perm I, (w.map (fun i => b (π i))).sum =
      ∑ i ∈ w.toFinset, b (π i) := fun π => (List.sum_toFinset _ hw).symm
  simp_rw [he]
  simpa only [List.toFinset_card_of_nodup hw] using
    permutation_subset_second_moment b hb hbound w.toFinset

omit [InnerProductSpace ℝ E] in
lemma norm_sum_sq_le_card {J : Type*} (s : Finset J) (v : J → E) :
    ‖∑ j ∈ s, v j‖ ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, ‖v j‖ ^ 2 := by
  calc
    _ ≤ (∑ j ∈ s, ‖v j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun j => ‖v j‖)

lemma permutation_weighted_prefix_moment (b : I → E) (hb : ∑ i, b i = 0)
    {G M : ℝ} (hbound : ∀ i, ‖b i‖ ≤ G)
    (w : List I) (hw : w.Nodup) (B : Equiv.Perm I → Fin w.length → E →L[ℝ] E)
    (hB : ∀ π j, ‖B π j‖ ≤ M) :
    (∑ π : Equiv.Perm I, ‖∑ j : Fin w.length,
      B π j (((w.take j.val).map (fun i => b (π i))).sum)‖ ^ 2) ≤
      (Fintype.card (Equiv.Perm I) : ℝ) * (w.length : ℝ) ^ 3 * M ^ 2 * G ^ 2 := by
  classical
  have hp : ∀ j : Fin w.length,
      (∑ π : Equiv.Perm I, ‖((w.take j.val).map (fun i => b (π i))).sum‖ ^ 2) ≤
      (Fintype.card (Equiv.Perm I) : ℝ) * w.length * G ^ 2 := by
    intro j
    calc
      _ ≤ (Fintype.card (Equiv.Perm I) : ℝ) * (w.take j.val).length * G ^ 2 :=
        permutation_list_second_moment b hb hbound _ hw.take
      _ ≤ _ := by gcongr; simp only [List.length_take]; exact Nat.min_le_right _ _
  have he : ∀ π : Equiv.Perm I,
      ‖∑ j : Fin w.length, B π j (((w.take j.val).map (fun i => b (π i))).sum)‖ ^ 2 ≤
      (w.length : ℝ) * M ^ 2 * ∑ j : Fin w.length,
        ‖((w.take j.val).map (fun i => b (π i))).sum‖ ^ 2 := by
    intro π
    calc
      _ ≤ (w.length : ℝ) * ∑ j : Fin w.length,
          ‖B π j (((w.take j.val).map (fun i => b (π i))).sum)‖ ^ 2 := by
        simpa only [Finset.card_univ, Fintype.card_fin] using
          norm_sum_sq_le_card Finset.univ (fun j => B π j (((w.take j.val).map (fun i => b (π i))).sum))
      _ ≤ (w.length : ℝ) * ∑ j : Fin w.length,
          M ^ 2 * ‖((w.take j.val).map (fun i => b (π i))).sum‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro j hj
        have hn : ‖B π j (((w.take j.val).map (fun i => b (π i))).sum)‖ ≤
            M * ‖((w.take j.val).map (fun i => b (π i))).sum‖ := ((B π j).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hB π j) (norm_nonneg _))
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = _ := by rw [← Finset.mul_sum]; ring
  calc
    _ ≤ ∑ π : Equiv.Perm I, (w.length : ℝ) * M ^ 2 * ∑ j : Fin w.length,
        ‖((w.take j.val).map (fun i => b (π i))).sum‖ ^ 2 := Finset.sum_le_sum (fun π _ => he π)
    _ = (w.length : ℝ) * M ^ 2 * ∑ j : Fin w.length, ∑ π : Equiv.Perm I,
        ‖((w.take j.val).map (fun i => b (π i))).sum‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (w.length : ℝ) * M ^ 2 * ∑ _j : Fin w.length,
        (Fintype.card (Equiv.Perm I) : ℝ) * w.length * G ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => hp j)) (by positivity)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end OracleTemplate.Reshuffling
