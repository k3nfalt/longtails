import LongTails.Proofs.EscapeChainCoordinates

namespace LongTails.Proofs.EscapeChainCount

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction
open EscapeChainCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

variable {K : ℕ} {u v : ℕ → E}

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma bessel (fr : Frame K u v) (x : E) :
    ∑ m ∈ Finset.range K, (⟪u m, x⟫ ^ 2 + ⟪v m, x⟫ ^ 2) ≤ ‖x‖ ^ 2 := by
  let w : Fin K ⊕ Fin K → E := Sum.elim (fun i => u i) (fun i => v i)
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    rintro (i | i) (j | j)
    · simp only [w, Sum.elim_inl, fr.uu i j i.2 j.2, Sum.inl.injEq, Fin.ext_iff]
    · simp [w, fr.uv i j i.2 j.2]
    · simp [w, fr.vu i.2 j.2]
    · simp only [w, Sum.elim_inr, fr.vv i j i.2 j.2, Sum.inr.injEq, Fin.ext_iff]
  have h := hw.sum_inner_products_le (s := Finset.univ) x
  rw [Fintype.sum_sum_type] at h
  simp only [w, Sum.elim_inl, Sum.elim_inr, Real.norm_eq_abs, sq_abs] at h
  rw [Fin.sum_univ_eq_sum_range (fun i => ⟪u i, x⟫ ^ 2),
    Fin.sum_univ_eq_sum_range (fun i => ⟪v i, x⟫ ^ 2)] at h
  rw [Finset.sum_add_distrib]
  exact h

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma resid_eq (l : ℕ) (x : E) :
    resid u v l x = ‖x‖ ^ 2 - ∑ m ∈ Finset.range l, (⟪u m, x⟫ ^ 2 + ⟪v m, x⟫ ^ 2) := by
  unfold resid
  rw [normsq_eq]
  simp [RidgeJets.value, sqf]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma resid_ge (fr : Frame K u v) {l : ℕ} (hl : l ≤ K) (x : E) :
    ∑ m ∈ Finset.Ico l K, (⟪u m, x⟫ ^ 2 + ⟪v m, x⟫ ^ 2) ≤ resid u v l x := by
  rw [resid_eq]
  have h := bessel fr x
  rw [← Finset.sum_range_add_sum_Ico _ hl] at h
  linarith

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma resid_nonneg (fr : Frame K u v) {l : ℕ} (hl : l ≤ K) (x : E) : 0 ≤ resid u v l x :=
  le_trans (Finset.sum_nonneg fun m _ => by positivity) (resid_ge fr hl x)

def active (u v : ℕ → E) (x : E) (l : ℕ) : Prop :=
  (l = 0 ∨ 3 / 5 < ⟪u (l - 1), x⟫) ∧ resid u v l x ≤ 16

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma active_card (fr : Frame K u v) (x : E) (n : ℕ) (hn : n ≤ K) [DecidablePred (active u v x)] :
    ((Finset.range n).filter (active u v x)).card ≤ 45 := by
  set S := (Finset.range n).filter (active u v x) with hS
  rcases S.eq_empty_or_nonempty with h0 | hne
  · rw [h0]; simp
  set l0 := S.min' hne
  have hl0 : l0 ∈ S := S.min'_mem hne
  have hl0K : l0 < K := lt_of_lt_of_le (Finset.mem_range.1 (Finset.mem_filter.1 hl0).1) hn
  have hres : resid u v l0 x ≤ 16 := (Finset.mem_filter.1 hl0).2.2
  set T := S.erase l0
  have hT : ∀ l ∈ T, 1 ≤ l ∧ l0 + 1 ≤ l ∧ l < K ∧ 3 / 5 < ⟪u (l - 1), x⟫ := by
    intro l hl
    have hne' := Finset.ne_of_mem_erase hl
    have hlS := Finset.mem_of_mem_erase hl
    have hle : l0 ≤ l := S.min'_le l hlS
    have hlt : l0 < l := lt_of_le_of_ne hle (Ne.symm hne')
    have hlK : l < K := lt_of_lt_of_le (Finset.mem_range.1 (Finset.mem_filter.1 hlS).1) hn
    rcases (Finset.mem_filter.1 hlS).2.1 with h | h
    · omega
    · exact ⟨by omega, by omega, hlK, h⟩
  have himg : T.image (fun l => l - 1) ⊆ Finset.Ico l0 K := by
    intro m hm
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 hm
    obtain ⟨h1, h2, h3, -⟩ := hT l hl
    exact Finset.mem_Ico.2 ⟨by omega, by omega⟩
  have hinj : Set.InjOn (fun l => l - 1) (T : Set ℕ) := by
    intro a ha b hb hab
    have := (hT a ha).1; have := (hT b hb).1
    simp only at hab; omega
  have hsum : ∑ l ∈ T, ⟪u (l - 1), x⟫ ^ 2 ≤ 16 := by
    rw [← Finset.sum_image (f := fun m => ⟪u m, x⟫ ^ 2) hinj]
    calc _ ≤ ∑ m ∈ Finset.Ico l0 K, ⟪u m, x⟫ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => sq_nonneg _)
      _ ≤ ∑ m ∈ Finset.Ico l0 K, (⟪u m, x⟫ ^ 2 + ⟪v m, x⟫ ^ 2) :=
          Finset.sum_le_sum fun m _ => le_add_of_nonneg_right (sq_nonneg _)
      _ ≤ resid u v l0 x := resid_ge fr hl0K.le x
      _ ≤ 16 := hres
  have hlow : (T.card : ℝ) * (9 / 25) ≤ ∑ l ∈ T, ⟪u (l - 1), x⟫ ^ 2 := by
    rw [← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro l hl
    have h := (hT l hl).2.2.2
    nlinarith
  have hcard : T.card + 1 = S.card := Finset.card_erase_add_one hl0
  have hT45 : (T.card : ℝ) < 45 := by nlinarith
  have : T.card < 45 := by exact_mod_cast hT45
  omega

end LongTails.Proofs.EscapeChainCount
