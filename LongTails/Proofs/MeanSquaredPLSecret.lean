import LongTails.Proofs.MeanSquaredPLMask

open scoped BigOperators RealInnerProductSpace

namespace LongTails.Proofs.MeanSquaredPLSecret

open LongTails.Proofs.ThirdOrderMaskedOracle LongTails.Proofs.MeanSquaredPLMask
open LongTails.Proofs.RelativeHessianLocalized (radius radius_pos)

variable {d n : ℕ}

noncomputable def simSecret (R : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d) : Space d :=
  ∑ s ∈ Finset.range R, maskUpTo R π w s • block π s w

noncomputable def secret (π : Fin (n + 1) ↪ Fin d) (w : Space d) : Space d :=
  simSecret (n + 1) π w

noncomputable def unitReply (π : Fin (n + 1) ↪ Fin d) (w : Space d) (c : ℝ) : Space d :=
  hardGrad π w + (c - 1) • secret π w

noncomputable def unitSim (R : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d) (c : ℝ) : Space d :=
  partGrad π (R - 1) w + (c - 1) • simSecret R π w

lemma simSecret_prefix (R : ℕ) (π ρ : Fin (n + 1) ↪ Fin d) (w : Space d)
    (h : ∀ k : Fin (n + 1), k.val < R → π k = ρ k) : simSecret R π w = simSecret R ρ w := by
  unfold simSecret
  apply Finset.sum_congr rfl
  intro s hs
  have hs' := Finset.mem_range.mp hs
  rw [maskUpTo_prefix R π ρ w s h, block_prefix π ρ s w (fun k hk => h k (by omega))]

lemma unitSim_prefix (R : ℕ) (hR : 1 ≤ R) (π ρ : Fin (n + 1) ↪ Fin d) (w : Space d) (c : ℝ)
    (h : ∀ k : Fin (n + 1), k.val < R → π k = ρ k) : unitSim R π w c = unitSim R ρ w c := by
  unfold unitSim
  rw [simSecret_prefix R π ρ w h, partGrad_prefix π ρ (R - 1) w (fun k hk => h k (by omega))]

lemma simSecret_outside (R : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d)
    (hw : 2 * radius n ≤ ‖w‖) : simSecret R π w = 0 := by
  unfold simSecret
  apply Finset.sum_eq_zero
  intro s _
  rw [block_outside π s w hw, smul_zero]

lemma simSecret_succ (r : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d)
    (h : ∀ i : Fin (n + 1), r ≤ i.val → |w (π i)| ≤ 1 / 40) :
    simSecret (r + 1) π w = simSecret r π w + block π r w := by
  unfold simSecret
  rw [Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro s _
    rw [maskUpTo_congr_small (r + 1) r π w s (fun i hi => h i (by
      rw [min_eq_right (Nat.le_succ r)] at hi
      exact hi))]
  · rw [maskUpTo_one (r + 1) π w r (fun i hi _ => h i hi), one_smul]

lemma simSecret_small (r : ℕ) (π : Fin (n + 1) ↪ Fin d) (w : Space d)
    (h : ∀ i : Fin (n + 1), r ≤ i.val → |w (π i)| ≤ 1 / 40) (k : ℕ) :
    simSecret (r + 1 + k) π w = simSecret (r + 1) π w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, simSecret_succ (r + 1 + k) π w (fun i hi => h i (by omega)), ih,
      block_small π r (r + 1 + k) w (by omega) h, add_zero]

lemma secret_eq_sim (r : ℕ) (hr : r ≤ n) (π : Fin (n + 1) ↪ Fin d) (w : Space d)
    (h : ∀ i : Fin (n + 1), r ≤ i.val → |w (π i)| ≤ 1 / 40) :
    secret π w = simSecret (r + 1) π w := by
  obtain ⟨k, hk⟩ : ∃ k, n + 1 = r + 1 + k := ⟨n - r, by omega⟩
  unfold secret
  rw [hk]
  exact simSecret_small r π w h k

lemma reply_eq_sim_succ (r : ℕ) (hr : r ≤ n) (π : Fin (n + 1) ↪ Fin d) (w : Space d) (c : ℝ)
    (h : ‖w‖ ≤ 2 * radius n → ∀ i : Fin (n + 1), r ≤ i.val → |w (π i)| ≤ 1 / 40) :
    unitReply π w c = unitSim (r + 1) π w c := by
  unfold unitReply unitSim
  rw [Nat.add_sub_cancel]
  by_cases hw : ‖w‖ ≤ 2 * radius n
  · rw [secret_eq_sim r hr π w (h hw),
      hardGrad_eq_part π r w (fun _ i hi _ => by have := h hw i hi; linarith)]
  · push Not at hw
    rw [hardGrad_outside π w hw.le, partGrad_outside π r w hw.le]
    unfold secret
    rw [simSecret_outside _ π w hw.le, simSecret_outside _ π w hw.le]

lemma reply_eq_sim_zero (r : ℕ) (hr : r ≤ n) (π : Fin (n + 1) ↪ Fin d)
    (w : Space d)
    (h : ‖w‖ ≤ 2 * radius n → ∀ i : Fin (n + 1), r ≤ i.val → |w (π i)| ≤ 1 / 40) :
    unitReply π w 0 = unitSim r π w 0 := by
  rw [reply_eq_sim_succ r hr π w 0 h]
  unfold unitSim
  rw [Nat.add_sub_cancel]
  by_cases hw : ‖w‖ ≤ 2 * radius n
  · rw [simSecret_succ r π w (h hw)]
    have hb : partGrad π r w = partGrad π (r - 1) w + block π r w := by
      unfold block
      abel
    rw [hb]
    simp only [zero_sub, neg_smul, one_smul]
    abel
  · push Not at hw
    rw [partGrad_outside π r w hw.le, partGrad_outside π (r - 1) w hw.le,
      simSecret_outside _ π w hw.le, simSecret_outside _ π w hw.le]

lemma reply_eq_sim_full (π : Fin (n + 1) ↪ Fin d) (w : Space d) (c : ℝ) :
    unitReply π w c = unitSim (n + 1) π w c := by
  unfold unitReply unitSim secret
  rw [Nat.add_sub_cancel,
    hardGrad_eq_part π n w (fun _ i hi hi' => absurd hi' (by omega))]

lemma term_bound (R : ℕ) (π : Fin (n + 1) ↪ Fin d) (s : ℕ) (w : Space d) :
    ‖maskUpTo R π w s • block π s w‖ ≤ 2 ^ 51 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (maskUpTo_bounds R π w s).1]
  have h1 := (maskUpTo_bounds R π w s).2
  have h2 := block_bound π s w
  have h3 := norm_nonneg (block π s w)
  nlinarith [(maskUpTo_bounds R π w s).1]

lemma term_lipschitz (R : ℕ) (π : Fin (n + 1) ↪ Fin d) (s : ℕ) (x y : Space d) :
    ‖maskUpTo R π x s • block π s x - maskUpTo R π y s • block π s y‖ ≤ 2 ^ 57 * ‖x - y‖ := by
  have he : maskUpTo R π x s • block π s x - maskUpTo R π y s • block π s y =
      (maskUpTo R π x s - maskUpTo R π y s) • block π s x +
        maskUpTo R π y s • (block π s x - block π s y) := by
    rw [sub_smul, smul_sub]
    abel
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (maskUpTo_bounds R π y s).1]
  have h1 := maskUpTo_lipschitz R π x y s
  have h2 := block_bound π s x
  have h3 := block_lipschitz π s x y
  have h4 := (maskUpTo_bounds R π y s).2
  have h5 := (maskUpTo_bounds R π y s).1
  have h6 := norm_nonneg (x - y)
  have h7 := norm_nonneg (block π s x)
  have h8 := norm_nonneg (block π s x - block π s y)
  have t1 : |maskUpTo R π x s - maskUpTo R π y s| * ‖block π s x‖ ≤
      40 * ‖x - y‖ * 2 ^ 51 := mul_le_mul h1 h2 h7 (by positivity)
  have t2 : maskUpTo R π y s * ‖block π s x - block π s y‖ ≤ 1 * (2 ^ 54 * ‖x - y‖) :=
    mul_le_mul h4 h3 h8 (by norm_num)
  nlinarith

lemma term_unique (π : Fin (n + 1) ↪ Fin d) (w : Space d) {s s' : ℕ} (hs' : s' ≤ n)
    (hlt : s < s') (h1 : maskUpTo (n + 1) π w s • block π s w ≠ 0)
    (h2 : maskUpTo (n + 1) π w s' • block π s' w ≠ 0) : False := by
  have hb : block π s' w ≠ 0 := fun h => h2 (by rw [h, smul_zero])
  have hm : maskUpTo (n + 1) π w s ≠ 0 := fun h => h1 (by rw [h, zero_smul])
  let i : Fin (n + 1) := ⟨s' - 1, by omega⟩
  have hlarge : 1 / 10 ≤ |w (π i)| := by
    by_contra hcon
    push Not at hcon
    apply hb
    apply block_flat
    intro j hj
    have hji : j = i := Fin.ext (show j.val = s' - 1 by omega)
    rw [hji]
    exact hcon
  exact hm (maskUpTo_zero (n + 1) π w s i (show s ≤ s' - 1 by omega) i.isLt (by linarith))

lemma sum_lipschitz_of_unique {ι : Type*} (S : Finset ι)
    (F : ι → Space d → Space d) (K : ℝ) (hK : 0 ≤ K)
    (hLip : ∀ s ∈ S, ∀ x y, ‖F s x - F s y‖ ≤ K * ‖x - y‖)
    (huniq : ∀ x, ∀ s ∈ S, ∀ s' ∈ S, F s x ≠ 0 → F s' x ≠ 0 → s = s') (x y : Space d) :
    ‖∑ s ∈ S, F s x - ∑ s ∈ S, F s y‖ ≤ 2 * K * ‖x - y‖ := by
  classical
  let A := S.filter (fun s => F s x ≠ 0)
  let B := S.filter (fun s => F s y ≠ 0)
  have hA : A.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    exact huniq x a ha'.1 b hb'.1 ha'.2 hb'.2)
  have hB : B.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => by
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    exact huniq y a ha'.1 b hb'.1 ha'.2 hb'.2)
  have hsub : A ∪ B ⊆ S := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsum : ∑ s ∈ S, F s x - ∑ s ∈ S, F s y = ∑ s ∈ A ∪ B, (F s x - F s y) := by
    rw [← Finset.sum_sub_distrib]
    symm
    apply Finset.sum_subset hsub
    intro s hs hns
    have h1 : F s x = 0 := by
      by_contra hne
      exact hns (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs, hne⟩))
    have h2 : F s y = 0 := by
      by_contra hne
      exact hns (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs, hne⟩))
    rw [h1, h2, sub_zero]
  rw [hsum]
  calc ‖∑ s ∈ A ∪ B, (F s x - F s y)‖ ≤ ∑ s ∈ A ∪ B, ‖F s x - F s y‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ A ∪ B, K * ‖x - y‖ :=
        Finset.sum_le_sum (fun s hs => hLip s (hsub hs) x y)
    _ = ((A ∪ B).card : ℝ) * (K * ‖x - y‖) := by simp
    _ ≤ 2 * (K * ‖x - y‖) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hK (norm_nonneg _))
        have := (Finset.card_union_le A B).trans (Nat.add_le_add hA hB)
        exact_mod_cast this
    _ = 2 * K * ‖x - y‖ := by ring

lemma secret_unique (π : Fin (n + 1) ↪ Fin d) (w : Space d) :
    ∀ s ∈ Finset.range (n + 1), ∀ s' ∈ Finset.range (n + 1),
      maskUpTo (n + 1) π w s • block π s w ≠ 0 → maskUpTo (n + 1) π w s' • block π s' w ≠ 0 →
        s = s' := by
  intro s hs s' hs' h1 h2
  have hsn := Finset.mem_range.mp hs
  have hsn' := Finset.mem_range.mp hs'
  rcases lt_trichotomy s s' with h | h | h
  · exact (term_unique π w (by omega) h h1 h2).elim
  · exact h
  · exact (term_unique π w (by omega) h h2 h1).elim

lemma secret_lipschitz (π : Fin (n + 1) ↪ Fin d) (x y : Space d) :
    ‖secret π x - secret π y‖ ≤ 2 ^ 58 * ‖x - y‖ := by
  have h := sum_lipschitz_of_unique (Finset.range (n + 1))
    (fun s w => maskUpTo (n + 1) π w s • block π s w) (2 ^ 57) (by positivity)
    (fun s _ x y => term_lipschitz (n + 1) π s x y) (fun w => secret_unique π w) x y
  unfold secret simSecret
  refine h.trans (le_of_eq ?_)
  ring

lemma secret_bound' (π : Fin (n + 1) ↪ Fin d) (w : Space d) : ‖secret π w‖ ≤ 2 ^ 51 := by
  classical
  unfold secret simSecret
  by_cases hex : ∃ s ∈ Finset.range (n + 1), maskUpTo (n + 1) π w s • block π s w ≠ 0
  · obtain ⟨s, hs, hne⟩ := hex
    rw [Finset.sum_eq_single_of_mem s hs (fun s' hs' hne' => by
      by_contra hcon
      exact hne' (secret_unique π w s' hs' s hs hcon hne))]
    exact term_bound (n + 1) π s w
  · push Not at hex
    rw [Finset.sum_eq_zero hex, norm_zero]
    positivity

lemma secret_continuous (π : Fin (n + 1) ↪ Fin d) : Continuous (secret π) := by
  have hLip : LipschitzWith (Real.toNNReal (2 ^ 58)) (secret π) :=
    LipschitzWith.of_dist_le_mul (fun x y => by
      rw [dist_eq_norm, dist_eq_norm]
      exact (secret_lipschitz π x y).trans
        (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _)))
  exact hLip.continuous

end LongTails.Proofs.MeanSquaredPLSecret
