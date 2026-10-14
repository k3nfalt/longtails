import LongTails.Proofs.AdjointBudget
import LongTails.Proofs.Execution

open scoped RealInnerProductSpace

namespace OracleTemplate.CohypomonotoneAdjoint

open CohypomonotoneInclusion (target)

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def stepT (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) (st : AdjState E) :
    AdjState E :=
  (adjointAnchored L L₂ ρ x0).update st
    (Sum.elim F (fun p : E × E => adj p.1 p.2) (((adjointAnchored L L₂ ρ x0).query st).2))

noncomputable def startState (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) :
    ℕ → AdjState E
  | 0 => ⟨0, 0, true, false, x0, x0, x0, 0, x0⟩
  | j + 1 => ⟨j + 1, 0, true, false, yv L ρ F (run0 L L₂ ρ F adj x0),
      tgt L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 j) j,
      pred L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 j) j, 0,
      run L L₂ ρ F adj x0 j⟩

noncomputable def cost (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) (j : ℕ) : ℕ :=
  1 + 2 * innerLen L L₂ ρ (loopRes L L₂ ρ F adj x0 j)

noncomputable def cum (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, cost L L₂ ρ F adj x0 i

variable {L L₂ ρ : ℝ} {F : E → E} {adj : E → E → E} {x0 : E}

lemma finish_congr (st st' : AdjState E) (f : E) (hk : st.k = st'.k) (ha : st.a = st'.a)
    (hv : st.v = st'.v) : finish L ρ st f = finish L ρ st' f := by
  cases st; cases st'
  simp only at hk ha hv
  subst hk ha hv
  rfl

lemma inner_pairs (j m : ℕ) (a t v last : E) :
    (stepT L L₂ ρ F adj x0)^[2 * (m + 1)] ⟨j, m + 1, false, true, a, t, v, res L ρ F t v, last⟩ =
      finish L ρ ⟨j, 0, true, false, a, t, (innerStep L L₂ ρ F adj t)^[m + 1] v, 0, last⟩
        (F ((innerStep L L₂ ρ F adj t)^[m + 1] v)) := by
  induction m generalizing v with
  | zero =>
    show stepT L L₂ ρ F adj x0 (stepT L L₂ ρ F adj x0 _) = _
    simp only [stepT, adjointAnchored, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false,
      Bool.false_eq_true]
    rfl
  | succ m ih =>
    rw [show 2 * (m + 1 + 1) = 2 * (m + 1) + 2 by ring, Function.iterate_add_apply]
    have h2 : (stepT L L₂ ρ F adj x0)^[2]
        (⟨j, m + 1 + 1, false, true, a, t, v, res L ρ F t v, last⟩ : AdjState E) =
        ⟨j, m + 1, false, true, a, t, innerStep L L₂ ρ F adj t v,
          res L ρ F t (innerStep L L₂ ρ F adj t v), last⟩ := by
      show stepT L L₂ ρ F adj x0 (stepT L L₂ ρ F adj x0 _) = _
      simp only [stepT, adjointAnchored, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false,
        Bool.false_eq_true, Nat.add_sub_cancel, Nat.add_one_ne_zero]
      rfl
    rw [h2, ih, ← Function.iterate_succ_apply]

lemma inner_last (j m : ℕ) (a t v last : E) (i : ℕ) (hi : i < 2 * (m + 1)) :
    ((stepT L L₂ ρ F adj x0)^[i]
      ⟨j, m + 1, false, true, a, t, v, res L ρ F t v, last⟩).last = last := by
  induction m generalizing v i with
  | zero =>
    interval_cases i
    · rfl
    · rfl
  | succ m ih =>
    rcases Nat.lt_or_ge i 2 with hi2 | hi2
    · interval_cases i
      · rfl
      · rfl
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 2 := ⟨i - 2, by omega⟩
      rw [Function.iterate_add_apply]
      have h2 : (stepT L L₂ ρ F adj x0)^[2]
          (⟨j, m + 1 + 1, false, true, a, t, v, res L ρ F t v, last⟩ : AdjState E) =
          ⟨j, m + 1, false, true, a, t, innerStep L L₂ ρ F adj t v,
            res L ρ F t (innerStep L L₂ ρ F adj t v), last⟩ := by
        show stepT L L₂ ρ F adj x0 (stepT L L₂ ρ F adj x0 _) = _
        simp only [stepT, adjointAnchored, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false,
          Bool.false_eq_true, Nat.add_sub_cancel, Nat.add_one_ne_zero]
        rfl
      rw [h2]
      exact ih _ _ (by omega)

lemma loop_end (j : ℕ) (a t v0 last : E) :
    (stepT L L₂ ρ F adj x0)^[1 + 2 * innerLen L L₂ ρ ‖res L ρ F t v0‖]
        ⟨j, 0, true, false, a, t, v0, 0, last⟩ =
      finish L ρ ⟨j, 0, true, false, a, t, innerRun L L₂ ρ F adj t v0
          (innerLen L L₂ ρ ‖res L ρ F t v0‖), 0, last⟩
        (F (innerRun L L₂ ρ F adj t v0 (innerLen L L₂ ρ ‖res L ρ F t v0‖))) := by
  set N := innerLen L L₂ ρ ‖res L ρ F t v0‖ with hN
  rw [add_comm, Function.iterate_add_apply]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · rw [h0]
    show stepT L L₂ ρ F adj x0 _ = _
    simp only [stepT, adjointAnchored, Sum.elim_inl, ite_false, Bool.false_eq_true, ite_true]
    have : innerLen L L₂ ρ ‖v0 + (2 * ρ + 1 / L) • F v0 - t‖ = 0 := h0
    simp only [this, ite_true]
    exact finish_congr _ _ _ rfl rfl rfl
  · obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    have h1 : (stepT L L₂ ρ F adj x0)^[1] (⟨j, 0, true, false, a, t, v0, 0, last⟩ : AdjState E) =
        ⟨j, m + 1, false, true, a, t, v0, res L ρ F t v0, last⟩ := by
      show stepT L L₂ ρ F adj x0 _ = _
      simp only [stepT, adjointAnchored, Sum.elim_inl, ite_false, Bool.false_eq_true, ite_true]
      have : innerLen L L₂ ρ ‖v0 + (2 * ρ + 1 / L) • F v0 - t‖ = m + 1 := by rw [← hm, hN]; rfl
      simp only [this, Nat.add_one_ne_zero, ite_false]
      rfl
    rw [h1, hm, inner_pairs]
    rfl

lemma loop_last (j : ℕ) (a t v0 last : E) (i : ℕ)
    (hi : i < 1 + 2 * innerLen L L₂ ρ ‖res L ρ F t v0‖) :
    ((stepT L L₂ ρ F adj x0)^[i] ⟨j, 0, true, false, a, t, v0, 0, last⟩).last = last := by
  set N := innerLen L L₂ ρ ‖res L ρ F t v0‖ with hN
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · rw [hi0]; rfl
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · omega
  · obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    rw [Function.iterate_add_apply]
    have h1 : (stepT L L₂ ρ F adj x0)^[1] (⟨j, 0, true, false, a, t, v0, 0, last⟩ : AdjState E) =
        ⟨j, m + 1, false, true, a, t, v0, res L ρ F t v0, last⟩ := by
      show stepT L L₂ ρ F adj x0 _ = _
      simp only [stepT, adjointAnchored, Sum.elim_inl, ite_false, Bool.false_eq_true, ite_true]
      have : innerLen L L₂ ρ ‖v0 + (2 * ρ + 1 / L) • F v0 - t‖ = m + 1 := by rw [← hm, hN]; rfl
      simp only [this, Nat.add_one_ne_zero, ite_false]
      rfl
    rw [h1]
    exact inner_last j m a t v0 last i' (by omega)

lemma start_eq (j : ℕ) :
    startState L L₂ ρ F adj x0 j = ⟨j, 0, true, false, (startState L L₂ ρ F adj x0 j).a,
      (startState L L₂ ρ F adj x0 j).t, (startState L L₂ ρ F adj x0 j).v, 0,
      (startState L L₂ ρ F adj x0 j).last⟩ := by
  cases j <;> rfl

lemma loopRes_eq (j : ℕ) :
    loopRes L L₂ ρ F adj x0 j =
      ‖res L ρ F (startState L L₂ ρ F adj x0 j).t (startState L L₂ ρ F adj x0 j).v‖ := by
  cases j <;> rfl

lemma run_eq (j : ℕ) :
    run L L₂ ρ F adj x0 j = innerRun L L₂ ρ F adj (startState L L₂ ρ F adj x0 j).t
      (startState L L₂ ρ F adj x0 j).v (innerLen L L₂ ρ (loopRes L L₂ ρ F adj x0 j)) := by
  cases j <;> rfl

lemma loop_step (j : ℕ) :
    (stepT L L₂ ρ F adj x0)^[cost L L₂ ρ F adj x0 j] (startState L L₂ ρ F adj x0 j) =
      startState L L₂ ρ F adj x0 (j + 1) := by
  rw [start_eq j]
  unfold cost
  rw [loopRes_eq, loop_end, ← loopRes_eq, ← run_eq]
  cases j with
  | zero => rfl
  | succ j => rfl

lemma loop_out (j i : ℕ) (hi : i < cost L L₂ ρ F adj x0 j) :
    ((stepT L L₂ ρ F adj x0)^[i] (startState L L₂ ρ F adj x0 j)).last =
      (startState L L₂ ρ F adj x0 j).last := by
  rw [start_eq j]
  unfold cost at hi
  rw [loopRes_eq] at hi
  exact loop_last j _ _ _ _ i hi

lemma cum_succ (j : ℕ) :
    cum L L₂ ρ F adj x0 (j + 1) = cum L L₂ ρ F adj x0 j + cost L L₂ ρ F adj x0 j := by
  simp [cum, Finset.sum_range_succ]

lemma iterate_cum (j : ℕ) :
    (stepT L L₂ ρ F adj x0)^[cum L L₂ ρ F adj x0 j] ⟨0, 0, true, false, x0, x0, x0, 0, x0⟩ =
      startState L L₂ ρ F adj x0 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [cum_succ, add_comm, Function.iterate_add_apply, ih, loop_step]

lemma cum_ge (j : ℕ) : j ≤ cum L L₂ ρ F adj x0 j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih => rw [cum_succ]; unfold cost; omega

lemma cum_mono {i j : ℕ} (h : i ≤ j) : cum L L₂ ρ F adj x0 i ≤ cum L L₂ ρ F adj x0 j := by
  unfold cum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun _ _ _ => Nat.zero_le _

lemma output_late (N K : ℕ) (hK : cum L L₂ ρ F adj x0 (N + 1) ≤ K) :
    ∃ m, N ≤ m ∧ ((stepT L L₂ ρ F adj x0)^[K] ⟨0, 0, true, false, x0, x0, x0, 0, x0⟩).last =
      run L L₂ ρ F adj x0 m := by
  have hex : ∃ j, K < cum L L₂ ρ F adj x0 (j + 1) := by
    refine ⟨K, ?_⟩
    have := cum_ge (L := L) (L₂ := L₂) (ρ := ρ) (F := F) (adj := adj) (x0 := x0) (K + 1)
    omega
  classical
  let j := Nat.find hex
  have hj : K < cum L L₂ ρ F adj x0 (j + 1) := Nat.find_spec hex
  have hjle : cum L L₂ ρ F adj x0 j ≤ K := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · rw [h0]; exact Nat.zero_le _
    · obtain ⟨j', hj'⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have := Nat.find_min hex (show j' < j by omega)
      rw [hj']
      omega
  have hNj : N + 1 ≤ j := by
    by_contra hc
    push Not at hc
    have := cum_mono (L := L) (L₂ := L₂) (ρ := ρ) (F := F) (adj := adj) (x0 := x0)
      (show j + 1 ≤ N + 1 by omega)
    omega
  obtain ⟨m, hm⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  refine ⟨m, by omega, ?_⟩
  have hsplit : K = (K - cum L L₂ ρ F adj x0 j) + cum L L₂ ρ F adj x0 j := by omega
  rw [hsplit, Function.iterate_add_apply, iterate_cum]
  have hi : K - cum L L₂ ρ F adj x0 j < cost L L₂ ρ F adj x0 j := by
    rw [cum_succ] at hj; omega
  rw [loop_out j _ hi, hm]
  rfl

lemma innerLen_le (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ) {x : ℝ} (hx : 0 ≤ x) :
    (innerLen L L₂ ρ x : ℝ) ≤ 16 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) ^ 2 * x +
      4 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L) + 2 := by
  have hl : 0 ≤ Real.log (11 + 10 * ρ * L) := Real.log_nonneg (by nlinarith [mul_nonneg hρ hL.le])
  have h1 := Nat.ceil_lt_add_one (show 0 ≤ 16 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) ^ 2 * x by
    positivity)
  have h2 := Nat.ceil_lt_add_one (show 0 ≤ 4 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L) by
    positivity)
  unfold innerLen
  push_cast
  linarith

lemma cum_le [FiniteDimensional ℝ E] {J : E → E →L[ℝ] E} (h : Hyp F J L L₂ ρ) (hL : 0 < L)
    (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ) (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) {xs : E}
    (hxs : F xs = 0) {D : ℝ} (hD : ‖x0 - xs‖ ≤ D) (N : ℕ) :
    (cum L L₂ ρ F adj x0 (N + 1) : ℝ) ≤
      ((N : ℝ) + 1) * (5 + 8 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L)) +
        32 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) ^ 2 *
          ((2 * ρ + 1 / L) * L * D * (1 + (24 + 4 * hsum N) * hsum N)) := by
  have hsum := loopRes_sum h hL hL₂ hρ hadj x0 hxs hD N
  have hc : ∀ j, (cost L L₂ ρ F adj x0 j : ℝ) ≤
      (5 + 8 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L)) +
        32 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) ^ 2 * loopRes L L₂ ρ F adj x0 j := by
    intro j
    have hx : 0 ≤ loopRes L L₂ ρ F adj x0 j := by cases j <;> exact norm_nonneg _
    have := innerLen_le hL hL₂ hρ hx
    unfold cost
    push_cast
    linarith
  unfold cum
  push_cast
  calc ∑ j ∈ Finset.range (N + 1), (cost L L₂ ρ F adj x0 j : ℝ)
      ≤ ∑ j ∈ Finset.range (N + 1), ((5 + 8 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L)) +
        32 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) ^ 2 * loopRes L L₂ ρ F adj x0 j) :=
        Finset.sum_le_sum fun j _ => hc j
    _ = ((N : ℝ) + 1) * (5 + 8 * (2 + 2 * ρ * L) ^ 2 * Real.log (11 + 10 * ρ * L)) +
        32 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) ^ 2 *
          ∑ j ∈ Finset.range (N + 1), loopRes L L₂ ρ F adj x0 j := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
        ring
    _ ≤ _ := by
        have : 0 ≤ 32 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) ^ 2 := by positivity
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum this)

end OracleTemplate.CohypomonotoneAdjoint
