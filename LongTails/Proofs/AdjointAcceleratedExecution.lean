import LongTails.Proofs.AdjointAcceleratedOuter
import LongTails.Proofs.AdjointExecution
import Mathlib.Analysis.Complex.ExponentialBounds

open scoped RealInnerProductSpace

namespace OracleTemplate.CohypomonotoneAdjoint.Acc

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def stepT (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) (st : AccState E) :
    AccState E :=
  (adjointAccelerated L L₂ ρ x0).update st
    (Sum.elim F (fun p : E × E => adj p.1 p.2) (((adjointAccelerated L L₂ ρ x0).query st).2))

noncomputable def startState (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) :
    ℕ → AccState E
  | 0 => ⟨0, 0, true, false, false, false, x0, x0, x0, 0, 0, 0, x0⟩
  | j + 1 => ⟨j + 1, 0, true, false, false, false, yv L ρ F (run0 L L₂ ρ F adj x0),
      tgt L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 j) j,
      pred L ρ F (yv L ρ F (run0 L L₂ ρ F adj x0)) (run L L₂ ρ F adj x0 j) j, 0, 0, 0,
      run L L₂ ρ F adj x0 j⟩

noncomputable def lcost (L L₂ ρ x : ℝ) : ℕ :=
  if useAgd L L₂ ρ x then 1 + 2 * agdLen L ρ else 1 + 2 * innerLen L L₂ ρ x

noncomputable def cost (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) (j : ℕ) : ℕ :=
  lcost L L₂ ρ (loopRes L L₂ ρ F adj x0 j)

noncomputable def cum (L L₂ ρ : ℝ) (F : E → E) (adj : E → E → E) (x0 : E) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, cost L L₂ ρ F adj x0 i

variable {L L₂ ρ : ℝ} {F : E → E} {adj : E → E → E} {x0 : E}

lemma finish_congr (st st' : AccState E) (u f : E) (hk : st.k = st'.k) (ha : st.a = st'.a) :
    accFinish L ρ st u f = accFinish L ρ st' u f := by
  cases st; cases st'
  simp only at hk ha
  subst hk ha
  rfl

lemma gd_pairs (j m : ℕ) (a t v xx zz last : E) :
    (stepT L L₂ ρ F adj x0)^[2 * (m + 1)]
        ⟨j, m + 1, false, true, false, false, a, t, v, res L ρ F t v, xx, zz, last⟩ =
      accFinish L ρ ⟨j, 0, true, false, false, false, a, t, 0, 0, 0, 0, last⟩
        ((innerStep L L₂ ρ F adj t)^[m + 1] v) (F ((innerStep L L₂ ρ F adj t)^[m + 1] v)) := by
  induction m generalizing v with
  | zero =>
    show stepT L L₂ ρ F adj x0 (stepT L L₂ ρ F adj x0 _) = _
    simp only [stepT, adjointAccelerated, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false,
      Bool.false_eq_true]
    exact finish_congr _ _ _ _ rfl rfl
  | succ m ih =>
    rw [show 2 * (m + 1 + 1) = 2 * (m + 1) + 2 by ring, Function.iterate_add_apply]
    have h2 : (stepT L L₂ ρ F adj x0)^[2]
        (⟨j, m + 1 + 1, false, true, false, false, a, t, v, res L ρ F t v, xx, zz, last⟩ :
          AccState E) =
        ⟨j, m + 1, false, true, false, false, a, t, innerStep L L₂ ρ F adj t v,
          res L ρ F t (innerStep L L₂ ρ F adj t v), xx, zz, last⟩ := by
      show stepT L L₂ ρ F adj x0 (stepT L L₂ ρ F adj x0 _) = _
      simp only [stepT, adjointAccelerated, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false,
        Bool.false_eq_true, Nat.add_sub_cancel, Nat.add_one_ne_zero]
      rfl
    rw [h2, ih, ← Function.iterate_succ_apply]

lemma gd_last (j m : ℕ) (a t v xx zz last : E) (i : ℕ) (hi : i < 2 * (m + 1)) :
    ((stepT L L₂ ρ F adj x0)^[i]
      ⟨j, m + 1, false, true, false, false, a, t, v, res L ρ F t v, xx, zz, last⟩).last =
        last := by
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
          (⟨j, m + 1 + 1, false, true, false, false, a, t, v, res L ρ F t v, xx, zz, last⟩ :
            AccState E) =
          ⟨j, m + 1, false, true, false, false, a, t, innerStep L L₂ ρ F adj t v,
            res L ρ F t (innerStep L L₂ ρ F adj t v), xx, zz, last⟩ := by
        show stepT L L₂ ρ F adj x0 (stepT L L₂ ρ F adj x0 _) = _
        simp only [stepT, adjointAccelerated, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false,
          Bool.false_eq_true, Nat.add_sub_cancel, Nat.add_one_ne_zero]
        rfl
      rw [h2]
      exact ih _ _ (by omega)

lemma agd_two (j m : ℕ) (a t last : E) (s : AgdState E) :
    (stepT L L₂ ρ F adj x0)^[2]
        (⟨j, m + 1 + 1, false, true, true, false, a, t, s.y, res L ρ F t s.y, s.x, s.z, last⟩ :
          AccState E) =
      ⟨j, m + 1, false, true, true, false, a, t, (agdStep L ρ F adj t s).y,
        res L ρ F t (agdStep L ρ F adj t s).y, (agdStep L ρ F adj t s).x,
        (agdStep L ρ F adj t s).z, last⟩ := by
  show stepT L L₂ ρ F adj x0 (stepT L L₂ ρ F adj x0 _) = _
  simp only [stepT, adjointAccelerated, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false,
    Bool.false_eq_true, Nat.add_sub_cancel, Nat.add_one_ne_zero, decide_false]
  rfl

lemma agd_pairs (j m : ℕ) (a t last : E) (s : AgdState E) :
    (stepT L L₂ ρ F adj x0)^[2 * (m + 1)]
        ⟨j, m + 1, false, true, true, false, a, t, s.y, res L ρ F t s.y, s.x, s.z, last⟩ =
      accFinish L ρ ⟨j, 0, true, false, false, false, a, t, 0, 0, 0, 0, last⟩
        ((agdStep L ρ F adj t)^[m + 1] s).x (F ((agdStep L ρ F adj t)^[m + 1] s).x) := by
  induction m generalizing s with
  | zero =>
    show stepT L L₂ ρ F adj x0 (stepT L L₂ ρ F adj x0 _) = _
    simp only [stepT, adjointAccelerated, Sum.elim_inl, Sum.elim_inr, ite_true, ite_false,
      Bool.false_eq_true, Nat.sub_self, decide_true]
    exact finish_congr _ _ _ _ rfl rfl
  | succ m ih =>
    rw [show 2 * (m + 1 + 1) = 2 * (m + 1) + 2 by ring, Function.iterate_add_apply, agd_two, ih,
      ← Function.iterate_succ_apply]

lemma agd_last (j m : ℕ) (a t last : E) (s : AgdState E) (i : ℕ) (hi : i < 2 * (m + 1)) :
    ((stepT L L₂ ρ F adj x0)^[i]
      ⟨j, m + 1, false, true, true, false, a, t, s.y, res L ρ F t s.y, s.x, s.z, last⟩).last =
        last := by
  induction m generalizing s i with
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
      rw [Function.iterate_add_apply, agd_two]
      exact ih _ _ (by omega)

lemma agdLen_pos (hL : 0 < L) (hρ : 0 ≤ ρ) : 0 < agdLen L ρ := by
  unfold agdLen
  apply Nat.ceil_pos.mpr
  have : 0 < Real.log (22 + 20 * ρ * L) := Real.log_pos (by nlinarith [mul_nonneg hρ hL.le])
  positivity

lemma first_agd {t v0 : E} (hu : useAgd L L₂ ρ ‖res L ρ F t v0‖ = true) (j : ℕ) (a last : E)
    (m : ℕ) (hm : agdLen L ρ = m + 1) :
    stepT L L₂ ρ F adj x0 (⟨j, 0, true, false, false, false, a, t, v0, 0, 0, 0, last⟩ : AccState E) =
      ⟨j, m + 1, false, true, true, false, a, t, v0, res L ρ F t v0, v0, v0, last⟩ := by
  have hu' : useAgd L L₂ ρ ‖v0 + (2 * ρ + 1 / L) • F v0 - t‖ = true := hu
  simp only [stepT, adjointAccelerated, Sum.elim_inl, ite_false, Bool.false_eq_true, ite_true,
    accLen, hu', hm, Nat.add_one_ne_zero]
  rfl

lemma first_gd {t v0 : E} (hu : useAgd L L₂ ρ ‖res L ρ F t v0‖ = false) (j : ℕ) (a last : E)
    (m : ℕ) (hm : innerLen L L₂ ρ ‖res L ρ F t v0‖ = m + 1) :
    stepT L L₂ ρ F adj x0 (⟨j, 0, true, false, false, false, a, t, v0, 0, 0, 0, last⟩ : AccState E) =
      ⟨j, m + 1, false, true, false, false, a, t, v0, res L ρ F t v0, v0, v0, last⟩ := by
  have hu' : useAgd L L₂ ρ ‖v0 + (2 * ρ + 1 / L) • F v0 - t‖ = false := hu
  have hm' : innerLen L L₂ ρ ‖v0 + (2 * ρ + 1 / L) • F v0 - t‖ = m + 1 := hm
  simp only [stepT, adjointAccelerated, Sum.elim_inl, ite_false, Bool.false_eq_true, ite_true,
    accLen, hu', hm', Nat.add_one_ne_zero]
  rfl

lemma loop_end (hL : 0 < L) (hρ : 0 ≤ ρ) (j : ℕ) (a t v0 last : E) :
    (stepT L L₂ ρ F adj x0)^[lcost L L₂ ρ ‖res L ρ F t v0‖]
        ⟨j, 0, true, false, false, false, a, t, v0, 0, 0, 0, last⟩ =
      accFinish L ρ ⟨j, 0, true, false, false, false, a, t, 0, 0, 0, 0, last⟩
        (innerSolve L L₂ ρ F adj t v0) (F (innerSolve L L₂ ρ F adj t v0)) := by
  unfold lcost innerSolve
  cases hu : useAgd L L₂ ρ ‖res L ρ F t v0‖ with
  | true =>
    simp only [ite_true]
    obtain ⟨m, hm⟩ : ∃ m, agdLen L ρ = m + 1 := ⟨agdLen L ρ - 1, by
      have := agdLen_pos hL hρ; omega⟩
    rw [add_comm, Function.iterate_add_apply, Function.iterate_one, first_agd hu j a last m hm,
      hm]
    exact agd_pairs (s := ⟨v0, v0, v0⟩) j m a t last
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    set N := innerLen L L₂ ρ ‖res L ρ F t v0‖ with hN
    rw [add_comm, Function.iterate_add_apply]
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]
      show stepT L L₂ ρ F adj x0 _ = _
      have hu' : useAgd L L₂ ρ ‖v0 + (2 * ρ + 1 / L) • F v0 - t‖ = false := hu
      have h0' : innerLen L L₂ ρ ‖v0 + (2 * ρ + 1 / L) • F v0 - t‖ = 0 := h0
      simp only [stepT, adjointAccelerated, Sum.elim_inl, ite_false, Bool.false_eq_true,
        ite_true, accLen, hu', h0']
      simp only [innerRun, Function.iterate_zero, id]
      exact finish_congr _ _ _ _ rfl rfl
    · obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      rw [Function.iterate_one, first_gd hu j a last m hm, hm, gd_pairs]
      rfl

lemma loop_last (hL : 0 < L) (hρ : 0 ≤ ρ) (j : ℕ) (a t v0 last : E) (i : ℕ)
    (hi : i < lcost L L₂ ρ ‖res L ρ F t v0‖) :
    ((stepT L L₂ ρ F adj x0)^[i]
      ⟨j, 0, true, false, false, false, a, t, v0, 0, 0, 0, last⟩).last = last := by
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · rw [hi0]; rfl
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [Function.iterate_add_apply, Function.iterate_one]
  unfold lcost at hi
  cases hu : useAgd L L₂ ρ ‖res L ρ F t v0‖ with
  | true =>
    rw [hu] at hi
    simp only [ite_true] at hi
    obtain ⟨m, hm⟩ : ∃ m, agdLen L ρ = m + 1 := ⟨agdLen L ρ - 1, by
      have := agdLen_pos hL hρ; omega⟩
    rw [first_agd hu j a last m hm]
    exact agd_last (s := ⟨v0, v0, v0⟩) j m a t last i' (by omega)
  | false =>
    rw [hu] at hi
    simp only [Bool.false_eq_true, ite_false] at hi
    set N := innerLen L L₂ ρ ‖res L ρ F t v0‖ with hN
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · omega
    · obtain ⟨m, hm⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      rw [first_gd hu j a last m hm]
      exact gd_last j m a t v0 v0 v0 last i' (by omega)

lemma start_eq (j : ℕ) :
    startState L L₂ ρ F adj x0 j = ⟨j, 0, true, false, false, false,
      (startState L L₂ ρ F adj x0 j).a, (startState L L₂ ρ F adj x0 j).t,
      (startState L L₂ ρ F adj x0 j).v, 0, 0, 0, (startState L L₂ ρ F adj x0 j).last⟩ := by
  cases j <;> rfl

lemma loopRes_eq (j : ℕ) :
    loopRes L L₂ ρ F adj x0 j =
      ‖res L ρ F (startState L L₂ ρ F adj x0 j).t (startState L L₂ ρ F adj x0 j).v‖ := by
  cases j <;> rfl

lemma run_eq (j : ℕ) :
    run L L₂ ρ F adj x0 j = innerSolve L L₂ ρ F adj (startState L L₂ ρ F adj x0 j).t
      (startState L L₂ ρ F adj x0 j).v := by
  cases j <;> rfl

lemma loop_step (hL : 0 < L) (hρ : 0 ≤ ρ) (j : ℕ) :
    (stepT L L₂ ρ F adj x0)^[cost L L₂ ρ F adj x0 j] (startState L L₂ ρ F adj x0 j) =
      startState L L₂ ρ F adj x0 (j + 1) := by
  rw [start_eq j]
  unfold cost
  rw [loopRes_eq, loop_end hL hρ, ← run_eq]
  cases j with
  | zero => rfl
  | succ j => rfl

lemma loop_out (hL : 0 < L) (hρ : 0 ≤ ρ) (j i : ℕ) (hi : i < cost L L₂ ρ F adj x0 j) :
    ((stepT L L₂ ρ F adj x0)^[i] (startState L L₂ ρ F adj x0 j)).last =
      (startState L L₂ ρ F adj x0 j).last := by
  rw [start_eq j]
  unfold cost at hi
  rw [loopRes_eq] at hi
  exact loop_last hL hρ j _ _ _ _ i hi

lemma cum_succ (j : ℕ) :
    cum L L₂ ρ F adj x0 (j + 1) = cum L L₂ ρ F adj x0 j + cost L L₂ ρ F adj x0 j := by
  simp [cum, Finset.sum_range_succ]

lemma iterate_cum (hL : 0 < L) (hρ : 0 ≤ ρ) (j : ℕ) :
    (stepT L L₂ ρ F adj x0)^[cum L L₂ ρ F adj x0 j]
        ⟨0, 0, true, false, false, false, x0, x0, x0, 0, 0, 0, x0⟩ =
      startState L L₂ ρ F adj x0 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [cum_succ, add_comm, Function.iterate_add_apply, ih, loop_step hL hρ]

lemma cum_ge (j : ℕ) : j ≤ cum L L₂ ρ F adj x0 j := by
  induction j with
  | zero => exact Nat.zero_le _
  | succ j ih =>
    rw [cum_succ]
    have : 1 ≤ cost L L₂ ρ F adj x0 j := by
      unfold cost lcost; split_ifs <;> omega
    omega

lemma cum_mono {i j : ℕ} (h : i ≤ j) : cum L L₂ ρ F adj x0 i ≤ cum L L₂ ρ F adj x0 j := by
  unfold cum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun _ _ _ => Nat.zero_le _

lemma output_late (hL : 0 < L) (hρ : 0 ≤ ρ) (N K : ℕ) (hK : cum L L₂ ρ F adj x0 (N + 1) ≤ K) :
    ∃ m, N ≤ m ∧ ((stepT L L₂ ρ F adj x0)^[K]
      ⟨0, 0, true, false, false, false, x0, x0, x0, 0, 0, 0, x0⟩).last = run L L₂ ρ F adj x0 m := by
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
  rw [hsplit, Function.iterate_add_apply, iterate_cum hL hρ]
  have hi : K - cum L L₂ ρ F adj x0 j < cost L L₂ ρ F adj x0 j := by
    rw [cum_succ] at hj; omega
  rw [loop_out hL hρ j _ hi, hm]
  rfl

lemma agdLen_le (hL : 0 < L) (hρ : 0 ≤ ρ) :
    (agdLen L ρ : ℝ) ≤ 4 * (2 + 2 * ρ * L) * Real.log (22 + 20 * ρ * L) + 1 := by
  have hl : 0 ≤ Real.log (22 + 20 * ρ * L) := Real.log_nonneg (by nlinarith [mul_nonneg hρ hL.le])
  have := Nat.ceil_lt_add_one (show 0 ≤ 4 * (2 + 2 * ρ * L) * Real.log (22 + 20 * ρ * L) by
    positivity)
  unfold agdLen
  linarith

lemma lcost_le (hL : 0 < L) (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ) {x : ℝ} (hx : 0 ≤ x) :
    (lcost L L₂ ρ x : ℝ) ≤ 3 + 8 * (2 + 2 * ρ * L) * Real.log (22 + 20 * ρ * L) +
      81 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) ^ 3 * Real.log (11 + 10 * ρ * L) * x := by
  set Λ := 2 + 2 * ρ * L with hΛ
  set γ := 2 * ρ + 1 / L with hγ
  set ℓ := Real.log (11 + 10 * ρ * L) with hℓ
  have hρL : 0 ≤ ρ * L := mul_nonneg hρ hL.le
  have hΛ2 : 2 ≤ Λ := by rw [hΛ]; linarith
  have hγ0 : 0 ≤ γ := by positivity
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ, Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  have hB : 0 ≤ 81 * γ * L₂ * Λ ^ 3 * ℓ * x := by positivity
  unfold lcost
  cases hu : useAgd L L₂ ρ x with
  | true =>
    simp only [ite_true]
    have := agdLen_le hL hρ
    push_cast
    nlinarith
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hbig : 1 < 7 * γ * L₂ * Λ * x := by
      have : ¬ (7 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) * x ≤ 1) := by
        simpa [useAgd] using hu
      push Not at this
      exact this
    have hin := innerLen_le hL hL₂ hρ hx
    rw [← hΛ, ← hγ, ← hℓ] at hin
    have hc : 0 ≤ γ * L₂ * Λ * x := by positivity
    have hA : 0 ≤ 3 + 8 * Λ * Real.log (22 + 20 * ρ * L) := by
      have : 0 ≤ Real.log (22 + 20 * ρ * L) := Real.log_nonneg (by linarith)
      positivity
    have k1 : 5 + 8 * Λ ^ 2 * ℓ ≤ (5 + 8 * Λ ^ 2 * ℓ) * (7 * γ * L₂ * Λ * x) := by
      have : 0 ≤ 5 + 8 * Λ ^ 2 * ℓ := by positivity
      nlinarith
    have k2 : 35 + 32 * Λ ≤ 25 * Λ ^ 2 * ℓ := by nlinarith
    have k3 : (5 + 8 * Λ ^ 2 * ℓ) * (7 * γ * L₂ * Λ * x) + 16 * γ * L₂ * Λ ^ 2 * x * 2 ≤
        81 * γ * L₂ * Λ ^ 3 * ℓ * x := by
      have e : 81 * γ * L₂ * Λ ^ 3 * ℓ * x - ((5 + 8 * Λ ^ 2 * ℓ) * (7 * γ * L₂ * Λ * x) +
          16 * γ * L₂ * Λ ^ 2 * x * 2) = (γ * L₂ * Λ * x) * (25 * Λ ^ 2 * ℓ - 35 - 32 * Λ) := by
        ring
      have := mul_nonneg hc (sub_nonneg.mpr k2)
      nlinarith
    push_cast
    nlinarith

lemma cum_le [FiniteDimensional ℝ E] {J : E → E →L[ℝ] E} (h : Hyp F J L L₂ ρ) (hL : 0 < L)
    (hL₂ : 0 ≤ L₂) (hρ : 0 ≤ ρ) (hadj : ∀ x w y, ⟪adj x w, y⟫ = ⟪w, J x y⟫) {xs : E}
    (hxs : F xs = 0) {D : ℝ} (hD : ‖x0 - xs‖ ≤ D) (N : ℕ) :
    (cum L L₂ ρ F adj x0 (N + 1) : ℝ) ≤
      ((N : ℝ) + 1) * (3 + 8 * (2 + 2 * ρ * L) * Real.log (22 + 20 * ρ * L)) +
        81 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) ^ 3 * Real.log (11 + 10 * ρ * L) *
          ((2 * ρ + 1 / L) * L * D * (1 + (24 + 4 * hsum N) * hsum N)) := by
  have hs := loopRes_sum h hL hL₂ hρ hadj x0 hxs hD N
  set A := 3 + 8 * (2 + 2 * ρ * L) * Real.log (22 + 20 * ρ * L) with hA
  set B := 81 * (2 * ρ + 1 / L) * L₂ * (2 + 2 * ρ * L) ^ 3 * Real.log (11 + 10 * ρ * L) with hB
  have hB0 : 0 ≤ B := by
    have : 0 ≤ Real.log (11 + 10 * ρ * L) := Real.log_nonneg (by nlinarith [mul_nonneg hρ hL.le])
    positivity
  have hc : ∀ j, (cost L L₂ ρ F adj x0 j : ℝ) ≤ A + B * loopRes L L₂ ρ F adj x0 j := by
    intro j
    have hx : 0 ≤ loopRes L L₂ ρ F adj x0 j := by cases j <;> exact norm_nonneg _
    exact lcost_le hL hL₂ hρ hx
  unfold cum
  push_cast
  calc ∑ j ∈ Finset.range (N + 1), (cost L L₂ ρ F adj x0 j : ℝ)
      ≤ ∑ j ∈ Finset.range (N + 1), (A + B * loopRes L L₂ ρ F adj x0 j) :=
        Finset.sum_le_sum fun j _ => hc j
    _ = ((N : ℝ) + 1) * A + B * ∑ j ∈ Finset.range (N + 1), loopRes L L₂ ρ F adj x0 j := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
        simp
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hs hB0)

end OracleTemplate.CohypomonotoneAdjoint.Acc
