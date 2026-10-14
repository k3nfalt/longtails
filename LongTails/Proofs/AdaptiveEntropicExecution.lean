import LongTails.Algorithms.AdaptiveEntropic
import LongTails.Proofs.SgdExecution
import LongTails.Proofs.QuantileClipping

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma fold_minimum_le {K : ℕ} (b : Fin K → ℝ) (l : List (Fin K)) (i : Fin K) :
    b (l.foldl (fun i j => if b j < b i then j else i) i) ≤ b i ∧
      ∀ j ∈ l, b (l.foldl (fun i j => if b j < b i then j else i) i) ≤ b j := by
  induction l generalizing i with
  | nil => simp
  | cons j l ih =>
    let k := if b j < b i then j else i
    have hk : b k ≤ b i ∧ b k ≤ b j := by
      dsimp [k]
      split_ifs with h
      · exact ⟨h.le, le_rfl⟩
      · exact ⟨le_rfl, le_of_not_gt h⟩
    have hr := ih k
    change b (l.foldl _ k) ≤ b i ∧ ∀ a ∈ j :: l, b (l.foldl _ k) ≤ b a
    refine ⟨hr.1.trans hk.1, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hr.1.trans hk.2
    · exact hr.2 a ha

lemma minimumIndex_le {K : ℕ} (hK : 0 < K) (b : Fin K → ℝ) (j : Fin K) :
    b (minimumIndex hK b) ≤ b j := by
  exact (fold_minimum_le b (List.finRange K) ⟨0, hK⟩).2 j (by simp)

lemma empiricalQuantile_le (q : Public) (s : State q) (j : Fin (trimCount q)) :
    empiricalQuantile q s ≤ s.extremes j := minimumIndex_le _ _ _

lemma pending_query (q : Public) (s : State q) (g : Vector q.d) :
    queryPoint q { s with pending := some g } = queryPoint q s := by
  rfl

lemma primary_update (q : Public) (s : State q) (g : Vector q.d)
    (hw : s.warmup = 0) (hp : s.pending = none) :
    updateState q s g = { s with pending := some g } := by
  simp [updateState, hw, hp]

lemma paired_query (q : Public) (s : State q) (g : Vector q.d)
    (hw : s.warmup = 0) (hp : s.pending = none) :
    queryPoint q (updateState q s g) = queryPoint q s := by
  rw [primary_update q s g hw hp]
  exact pending_query q s g

lemma primary_output (q : Public) (s : State q) (g : Vector q.d)
    (hw : s.warmup = 0) (hp : s.pending = none) :
    (updateState q s g).y = s.y := by
  rw [primary_update q s g hw hp]

structure ExecutionInvariant (q : Public) (n : ℕ) (s : State q) : Prop where
  warm_le : s.warmup ≤ preload q
  warm_pending : 0 < s.warmup → s.pending = none
  warm_completed : 0 < s.warmup → s.completed = 0
  clock : n + s.warmup = preload q + 2 * s.completed + if s.pending.isSome then 1 else 0
  history : s.history.length + s.warmup = preload q + s.completed

lemma initial_invariant (q : Public) : ExecutionInvariant q 0 (initialState q) := by
  constructor <;> simp [initialState]

lemma update_invariant (q : Public) (n : ℕ) (s : State q) (g : Vector q.d)
    (hs : ExecutionInvariant q n s) : ExecutionInvariant q (n + 1) (updateState q s g) := by
  rcases hs with ⟨hle, hp, hc, hclock, hhist⟩
  by_cases hw : 0 < s.warmup
  · have hpn := hp hw
    have hcn := hc hw
    simp only [hpn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hcn] at hclock hhist
    constructor
    · simpa [updateState, hw] using (Nat.sub_le s.warmup 1).trans hle
    · intro _
      simpa [updateState, hw] using hpn
    · intro _
      simpa [updateState, hw] using hcn
    · simp [updateState, hw, hpn, hcn]
      omega
    · simp [updateState, hw, hcn]
      omega
  · have hw0 : s.warmup = 0 := by omega
    cases hpend : s.pending with
    | none =>
      simp only [hw0, hpend, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        Nat.add_zero] at hclock hhist
      constructor
      · simp [updateState, hw0, hpend]
      · simp [updateState, hw0, hpend]
      · simp [updateState, hw0, hpend]
      · simp [updateState, hw0, hpend]
        omega
      · simpa [updateState, hw, hw0, hpend] using hhist
    | some g₁ =>
      simp only [hw0, hpend, Option.isSome_some, ↓reduceIte, Nat.add_zero] at hclock hhist
      constructor
      · simp [updateState, hw, hpend]
      · simp [updateState, hw, hpend]
      · simp [updateState, hw, hpend]
      · simp [updateState, hw, hpend]
        omega
      · simp [updateState, hw, hpend]
        omega

lemma advance_invariant (q : Public) (reply : ℕ → simplex q.d → Vector q.d)
    (N call n : ℕ) (s : State q) (hs : ExecutionInvariant q n s) :
    ExecutionInvariant q (n + N)
      (StochasticGradient.advance (fun k s => updateState q s (reply k (queryPoint q s)))
        N call s) := by
  induction N generalizing call n s with
  | zero => simpa [StochasticGradient.advance] using hs
  | succ N ih =>
    simpa only [StochasticGradient.advance, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using ih (call + 1) (n + 1) _ (update_invariant q n s _ hs)

lemma invariant_completed (q : Public) (n : ℕ) (s : State q)
    (hs : ExecutionInvariant q n s) : s.completed = (n - preload q) / 2 := by
  have hc := hs.clock
  by_cases hw : 0 < s.warmup
  · have hp := hs.warm_pending hw
    have hz := hs.warm_completed hw
    simp [hp, hz] at hc
    omega
  · have hz : s.warmup = 0 := by omega
    simp only [hz, Nat.add_zero] at hc
    cases hp : s.pending <;> simp [hp] at hc <;> omega

lemma invariant_history (q : Public) (n : ℕ) (s : State q)
    (hs : ExecutionInvariant q n s) (hn : preload q ≤ n) :
    s.warmup = 0 ∧ s.history.length = preload q + s.completed := by
  have hc := hs.clock
  have hh := hs.history
  by_cases hw : 0 < s.warmup
  · have hp := hs.warm_pending hw
    have hz := hs.warm_completed hw
    simp [hp, hz] at hc
    omega
  · constructor <;> omega

lemma update_completed_mono (q : Public) (s : State q) (g : Vector q.d) :
    s.completed ≤ (updateState q s g).completed := by
  unfold updateState
  split_ifs
  · exact le_rfl
  · cases s.pending <;> simp

lemma update_extremes_mono (q : Public) (s : State q) (g : Vector q.d)
    (j : Fin (trimCount q)) : s.extremes j ≤ (updateState q s g).extremes j := by
  unfold updateState
  split_ifs
  · exact le_rfl
  · cases hp : s.pending with
    | none => exact le_rfl
    | some g₁ =>
      simp only
      by_cases hj : j = quantileIndex q s
      · subst j
        simp only [Function.update_self]
        exact le_max_left _ _
      · rw [Function.update_of_ne hj]

lemma update_quantile_mono (q : Public) (s : State q) (g : Vector q.d) :
    empiricalQuantile q s ≤ empiricalQuantile q (updateState q s g) := by
  exact (empiricalQuantile_le q s (quantileIndex q (updateState q s g))).trans
    (update_extremes_mono q s g _)

lemma update_variation_mono (q : Public) (s : State q) (g : Vector q.d) :
    s.variation ≤ (updateState q s g).variation := by
  unfold updateState
  split_ifs
  · exact le_rfl
  · cases hp : s.pending with
    | none => exact le_rfl
    | some g₁ =>
      simp only
      exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (sq_nonneg _))

lemma window_mono (q : Public) : Monotone (window q) := by
  intro m n hmn
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 16)
  apply add_le_add_right
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right hmn 1

lemma geometry_pos (q : Public) : 0 < geometry q := by
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)

lemma update_regularization_mono (q : Public) (hL : 0 ≤ q.L)
    (s : State q) (g : Vector q.d) :
    regularization q s ≤ regularization q (updateState q s g) := by
  have hD := (geometry_pos q).le
  have hc := update_completed_mono q s g
  have hw := window_mono q (Nat.add_le_add_right hc 1)
  have hwr : (window q (s.completed + 1) : ℝ) ≤
      window q ((updateState q s g).completed + 1) := by exact_mod_cast hw
  unfold regularization
  apply max_le_max
  · apply div_le_div_of_nonneg_right _ hD
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hwr (mul_nonneg (by norm_num) hL)) (Nat.cast_nonneg _)
  · apply max_le_max
    · apply div_le_div_of_nonneg_right _ hD
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (update_quantile_mono q s g) (by norm_num))
        (Nat.cast_nonneg _)
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (update_variation_mono q s g) hD)

lemma confidence_ge_two (q : Public) (hδ : 0 < q.δ) (hδ1 : q.δ < 1) :
    2 ≤ confidence q := by
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hl : 2 ≤ Real.log (16 : ℝ) := by rw [he]; norm_num at htwo; linarith
  apply hl.trans
  apply Real.log_le_log (by norm_num : (0 : ℝ) < 16)
  apply (le_div_iff₀ hδ).mpr
  linarith

lemma window_history_bound (q : Public) (hH : 2 ≤ confidence q) (n : ℕ) :
    window q (n + 1) ≤ preload q + n := by
  have hn : (0 : ℝ) < n + 2 := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hn (by norm_num : (0 : ℝ) < 16))
  rw [Real.log_div hn.ne' (by norm_num : (16 : ℝ) ≠ 0)] at hlog
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hsixteen : Real.log (16 : ℝ) ≤ 4 := by
    have he : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
      norm_num
    rw [he]
    linarith
  have hp : 64 * confidence q ≤ (preload q : ℝ) := Nat.le_ceil _
  unfold window
  apply Nat.ceil_le.mpr
  push_cast
  have he : ((n : ℝ) + 1 + 1) = n + 2 := by ring
  rw [he]
  linarith

lemma invariant_history_sufficient (q : Public) (hH : 2 ≤ confidence q)
    (n : ℕ) (s : State q) (hs : ExecutionInvariant q n s) (hn : preload q ≤ n) :
    window q (s.completed + 1) ≤ s.history.length := by
  rw [(invariant_history q n s hs hn).2]
  exact window_history_bound q hH s.completed

end OracleTemplate.AdaptiveHeavyTailSimplex
