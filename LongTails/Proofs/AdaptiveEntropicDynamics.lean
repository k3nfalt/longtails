import LongTails.Proofs.AdaptiveEntropicProcess
import LongTails.Proofs.AdaptiveEntropicExecution
import LongTails.Proofs.AdaptiveEntropicEnergy

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma blockUpdate_observable_le (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (F : State q → ℝ)
    (hF : ∀ s v, F s ≤ F (updateState q s v))
    (n : ℕ) (s : State q) (b : Fin n → Ω) : F s ≤ F (blockUpdate q g n s b) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    exact (hF s _).trans (ih _ _)

lemma blockTrace_observable_mono (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (F : State q → ℝ)
    (hF : ∀ s v, F s ≤ F (updateState q s v)) (ξ : ℕ → Ω) :
    Monotone (fun n => F (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ n).1) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [StochasticGeneralized.blockTrace_succ]
  exact blockUpdate_observable_le q g F hF _ _ _

lemma trace_quantile_nonneg (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    0 ≤ empiricalQuantile q (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ n).1 := by
  have h := blockTrace_observable_mono q g (empiricalQuantile q) (update_quantile_mono q) ξ
    (show 0 ≤ n by omega)
  simpa [StochasticGeneralized.blockTrace_zero, empiricalQuantile, initialState] using h

lemma trace_variation_nonneg (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    0 ≤ (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ n).1.variation := by
  have h := blockTrace_observable_mono q g (fun s => s.variation) (update_variation_mono q) ξ
    (show 0 ≤ n by omega)
  simpa [StochasticGeneralized.blockTrace_zero, initialState] using h

lemma trace_regularization_mono (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (hL : 0 ≤ q.L) (ξ : ℕ → Ω) :
    Monotone (fun n => regularization q (StochasticGeneralized.blockTrace (analysisCost q)
      (blockUpdate q g) (initialState q) ξ n).1) :=
  blockTrace_observable_mono q g (regularization q) (update_regularization_mono q hL) ξ

lemma regularization_pos (q : Public) (hL : 0 < q.L) (hH : 2 ≤ confidence q) (s : State q) :
    0 < regularization q s := by
  have hg := geometry_pos q
  have hK : 0 < trimCount q := by unfold trimCount; omega
  have hlog : 0 ≤ Real.log (((s.completed + 1 : ℕ) : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (s.completed + 1); linarith)
  have hk : 0 < window q (s.completed + 1) := by
    unfold window
    apply Nat.ceil_pos.mpr
    nlinarith
  have ht : 0 < 128 * q.L * window q (s.completed + 1) * trimCount q / geometry q := by positivity
  exact ht.trans_le (le_max_left _ _)

lemma clippingThreshold_nonneg (q : Public) (hL : 0 ≤ q.L) (s : State q)
    (hQ : 0 ≤ empiricalQuantile q s) : 0 ≤ clippingThreshold q s := by
  unfold clippingThreshold driftRadius
  positivity

lemma blockFromStream_pair_dynamics (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (s : State q) (ξ : ℕ → Ω)
    (hw : s.warmup = 0) (hp : s.pending = none) :
    let c := medianCenter (s.history.take (window q (s.completed + 1)))
    let h := clippedReply (clippingThreshold q s) c (g (queryPoint q s) (ξ 0))
    let h' := clippedReply (clippingThreshold q s) c (g (queryPoint q s) (ξ 1))
    let S := s.sumGradient + ((s.completed + 1 : ℕ) : ℝ) • h
    let z := softmax (by have := q.hd; omega) (-(1 / regularization q s) • S)
    (blockFromStream q g 2 s ξ).sumGradient = S ∧
      (blockFromStream q g 2 s ξ).y = mix s.completed s.y z ∧
      (blockFromStream q g 2 s ξ).variation =
        s.variation + ((s.completed + 1 : ℕ) : ℝ) ^ 2 * dualNorm (h - h') ^ 2 := by
  dsimp only
  simp only [blockFromStream, blockUpdate, updateState, hw, Nat.lt_irrefl, ite_false, hp]
  refine ⟨rfl, rfl, ?_⟩
  simp [queryPoint, hw, predictableProx, regularization, empiricalQuantile, quantileIndex,
    clippingThreshold, driftRadius]

lemma blockTrace_warm_fields (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) {n : ℕ} (hn : n ≤ preload q) :
    let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ n).1
    s.sumGradient = 0 ∧ s.y = uniform q ∧ s.extremes = (fun _ => 0) ∧ s.variation = 0 := by
  induction n with
  | zero => simp [StochasticGeneralized.blockTrace_zero, initialState]
  | succ n ih =>
    have hprev := ih (show n ≤ preload q by omega)
    let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ n
    have hw : 0 < tr.1.warmup := by
      have hs := (blockTrace_structure q g ξ n).2.2.1
      change tr.1.warmup = preload q - n at hs
      omega
    rw [StochasticGeneralized.blockTrace_succ]
    change let s := blockFromStream q g (analysisCost q tr.1) tr.1 tr.2
      s.sumGradient = 0 ∧ s.y = uniform q ∧ s.extremes = (fun _ => 0) ∧ s.variation = 0
    simp only [analysisCost, ite_eq_left hw]
    change let s := blockFromStream q g 1 tr.1 tr.2
      s.sumGradient = 0 ∧ s.y = uniform q ∧ s.extremes = (fun _ => 0) ∧ s.variation = 0
    simpa only [blockFromStream, blockUpdate, updateState, ite_eq_left hw] using hprev

lemma weighted_clippingThreshold (q : Public) (s : State q) :
    ((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s =
      24 * q.L * window q (s.completed + 1) + empiricalQuantile q s := by
  unfold clippingThreshold driftRadius
  push_cast
  have ht : (s.completed : ℝ) + 1 ≠ 0 := by positivity
  field_simp

lemma weighted_clippingThreshold_le_regularization (q : Public) (hL : 0 ≤ q.L)
    (s : State q) :
    ((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s ≤
      regularization q s * geometry q / (4 * trimCount q) := by
  have hD := geometry_pos q
  have hKn : 0 < trimCount q := by unfold trimCount; omega
  have hK : 0 < (trimCount q : ℝ) := by exact_mod_cast hKn
  have hl : 128 * q.L * window q (s.completed + 1) * trimCount q / geometry q ≤
      regularization q s := le_max_left _ _
  have hq : 128 * empiricalQuantile q s * trimCount q / geometry q ≤
      regularization q s := (le_max_left _ _).trans (le_max_right _ _)
  have hl' := (div_le_iff₀ hD).mp hl
  have hq' := (div_le_iff₀ hD).mp hq
  have hB : 0 ≤ regularization q s :=
    (by positivity : 0 ≤ 128 * q.L * window q (s.completed + 1) *
      trimCount q / geometry q).trans hl
  rw [weighted_clippingThreshold]
  apply (le_div_iff₀ (show 0 < 4 * (trimCount q : ℝ) by positivity)).mpr
  nlinarith [mul_nonneg hB hD.le]

lemma variation_le_regularization_sq (q : Public)
    (s : State q) (hW : 0 ≤ s.variation) :
    s.variation ≤ geometry q * (regularization q s / 128) ^ 2 := by
  have hD := geometry_pos q
  have hs : 128 * Real.sqrt (s.variation / geometry q) ≤ regularization q s :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hn : 0 ≤ s.variation / geometry q := div_nonneg hW hD.le
  have ht : Real.sqrt (s.variation / geometry q) ≤ regularization q s / 128 := by linarith
  have hh := pow_le_pow_left₀ (Real.sqrt_nonneg _) ht 2
  rw [Real.sq_sqrt hn] at hh
  simpa only [mul_comm] using (div_le_iff₀ hD).mp hh

lemma geometry_le_trimCount (q : Public) (hH : 0 ≤ confidence q) :
    geometry q ≤ (trimCount q : ℝ) := by
  have hc : 64 * (geometry q + confidence q) ≤ (⌈64 * (geometry q + confidence q)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have ht : (⌈64 * (geometry q + confidence q)⌉₊ : ℝ) ≤ (trimCount q : ℝ) := by
    exact_mod_cast (le_max_right 1 _)
  have hD := (geometry_pos q).le
  linarith

lemma window_succ_le_twice (q : Public) (hH : 2 ≤ confidence q) (t : ℕ) :
    window q (t + 1) ≤ 2 * window q t := by
  have ha : 0 < (t : ℝ) + 1 := by positivity
  have hb : 0 < (t : ℝ) + 2 := by positivity
  have hr : ((t : ℝ) + 2) / ((t : ℝ) + 1) ≤ 2 := by
    apply (div_le_iff₀ ha).mpr
    linarith [Nat.cast_nonneg (α := ℝ) t]
  have hl := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at hl
  have hg : 0 ≤ Real.log ((t : ℝ) + 1) := Real.log_nonneg
    (by have := Nat.cast_nonneg (α := ℝ) t; linarith)
  have hc : 16 * (confidence q + Real.log ((t : ℝ) + 1)) ≤ (window q t : ℝ) := by
    exact Nat.le_ceil _
  unfold window
  apply Nat.ceil_le.mpr
  push_cast
  rw [show (t : ℝ) + 1 + 1 = (t : ℝ) + 2 by ring]
  change 16 * (confidence q + Real.log ((t : ℝ) + 2)) ≤ 2 * (window q t : ℝ)
  nlinarith

end OracleTemplate.AdaptiveHeavyTailSimplex
