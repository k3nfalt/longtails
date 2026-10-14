import LongTails.Proofs.AdaptiveEntropicErrors

open MeasureTheory
open scoped OracleTemplate.AdaptiveList RealInnerProductSpace

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def macroState (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) : State q :=
  (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
    (initialState q) ξ (preload q + n)).1

noncomputable def macroStream (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) : ℕ → Ω :=
  (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
    (initialState q) ξ (preload q + n)).2

noncomputable def macroReply (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) : Vector q.d :=
  clippedReply (clippingThreshold q (macroState q g ξ n)) (historyCenter q (macroState q g ξ n))
    (g (queryPoint q (macroState q g ξ n)) (macroStream q g ξ n 0))

lemma macroState_structure (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    (macroState q g ξ n).pending = none ∧ (macroState q g ξ n).warmup = 0 ∧
      (macroState q g ξ n).completed = n := by
  have h := blockTrace_structure q g ξ (preload q + n)
  exact ⟨h.1, by simpa [macroState] using h.2.2.1,
    by simpa [macroState] using h.2.2.2⟩

lemma macroState_cost (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    analysisCost q (macroState q g ξ n) = 2 := by
  rw [analysisCost, (macroState_structure q g ξ n).2.1]
  norm_num

lemma macroState_succ (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    macroState q g ξ (n + 1) =
      blockFromStream q g 2 (macroState q g ξ n) (macroStream q g ξ n) := by
  unfold macroState
  rw [show preload q + (n + 1) = (preload q + n) + 1 by omega,
    StochasticGeneralized.blockTrace_succ]
  change blockFromStream q g (analysisCost q (macroState q g ξ n))
    (macroState q g ξ n) (macroStream q g ξ n) = _
  rw [macroState_cost]
  rfl

lemma macroState_zero_fields (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) :
    (macroState q g ξ 0).sumGradient = 0 ∧ (macroState q g ξ 0).y = uniform q := by
  have h := blockTrace_warm_fields q g ξ (Nat.le_refl (preload q))
  exact ⟨h.1, h.2.1⟩

lemma macroState_pair_dynamics (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    (macroState q g ξ (n + 1)).sumGradient =
      (macroState q g ξ n).sumGradient + ((n : ℝ) + 1) • macroReply q g ξ n ∧
    (macroState q g ξ (n + 1)).y = mix n (macroState q g ξ n).y
      (softmax (by have := q.hd; omega) (-(1 / regularization q (macroState q g ξ n)) •
        ((macroState q g ξ n).sumGradient + ((n : ℝ) + 1) • macroReply q g ξ n))) := by
  have hs := macroState_structure q g ξ n
  have h := blockFromStream_pair_dynamics q g (macroState q g ξ n) (macroStream q g ξ n) hs.2.1 hs.1
  rw [← macroState_succ] at h
  simp only [hs.2.2, Nat.cast_add, Nat.cast_one] at h
  constructor
  · simpa only [macroReply, historyCenter, hs.2.2] using h.1
  · simpa only [macroReply, historyCenter, hs.2.2] using h.2.1

lemma macroState_sumGradient (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    (macroState q g ξ n).sumGradient =
      ∑ i ∈ Finset.range n, ((i : ℝ) + 1) • macroReply q g ξ i := by
  induction n with
  | zero => simpa only [Finset.range_zero, Finset.sum_empty] using (macroState_zero_fields q g ξ).1
  | succ n ih => rw [(macroState_pair_dynamics q g ξ n).1, Finset.sum_range_succ, ih]

lemma macroState_pre (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    predictableProx q (macroState q g ξ n) =
      softmax (by have := q.hd; omega) (-(1 / regularization q (macroState q g ξ n)) •
        ∑ i ∈ Finset.range n, ((i : ℝ) + 1) • macroReply q g ξ i) := by
  rw [predictableProx, macroState_sumGradient]

lemma macroState_query (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    queryPoint q (macroState q g ξ n) =
      mix n (macroState q g ξ n).y (predictableProx q (macroState q g ξ n)) := by
  rw [queryPoint, (macroState_structure q g ξ n).2.1]
  simp only [Nat.lt_irrefl, ite_false, (macroState_structure q g ξ n).2.2]

lemma accumulated_eq_macro_sum (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d)
    (X : (n : ℕ) → State q → (Fin n → Ω) → ℝ)
    (hw : ∀ s b, 0 < s.warmup → X (analysisCost q s) s b = 0) (T : ℕ) (ξ : ℕ → Ω) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g) X
      (preload q + T) (initialState q) ξ =
      ∑ n ∈ Finset.range T, X 2 (macroState q g ξ n) (fun i => macroStream q g ξ n i) := by
  rw [StochasticGeneralized.accumulated_eq_sum, Finset.sum_range_add]
  have hz : (∑ j ∈ Finset.range (preload q),
      X (analysisCost q (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ j).1)
        (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g) (initialState q) ξ j).1
        (fun i => (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
          (initialState q) ξ j).2 i)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    apply hw
    have hs := (blockTrace_structure q g ξ j).2.2.1
    have hj' := Finset.mem_range.mp hj
    omega
  rw [hz, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  change X (analysisCost q (macroState q g ξ n)) (macroState q g ξ n)
    (fun i => macroStream q g ξ n i) = _
  rw [macroState_cost]

lemma regularization_ge_smoothness (q : Public) (hL : 0 ≤ q.L) (hH : 2 ≤ confidence q)
    (s : State q) : 8 * q.L ≤ regularization q s := by
  have hD := geometry_pos q
  have hKD := geometry_le_trimCount q (by linarith : 0 ≤ confidence q)
  have hlog : 0 ≤ Real.log (((s.completed + 1 : ℕ) : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (s.completed + 1); linarith)
  have hk : 0 < window q (s.completed + 1) := by
    unfold window
    apply Nat.ceil_pos.mpr
    nlinarith
  have hkr : 1 ≤ (window q (s.completed + 1) : ℝ) := by exact_mod_cast hk
  have hK : 0 ≤ (trimCount q : ℝ) := Nat.cast_nonneg _
  have hwK : (trimCount q : ℝ) ≤ window q (s.completed + 1) * (trimCount q : ℝ) := by
    nlinarith
  have hbase : 128 * q.L ≤
      128 * q.L * window q (s.completed + 1) * trimCount q / geometry q := by
    apply (le_div_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left (hKD.trans hwK) (show 0 ≤ 128 * q.L by positivity)
    nlinarith only [h]
  exact (show 8 * q.L ≤ 128 * q.L by nlinarith).trans
    (hbase.trans (le_max_left _ _))

lemma macroState_y_succ (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (n : ℕ) :
    (macroState q g ξ (n + 1)).y = mix n (macroState q g ξ n).y
      (softmax (by have := q.hd; omega) (-(1 / regularization q (macroState q g ξ n)) •
        ∑ i ∈ Finset.range (n + 1), ((i : ℝ) + 1) • macroReply q g ξ i)) := by
  rw [(macroState_pair_dynamics q g ξ n).2, macroState_sumGradient, Finset.sum_range_succ]

lemma macroState_regularization_mono (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (ξ : ℕ → Ω) (hL : 0 ≤ q.L) :
    Monotone (fun n => regularization q (macroState q g ξ n)) := by
  intro m n hmn
  exact trace_regularization_mono q g hL ξ (Nat.add_le_add_left hmn (preload q))

lemma actual_accelerated_energy (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (g : simplex q.d → Ω → Vector q.d) (P : Measure Ω) (ξ : ℕ → Ω)
    {f : Vector q.d → ℝ} (hL : 0 < q.L) (hH : 2 ≤ confidence q)
    (hc : ConvexOn ℝ (simplex q.d) f)
    (hg : ∀ x ∈ simplex q.d, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ simplex q.d, ∀ y ∈ simplex q.d,
      dualNorm (gradient f x - gradient f y) ≤ q.L * oneNorm (x - y))
    (T : ℕ) (xstar : simplex q.d) :
    (T : ℝ) * (T + 1) / 2 * (f (macroState q g ξ T).y - f xstar) ≤
      regularization q (macroState q g ξ T) * entropy xstar +
        ∑ n ∈ Finset.range T,
          (-((n : ℝ) + 1) * ⟪oracleFluctuation q g P (macroState q g ξ n)
            (macroStream q g ξ n 0), (predictableProx q (macroState q g ξ n)).val - xstar.val⟫ +
          2 * ((n : ℝ) + 1) ^ 2 * dualNorm (oracleFluctuation q g P (macroState q g ξ n)
            (macroStream q g ξ n 0)) ^ 2 / regularization q (macroState q g ξ n) +
          2 * ((n : ℝ) + 1) * dualNorm (oracleBias q g (fun x => gradient f x) P
            (macroState q g ξ n))) := by
  let B := fun n => regularization q (macroState q g ξ n)
  let u := fun n => oracleFluctuation q g P (macroState q g ξ n) (macroStream q g ξ n 0)
  let b := fun n => oracleBias q g (fun x => gradient f x) P (macroState q g ξ n)
  let y := fun n => (macroState q g ξ n).y
  have he := accelerated_energy q hL.le hc hg hlip B (macroReply q g ξ) u b y
    (fun n => regularization_pos q hL hH _) (macroState_regularization_mono q g ξ hL.le)
    (fun n => regularization_ge_smoothness q hL.le hH _) T xstar
  dsimp only at he
  have hp (n : ℕ) : softmax (by have := q.hd; omega) (-(1 / B n) •
      ∑ i ∈ Finset.range n, ((i : ℝ) + 1) • macroReply q g ξ i) =
      predictableProx q (macroState q g ξ n) := (macroState_pre q g ξ n).symm
  have hy : ∀ n, y (n + 1) = mix n (y n)
      (softmax (by have := q.hd; omega) (-(1 / B n) •
        ∑ i ∈ Finset.range (n + 1), ((i : ℝ) + 1) • macroReply q g ξ i)) :=
    macroState_y_succ q g ξ
  have herr : ∀ n, gradient f (mix n (y n)
      (softmax (by have := q.hd; omega) (-(1 / B n) •
        ∑ i ∈ Finset.range n, ((i : ℝ) + 1) • macroReply q g ξ i))) - macroReply q g ξ n =
      -u n - b n := by
    intro n
    rw [hp n, ← macroState_query]
    exact oracle_error_identity q g (fun x => gradient f x) P (macroState q g ξ n)
      (macroStream q g ξ n 0)
  have h := he hy herr
  simpa only [hp] using h

end OracleTemplate.AdaptiveHeavyTailSimplex
