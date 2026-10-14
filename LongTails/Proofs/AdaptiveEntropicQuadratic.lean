import LongTails.Proofs.AdaptiveEntropicVarianceConcentration

open MeasureTheory
open scoped OracleTemplate.AdaptiveList

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma accumulated_bounded_forward_tail {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (X : (n : ℕ) → S → (Fin n → Ω) → ℝ)
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hX : ∀ n, Measurable (Function.uncurry (X n)))
    {C : ℝ} (hC : 0 < C) (hb : ∀ n s b, 0 ≤ X n s b ∧ X n s b ≤ C)
    (N : ℕ) (s : S) (H : ℝ) :
    let m := fun n s (_ : Fin n → Ω) => ∫ b, X n s b ∂Measure.pi (fun _ : Fin n => P)
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 2 * StochasticGeneralized.accumulated cost next m N s ξ + 2 * C * H ≤
        StochasticGeneralized.accumulated cost next X N s ξ} ≤ ENNReal.ofReal (Real.exp (-H)) := by
  intro m
  let Y := fun n s b => X n s b / C
  have hY : ∀ n, Measurable (Function.uncurry (Y n)) := fun n => (hX n).div_const C
  have hunit : ∀ n s b, 0 ≤ Y n s b ∧ Y n s b ≤ 1 := by
    intro n s b
    exact ⟨div_nonneg (hb n s b).1 hC.le, (div_le_one₀ hC).mpr (hb n s b).2⟩
  have h := AdaptiveEntropicConcentration.accumulated_forward_tail P cost next Y hc hn hY hunit N s H
  have he : (fun n s (_ : Fin n → Ω) => ∫ b, Y n s b ∂Measure.pi (fun _ : Fin n => P)) =
      fun n s b => m n s b / C := by
    funext n s b
    exact integral_div C _
  rw [he] at h
  simp only [Y, accumulated_div_const] at h
  apply le_trans (measure_mono ?_) h
  intro ξ hξ
  change 2 * StochasticGeneralized.accumulated cost next m N s ξ + 2 * C * H ≤
    StochasticGeneralized.accumulated cost next X N s ξ at hξ
  change 2 * (_ / C) + 2 * H ≤ _ / C
  apply (le_div_iff₀ hC).mpr
  simp only [add_mul, mul_assoc, div_mul_cancel₀ _ hC.ne']
  nlinarith

lemma accumulated_bounded_inverse_tail {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (X : (n : ℕ) → S → (Fin n → Ω) → ℝ)
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hX : ∀ n, Measurable (Function.uncurry (X n)))
    {C : ℝ} (hC : 0 < C) (hb : ∀ n s b, 0 ≤ X n s b ∧ X n s b ≤ C)
    (N : ℕ) (s : S) (H : ℝ) :
    let m := fun n s (_ : Fin n → Ω) => ∫ b, X n s b ∂Measure.pi (fun _ : Fin n => P)
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 2 * StochasticGeneralized.accumulated cost next X N s ξ + 4 * C * H <
        StochasticGeneralized.accumulated cost next m N s ξ} ≤ ENNReal.ofReal (Real.exp (-H)) := by
  intro m
  let Y := fun n s b => X n s b / C
  have hY : ∀ n, Measurable (Function.uncurry (Y n)) := fun n => (hX n).div_const C
  have hunit : ∀ n s b, 0 ≤ Y n s b ∧ Y n s b ≤ 1 := by
    intro n s b
    exact ⟨div_nonneg (hb n s b).1 hC.le, (div_le_one₀ hC).mpr (hb n s b).2⟩
  have h := AdaptiveEntropicConcentration.accumulated_inverse_tail P cost next Y hc hn hY hunit N s H
  have he : (fun n s (_ : Fin n → Ω) => ∫ b, Y n s b ∂Measure.pi (fun _ : Fin n => P)) =
      fun n s b => m n s b / C := by
    funext n s b
    exact integral_div C _
  rw [he] at h
  simp only [Y, accumulated_div_const] at h
  apply le_trans (measure_mono ?_) h
  intro ξ hξ
  change 2 * StochasticGeneralized.accumulated cost next X N s ξ + 4 * C * H <
    StochasticGeneralized.accumulated cost next m N s ξ at hξ
  change 2 * (_ / C) + 4 * H < _ / C
  apply (lt_div_iff₀ hC).mpr
  simp only [add_mul, mul_assoc, div_mul_cancel₀ _ hC.ne']
  nlinarith

noncomputable def quadraticNoiseScore (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (P : Measure Ω) (n : ℕ) (s : State q) (b : Fin n → Ω) : ℝ :=
  pairScore (fun s a _ => ‖weightedNoise q g μ σ A T P s a‖ ^ 2 / regularization q s) n s b

lemma measurable_quadraticNoiseScore (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ A : ℝ) (T : ℕ) (P : Measure Ω) [SFinite P] (n : ℕ) :
    Measurable (Function.uncurry (quadraticNoiseScore q g μ σ A T P n)) := by
  have hZ := (measurable_weightedNoise q hg hμ σ A T P).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd) :
      Measurable (fun w : State q × (Ω × Ω) => (w.1, w.2.1)))
  exact measurable_pairScore ((hZ.norm.pow_const 2).div
    ((measurable_regularization q).comp measurable_fst)) n

lemma quadraticNoiseScore_range (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (T n : ℕ) (s : State q) (b : Fin n → Ω)
    (hL : 0 < q.L) (hH : 2 ≤ confidence q) :
    0 ≤ quadraticNoiseScore q g μ σ A T P n s b ∧
      quadraticNoiseScore q g μ σ A T P n s b ≤
        (24 * q.L * window q (T + 1) + A) * geometry q / trimCount q := by
  unfold quadraticNoiseScore pairScore
  split_ifs
  · exact ⟨div_nonneg (sq_nonneg _) (regularization_pos q hL hH s).le,
      weightedNoise_quadratic_range q hg hμ σ hA T s _ hL hH⟩
  · constructor
    · exact le_rfl
    · have hD := (geometry_pos q).le
      have hK : 0 ≤ (trimCount q : ℝ) := Nat.cast_nonneg _
      exact div_nonneg (mul_nonneg (by positivity) hD) hK

lemma pairedVariation_div_range (q : Public) {Ω : Type*}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (T n : ℕ) (s : State q) (b : Fin n → Ω)
    (hL : 0 < q.L) (hH : 2 ≤ confidence q) :
    0 ≤ pairedVariation q g μ σ A T n s b / regularization q s ∧
      pairedVariation q g μ σ A T n s b / regularization q s ≤
        (24 * q.L * window q (T + 1) + A) * geometry q / trimCount q := by
  classical
  have hB := regularization_pos q hL hH s
  have hD := geometry_pos q
  have hKn : 0 < trimCount q := by unfold trimCount; omega
  have hK : 0 < (trimCount q : ℝ) := by exact_mod_cast hKn
  refine ⟨div_nonneg (pairedVariation_range q g μ σ hA hL.le T n s b).1 hB.le, ?_⟩
  by_cases hs : boundedActive q μ σ A T s
  · unfold pairedVariation pairScore
    split_ifs
    · have hc : 0 ≤ ((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s :=
        mul_nonneg (Nat.cast_nonneg _) (clippingThreshold_nonneg q hL.le s hs.1.2.1)
      have hu := weighted_clippingThreshold_le_cap q μ σ A T s hL.le hs
      have h1 := weightedResidual_local_range q μ σ A T s
        (g (queryPoint q s) (b (Fin.cast ‹n = 2›.symm 0))) hL.le hs
      have h2 := weightedResidual_local_range q μ σ A T s
        (g (queryPoint q s) (b (Fin.cast ‹n = 2›.symm 1))) hL.le hs
      have hd : ‖weightedResidual q μ σ A T s (g (queryPoint q s) (b (Fin.cast ‹n = 2›.symm 0))) -
          weightedResidual q μ σ A T s (g (queryPoint q s) (b (Fin.cast ‹n = 2›.symm 1)))‖ ≤
          2 * (((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s) :=
        (norm_sub_le _ _).trans (by linarith)
      have hp := pow_le_pow_left₀ (norm_nonneg _) hd 2
      exact normalized_quadratic_range hc hu hB hD.le hK (by nlinarith)
        (weighted_clippingThreshold_le_regularization q hL.le s)
    · simp only [zero_div]
      exact div_nonneg (mul_nonneg (by positivity) hD.le) hK.le
  · rw [pairedVariation_inactive q g μ σ A T n s b hs, zero_div]
    exact div_nonneg (mul_nonneg (by positivity) hD.le) hK.le

lemma quadraticNoiseScore_mean_le_pair (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (T n : ℕ) (s : State q)
    (hL : 0 < q.L) (hH : 2 ≤ confidence q) :
    (∫ b, quadraticNoiseScore q g μ σ A T P n s b ∂Measure.pi (fun _ : Fin n => P)) ≤
      (∫ b, pairedVariation q g μ σ A T n s b ∂Measure.pi (fun _ : Fin n => P)) /
        regularization q s := by
  by_cases hn : n = 2
  · subst n
    unfold quadraticNoiseScore
    rw [integral_pairScore]
    change (∫ w : Ω × Ω, (fun ω => ‖weightedNoise q g μ σ A T P s ω‖ ^ 2 /
      regularization q s) w.1 ∂P.prod P) ≤ _
    rw [integral_fun_fst (μ := P) (ν := P)
      (fun ω : Ω => ‖weightedNoise q g μ σ A T P s ω‖ ^ 2 / regularization q s)]
    simp only [probReal_univ, one_smul]
    rw [integral_div]
    exact div_le_div_of_nonneg_right
      (weightedResidual_centered_second_le_pair (P := P) q hμ hg σ hA hL.le T s)
      (regularization_pos q hL hH s).le
  · simp only [quadraticNoiseScore, pairedVariation, pairScore, dite_eq_right hn, integral_zero,
      zero_div, le_refl]

lemma cap_radius_pos (q : Public) {A : ℝ} (hA : 0 ≤ A)
    (hL : 0 < q.L) (hH : 2 ≤ confidence q) (T : ℕ) :
    0 < 24 * q.L * window q (T + 1) + A := by
  have hk : 0 < window q (T + 1) := by
    unfold window
    apply Nat.ceil_pos.mpr
    have hl : 0 ≤ Real.log (((T + 1 : ℕ) : ℝ) + 1) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (T + 1); linarith)
    nlinarith
  positivity

noncomputable def weightedPairScore (q : Public) {Ω : Type*}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T n : ℕ) (s : State q) (b : Fin n → Ω) : ℝ :=
  pairedVariation q g μ σ A T n s b / regularization q s

lemma measurable_weightedPairScore (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ A : ℝ) (T n : ℕ) : Measurable (Function.uncurry (weightedPairScore q g μ σ A T n)) :=
  (measurable_pairedVariation q hg hμ σ A T n).div
    ((measurable_regularization q).comp measurable_fst)

lemma quadratic_compensator_le_pair (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (T N : ℕ) (ξ : ℕ → Ω)
    (hL : 0 < q.L) (hH : 2 ≤ confidence q) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (fun n s (_ : Fin n → Ω) => ∫ b, quadraticNoiseScore q g μ σ A T P n s b
        ∂Measure.pi (fun _ : Fin n => P)) N (initialState q) ξ ≤
      StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
        (fun n s (_ : Fin n → Ω) => ∫ b, weightedPairScore q g μ σ A T n s b
          ∂Measure.pi (fun _ : Fin n => P)) N (initialState q) ξ := by
  rw [StochasticGeneralized.accumulated_eq_sum, StochasticGeneralized.accumulated_eq_sum]
  apply Finset.sum_le_sum
  intro j hj
  simp only [weightedPairScore, integral_div]
  exact quadraticNoiseScore_mean_le_pair q hg hμ σ hA T _ _ hL hH

lemma quadratic_energy_tail (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (T N : ℕ)
    (hL : 0 < q.L) (hH : 2 ≤ confidence q) (H : ℝ) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 8 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
        (weightedPairScore q g μ σ A T) N (initialState q) ξ +
          20 * ((24 * q.L * window q (T + 1) + A) * geometry q / trimCount q) * H <
        2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
          (quadraticNoiseScore q g μ σ A T P) N (initialState q) ξ} ≤
      2 * ENNReal.ofReal (Real.exp (-H)) := by
  let C := (24 * q.L * window q (T + 1) + A) * geometry q / trimCount q
  have hD := geometry_pos q
  have hKn : 0 < trimCount q := by unfold trimCount; omega
  have hK : 0 < (trimCount q : ℝ) := by exact_mod_cast hKn
  have hC : 0 < C := by dsimp [C]; exact div_pos (mul_pos (cap_radius_pos q hA hL hH T) hD) hK
  let X := quadraticNoiseScore q g μ σ A T P
  let Y := weightedPairScore q g μ σ A T
  let mX := fun n s (_ : Fin n → Ω) => ∫ b, X n s b ∂Measure.pi (fun _ : Fin n => P)
  let mY := fun n s (_ : Fin n → Ω) => ∫ b, Y n s b ∂Measure.pi (fun _ : Fin n => P)
  let E1 := {ξ | 2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
    mX N (initialState q) ξ + 2 * C * H ≤
      StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g) X N (initialState q) ξ}
  let E2 := {ξ | 2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
    Y N (initialState q) ξ + 4 * C * H <
      StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g) mY N (initialState q) ξ}
  have h1 : (Measure.infinitePi fun _ : ℕ => P) E1 ≤ ENNReal.ofReal (Real.exp (-H)) :=
    accumulated_bounded_forward_tail P (analysisCost q) (blockUpdate q g) X
      (measurable_analysisCost q) (measurable_blockUpdate q hg)
      (measurable_quadraticNoiseScore q hg hμ σ A T P) hC
      (fun n s b => quadraticNoiseScore_range q hg hμ σ hA T n s b hL hH) N (initialState q) H
  have h2 : (Measure.infinitePi fun _ : ℕ => P) E2 ≤ ENNReal.ofReal (Real.exp (-H)) :=
    accumulated_bounded_inverse_tail P (analysisCost q) (blockUpdate q g) Y
      (measurable_analysisCost q) (measurable_blockUpdate q hg)
      (measurable_weightedPairScore q hg hμ σ A T) hC
      (fun n s b => pairedVariation_div_range q g μ σ hA T n s b hL hH) N (initialState q) H
  have hset : {ξ | 8 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      Y N (initialState q) ξ + 20 * C * H <
        2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g) X N (initialState q) ξ} ⊆
      E1 ∪ E2 := by
    intro ξ hξ
    by_cases he1 : ξ ∈ E1
    · exact Or.inl he1
    · apply Or.inr
      have hmean := quadratic_compensator_le_pair q P hg hμ σ hA T N ξ hL hH
      change ¬ (2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
        mX N (initialState q) ξ + 2 * C * H ≤
          StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g) X N (initialState q) ξ) at he1
      change StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g) mX N
        (initialState q) ξ ≤ StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
          mY N (initialState q) ξ at hmean
      change 2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g) Y N
        (initialState q) ξ + 4 * C * H <
          StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g) mY N (initialState q) ξ
      have hf := lt_of_not_ge he1
      change 8 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g) Y N
        (initialState q) ξ + 20 * C * H <
          2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g) X N (initialState q) ξ at hξ
      linarith
  have hp := (measure_mono hset).trans ((measure_union_le E1 E2).trans (add_le_add h1 h2))
  simpa only [two_mul] using hp

lemma pairedVariation_le_regularization_sq (q : Public) {Ω : Type*}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T n : ℕ) (s : State q) (b : Fin n → Ω)
    (hL : 0 < q.L) (hH : 2 ≤ confidence q) :
    pairedVariation q g μ σ A T n s b ≤ geometry q * (regularization q s) ^ 2 / 4 := by
  classical
  have hD := (geometry_pos q).le
  have hK : 1 ≤ (trimCount q : ℝ) := by
    unfold trimCount
    exact_mod_cast (le_max_left 1 _)
  have hDK := geometry_le_trimCount q (by linarith : 0 ≤ confidence q)
  unfold pairedVariation pairScore
  split_ifs with hn
  · by_cases hs : boundedActive q μ σ A T s
    · have hc : 0 ≤ ((s.completed + 1 : ℕ) : ℝ) * clippingThreshold q s :=
        mul_nonneg (Nat.cast_nonneg _) (clippingThreshold_nonneg q hL.le s hs.1.2.1)
      exact (weightedResidual_pair_local_range q μ σ A T s _ _ hL.le hs).trans
        (clipped_increment_le_regularization_sq hc hD hK hDK
          (weighted_clippingThreshold_le_regularization q hL.le s))
    · simp only [weightedResidual, ite_eq_right hs, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      positivity
  · positivity

lemma pairedVariation_prefix_regularization (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) {A : ℝ} (T n : ℕ) (ξ : ℕ → Ω)
    (hL : 0 < q.L) (hH : 2 ≤ confidence q) :
    (∑ j ∈ Finset.range (n + 1),
      let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g) (initialState q) ξ j
      pairedVariation q g μ σ A T (analysisCost q tr.1) tr.1 (fun i => tr.2 i)) ≤
      geometry q * (regularization q (StochasticGeneralized.blockTrace (analysisCost q)
        (blockUpdate q g) (initialState q) ξ n).1) ^ 2 := by
  rw [Finset.sum_range_succ]
  let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g) (initialState q) ξ n).1
  have hp := accumulated_pairedVariation_le_actual q g μ σ A T n ξ
  rw [StochasticGeneralized.accumulated_eq_sum] at hp
  have hc := pairedVariation_le_regularization_sq q g μ σ A T (analysisCost q s) s
    (fun i => (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g) (initialState q) ξ n).2 i)
    hL hH
  have hw := variation_le_regularization_sq q s (trace_variation_nonneg q g ξ n)
  have hd := mul_nonneg (geometry_pos q).le (sq_nonneg (regularization q s))
  change _ ≤ geometry q * (regularization q s) ^ 2
  change (∑ j ∈ Finset.range n,
    let tr := StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g) (initialState q) ξ j
    pairedVariation q g μ σ A T (analysisCost q tr.1) tr.1 (fun i => tr.2 i)) ≤ s.variation at hp
  nlinarith

lemma weightedPair_accumulated_sqrt_bound (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (T N : ℕ) (ξ : ℕ → Ω)
    (hL : 0 < q.L) (hH : 2 ≤ confidence q) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (weightedPairScore q g μ σ A T) N (initialState q) ξ ≤
      2 * Real.sqrt (geometry q) * Real.sqrt (StochasticGeneralized.accumulated
        (analysisCost q) (blockUpdate q g) (pairedVariation q g μ σ A T) N (initialState q) ξ) := by
  let tr := fun n => StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g) (initialState q) ξ n
  let a := fun n => pairedVariation q g μ σ A T (analysisCost q (tr n).1) (tr n).1 (fun i => (tr n).2 i)
  let b := fun n => regularization q (tr n).1
  have ha : ∀ n, 0 ≤ a n := fun n =>
    (pairedVariation_range q g μ σ hA hL.le T _ _ _).1
  have hb : ∀ n, 0 < b n := fun n => regularization_pos q hL hH _
  have hbound : ∀ n, (∑ i ∈ Finset.range (n + 1), a i) ≤ geometry q * (b n) ^ 2 :=
    fun n => pairedVariation_prefix_regularization q g μ σ T n ξ hL hH
  rw [StochasticGeneralized.accumulated_eq_sum, StochasticGeneralized.accumulated_eq_sum]
  exact weighted_sum_sqrt_bound a b (geometry_pos q).le ha hb hbound N

lemma weightedPair_accumulated_actual_bound (q : Public) {Ω : Type}
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (T N : ℕ) (ξ : ℕ → Ω)
    (hL : 0 < q.L) (hH : 2 ≤ confidence q) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (weightedPairScore q g μ σ A T) N (initialState q) ξ ≤
      2 * Real.sqrt (geometry q) * Real.sqrt ((StochasticGeneralized.blockTrace (analysisCost q)
        (blockUpdate q g) (initialState q) ξ N).1.variation) := by
  exact (weightedPair_accumulated_sqrt_bound q g μ σ hA T N ξ hL hH).trans
    (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (accumulated_pairedVariation_le_actual q g μ σ A T N ξ)) (by positivity))

lemma quadratic_energy_actual_tail (q : Public) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (T N : ℕ)
    (hL : 0 < q.L) (hH : 2 ≤ confidence q) (H : ℝ) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 16 * Real.sqrt (geometry q) * Real.sqrt ((StochasticGeneralized.blockTrace
        (analysisCost q) (blockUpdate q g) (initialState q) ξ N).1.variation) +
          20 * ((24 * q.L * window q (T + 1) + A) * geometry q / trimCount q) * H <
        2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
          (quadraticNoiseScore q g μ σ A T P) N (initialState q) ξ} ≤
      2 * ENNReal.ofReal (Real.exp (-H)) := by
  apply le_trans (measure_mono ?_) (quadratic_energy_tail q P hg hμ σ hA T N hL hH H)
  intro ξ hξ
  have hb := weightedPair_accumulated_actual_bound q g μ σ hA T N ξ hL hH
  change 8 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
    (weightedPairScore q g μ σ A T) N (initialState q) ξ +
      20 * ((24 * q.L * window q (T + 1) + A) * geometry q / trimCount q) * H <
        2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
          (quadraticNoiseScore q g μ σ A T P) N (initialState q) ξ
  change 16 * Real.sqrt (geometry q) * Real.sqrt ((StochasticGeneralized.blockTrace
    (analysisCost q) (blockUpdate q g) (initialState q) ξ N).1.variation) +
      20 * ((24 * q.L * window q (T + 1) + A) * geometry q / trimCount q) * H <
        2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
          (quadraticNoiseScore q g μ σ A T P) N (initialState q) ξ at hξ
  linarith

end OracleTemplate.AdaptiveHeavyTailSimplex
