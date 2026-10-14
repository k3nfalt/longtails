import LongTails.Proofs.AdaptiveEntropicMacro

open MeasureTheory
open scoped OracleTemplate.AdaptiveList RealInnerProductSpace

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma pairScore_warm_cost (q : Public) {Ω : Type} (X : State q → Ω → Ω → ℝ)
    (s : State q) (b : Fin (analysisCost q s) → Ω) (hw : 0 < s.warmup) :
    pairScore X (analysisCost q s) s b = 0 := by
  have hc : analysisCost q s = 1 := by simp [analysisCost, hw]
  unfold pairScore
  have hn : analysisCost q s ≠ 2 := by omega
  rw [dite_eq_right hn]

lemma linear_score_macro_sum (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} (g : simplex q.d → Ω → Vector q.d)
    (μ : simplex q.d → Vector q.d) (σ A : ℝ) (T : ℕ) (xstar : simplex q.d)
    (ξ : ℕ → Ω)
    (hc : ∀ j < preload q + T,
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      s.warmup = 0 → centerGood q μ σ s)
    (hQ : empiricalQuantile q (macroState q g ξ T) ≤ A) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (linearNoiseScore q g μ σ A T P xstar) (preload q + T) (initialState q) ξ =
      ∑ n ∈ Finset.range T, -((n : ℝ) + 1) *
        ⟪oracleFluctuation q g P (macroState q g ξ n) (macroStream q g ξ n 0),
          (predictableProx q (macroState q g ξ n)).val - xstar.val⟫ := by
  rw [accumulated_linearNoiseScore_eq_fluctuation q g μ σ A T xstar ξ hc hQ]
  rw [accumulated_eq_macro_sum q g _ (pairScore_warm_cost q _) T ξ]
  apply Finset.sum_congr rfl
  intro n hn
  change -(((macroState q g ξ n).completed + 1 : ℕ) : ℝ) *
      ⟪oracleFluctuation q g P (macroState q g ξ n) (macroStream q g ξ n 0),
        (predictableProx q (macroState q g ξ n)).val - xstar.val⟫ = _
  rw [(macroState_structure q g ξ n).2.2, Nat.cast_add, Nat.cast_one]

lemma quadratic_score_macro_sum (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} (g : simplex q.d → Ω → Vector q.d)
    (μ : simplex q.d → Vector q.d) (σ A : ℝ) (T : ℕ) (ξ : ℕ → Ω)
    (hc : ∀ j < preload q + T,
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      s.warmup = 0 → centerGood q μ σ s)
    (hQ : empiricalQuantile q (macroState q g ξ T) ≤ A) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (quadraticNoiseScore q g μ σ A T P) (preload q + T) (initialState q) ξ =
      ∑ n ∈ Finset.range T, ((n : ℝ) + 1) ^ 2 *
        dualNorm (oracleFluctuation q g P (macroState q g ξ n) (macroStream q g ξ n 0)) ^ 2 /
          regularization q (macroState q g ξ n) := by
  rw [accumulated_quadraticNoiseScore_eq_fluctuation q g μ σ A T ξ hc hQ]
  rw [accumulated_eq_macro_sum q g _ (pairScore_warm_cost q _) T ξ]
  apply Finset.sum_congr rfl
  intro n hn
  change (((macroState q g ξ n).completed + 1 : ℕ) : ℝ) ^ 2 *
      dualNorm (oracleFluctuation q g P (macroState q g ξ n) (macroStream q g ξ n 0)) ^ 2 /
        regularization q (macroState q g ξ n) = _
  rw [(macroState_structure q g ξ n).2.2, Nat.cast_add, Nat.cast_one]

lemma cappedBias_compensator_macro_sum (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ A : ℝ) (T : ℕ) (ξ : ℕ → Ω) :
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (fun n s (_ : Fin n → Ω) => ∫ b, firstScore (cappedBiasScore q g μ σ A) n s b
        ∂Measure.pi (fun _ : Fin n => P)) (preload q + T) (initialState q) ξ =
      ∑ n ∈ Finset.range T, ∫ ω, cappedBiasScore q g μ σ A (macroState q g ξ n) ω ∂P := by
  rw [accumulated_eq_macro_sum q g _ ?_ T ξ]
  · apply Finset.sum_congr rfl
    intro n hn
    exact integral_firstScore (macroState q g ξ n)
      ((measurable_cappedBiasScore q hg hμ σ A).comp measurable_prodMk_left) (by norm_num : 0 < 2)
  · intro s b hs
    have hbad : ¬cappedActive q μ σ A s := by
      intro hc
      have hw := hc.1.1
      omega
    have hcost : analysisCost q s = 1 := by simp [analysisCost, hs]
    rw [hcost]
    simp [firstScore, cappedBiasScore, hbad]

lemma bias_macro_sum_bound (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ A p : ℝ} (hσ : 0 ≤ σ) (hA : 0 < A) (hL : 0 ≤ q.L)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (hgi : ∀ x, Integrable (g x) P) (hgu : ∀ x, (∫ ω, g x ω ∂P) = μ x)
    (T : ℕ) (ξ : ℕ → Ω)
    (hc : ∀ j < preload q + T,
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      s.warmup = 0 → centerGood q μ σ s)
    (hQ : empiricalQuantile q (macroState q g ξ T) ≤ A) :
    (∑ n ∈ Finset.range T, ((n : ℝ) + 1) * dualNorm (oracleBias q g μ P (macroState q g ξ n))) ≤
      A * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
        (fun n s (_ : Fin n → Ω) => ∫ b, firstScore (cappedBiasScore q g μ σ A) n s b
          ∂Measure.pi (fun _ : Fin n => P)) (preload q + T) (initialState q) ξ +
      130 * (T : ℝ) ^ (p + 1) * σ ^ p / A ^ (p - 1) := by
  rw [cappedBias_compensator_macro_sum q hg hμ σ A T ξ]
  have hsum : (∑ n ∈ Finset.range T, ((n : ℝ) + 1) *
      dualNorm (oracleBias q g μ P (macroState q g ξ n))) ≤
      ∑ n ∈ Finset.range T,
        (A * (∫ ω, cappedBiasScore q g μ σ A (macroState q g ξ n) ω ∂P) +
        130 * (T : ℝ) ^ p * σ ^ p / A ^ (p - 1)) := by
    apply Finset.sum_le_sum
    intro n hn
    have hnT := Finset.mem_range.mp hn
    have hact := boundedActive_prefix q g μ σ A T ξ hc hQ (preload q + n) (by omega)
      (macroState_structure q g ξ n).2.1
    have hb := weighted_bias_le_capped_tail q hg hμ hσ hA hL hp hp2 hi hm
      (macroState q g ξ n) hact.1 (hgi _) (hgu _)
    rw [(macroState_structure q g ξ n).2.2, Nat.cast_add, Nat.cast_one] at hb
    have ht : (n : ℝ) + 1 ≤ T := by exact_mod_cast (show n + 1 ≤ T by omega)
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (n : ℝ) + 1) ht (by linarith : 0 ≤ p)
    have hnoise : 130 * ((n : ℝ) + 1) ^ p * σ ^ p / A ^ (p - 1) ≤
        130 * (T : ℝ) ^ p * σ ^ p / A ^ (p - 1) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num))
          (Real.rpow_nonneg hσ p)) (Real.rpow_nonneg hA.le (p - 1))
    exact hb.trans (add_le_add le_rfl hnoise)
  calc
    _ ≤ _ := hsum
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hpT : (T : ℝ) ^ (p + 1) = (T : ℝ) ^ p * (T : ℝ) := by
        rw [Real.rpow_add_of_nonneg (Nat.cast_nonneg T) (by linarith : 0 ≤ p) (by norm_num : (0 : ℝ) ≤ 1), Real.rpow_one]
      rw [hpT]
      ring

lemma regularization_entropy_bound (q : Public) (hH : 0 ≤ confidence q)
    (s : State q) (xstar : simplex q.d) {U : ℝ} (hU : 0 ≤ U)
    (hLw : q.L * window q (s.completed + 1) ≤ U)
    (hQ : empiricalQuantile q s ≤ U)
    (hW : s.variation ≤ (trimCount q : ℝ) * U ^ 2) :
    regularization q s * entropy xstar ≤ 128 * (trimCount q : ℝ) * U := by
  have hD := geometry_pos q
  have hKD := geometry_le_trimCount q hH
  have hK : 0 ≤ (trimCount q : ℝ) := Nat.cast_nonneg _
  have hWD : s.variation * geometry q ≤ (trimCount q : ℝ) ^ 2 * U ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hW hD.le
    have h2 := mul_le_mul_of_nonneg_left hKD (mul_nonneg hK (sq_nonneg U))
    nlinarith only [h1, h2]
  have hr : Real.sqrt (s.variation / geometry q) ≤ (trimCount q : ℝ) * U / geometry q := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [div_pow]
      apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
      have he : s.variation / geometry q * (geometry q) ^ 2 = s.variation * geometry q := by
        field_simp
      rw [he, mul_pow]
      exact hWD
  have hb : 128 * q.L * window q (s.completed + 1) * trimCount q / geometry q ≤
      128 * (trimCount q : ℝ) * U / geometry q := by
    apply div_le_div_of_nonneg_right _ hD.le
    have h := mul_le_mul_of_nonneg_left hLw (show 0 ≤ 128 * (trimCount q : ℝ) by positivity)
    nlinarith only [h]
  have hq : 128 * empiricalQuantile q s * trimCount q / geometry q ≤
      128 * (trimCount q : ℝ) * U / geometry q := by
    apply div_le_div_of_nonneg_right _ hD.le
    have h := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 128 * (trimCount q : ℝ) by positivity)
    nlinarith only [h]
  have hw : 128 * Real.sqrt (s.variation / geometry q) ≤
      128 * (trimCount q : ℝ) * U / geometry q := by
    simpa only [mul_div_assoc, mul_assoc] using mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 128)
  have hB : regularization q s ≤ 128 * (trimCount q : ℝ) * U / geometry q :=
    max_le hb (max_le hq hw)
  have hBn : 0 ≤ regularization q s :=
    (show 0 ≤ 128 * Real.sqrt (s.variation / geometry q) by positivity).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have he : entropy xstar ≤ geometry q := (entropy_upper xstar).trans (le_max_right _ _)
  calc
    _ ≤ regularization q s * geometry q := mul_le_mul_of_nonneg_left he hBn
    _ ≤ (128 * (trimCount q : ℝ) * U / geometry q) * geometry q :=
      mul_le_mul_of_nonneg_right hB hD.le
    _ = _ := div_mul_cancel₀ _ hD.ne'

lemma actual_energy_from_scores (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {f : Vector q.d → ℝ} (hL : 0 < q.L) (hH : 2 ≤ confidence q)
    (hf : ConvexOn ℝ (simplex q.d) f)
    (hgrad : ∀ x ∈ simplex q.d, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ simplex q.d, ∀ y ∈ simplex q.d,
      dualNorm (gradient f x - gradient f y) ≤ q.L * oneNorm (x - y))
    (hμ : Measurable (fun x : simplex q.d => gradient f x))
    {σ A p : ℝ} (hσ : 0 ≤ σ) (hA : 0 < A) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - gradient f x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - gradient f x) ^ p ∂P) ≤ σ ^ p)
    (hgi : ∀ x, Integrable (g x) P) (hgu : ∀ x, (∫ ω, g x ω ∂P) = gradient f x)
    (T : ℕ) (xstar : simplex q.d) (ξ : ℕ → Ω)
    (hc : ∀ j < preload q + T,
      let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
        (initialState q) ξ j).1
      s.warmup = 0 → centerGood q (fun x => gradient f x) σ s)
    (hQ : empiricalQuantile q (macroState q g ξ T) ≤ A) :
    (T : ℝ) * (T + 1) / 2 * (f (macroState q g ξ T).y - f xstar) ≤
      regularization q (macroState q g ξ T) * entropy xstar +
      StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
        (linearNoiseScore q g (fun x => gradient f x) σ A T P xstar)
        (preload q + T) (initialState q) ξ +
      2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
        (quadraticNoiseScore q g (fun x => gradient f x) σ A T P)
        (preload q + T) (initialState q) ξ +
      2 * (A * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
        (fun n s (_ : Fin n → Ω) => ∫ b, firstScore (cappedBiasScore q g
          (fun x => gradient f x) σ A) n s b ∂Measure.pi (fun _ : Fin n => P))
        (preload q + T) (initialState q) ξ +
        130 * (T : ℝ) ^ (p + 1) * σ ^ p / A ^ (p - 1)) := by
  have he := actual_accelerated_energy q g P ξ hL hH hf hgrad hlip T xstar
  have hlin := linear_score_macro_sum (P := P) q g (fun x => gradient f x) σ A T xstar ξ hc hQ
  have hquad := quadratic_score_macro_sum (P := P) q g (fun x => gradient f x) σ A T ξ hc hQ
  have hb := bias_macro_sum_bound q hg hμ hσ hA hL.le hp hp2 hi hm hgi hgu T ξ hc hQ
  have hqs : (∑ n ∈ Finset.range T, 2 * ((n : ℝ) + 1) ^ 2 *
      dualNorm (oracleFluctuation q g P (macroState q g ξ n) (macroStream q g ξ n 0)) ^ 2 /
        regularization q (macroState q g ξ n)) =
      2 * (∑ n ∈ Finset.range T, ((n : ℝ) + 1) ^ 2 *
      dualNorm (oracleFluctuation q g P (macroState q g ξ n) (macroStream q g ξ n 0)) ^ 2 /
        regularization q (macroState q g ξ n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hbs : (∑ n ∈ Finset.range T, 2 * ((n : ℝ) + 1) *
      dualNorm (oracleBias q g (fun x => gradient f x) P (macroState q g ξ n))) =
      2 * (∑ n ∈ Finset.range T, ((n : ℝ) + 1) *
      dualNorm (oracleBias q g (fun x => gradient f x) P (macroState q g ξ n))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hqs, hbs, ← hlin, ← hquad] at he
  linarith only [he, hb]

lemma energy_envelope {E B X Y C R A U K D H V W : ℝ}
    (hK : 0 < K) (hU : 0 < U) (hA : 0 ≤ A) (hAU : A ≤ U)
    (hD : 0 ≤ D) (hDK : D ≤ K) (hH : 0 ≤ H) (hHK : H ≤ K / 64)
    (hV : V ≤ K * U ^ 2 / 256) (hW : W ≤ K * U ^ 2)
    (hB : B ≤ 128 * K * U) (hX : X ≤ 4 * U * H + V / U)
    (hY : Y ≤ 16 * Real.sqrt D * Real.sqrt W + 20 * U * D * H / K)
    (hC : C ≤ 2 * K + 4 * H) (hR : R ≤ K * A / 31)
    (hE : E ≤ B + X + Y + 2 * (A * C + R)) : E ≤ 170 * K * U := by
  have hDH : D * H ≤ K ^ 2 / 64 := by
    have h1 := mul_le_mul_of_nonneg_right hDK hH
    have h2 := mul_le_mul_of_nonneg_left hHK hK.le
    nlinarith only [h1, h2]
  have hroot : Real.sqrt D * Real.sqrt W ≤ K * U := by
    rw [← Real.sqrt_mul hD]
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have h1 := mul_le_mul_of_nonneg_left hW hD
      have h2 := mul_le_mul_of_nonneg_right hDK (mul_nonneg hK.le (sq_nonneg U))
      nlinarith only [h1, h2]
  have hnoise : V / U ≤ K * U / 256 := by
    apply (div_le_iff₀ hU).mpr
    nlinarith only [hV]
  have hlin : X ≤ 8 * K * U := by
    have h := mul_le_mul_of_nonneg_left hHK (show 0 ≤ 4 * U by positivity)
    nlinarith only [hX, hnoise, h, mul_pos hK hU]
  have hquadterm : 20 * U * D * H / K ≤ 20 * K * U / 64 := by
    apply (div_le_iff₀ hK).mpr
    have h := mul_le_mul_of_nonneg_left hDH (show 0 ≤ 20 * U by positivity)
    nlinarith only [h]
  have hquad : Y ≤ 26 * K * U := by
    have h := mul_le_mul_of_nonneg_left hroot (by norm_num : (0 : ℝ) ≤ 16)
    nlinarith only [hY, hquadterm, h, mul_pos hK hU]
  have hcomp : C ≤ 3 * K := by linarith only [hC, hHK, hK]
  have hAC : A * C ≤ 3 * K * U := by
    have h1 := mul_le_mul_of_nonneg_left hcomp hA
    have h2 := mul_le_mul_of_nonneg_left hAU (show 0 ≤ 3 * K by positivity)
    nlinarith only [h1, h2]
  have htail : R ≤ K * U / 31 := by
    have h := mul_le_mul_of_nonneg_left hAU hK.le
    linarith only [hR, h]
  have hbias : 2 * (A * C + R) ≤ 8 * K * U := by
    nlinarith only [hAC, htail, mul_pos hK hU]
  linarith only [hE, hB, hlin, hquad, hbias]

end OracleTemplate.AdaptiveHeavyTailSimplex
