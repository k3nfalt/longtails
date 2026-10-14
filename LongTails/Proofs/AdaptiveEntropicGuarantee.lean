import LongTails.Proofs.AdaptiveEntropicTuning
import LongTails.Proofs.AdaptiveEntropicCap

open MeasureTheory

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

lemma measure_union_six_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (E₁ E₂ E₃ E₄ E₅ E₆ : Set Ω) {b : ENNReal}
    (h₁ : P E₁ ≤ b) (h₂ : P E₂ ≤ b) (h₃ : P E₃ ≤ b)
    (h₄ : P E₄ ≤ b) (h₅ : P E₅ ≤ 2 * b) (h₆ : P E₆ ≤ b) :
    P (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅ ∪ E₆) ≤ 7 * b := by
  have h12 := (measure_union_le E₁ E₂).trans (add_le_add h₁ h₂)
  have h123 := (measure_union_le (E₁ ∪ E₂) E₃).trans (add_le_add h12 h₃)
  have h1234 := (measure_union_le (E₁ ∪ E₂ ∪ E₃) E₄).trans (add_le_add h123 h₄)
  have h12345 := (measure_union_le (E₁ ∪ E₂ ∪ E₃ ∪ E₄) E₅).trans (add_le_add h1234 h₅)
  calc
    _ ≤ b + b + b + b + 2 * b + b :=
      (measure_union_le (E₁ ∪ E₂ ∪ E₃ ∪ E₄ ∪ E₅) E₆).trans (add_le_add h12345 h₆)
    _ = _ := by ring

lemma assembled_energy_tail (q : Public) {Ω : Type} [MeasurableSpace Ω]
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
    (T : ℕ) (xstar : simplex q.d)
    (hcount : T * (130 * (T : ℝ) ^ p * σ ^ p / A ^ p) ≤ (trimCount q : ℝ) / 31)
    (hV : T * (16 * (24 * q.L * window q (T + 1) + A) ^ (2 - p) *
      (T : ℝ) ^ p * σ ^ p) ≤ (trimCount q : ℝ) * (24 * q.L * window q (T + 1) + A) ^ 2 / 256)
    (hR : 130 * (T : ℝ) ^ (p + 1) * σ ^ p / A ^ (p - 1) ≤ (trimCount q : ℝ) * A / 31) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 170 * (trimCount q : ℝ) * (24 * q.L * window q (T + 1) + A) <
        (T : ℝ) * (T + 1) / 2 * (f (macroState q g ξ T).y - f xstar)} ≤
      7 * ENNReal.ofReal (Real.exp (-confidence q)) := by
  let μ := fun x : simplex q.d => gradient f x
  let U := 24 * q.L * window q (T + 1) + A
  let V := T * (16 * U ^ (2 - p) * (T : ℝ) ^ p * σ ^ p)
  let Q := Measure.infinitePi (fun _ : ℕ => P)
  let centerPrefix : (ℕ → Ω) → Prop := fun ξ => ∀ j < preload q + T,
    let s := (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ j).1
    s.warmup = 0 → centerGood q μ σ s
  let E₁ := ⋃ i ∈ Finset.range T, {ξ | ¬ centerGood q μ σ
    (StochasticGeneralized.blockTrace (analysisCost q) (blockUpdate q g)
      (initialState q) ξ (preload q + i)).1}
  let E₂ := {ξ | centerPrefix ξ ∧ A < empiricalQuantile q (macroState q g ξ T)}
  let E₃ := {ξ | centerPrefix ξ ∧ empiricalQuantile q (macroState q g ξ T) ≤ A ∧
    2 * T * (16 * U ^ (2 - p) * (T : ℝ) ^ p * σ ^ p) + 8 * U ^ 2 * confidence q ≤
      (macroState q g ξ T).variation}
  let E₄ := {ξ | 2 * (trimCount q : ℝ) + 4 * confidence q <
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (fun n s (_ : Fin n → Ω) => ∫ b, firstScore (cappedBiasScore q g μ σ A) n s b
        ∂Measure.pi (fun _ : Fin n => P)) (preload q + T) (initialState q) ξ}
  let E₅ := {ξ | 16 * Real.sqrt (geometry q) * Real.sqrt ((macroState q g ξ T).variation) +
    20 * (U * geometry q / trimCount q) * confidence q <
      2 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
        (quadraticNoiseScore q g μ σ A T P) (preload q + T) (initialState q) ξ}
  let E₆ := {ξ | 4 * U * confidence q + V / U <
    StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (linearNoiseScore q g μ σ A T P xstar) (preload q + T) (initialState q) ξ}
  have hU : 0 < U := by dsimp [U]; positivity
  have hK : 0 < (trimCount q : ℝ) := by
    have hn : 1 ≤ trimCount q := le_max_left _ _
    exact_mod_cast (show 0 < trimCount q by omega)
  have h₁ : Q E₁ ≤ ENNReal.ofReal (Real.exp (-confidence q)) :=
    all_centers_failure q hg hμ hL.le hH
      (fun x y => hlip x x.property y y.property) hσ hp hi hm T
  have hbudget : T * (130 * (T : ℝ) ^ p * σ ^ p / A ^ p) ≤ (trimCount q : ℝ) / 8 := by
    linarith only [hcount, hK]
  have h₂ : Q E₂ ≤ ENNReal.ofReal (Real.exp (-confidence q)) := by
    have h := quantile_cap_failure q P hg hμ hσ hp hp2 hA hi hm T hbudget
    have he : Real.exp (-(trimCount q : ℝ) / 8) ≤ Real.exp (-confidence q) := by
      apply Real.exp_le_exp.mpr
      have ht := confidence_le_trimCount q
      linarith only [ht, hK]
    exact (show Q E₂ ≤ ENNReal.ofReal (Real.exp (-(trimCount q : ℝ) / 8)) from h).trans
      (ENNReal.ofReal_le_ofReal he)
  have h₃ : Q E₃ ≤ ENNReal.ofReal (Real.exp (-confidence q)) :=
    actual_variation_tail q P hg hμ hσ hA.le hL.le hp hp2 hi hm T hU (confidence q)
  have h₄ : Q E₄ ≤ ENNReal.ofReal (Real.exp (-confidence q)) :=
    cappedBias_compensator_tail q P hg hμ σ hA (preload q + T) (confidence q)
  have h₅ : Q E₅ ≤ 2 * ENNReal.ofReal (Real.exp (-confidence q)) :=
    quadratic_energy_actual_tail q P hg hμ σ hA.le T (preload q + T) hL hH (confidence q)
  have h₆ : Q E₆ ≤ ENNReal.ofReal (Real.exp (-confidence q)) :=
    linear_noise_tail q hg hμ hσ hA.le hL.le hp hp2 hi hm T hU xstar (confidence q)
  apply le_trans (measure_mono ?_)
    (measure_union_six_bound Q E₁ E₂ E₃ E₄ E₅ E₆ h₁ h₂ h₃ h₄ h₅ h₆)
  intro ξ hξ
  by_contra hn
  have hn₁ : ξ ∉ E₁ := fun h => hn (by simp only [Set.mem_union]; tauto)
  have hn₂ : ξ ∉ E₂ := fun h => hn (by simp only [Set.mem_union]; tauto)
  have hn₃ : ξ ∉ E₃ := fun h => hn (by simp only [Set.mem_union]; tauto)
  have hn₄ : ξ ∉ E₄ := fun h => hn (by simp only [Set.mem_union]; tauto)
  have hn₅ : ξ ∉ E₅ := fun h => hn (by simp only [Set.mem_union]; tauto)
  have hn₆ : ξ ∉ E₆ := fun h => hn (by simp only [Set.mem_union]; tauto)
  have hc := centers_prefix_of_not_failure q g μ σ T ξ hn₁
  have hQ : empiricalQuantile q (macroState q g ξ T) ≤ A := by
    apply not_lt.mp
    intro hq
    exact hn₂ ⟨hc, hq⟩
  have hWstrict : (macroState q g ξ T).variation <
      2 * T * (16 * U ^ (2 - p) * (T : ℝ) ^ p * σ ^ p) + 8 * U ^ 2 * confidence q := by
    apply not_le.mp
    intro hw
    exact hn₃ ⟨hc, hQ, hw⟩
  have hW : (macroState q g ξ T).variation ≤ (trimCount q : ℝ) * U ^ 2 := by
    have ht := confidence_le_trimCount q
    have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 8 * U ^ 2 by positivity)
    nlinarith only [hWstrict, hV, hh, mul_pos hK (sq_pos_of_pos hU)]
  have he := actual_energy_on_good_path q hg hL hH hf hgrad hlip hμ hσ hA hp hp2
    hi hm hgi hgu T xstar ξ (show U = _ from rfl) hV hR hc hQ hW
    (not_lt.mp hn₆) (not_lt.mp hn₅) (not_lt.mp hn₄)
  exact (not_lt_of_ge he) hξ

lemma objective_rate_tail (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {f : Vector q.d → ℝ} (hL : 0 < q.L) (hδ : 0 < q.δ) (hδ1 : q.δ < 1)
    (hf : ConvexOn ℝ (simplex q.d) f)
    (hgrad : ∀ x ∈ simplex q.d, HasGradientAt f (gradient f x) x)
    (hlip : ∀ x ∈ simplex q.d, ∀ y ∈ simplex q.d,
      dualNorm (gradient f x - gradient f y) ≤ q.L * oneNorm (x - y))
    {σ p : ℝ} (hσ : 0 ≤ σ) (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - gradient f x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - gradient f x) ^ p ∂P) ≤ σ ^ p)
    (hgi : ∀ x, Integrable (g x) P) (hgu : ∀ x, (∫ ω, g x ω ∂P) = gradient f x)
    (T : ℕ) (hT : 0 < T) (xstar : simplex q.d) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 16777216 * (q.L * trimCount q * window q T / (T : ℝ) ^ 2 +
        σ * ((trimCount q : ℝ) / T) ^ ((p - 1) / p)) <
          f (macroState q g ξ T).y - f xstar} ≤ ENNReal.ofReal q.δ := by
  have hH := confidence_ge_two q hδ hδ1
  have hμ := measurable_restricted_gradient hg hgu
  let A := analysisCap q σ p T
  let U := 24 * q.L * window q (T + 1) + A
  have hA : 0 < A := analysisCap_pos q hL hH hσ T
  have hU : 0 < U := by dsimp [U]; positivity
  have hc := analysisCap_controls q hL hH hσ hp T
  have he := assembled_energy_tail q hg hL hH hf hgrad hlip hμ hσ hA hp hp2
    hi hm hgi hgu T xstar hc.1 hc.2.2 hc.2.1
  apply le_trans (measure_mono ?_) (he.trans (confidence_failure q hδ))
  intro ξ hξ
  change 170 * (trimCount q : ℝ) * U < _
  by_contra hn
  have henergy := le_of_not_gt hn
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hK : 0 ≤ (trimCount q : ℝ) := Nat.cast_nonneg _
  have hgap := objective_gap_from_energy hTr hK hU.le henergy
  have hrate := analytic_envelope_rate q hL.le hH hσ (by linarith : 0 < p) hT
  have hUeq : U = 48 * q.L * window q (T + 1) +
      4096 * σ * ((T : ℝ) ^ (p + 1) / trimCount q) ^ (1 / p) := by
    dsimp [U, A, analysisCap]
    ring
  rw [hUeq] at hgap
  exact (not_lt_of_ge (hgap.trans hrate)) hξ

end OracleTemplate.AdaptiveHeavyTailSimplex
