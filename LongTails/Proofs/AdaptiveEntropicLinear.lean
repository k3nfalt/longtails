import LongTails.Proofs.AdaptiveEntropicQuadratic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory
open scoped OracleTemplate.AdaptiveList RealInnerProductSpace

namespace OracleTemplate.AdaptiveHeavyTailSimplex

open LongTails.Setups.AdaptiveHeavyTailSimplex

noncomputable def simplexPairing {d : ℕ} (z : Vector d) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i, (z i) • ContinuousLinearMap.proj i

lemma simplexPairing_apply {d : ℕ} (z : Vector d) (u : Fin d → ℝ) :
    simplexPairing z u = ∑ i, z i * u i := by
  simp [simplexPairing]

lemma simplexPairing_eq_inner {d : ℕ} (z : Vector d) (u : Fin d → ℝ) :
    simplexPairing z u = ⟪WithLp.toLp 2 u, z⟫ := by
  simp [simplexPairing_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

lemma simplexPairing_abs_bound {d : ℕ} (z : Vector d) (u : Fin d → ℝ) :
    |simplexPairing z u| ≤ ‖u‖ * oneNorm z := by
  rw [simplexPairing_eq_inner]
  exact abs_inner_le_dual_one (WithLp.toLp 2 u) z

noncomputable def scalarNoise (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (P : Measure Ω) (xstar : simplex q.d) (s : State q) (ω : Ω) : ℝ :=
  simplexPairing (xstar.val - (predictableProx q s).val) (weightedNoise q g μ σ A T P s ω)

lemma measurable_scalarNoise (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ A : ℝ) (T : ℕ) (P : Measure Ω) [SFinite P] (xstar : simplex q.d) :
    Measurable (Function.uncurry (scalarNoise q g μ σ A T P xstar)) := by
  have hN := measurable_weightedNoise q hg hμ σ A T P
  have hz : Measurable (fun w : State q × Ω => xstar.val - (predictableProx q w.1).val) :=
    measurable_const.sub (measurable_subtype_coe.comp ((measurable_predictableProx q).comp measurable_fst))
  change Measurable (fun w : State q × Ω => scalarNoise q g μ σ A T P xstar w.1 w.2)
  simp only [scalarNoise, simplexPairing_apply]
  apply Finset.measurable_sum
  intro i hi
  exact (((PiLp.continuous_apply 2 (fun _ : Fin q.d => ℝ) i).measurable).comp hz).mul
    ((measurable_pi_apply i).comp hN)

lemma scalarNoise_abs_le_norm (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (P : Measure Ω) (xstar : simplex q.d) (s : State q) (ω : Ω) :
    |scalarNoise q g μ σ A T P xstar s ω| ≤ 2 * ‖weightedNoise q g μ σ A T P s ω‖ := by
  have h := simplexPairing_abs_bound (xstar.val - (predictableProx q s).val)
    (weightedNoise q g μ σ A T P s ω)
  have hm := mul_le_mul_of_nonneg_left (simplex_diameter xstar (predictableProx q s))
    (norm_nonneg (weightedNoise q g μ σ A T P s ω))
  exact h.trans (by linarith)

lemma scalarNoise_range (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T : ℕ)
    (xstar : simplex q.d) (s : State q) (ω : Ω) :
    |scalarNoise q g μ σ A T P xstar s ω| ≤ 4 * (24 * q.L * window q (T + 1) + A) := by
  have h := scalarNoise_abs_le_norm q g μ σ A T P xstar s ω
  have hb := weightedNoise_range (P := P) q hg hμ σ hA hL T s ω
  linarith

lemma integral_scalarNoise_eq_zero (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T : ℕ)
    (xstar : simplex q.d) (s : State q) :
    (∫ ω, scalarNoise q g μ σ A T P xstar s ω ∂P) = 0 := by
  have hN : Measurable (fun ω => weightedNoise q g μ σ A T P s ω) :=
    (measurable_weightedNoise q hg hμ σ A T P).comp measurable_prodMk_left
  have hi : Integrable (fun ω => weightedNoise q g μ σ A T P s ω) P :=
    Integrable.of_bound hN.aestronglyMeasurable (2 * (24 * q.L * window q (T + 1) + A))
      (Filter.Eventually.of_forall (fun ω => weightedNoise_range (P := P) q hg hμ σ hA hL T s ω))
  unfold scalarNoise
  rw [(simplexPairing (xstar.val - (predictableProx q s).val)).integral_comp_comm hi,
    integral_weightedNoise_eq_zero q hg hμ σ hA hL T s, map_zero]

lemma scalar_second_le_vector_second {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} {Z : Ω → E}
    (hX : Measurable X) (hZ : Measurable Z) {U : ℝ}
    (hZb : ∀ ω, ‖Z ω‖ ≤ 2 * U) (hXb : ∀ ω, |X ω| ≤ 2 * ‖Z ω‖) :
    (∫ ω, (X ω) ^ 2 ∂P) ≤ 4 * ∫ ω, ‖Z ω‖ ^ 2 ∂P := by
  have hzb (ω : Ω) : ‖Z ω‖ ^ 2 ≤ 4 * U ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg (Z ω)) (hZb ω) 2
    nlinarith only [h]
  have hxb (ω : Ω) : (X ω) ^ 2 ≤ 4 * ‖Z ω‖ ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (X ω)) (hXb ω) 2
    rw [sq_abs] at h
    nlinarith only [h]
  have hiZ : Integrable (fun ω => ‖Z ω‖ ^ 2) P := by
    apply Integrable.of_bound (hZ.norm.pow_const 2).aestronglyMeasurable (4 * U ^ 2)
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖Z ω‖))] using hzb ω)
  have hiX : Integrable (fun ω => (X ω) ^ 2) P := by
    apply Integrable.of_bound (hX.pow_const 2).aestronglyMeasurable (16 * U ^ 2)
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      linarith only [hxb ω, hzb ω])
  have h := integral_mono hiX (hiZ.const_mul 4) hxb
  rwa [integral_const_mul] at h

section

attribute [local irreducible] weightedNoise scalarNoise

lemma scalarNoise_second_le_norm (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T : ℕ)
    (xstar : simplex q.d) (s : State q) :
    (∫ ω, (scalarNoise q g μ σ A T P xstar s ω) ^ 2 ∂P) ≤
      4 * ∫ ω, ‖weightedNoise q g μ σ A T P s ω‖ ^ 2 ∂P := by
  have hN : Measurable (fun ω => weightedNoise q g μ σ A T P s ω) :=
    (measurable_weightedNoise q hg hμ σ A T P).comp measurable_prodMk_left
  have hX : Measurable (fun ω => scalarNoise q g μ σ A T P xstar s ω) :=
    (measurable_scalarNoise q hg hμ σ A T P xstar).comp measurable_prodMk_left
  apply scalar_second_le_vector_second (P := P)
    (X := fun ω => scalarNoise q g μ σ A T P xstar s ω)
    (Z := fun ω => weightedNoise q g μ σ A T P s ω)
    (U := 24 * q.L * window q (T + 1) + A) hX hN
  · intro ω
    exact weightedNoise_range (P := P) q hg hμ σ hA hL T s ω
  · intro ω
    exact scalarNoise_abs_le_norm q g μ σ A T P xstar s ω

end

lemma scalarNoise_second_le_pair (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T : ℕ)
    (xstar : simplex q.d) (s : State q) :
    (∫ ω, (scalarNoise q g μ σ A T P xstar s ω) ^ 2 ∂P) ≤
      4 * ∫ b, pairedVariation q g μ σ A T 2 s b ∂Measure.pi (fun _ : Fin 2 => P) := by
  have hcent := weightedResidual_centered_second_le_pair (P := P) q hμ hg σ hA hL T s
  have hcent' : (∫ ω, ‖weightedNoise q g μ σ A T P s ω‖ ^ 2 ∂P) ≤
      ∫ b, pairedVariation q g μ σ A T 2 s b ∂Measure.pi (fun _ : Fin 2 => P) := by
    change (∫ ω, ‖weightedResidual q μ σ A T s (g (queryPoint q s) ω) -
      ∫ z, weightedResidual q μ σ A T s (g (queryPoint q s) z) ∂P‖ ^ 2 ∂P) ≤
      ∫ b : Fin 2 → Ω, ‖weightedResidual q μ σ A T s (g (queryPoint q s) (b 0)) -
        weightedResidual q μ σ A T s (g (queryPoint q s) (b 1))‖ ^ 2
        ∂Measure.pi (fun _ => P)
    exact hcent
  exact (scalarNoise_second_le_norm q hg hμ σ hA hL T xstar s).trans
    (mul_le_mul_of_nonneg_left hcent' (by norm_num))

lemma bounded_zero_mean_mgf {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : Measurable X) {M v : ℝ} (hM : 0 < M)
    (hb : ∀ ω, |X ω| ≤ M) (hm : (∫ ω, X ω ∂P) = 0)
    (hv : (∫ ω, (X ω) ^ 2 ∂P) ≤ v) :
    Integrable (fun ω => Real.exp (X ω / M - v / M ^ 2)) P ∧
      (∫ ω, Real.exp (X ω / M - v / M ^ 2) ∂P) ≤ 1 := by
  have hr (ω : Ω) : |X ω / M| ≤ 1 := by
    rw [abs_div, abs_of_pos hM]
    exact (div_le_one₀ hM).mpr (hb ω)
  have hm' : (∫ ω, X ω / M ∂P) ≤ 0 := by
    rw [integral_div, hm, zero_div]
  have hv' : (∫ ω, (X ω / M) ^ 2 ∂P) ≤ v / M ^ 2 := by
    simp_rw [div_pow]
    rw [integral_div]
    exact div_le_div_of_nonneg_right hv (sq_nonneg M)
  have h := RobustGradient.bounded_increment_mgf (hX.div_const M) hr hm' hv'
  have hs := AdaptiveEntropicConcentration.exponential_shift h.1 h.2
    (c := -(v / M ^ 2)) (by simp)
  simpa only [zero_add, sub_eq_add_neg, add_comm] using hs

noncomputable def linearNoiseScore (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    (g : simplex q.d → Ω → Vector q.d) (μ : simplex q.d → Vector q.d)
    (σ A : ℝ) (T : ℕ) (P : Measure Ω) (xstar : simplex q.d)
    (n : ℕ) (s : State q) (b : Fin n → Ω) : ℝ :=
  pairScore (fun s a _ => scalarNoise q g μ σ A T P xstar s a) n s b

lemma measurable_linearNoiseScore (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ A : ℝ) (T : ℕ) (P : Measure Ω) [SFinite P] (xstar : simplex q.d) (n : ℕ) :
    Measurable (Function.uncurry (linearNoiseScore q g μ σ A T P xstar n)) := by
  have hX := (measurable_scalarNoise q hg hμ σ A T P xstar).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd) :
      Measurable (fun w : State q × (Ω × Ω) => (w.1, w.2.1)))
  exact measurable_pairScore hX n

lemma linearNoiseScore_range (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T n : ℕ)
    (xstar : simplex q.d) (s : State q) (b : Fin n → Ω) :
    |linearNoiseScore q g μ σ A T P xstar n s b| ≤
      4 * (24 * q.L * window q (T + 1) + A) := by
  unfold linearNoiseScore pairScore
  split_ifs
  · exact scalarNoise_range q hg hμ σ hA hL T xstar s _
  · simp only [abs_zero]
    positivity

lemma integral_linearNoiseScore_eq_zero (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T n : ℕ)
    (xstar : simplex q.d) (s : State q) :
    (∫ b, linearNoiseScore q g μ σ A T P xstar n s b
      ∂Measure.pi (fun _ : Fin n => P)) = 0 := by
  by_cases hn : n = 2
  · subst n
    unfold linearNoiseScore
    rw [integral_pairScore]
    change (∫ w : Ω × Ω, (fun ω => scalarNoise q g μ σ A T P xstar s ω) w.1
      ∂P.prod P) = 0
    rw [integral_fun_fst (μ := P) (ν := P)
      (fun ω : Ω => scalarNoise q g μ σ A T P xstar s ω)]
    simp only [probReal_univ, one_smul]
    exact integral_scalarNoise_eq_zero q hg hμ σ hA hL T xstar s
  · simp only [linearNoiseScore, pairScore, dite_eq_right hn, integral_zero]

lemma linearNoiseScore_second_le_pair (q : Public) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    (σ : ℝ) {A : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ q.L) (T n : ℕ)
    (xstar : simplex q.d) (s : State q) :
    (∫ b, (linearNoiseScore q g μ σ A T P xstar n s b) ^ 2
      ∂Measure.pi (fun _ : Fin n => P)) ≤
      4 * ∫ b, pairedVariation q g μ σ A T n s b ∂Measure.pi (fun _ : Fin n => P) := by
  by_cases hn : n = 2
  · subst n
    change (∫ b : Fin 2 → Ω, (scalarNoise q g μ σ A T P xstar s (b 0)) ^ 2
      ∂Measure.pi (fun _ => P)) ≤ _
    have he := integral_pairScore P
      (fun (s : State q) a _ => (scalarNoise q g μ σ A T P xstar s a) ^ 2) s
    change (∫ b : Fin 2 → Ω, (scalarNoise q g μ σ A T P xstar s (b 0)) ^ 2
      ∂Measure.pi (fun _ => P)) =
      ∫ w : Ω × Ω, (scalarNoise q g μ σ A T P xstar s w.1) ^ 2 ∂P.prod P at he
    rw [he]
    rw [integral_fun_fst (μ := P) (ν := P)
      (fun ω : Ω => (scalarNoise q g μ σ A T P xstar s ω) ^ 2)]
    simp only [probReal_univ, one_smul]
    exact scalarNoise_second_le_pair q hg hμ σ hA hL T xstar s
  · simp [linearNoiseScore, pairedVariation, pairScore, hn]

lemma accumulated_zero_mean_mgf {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (X : (n : ℕ) → S → (Fin n → Ω) → ℝ) (V : ℕ → S → ℝ)
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hX : ∀ n, Measurable (Function.uncurry (X n))) (hV : ∀ n, Measurable (V n))
    {M : ℝ} (hM : 0 < M) (hb : ∀ n s b, |X n s b| ≤ M)
    (hm : ∀ n s, (∫ b, X n s b ∂Measure.pi (fun _ : Fin n => P)) = 0)
    (hv : ∀ n s, (∫ b, (X n s b) ^ 2 ∂Measure.pi (fun _ : Fin n => P)) ≤ V n s)
    (N : ℕ) (s : S) :
    let inc := fun n s b => X n s b / M - V n s / M ^ 2
    Integrable (fun ξ => Real.exp (StochasticGeneralized.accumulated cost next inc N s ξ))
      (Measure.infinitePi fun _ : ℕ => P) ∧
      (∫ ξ, Real.exp (StochasticGeneralized.accumulated cost next inc N s ξ)
        ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 1 := by
  intro inc
  apply StochasticGeneralized.accumulated_exp_control P hc hn
  · intro n
    exact ((hX n).div_const M).sub (((hV n).comp measurable_fst).div_const (M ^ 2))
  · intro s
    exact (bounded_zero_mean_mgf ((hX (cost s)).comp measurable_prodMk_left)
      hM (hb (cost s) s) (hm (cost s) s) (hv (cost s) s)).1
  · intro s
    exact (bounded_zero_mean_mgf ((hX (cost s)).comp measurable_prodMk_left)
      hM (hb (cost s) s) (hm (cost s) s) (hv (cost s) s)).2

lemma accumulated_zero_mean_tail {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (cost : S → ℕ)
    (next : (n : ℕ) → S → (Fin n → Ω) → S)
    (X : (n : ℕ) → S → (Fin n → Ω) → ℝ) (V : ℕ → S → ℝ)
    (hc : Measurable cost) (hn : ∀ n, Measurable (Function.uncurry (next n)))
    (hX : ∀ n, Measurable (Function.uncurry (X n))) (hV : ∀ n, Measurable (V n))
    {M : ℝ} (hM : 0 < M) (hb : ∀ n s b, |X n s b| ≤ M)
    (hm : ∀ n s, (∫ b, X n s b ∂Measure.pi (fun _ : Fin n => P)) = 0)
    (hv : ∀ n s, (∫ b, (X n s b) ^ 2 ∂Measure.pi (fun _ : Fin n => P)) ≤ V n s)
    (N : ℕ) (s : S) {v : ℝ}
    (hvs : ∀ ξ, StochasticGeneralized.accumulated cost next (fun n s _ => V n s) N s ξ ≤ v)
    (H : ℝ) :
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | M * H + v / M < StochasticGeneralized.accumulated cost next X N s ξ} ≤
      ENNReal.ofReal (Real.exp (-H)) := by
  let inc := fun n s b => X n s b / M - V n s / M ^ 2
  have hmg := accumulated_zero_mean_mgf P cost next X V hc hn hX hV hM hb hm hv N s
  change Integrable (fun ξ => Real.exp (StochasticGeneralized.accumulated cost next inc N s ξ)) _ ∧
    (∫ ξ, Real.exp (StochasticGeneralized.accumulated cost next inc N s ξ)
      ∂Measure.infinitePi (fun _ : ℕ => P)) ≤ 1 at hmg
  have ht := StochasticGeneralized.exponential_tail (t := 1) (C := 0) (r := H)
    (by norm_num) (by simpa only [one_mul] using hmg.1)
    (by simpa only [one_mul, Real.exp_zero] using hmg.2)
  simp only [one_mul, zero_sub] at ht
  apply le_trans (measure_mono ?_) ht
  intro ξ hξ
  change M * H + v / M < StochasticGeneralized.accumulated cost next X N s ξ at hξ
  change H < StochasticGeneralized.accumulated cost next inc N s ξ
  have hi : inc = fun n s b => (1 / M) * X n s b + (-1 / M ^ 2) * V n s := by
    funext n s b
    dsimp [inc]
    ring
  rw [hi, StochasticGeneralized.accumulated_linear]
  have hvnorm := div_le_div_of_nonneg_right (hvs ξ) (sq_nonneg M)
  have hx : H + v / M ^ 2 < StochasticGeneralized.accumulated cost next X N s ξ / M := by
    apply (lt_div_iff₀ hM).mpr
    calc
      (H + v / M ^ 2) * M = M * H + v / M := by field_simp
      _ < _ := hξ
  have he : (-1 / M ^ 2) *
      StochasticGeneralized.accumulated cost next (fun n s _ => V n s) N s ξ =
      -(StochasticGeneralized.accumulated cost next (fun n s _ => V n s) N s ξ / M ^ 2) := by ring
  rw [he, one_div_mul_eq_div]
  linarith only [hvnorm, hx]

lemma linear_noise_tail (q : Public) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {g : simplex q.d → Ω → Vector q.d} (hg : Measurable (Function.uncurry g))
    {μ : simplex q.d → Vector q.d} (hμ : Measurable μ)
    {σ A p : ℝ} (hσ : 0 ≤ σ) (hA : 0 ≤ A) (hL : 0 ≤ q.L)
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hi : ∀ x, Integrable (fun ω => dualNorm (g x ω - μ x) ^ p) P)
    (hm : ∀ x, (∫ ω, dualNorm (g x ω - μ x) ^ p ∂P) ≤ σ ^ p)
    (T : ℕ) (hU : 0 < 24 * q.L * window q (T + 1) + A)
    (xstar : simplex q.d) (H : ℝ) :
    let U := 24 * q.L * window q (T + 1) + A
    let V := T * (16 * U ^ (2 - p) * (T : ℝ) ^ p * σ ^ p)
    (Measure.infinitePi fun _ : ℕ => P)
      {ξ | 4 * U * H + V / U < StochasticGeneralized.accumulated
        (analysisCost q) (blockUpdate q g) (linearNoiseScore q g μ σ A T P xstar)
        (preload q + T) (initialState q) ξ} ≤ ENNReal.ofReal (Real.exp (-H)) := by
  intro U V
  let X := linearNoiseScore q g μ σ A T P xstar
  let Y := fun n s (_ : Fin n → Ω) =>
    ∫ b, pairedVariation q g μ σ A T n s b ∂Measure.pi (fun _ : Fin n => P)
  let C := fun n s => 4 * ∫ b, pairedVariation q g μ σ A T n s b
    ∂Measure.pi (fun _ : Fin n => P)
  have hC (n : ℕ) : Measurable (C n) :=
    ((measurable_pairedVariation q hg hμ σ A T n).stronglyMeasurable.integral_prod_right.measurable).const_mul 4
  have hs (ξ : ℕ → Ω) : StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
      (fun n s _ => C n s) (preload q + T) (initialState q) ξ ≤ 4 * V := by
    have he : StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
        (fun n s _ => C n s) (preload q + T) (initialState q) ξ =
        4 * StochasticGeneralized.accumulated (analysisCost q) (blockUpdate q g)
          Y (preload q + T) (initialState q) ξ := by
      rw [StochasticGeneralized.accumulated_eq_sum, StochasticGeneralized.accumulated_eq_sum,
        Finset.mul_sum]
    rw [he]
    exact mul_le_mul_of_nonneg_left
      (pairedVariation_compensator_sum q hg hμ hσ hA hL hp hp2 hi hm T hU ξ) (by norm_num)
  have ht := accumulated_zero_mean_tail P (analysisCost q) (blockUpdate q g) X C
    (measurable_analysisCost q) (measurable_blockUpdate q hg)
    (measurable_linearNoiseScore q hg hμ σ A T P xstar) hC
    (show 0 < 4 * U by dsimp [U]; positivity)
    (fun n s b => linearNoiseScore_range q hg hμ σ hA hL T n xstar s b)
    (fun n s => integral_linearNoiseScore_eq_zero q hg hμ σ hA hL T n xstar s)
    (fun n s => linearNoiseScore_second_le_pair q hg hμ σ hA hL T n xstar s)
    (preload q + T) (initialState q) hs H
  have he : (4 * V) / (4 * U) = V / U := by field_simp
  rw [he] at ht
  exact ht

end OracleTemplate.AdaptiveHeavyTailSimplex
