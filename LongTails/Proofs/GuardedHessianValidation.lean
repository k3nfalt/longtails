import LongTails.Proofs.GuardedHessianTrial
import LongTails.Proofs.AdaptiveEntropicExecution
import LongTails.Proofs.AdaptiveEntropicStateMeasurable

open MeasureTheory
open LongTails.Algorithms.GuardedHessianTransport

namespace LongTails.Proofs.GuardedHessianValidation

lemma bestEstimate_minimizes {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (estimates : Fin (n + 1) → E) (j : Fin (n + 1)) :
    ‖estimates (bestEstimate estimates)‖ ≤ ‖estimates j‖ :=
  OracleTemplate.AdaptiveHeavyTailSimplex.minimumIndex_le (Nat.succ_pos n)
    (fun i => ‖estimates i‖) j

lemma selected_validation_bound {E : Type*} [NormedAddCommGroup E] {n : ℕ}
    (values estimates : Fin (n + 1) → E) {r M : ℝ} (hr : 0 ≤ r)
    (h0 : ‖values 0‖ ≤ M) :
    ‖values (bestEstimate estimates)‖ ≤ r +
      (if ∀ j : Fin n, r < ‖values j.succ‖ then M else 0) +
      2 * ∑ j, ‖estimates j - values j‖ := by
  classical
  have he (j : Fin (n + 1)) : ‖estimates j - values j‖ ≤ ∑ i, ‖estimates i - values i‖ :=
    Finset.single_le_sum (fun i _ => norm_nonneg (estimates i - values i)) (Finset.mem_univ j)
  have hsel (j : Fin (n + 1)) := GuardedGradientMoments.selected_norm_le values estimates
    (bestEstimate estimates) j (bestEstimate_minimizes estimates j)
  by_cases hb : ∀ j : Fin n, r < ‖values j.succ‖
  · rw [ite_eq_left hb]
    linarith [hsel 0, he 0, he (bestEstimate estimates)]
  · simp only [hb, ↓reduceIte, add_zero]
    push Not at hb
    obtain ⟨j, hj⟩ := hb
    linarith [hsel j.succ, he j.succ, he (bestEstimate estimates)]

lemma measurable_bestEstimate {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] {n : ℕ} : Measurable (bestEstimate (E := E) (n := n)) :=
  (OracleTemplate.AdaptiveHeavyTailSimplex.measurable_minimumIndex _).comp (by fun_prop)

lemma validation_expected_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
    (values estimates : Ω → Fin (n + 1) → E)
    (hv : Measurable values) (he : Measurable estimates) {r M v δ : ℝ}
    (hr : 0 ≤ r) (hM : 0 ≤ M) (h0 : ∀ ω, ‖values ω 0‖ ≤ M)
    (hi : ∀ j, Integrable (fun ω => ‖estimates ω j - values ω j‖) P)
    (hb : ∀ j, (∫ ω, ‖estimates ω j - values ω j‖ ∂P) ≤ v)
    (hbad : P.real {ω | ∀ j : Fin n, r < ‖values ω j.succ‖} ≤ δ) :
    Integrable (fun ω => ‖values ω (bestEstimate (estimates ω))‖) P ∧
      (∫ ω, ‖values ω (bestEstimate (estimates ω))‖ ∂P) ≤ r + M * δ + 2 * (n + 1 : ℕ) * v := by
  classical
  let A := {ω | ∀ j : Fin n, r < ‖values ω j.succ‖}
  have hA : MeasurableSet A := by
    change MeasurableSet {ω | ∀ j : Fin n, r < ‖values ω j.succ‖}
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun j : Fin n =>
      measurableSet_lt measurable_const ((measurable_pi_apply j.succ).comp hv).norm)
  let W := fun ω => r + (if ω ∈ A then M else 0) + 2 * ∑ j, ‖estimates ω j - values ω j‖
  have hind : Integrable (fun ω => if ω ∈ A then M else 0) P :=
    by
      convert (integrable_const M (μ := P)).indicator hA using 1
      ext ω
      simp only [Set.indicator_apply]
  have hWi : Integrable W P := ((integrable_const r).add hind).add
    ((integrable_finsetSum _ (fun j _ => hi j)).const_mul 2)
  have hchosen : Measurable (fun ω => values ω (bestEstimate (estimates ω))) :=
    (measurable_from_prod_countable_left
      (f := fun w : Ω × Fin (n + 1) => values w.1 w.2)
      (fun j => (measurable_pi_apply j).comp hv)).comp
      (measurable_id.prodMk (measurable_bestEstimate.comp he))
  have hbound (ω : Ω) : ‖values ω (bestEstimate (estimates ω))‖ ≤ W ω :=
    selected_validation_bound (values ω) (estimates ω) hr (h0 ω)
  have hFi : Integrable (fun ω => ‖values ω (bestEstimate (estimates ω))‖) P :=
    hWi.mono' hchosen.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hbound ω))
  refine ⟨hFi, ?_⟩
  have hh := integral_mono hFi hWi hbound
  have hsum : (∑ j, ∫ ω, ‖estimates ω j - values ω j‖ ∂P) ≤ (n + 1 : ℕ) * v := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)
  have hindval : (∫ ω, (if ω ∈ A then M else 0) ∂P) = P.real A * M := by
    simpa only [Set.indicator_apply, smul_eq_mul] using integral_indicator_const (μ := P) M hA
  have hadd := integral_add ((integrable_const r).add hind) ((integrable_finsetSum Finset.univ (fun j _ => hi j)).const_mul 2)
  simp only [Pi.add_apply] at hadd
  dsimp only [W] at hh
  rw [hadd,
    integral_add (integrable_const r) hind, integral_const, probReal_univ, one_smul,
    hindval, integral_const_mul, integral_finsetSum _ (fun j _ => hi j)] at hh
  have hbad' := mul_le_mul_of_nonneg_left hbad hM
  nlinarith


lemma independent_all_bad {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n : ℕ) (A : Set Ω) {δ : ℝ}
    (hb : P.real A ≤ δ) :
    (Measure.pi (fun _ : Fin n => P)).real {w | ∀ j, w j ∈ A} ≤ δ ^ n := by
  classical
  have he : {w : Fin n → Ω | ∀ j, w j ∈ A} = Set.univ.pi (fun _ => A) := by
    ext w
    simp
  rw [he, Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  calc
    _ ≤ ∏ _j : Fin n, δ := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact ENNReal.toReal_nonneg
      · intro j _
        exact hb
    _ = δ ^ n := by simp

lemma fresh_validation_error {S Ω E : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ : Measure S} {P : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (e : S × Ω → E) (G : S → ℝ)
    (he : Measurable e) (hG : Measurable G) (hG0 : ∀ s, 0 ≤ G s)
    {p σ α M : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hα : 0 ≤ α)
    (hM : 0 < M) (B : ℕ) (hB : 0 < B)
    (hi : ∀ s, Integrable (fun ω => e (s, ω)) P)
    (hm : ∀ s, (∫ ω, e (s, ω) ∂P) = 0)
    (hpi : ∀ s, Integrable (fun ω => ‖e (s, ω)‖ ^ p) P)
    (hb : ∀ s, (∫ ω, ‖e (s, ω)‖ ^ p ∂P) ≤ σ ^ p + α ^ p * G s ^ p)
    (hGi : Integrable (fun s => G s ^ 2) μ)
    (hGb : (∫ s, G s ^ 2 ∂μ) ≤ 9 * M ^ 2) :
    let F := fun w : S × (ℕ → Ω) => (B : ℝ)⁻¹ • ∑ k ∈ Finset.range B, e (w.1, w.2 k)
    Integrable (fun w => ‖F w‖) (μ.prod (Measure.infinitePi fun _ : ℕ => P)) ∧
      (∫ w, ‖F w‖ ∂μ.prod (Measure.infinitePi fun _ : ℕ => P)) ≤
        60 * (σ + α * M) * ((B : ℝ) ^ (p - 1))⁻¹ ^ p⁻¹ := by
  intro F
  have hpow := GuardedHessianEstimator.masked_batch_moment e (fun _ => true) G
    he measurable_const hG hG0 hp hp2 hσ hα hM B hB hi hm hpi hb hGi hGb
  simp only [↓reduceIte] at hpow
  have hFm : Measurable F := by dsimp only [F]; fun_prop
  apply GuardedHessianNoise.norm_first_from_power hFm hp (by positivity) hpow.1
  have hden : 0 < (B : ℝ) ^ (p - 1) := Real.rpow_pos_of_pos (by exact_mod_cast hB) _
  have hscale : 6 * (σ ^ p + (1 + 9) * α ^ p * M ^ p) ≤ 60 * (σ + α * M) ^ p := by
    have hh := Real.add_rpow_le_rpow_add hσ (mul_nonneg hα hM.le) hp
    rw [Real.mul_rpow hα hM.le] at hh
    nlinarith [Real.rpow_nonneg hσ p]
  have hs := div_le_div_of_nonneg_right hscale hden.le
  have hroot := GuardedHessianNoise.scaled_root_power (by norm_num : (1 : ℝ) ≤ 60)
    (show 0 ≤ σ + α * M by positivity) (inv_nonneg.mpr hden.le) hp
  calc
    _ ≤ 60 * (σ + α * M) ^ p / (B : ℝ) ^ (p - 1) := hpow.2.trans hs
    _ = 60 * ((B : ℝ) ^ (p - 1))⁻¹ * (σ + α * M) ^ p := by ring
    _ ≤ _ := hroot

lemma fresh_mean_error {S Ω E : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure S) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (V : S → E) (g : E → E) (a : E → Ω → E)
    (hV : Measurable V) (hg : Measurable g) (ha : Measurable (Function.uncurry a))
    {p σ α M : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hα : 0 ≤ α)
    (hM : 0 < M) (B offset : ℕ) (hB : 0 < B)
    (hi : ∀ x, Integrable (a x) P) (hm : ∀ x, (∫ ω, a x ω ∂P) = g x)
    (hpi : ∀ x, Integrable (fun ω => ‖a x ω - g x‖ ^ p) P)
    (hb : ∀ x, (∫ ω, ‖a x ω - g x‖ ^ p ∂P) ≤ σ ^ p + α ^ p * ‖g x‖ ^ p)
    (hGi : Integrable (fun s => ‖g (V s)‖ ^ 2) μ)
    (hGb : (∫ s, ‖g (V s)‖ ^ 2 ∂μ) ≤ 9 * M ^ 2) :
    let F := fun w : S × (ℕ → Ω) =>
      ‖(B : ℝ)⁻¹ • ∑ k ∈ Finset.range B, a (V w.1) (w.2 (offset + k)) - g (V w.1)‖
    Integrable F (μ.prod (Measure.infinitePi fun _ : ℕ => P)) ∧
      (∫ w, F w ∂μ.prod (Measure.infinitePi fun _ : ℕ => P)) ≤
        60 * (σ + α * M) * ((B : ℝ) ^ (p - 1))⁻¹ ^ p⁻¹ := by
  intro F
  let e : S × Ω → E := fun w => a (V w.1) w.2 - g (V w.1)
  have he : Measurable e := (ha.comp ((hV.comp measurable_fst).prodMk measurable_snd)).sub (hg.comp (hV.comp measurable_fst))
  have hei (s : S) : Integrable (fun ω => e (s, ω)) P := by
    change Integrable (fun ω => a (V s) ω - g (V s)) P
    exact (hi (V s)).sub (integrable_const (g (V s)))
  have hem (s : S) : (∫ ω, e (s, ω) ∂P) = 0 := by
    dsimp only [e]
    rw [integral_sub (hi (V s)) (integrable_const _), hm, integral_const, probReal_univ, one_smul, sub_self]
  have hbase := fresh_validation_error e (fun s => ‖g (V s)‖) he (hg.comp hV).norm
    (fun _ => norm_nonneg _) hp hp2 hσ hα hM B hB hei hem
    (fun s => hpi (V s)) (fun s => hb (V s)) hGi hGb
  let H := fun w : S × (ℕ → Ω) => ‖(B : ℝ)⁻¹ • ∑ k ∈ Finset.range B, e (w.1, w.2 k)‖
  have hH : Measurable H := by dsimp only [H]; fun_prop
  have hshift : MeasurePreserving (fun ξ : ℕ → Ω => fun k => ξ (offset + k))
      (Measure.infinitePi fun _ : ℕ => P) (Measure.infinitePi fun _ : ℕ => P) :=
    measurePreserving_snd.comp (OracleTemplate.StochasticGeneralized.splitStream_preserving P offset)
  have hpres := (MeasurePreserving.id μ).prod hshift
  have heq : H ∘ Prod.map id (fun ξ : ℕ → Ω => fun k => ξ (offset + k)) = F := by
    funext w
    dsimp only [H, F, Function.comp_def, Prod.map, id_eq, e]
    rw [Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast Nat.ne_of_gt hB), one_smul]
  refine ⟨?_, ?_⟩
  · rw [← heq]
    exact (hpres.integrable_comp hH.aestronglyMeasurable).mpr hbase.1
  · have hh : (∫ w, H w ∂μ.prod (Measure.infinitePi fun _ : ℕ => P)) =
        ∫ w, F w ∂μ.prod (Measure.infinitePi fun _ : ℕ => P) := by
      conv_lhs => rw [← hpres.map_eq]
      rw [integral_map hpres.measurable.aemeasurable hH.aestronglyMeasurable]
      exact congrArg (fun f => ∫ w, f w ∂μ.prod (Measure.infinitePi fun _ : ℕ => P)) heq
    rw [← hh]
    exact hbase.2

lemma fresh_validated_selection {S Ω E : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure S) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (K : ℕ) (V : S → Fin (K + 1) → E) (g : E → E) (a : E → Ω → E)
    (hV : Measurable V) (hg : Measurable g) (ha : Measurable (Function.uncurry a))
    {p σ α M r δ : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ) (hα : 0 ≤ α)
    (hM : 0 < M) (hr : 0 ≤ r) (B : ℕ) (hB : 0 < B)
    (hi : ∀ x, Integrable (a x) P) (hm : ∀ x, (∫ ω, a x ω ∂P) = g x)
    (hpi : ∀ x, Integrable (fun ω => ‖a x ω - g x‖ ^ p) P)
    (hb : ∀ x, (∫ ω, ‖a x ω - g x‖ ^ p ∂P) ≤ σ ^ p + α ^ p * ‖g x‖ ^ p)
    (hGi : ∀ j, Integrable (fun s => ‖g (V s j)‖ ^ 2) μ)
    (hGb : ∀ j, (∫ s, ‖g (V s j)‖ ^ 2 ∂μ) ≤ 9 * M ^ 2)
    (h0 : ∀ s, ‖g (V s 0)‖ ≤ M)
    (hbad : μ.real {s | ∀ j : Fin K, r < ‖g (V s j.succ)‖} ≤ δ) :
    let estimates := fun w : S × (ℕ → Ω) => fun j : Fin (K + 1) =>
      (B : ℝ)⁻¹ • ∑ i ∈ Finset.range B, a (V w.1 j) (w.2 (j.val * B + i))
    let F := fun w : S × (ℕ → Ω) => ‖g (V w.1 (bestEstimate (estimates w)))‖
    Integrable F (μ.prod (Measure.infinitePi fun _ : ℕ => P)) ∧
      (∫ w, F w ∂μ.prod (Measure.infinitePi fun _ : ℕ => P)) ≤
        r + M * δ + 120 * (K + 1 : ℕ) * (σ + α * M) * ((B : ℝ) ^ (p - 1))⁻¹ ^ p⁻¹ := by
  intro estimates F
  let values := fun w : S × (ℕ → Ω) => fun j : Fin (K + 1) => g (V w.1 j)
  have hvalues : Measurable values := by
    apply Measurable.of_eval
    intro j
    exact hg.comp ((measurable_pi_apply j).comp (hV.comp measurable_fst))
  have hestimates : Measurable estimates := by
    apply Measurable.of_eval
    intro j
    dsimp only [estimates]
    fun_prop
  have herr (j : Fin (K + 1)) := fresh_mean_error μ P (fun s => V s j) g a
    ((measurable_pi_apply j).comp hV) hg ha hp hp2 hσ hα hM B (j.val * B) hB
    hi hm hpi hb (hGi j) (hGb j)
  have hAm : MeasurableSet {s | ∀ j : Fin K, r < ‖g (V s j.succ)‖} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun j => measurableSet_lt measurable_const
      (hg.comp ((measurable_pi_apply j.succ).comp hV)).norm)
  have hbad' : (μ.prod (Measure.infinitePi fun _ : ℕ => P)).real
      {w | ∀ j : Fin K, r < ‖values w j.succ‖} ≤ δ := by
    have hh := (measurePreserving_fst (μ := μ) (ν := Measure.infinitePi fun _ : ℕ => P)).measureReal_preimage
      hAm.nullMeasurableSet
    exact hh.trans_le hbad
  have hh := validation_expected_bound (μ.prod (Measure.infinitePi fun _ : ℕ => P))
    values estimates hvalues hestimates hr hM.le (fun w => h0 w.1)
    (fun j => (herr j).1) (fun j => (herr j).2) hbad'
  refine ⟨hh.1, hh.2.trans ?_⟩
  apply le_of_eq
  ring

end LongTails.Proofs.GuardedHessianValidation
