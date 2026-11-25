import LongTails.Proofs.FiniteVarianceBatch
import LongTails.Proofs.MultiplicativeRobustMedoid
import LongTails.Proofs.MultiplicativeRobustConfidence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.StochasticEllSmoothEstimator

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [IsProbabilityMeasure P] in
lemma integral_norm_le_of_sq {V : Ω → E} (hV : AEStronglyMeasurable V P)
    (hV2 : Integrable (fun ω => ‖V ω‖ ^ 2) P) {c : ℝ} (hc : 0 < c)
    (h : (∫ ω, ‖V ω‖ ^ 2 ∂P) ≤ c ^ 2) [IsProbabilityMeasure P] :
    Integrable (fun ω => ‖V ω‖) P ∧ (∫ ω, ‖V ω‖ ∂P) ≤ c := by
  have hpt (ω : Ω) : ‖V ω‖ ≤ (‖V ω‖ ^ 2 + c ^ 2) / (2 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (‖V ω‖ - c)]
  have hbi : Integrable (fun ω => (‖V ω‖ ^ 2 + c ^ 2) / (2 * c)) P :=
    (hV2.add (integrable_const _)).div_const _
  have hi : Integrable (fun ω => ‖V ω‖) P :=
    hbi.mono' hV.norm (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hpt ω)
  refine ⟨hi, ?_⟩
  calc (∫ ω, ‖V ω‖ ∂P) ≤ ∫ ω, (‖V ω‖ ^ 2 + c ^ 2) / (2 * c) ∂P :=
        integral_mono hi hbi hpt
    _ = ((∫ ω, ‖V ω‖ ^ 2 ∂P) + c ^ 2) / (2 * c) := by
        rw [integral_div, integral_add hV2 (integrable_const _), integral_const, probReal_univ,
          one_smul]
    _ ≤ c := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma centered_second_moment_le {Z : Ω → E} (hZi : Integrable Z P)
    (hZ2 : Integrable (fun ω => ‖Z ω‖ ^ 2) P) :
    Integrable (fun ω => ‖Z ω - ∫ ω', Z ω' ∂P‖ ^ 2) P ∧
      (∫ ω, ‖Z ω - ∫ ω', Z ω' ∂P‖ ^ 2 ∂P) ≤ ∫ ω, ‖Z ω‖ ^ 2 ∂P := by
  set m := ∫ ω', Z ω' ∂P
  have hexp (ω : Ω) : ‖Z ω - m‖ ^ 2 = ‖Z ω‖ ^ 2 - 2 * ⟪Z ω, m⟫ + ‖m‖ ^ 2 := by
    rw [@norm_sub_sq_real]
  have hin : Integrable (fun ω => ⟪Z ω, m⟫) P := hZi.inner_const m
  have hint : Integrable (fun ω => ‖Z ω‖ ^ 2 - 2 * ⟪Z ω, m⟫ + ‖m‖ ^ 2) P :=
    (hZ2.sub (hin.const_mul 2)).add (integrable_const _)
  have he : (fun ω => ‖Z ω - m‖ ^ 2) = fun ω => ‖Z ω‖ ^ 2 - 2 * ⟪Z ω, m⟫ + ‖m‖ ^ 2 := by
    funext ω; exact hexp ω
  refine ⟨he ▸ hint, ?_⟩
  have h1 : Integrable (fun ω => ‖Z ω‖ ^ 2 - 2 * ⟪Z ω, m⟫) P := hZ2.sub (hin.const_mul 2)
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp),
    integral_add h1 (integrable_const _),
    integral_sub hZ2 (hin.const_mul 2), integral_const_mul, integral_const, probReal_univ,
    one_smul]
  have hm : (∫ ω, ⟪Z ω, m⟫ ∂P) = ‖m‖ ^ 2 := by
    have h2 : (∫ ω, ⟪Z ω, m⟫ ∂P) = ⟪m, ∫ ω, Z ω ∂P⟫ := by
      rw [← integral_inner hZi m]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => real_inner_comm _ _)
    rw [h2, real_inner_self_eq_norm_sq]
  rw [hm]
  nlinarith [sq_nonneg ‖m‖]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma tail_part_le {Y : Ω → E} {p τ : ℝ} (hp1 : 1 < p) (hτ : 0 < τ) (ω : Ω) :
    ‖(if ‖Y ω‖ ≤ τ then (0 : E) else Y ω)‖ ≤ ‖Y ω‖ ^ p / τ ^ (p - 1) := by
  by_cases h : ‖Y ω‖ ≤ τ
  · rw [ite_eq_left h, norm_zero]; positivity
  · rw [ite_eq_right h]
    push Not at h
    have hy : 0 < ‖Y ω‖ := hτ.trans h
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hτ _)]
    have h1 : τ ^ (p - 1) ≤ ‖Y ω‖ ^ (p - 1) :=
      Real.rpow_le_rpow hτ.le h.le (by linarith)
    have h2 : ‖Y ω‖ ^ p = ‖Y ω‖ * ‖Y ω‖ ^ (p - 1) := by
      rw [← Real.rpow_one_add' hy.le (by linarith)]
      congr 1; ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 hy.le

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma head_part_sq_le {Y : Ω → E} {p τ : ℝ} (hp2 : p ≤ 2) (hτ : 0 < τ) (ω : Ω) :
    ‖(if ‖Y ω‖ ≤ τ then Y ω else 0)‖ ^ 2 ≤ τ ^ (2 - p) * ‖Y ω‖ ^ p := by
  by_cases h : ‖Y ω‖ ≤ τ
  · rw [ite_eq_left h]
    have hy := norm_nonneg (Y ω)
    rcases hy.eq_or_lt with h0 | h0
    · rw [← h0]
      have : (0 : ℝ) ^ (2 : ℕ) = 0 := by norm_num
      rw [this]
      positivity
    · have h1 : ‖Y ω‖ ^ (2 - p) ≤ τ ^ (2 - p) := Real.rpow_le_rpow hy h (by linarith)
      have h2 : ‖Y ω‖ ^ (2 : ℕ) = ‖Y ω‖ ^ (2 - p) * ‖Y ω‖ ^ p := by
        rw [← Real.rpow_add h0, ← Real.rpow_natCast]
        congr 1; push_cast; ring
      rw [h2]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · rw [ite_eq_right h, norm_zero]
    have : (0 : ℝ) ^ (2 : ℕ) = 0 := by norm_num
    rw [this]
    positivity

lemma block_mean_truncated {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P) (u : E)
    (hmean : (∫ ω, X ω ∂P) = u) {p σ τ c : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (hτ : 0 < τ)
    (hc : 0 < c)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P) (hmom : (∫ ω, ‖X ω - u‖ ^ p ∂P) ≤ σ ^ p)
    (n : ℕ) (hn : 0 < n) (hcτ : τ ^ (2 - p) * σ ^ p / n ≤ c ^ 2) :
    Integrable (fun ζ : Fin n → Ω => ‖(1 / (n : ℝ)) • ∑ i, X (ζ i) - u‖)
        (Measure.pi fun _ : Fin n => P) ∧
      (∫ ζ, ‖(1 / (n : ℝ)) • ∑ i, X (ζ i) - u‖ ∂(Measure.pi fun _ : Fin n => P)) ≤
        c + 2 * (σ ^ p / τ ^ (p - 1)) := by
  classical
  set Q := Measure.pi fun _ : Fin n => P
  let Y : Ω → E := fun ω => X ω - u
  let Z : Ω → E := fun ω => if ‖Y ω‖ ≤ τ then Y ω else 0
  let W : Ω → E := fun ω => if ‖Y ω‖ ≤ τ then 0 else Y ω
  have hYm : Measurable Y := hX.sub measurable_const
  have hset : MeasurableSet {ω | ‖Y ω‖ ≤ τ} := measurableSet_le hYm.norm measurable_const
  have hZm : Measurable Z := Measurable.ite hset hYm measurable_const
  have hWm : Measurable W := Measurable.ite hset measurable_const hYm
  have hYi : Integrable Y P := hXi.sub (integrable_const u)
  have hsplit (ω : Ω) : Y ω = Z ω + W ω := by
    simp only [Z, W]; split_ifs <;> simp
  have hWpt (ω : Ω) : ‖W ω‖ ≤ ‖Y ω‖ ^ p / τ ^ (p - 1) := tail_part_le (Y := Y) hp1 hτ ω
  have hZpt (ω : Ω) : ‖Z ω‖ ^ 2 ≤ τ ^ (2 - p) * ‖Y ω‖ ^ p := head_part_sq_le (Y := Y) hp2 hτ ω
  have hWni : Integrable (fun ω => ‖W ω‖) P :=
    (hpi.div_const _).mono' hWm.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hWpt ω)
  have hWi : Integrable W P := (integrable_norm_iff hWm.aestronglyMeasurable).mp hWni
  have hZi : Integrable Z P := by
    have : Z = fun ω => Y ω - W ω := by funext ω; rw [hsplit ω]; abel
    rw [this]; exact hYi.sub hWi
  have hZ2 : Integrable (fun ω => ‖Z ω‖ ^ 2) P :=
    (hpi.const_mul (τ ^ (2 - p))).mono' (hZm.norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hZpt ω)
  have hWint : (∫ ω, ‖W ω‖ ∂P) ≤ σ ^ p / τ ^ (p - 1) := by
    calc (∫ ω, ‖W ω‖ ∂P) ≤ ∫ ω, ‖Y ω‖ ^ p / τ ^ (p - 1) ∂P :=
          integral_mono hWni (hpi.div_const _) hWpt
      _ = (∫ ω, ‖Y ω‖ ^ p ∂P) / τ ^ (p - 1) := integral_div _ _
      _ ≤ σ ^ p / τ ^ (p - 1) :=
          div_le_div_of_nonneg_right hmom (Real.rpow_pos_of_pos hτ _).le
  set mZ := ∫ ω, Z ω ∂P with hmZ
  have hmZW : ‖mZ‖ ≤ σ ^ p / τ ^ (p - 1) := by
    have hY0 : (∫ ω, Y ω ∂P) = 0 := by
      simp only [Y]; rw [integral_sub hXi (integrable_const u), hmean, integral_const,
        probReal_univ, one_smul, sub_self]
    have : mZ = -(∫ ω, W ω ∂P) := by
      have h1 : (∫ ω, Y ω ∂P) = mZ + ∫ ω, W ω ∂P := by
        rw [hmZ, ← integral_add hZi hWi]
        exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
      rw [hY0] at h1
      exact eq_neg_of_add_eq_zero_left h1.symm
    rw [this, norm_neg]
    exact (norm_integral_le_integral_norm _).trans hWint
  have hvar := centered_second_moment_le hZi hZ2
  have hmv := OracleTemplate.RobustGradient.finite_mean_variance (P := P) hZm hZi mZ hvar.1
    rfl n hn
  have hZbound : (∫ ω, ‖Z ω - mZ‖ ^ 2 ∂P) / n ≤ c ^ 2 := by
    have h1 : (∫ ω, ‖Z ω‖ ^ 2 ∂P) ≤ τ ^ (2 - p) * σ ^ p := by
      calc (∫ ω, ‖Z ω‖ ^ 2 ∂P) ≤ ∫ ω, τ ^ (2 - p) * ‖Y ω‖ ^ p ∂P :=
            integral_mono hZ2 (hpi.const_mul _) hZpt
        _ = τ ^ (2 - p) * ∫ ω, ‖Y ω‖ ^ p ∂P := integral_const_mul _ _
        _ ≤ τ ^ (2 - p) * σ ^ p :=
            mul_le_mul_of_nonneg_left hmom (Real.rpow_nonneg hτ.le _)
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc (∫ ω, ‖Z ω - mZ‖ ^ 2 ∂P) / n ≤ (τ ^ (2 - p) * σ ^ p) / n :=
          div_le_div_of_nonneg_right (hvar.2.trans h1) hn'.le
      _ ≤ c ^ 2 := hcτ
  have hZmean := integral_norm_le_of_sq (P := Q)
    (V := fun ζ : Fin n → Ω => (1 / (n : ℝ)) • ∑ i, Z (ζ i) - mZ)
    (by
      apply Measurable.aestronglyMeasurable
      exact ((Finset.measurable_sum _ fun i _ => hZm.comp (measurable_pi_apply i)).const_smul
        _).sub_const _)
    hmv.1 hc (by rw [hmv.2]; exact hZbound)
  have hWsum : ∀ i : Fin n, Integrable (fun ζ : Fin n → Ω => ‖W (ζ i)‖) Q := fun i =>
    ((measurePreserving_eval (fun _ : Fin n => P) i).integrable_comp
      hWni.aestronglyMeasurable).mpr hWni
  have hWint_i : ∀ i : Fin n, (∫ ζ, ‖W (ζ i)‖ ∂Q) = ∫ ω, ‖W ω‖ ∂P := fun i =>
    (measurePreserving_eval (fun _ : Fin n => P) i).hasLaw.integral_comp
      (f := fun ω => ‖W ω‖) hWni.aestronglyMeasurable
  have hWmean_i : Integrable (fun ζ : Fin n → Ω => (1 / (n : ℝ)) * ∑ i, ‖W (ζ i)‖) Q :=
    (integrable_finsetSum _ fun i _ => hWsum i).const_mul _
  have hpt (ζ : Fin n → Ω) : ‖(1 / (n : ℝ)) • ∑ i, X (ζ i) - u‖ ≤
      ‖(1 / (n : ℝ)) • ∑ i, Z (ζ i) - mZ‖ + ‖mZ‖ + (1 / (n : ℝ)) * ∑ i, ‖W (ζ i)‖ := by
    have he : (1 / (n : ℝ)) • ∑ i, X (ζ i) - u =
        ((1 / (n : ℝ)) • ∑ i, Z (ζ i) - mZ) + mZ + (1 / (n : ℝ)) • ∑ i, W (ζ i) := by
      rw [OracleTemplate.RobustGradient.finite_mean_centered u n hn]
      have : ∀ i, X (ζ i) - u = Z (ζ i) + W (ζ i) := fun i => hsplit (ζ i)
      simp only [this, Finset.sum_add_distrib, smul_add]
      abel
    rw [he]
    have hn' : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
    refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) ?_)
    rw [norm_smul, Real.norm_of_nonneg hn']
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hn'
  have hRi : Integrable (fun ζ : Fin n → Ω =>
      ‖(1 / (n : ℝ)) • ∑ i, Z (ζ i) - mZ‖ + ‖mZ‖ + (1 / (n : ℝ)) * ∑ i, ‖W (ζ i)‖) Q :=
    (hZmean.1.add (integrable_const _)).add hWmean_i
  have hLm : Measurable (fun ζ : Fin n → Ω => ‖(1 / (n : ℝ)) • ∑ i, X (ζ i) - u‖) :=
    (((Finset.measurable_sum _ fun i _ => hX.comp (measurable_pi_apply i)).const_smul _).sub_const
      _).norm
  have hLi : Integrable (fun ζ : Fin n → Ω => ‖(1 / (n : ℝ)) • ∑ i, X (ζ i) - u‖) Q :=
    hRi.mono' hLm.aestronglyMeasurable (Filter.Eventually.of_forall fun ζ => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hpt ζ)
  refine ⟨hLi, ?_⟩
  have hWm_int : (∫ ζ, (1 / (n : ℝ)) * ∑ i, ‖W (ζ i)‖ ∂Q) = ∫ ω, ‖W ω‖ ∂P := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ => hWsum i]
    simp only [hWint_i, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  calc (∫ ζ, ‖(1 / (n : ℝ)) • ∑ i, X (ζ i) - u‖ ∂Q)
      ≤ ∫ ζ, (‖(1 / (n : ℝ)) • ∑ i, Z (ζ i) - mZ‖ + ‖mZ‖ +
          (1 / (n : ℝ)) * ∑ i, ‖W (ζ i)‖) ∂Q := integral_mono hLi hRi hpt
    _ = (∫ ζ, ‖(1 / (n : ℝ)) • ∑ i, Z (ζ i) - mZ‖ ∂Q) + ‖mZ‖ + ∫ ω, ‖W ω‖ ∂P := by
        have hA : Integrable (fun ζ : Fin n → Ω => ‖(1 / (n : ℝ)) • ∑ i, Z (ζ i) - mZ‖ + ‖mZ‖) Q :=
          hZmean.1.add (integrable_const _)
        rw [integral_add hA hWmean_i, integral_add hZmean.1 (integrable_const _), integral_const,
          probReal_univ, one_smul, hWm_int]
    _ ≤ c + 2 * (σ ^ p / τ ^ (p - 1)) := by linarith [hZmean.2]

lemma truncation_scale {p σ : ℝ} (hp1 : 1 < p) (hσ : 0 < σ) {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) ^ (1 / p) * σ) ^ (2 - p) * σ ^ p / n = (σ / (n : ℝ) ^ ((p - 1) / p)) ^ 2 ∧
      σ ^ p / ((n : ℝ) ^ (1 / p) * σ) ^ (p - 1) = σ / (n : ℝ) ^ ((p - 1) / p) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp0 : 0 < p := by linarith
  set a := (n : ℝ) ^ (1 / p) with ha
  have ha0 : 0 < a := Real.rpow_pos_of_pos hn' _
  have hna : (n : ℝ) = a ^ p := by
    rw [ha, ← Real.rpow_mul hn'.le, one_div_mul_cancel hp0.ne', Real.rpow_one]
  have hnA : (n : ℝ) ^ ((p - 1) / p) = a ^ (p - 1) := by
    rw [ha, ← Real.rpow_mul hn'.le]; congr 1; field_simp
  set A := a ^ (p - 1) with hA
  set S := σ ^ (p - 1) with hS
  have hA0 : 0 < A := Real.rpow_pos_of_pos ha0 _
  have hS0 : 0 < S := Real.rpow_pos_of_pos hσ _
  have hap : a ^ p = A * a := by
    rw [hA, ← Real.rpow_add_one ha0.ne']; congr 1; ring
  have ha2 : a ^ (2 - p) = a / A := by
    rw [hA, show 2 - p = 1 - (p - 1) by ring, Real.rpow_sub ha0, Real.rpow_one]
  have hσp : σ ^ p = S * σ := by
    rw [hS, ← Real.rpow_add_one hσ.ne']; congr 1; ring
  have hσ2 : σ ^ (2 - p) = σ / S := by
    rw [hS, show 2 - p = 1 - (p - 1) by ring, Real.rpow_sub hσ, Real.rpow_one]
  have hmul2 : (a * σ) ^ (2 - p) = a / A * (σ / S) := by
    rw [Real.mul_rpow ha0.le hσ.le, ha2, hσ2]
  have hmul1 : (a * σ) ^ (p - 1) = A * S := by
    rw [Real.mul_rpow ha0.le hσ.le]
  rw [hnA]
  constructor
  · rw [hmul2, hσp, hna, hap]
    field_simp
  · rw [hmul1, hσp]
    field_simp

lemma block_mean_first_moment {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P) (u : E)
    (hmean : (∫ ω, X ω ∂P) = u) {p σ : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2) (hσ : 0 ≤ σ)
    (hpi : Integrable (fun ω => ‖X ω - u‖ ^ p) P) (hmom : (∫ ω, ‖X ω - u‖ ^ p ∂P) ≤ σ ^ p)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun ζ : Fin n → Ω => ‖(1 / (n : ℝ)) • ∑ i, X (ζ i) - u‖)
        (Measure.pi fun _ : Fin n => P) ∧
      (∫ ζ, ‖(1 / (n : ℝ)) • ∑ i, X (ζ i) - u‖ ∂(Measure.pi fun _ : Fin n => P)) ≤
        3 * σ / (n : ℝ) ^ ((p - 1) / p) := by
  rcases hσ.eq_or_lt with h0 | hσ0
  · subst h0
    have hz : (0 : ℝ) ^ p = 0 := Real.zero_rpow (by linarith)
    have hint := (block_mean_truncated hX hXi u hmean hp1 hp2 one_pos one_pos hpi hmom n hn
      (by rw [hz]; simp)).1
    refine ⟨hint, ?_⟩
    rw [mul_zero, zero_div]
    apply le_of_forall_pos_le_add
    intro η hη
    have h := (block_mean_truncated hX hXi u hmean hp1 hp2 one_pos hη hpi hmom n hn
      (by rw [hz]; simp; positivity)).2
    rw [hz, zero_div, mul_zero, add_zero] at h
    linarith
  · obtain ⟨h1, h2⟩ := truncation_scale hp1 hσ0 hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hτ : 0 < (n : ℝ) ^ (1 / p) * σ := by positivity
    have hc : 0 < σ / (n : ℝ) ^ ((p - 1) / p) := by positivity
    have h := block_mean_truncated hX hXi u hmean hp1 hp2 hτ hc hpi hmom n hn h1.le
    rw [h2] at h
    refine ⟨h.1, h.2.trans_eq ?_⟩
    ring

variable {X : Ω → E}

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma medoid_estimate (hX : Measurable X) (u : E) {α : ℝ} (hα : 0 < α)
    (hXi : Integrable (fun ω => ‖X ω - u‖) P) (hM : (∫ ω, ‖X ω - u‖ ∂P) ≤ α / 1536)
    (K : ℕ) (hK : 3 ≤ K) :
    (Measure.pi fun _ : Fin (2 * K + 1 + 1) => P).real
        {ξ | α < ‖OracleTemplate.MultiplicativeRobustEstimator.medoid (fun i => X (ξ i)) - u‖} ≤
        (1 / 2) ^ (2 * K + 2) ∧
      Integrable (fun ξ : Fin (2 * K + 1 + 1) → Ω =>
        {ξ | α < ‖OracleTemplate.MultiplicativeRobustEstimator.medoid (fun i => X (ξ i)) - u‖}.indicator
          (fun ξ => ‖OracleTemplate.MultiplicativeRobustEstimator.medoid (fun i => X (ξ i)) - u‖) ξ)
        (Measure.pi fun _ : Fin (2 * K + 1 + 1) => P) ∧
      (∫ ξ, {ξ | α < ‖OracleTemplate.MultiplicativeRobustEstimator.medoid (fun i => X (ξ i)) - u‖}.indicator
          (fun ξ => ‖OracleTemplate.MultiplicativeRobustEstimator.medoid (fun i => X (ξ i)) - u‖) ξ
          ∂(Measure.pi fun _ : Fin (2 * K + 1 + 1) => P)) ≤ α / 22 * (1 / 2) ^ (K + 1) := by
  set Q := Measure.pi fun _ : Fin (2 * K + 1 + 1) => P
  set D : (Fin (2 * K + 1 + 1) → Ω) → ℝ := fun ξ =>
    ‖OracleTemplate.MultiplicativeRobustEstimator.medoid (fun i => X (ξ i)) - u‖ with hD
  set A := {ξ : Fin (2 * K + 1 + 1) → Ω | α < D ξ} with hA
  have hmark : P.real {ω | α / 6 < ‖X ω - u‖} ≤ 1 / 256 := by
    have hr : 0 < α / 6 := by positivity
    have h := (hXi.div_const (α / 6)).measure_le_integral
      (Filter.Eventually.of_forall (fun ω => div_nonneg (norm_nonneg _) hr.le))
      (s := {ω | α / 6 < ‖X ω - u‖}) (fun ω hω => (one_le_div hr).mpr hω.le)
    have hb : P {ω | α / 6 < ‖X ω - u‖} ≤ ENNReal.ofReal (1 / 256 : ℝ) := by
      apply h.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [integral_div]
      apply (div_le_iff₀ hr).mpr
      linarith
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 256)] using ht
  have hfail := OracleTemplate.MultiplicativeRobustEstimator.medoid_failure_probability (P := P)
    hX u (by positivity : (0 : ℝ) ≤ α / 6) hmark (2 * K + 1)
  have hθ : Q.real A ≤ (1 / 2) ^ (2 * K + 2) := by
    have h6 : 6 * (α / 6) = α := by ring
    rw [h6] at hfail
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfail
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    exact ht
  have hsec := OracleTemplate.MultiplicativeRobustEstimator.medoid_second_moment (P := P) hX u hXi
    (2 * K + 1) (by omega)
  have hDm : Measurable D := by
    simp only [hD]
    exact ((OracleTemplate.MultiplicativeRobustEstimator.measurable_medoid.comp
      (Measurable.of_eval fun i => hX.comp (measurable_pi_apply i))).sub_const u).norm
  have hAm : MeasurableSet A := measurableSet_lt measurable_const hDm
  set M := α / 1536 with hMdef
  set lam := 68 * M * 2 ^ (K + 1) with hlam
  have hlam0 : 0 < lam := by positivity
  have hpt (ξ : Fin (2 * K + 1 + 1) → Ω) :
      A.indicator D ξ ≤ D ξ ^ 2 / (2 * lam) + lam / 2 * A.indicator (fun _ => (1 : ℝ)) ξ := by
    by_cases h : ξ ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (D ξ - lam)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero, add_zero]
      positivity
  have hind1 : Integrable (A.indicator (fun _ => (1 : ℝ))) Q :=
    (integrable_const (1 : ℝ)).indicator hAm
  have hrhs : Integrable (fun ξ => D ξ ^ 2 / (2 * lam) + lam / 2 * A.indicator (fun _ => (1 : ℝ)) ξ)
      Q := (hsec.1.div_const _).add (hind1.const_mul _)
  have hDi : Integrable (A.indicator D) Q := by
    refine hrhs.mono' (hDm.indicator hAm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ => norm_nonneg _) ξ)]
    exact hpt ξ
  refine ⟨hθ, hDi, ?_⟩
  calc (∫ ξ, A.indicator D ξ ∂Q)
      ≤ ∫ ξ, (D ξ ^ 2 / (2 * lam) + lam / 2 * A.indicator (fun _ => (1 : ℝ)) ξ) ∂Q :=
        integral_mono hDi hrhs hpt
    _ = (∫ ξ, D ξ ^ 2 ∂Q) / (2 * lam) + lam / 2 * Q.real A := by
        rw [integral_add (hsec.1.div_const _) (hind1.const_mul _), integral_div, integral_const_mul,
          integral_indicator_const _ hAm, smul_eq_mul, mul_one]
    _ ≤ 4608 * M ^ 2 / (2 * lam) + lam / 2 * (1 / 2) ^ (2 * K + 2) := by
        gcongr
        · exact hsec.2.trans (by gcongr)
    _ ≤ α / 22 * (1 / 2) ^ (K + 1) := by
        set y : ℝ := (1 / 2) ^ (K + 1) with hy
        have hy0 : 0 < y := by positivity
        have hp2 : ((1 : ℝ) / 2) ^ (2 * K + 2) = y * y := by
          rw [hy, ← pow_add]; congr 1; ring
        have h2y : (2 : ℝ) ^ (K + 1) = 1 / y := by
          rw [hy, eq_div_iff hy0.ne', ← mul_pow]; norm_num
        have hM0 : 0 < M := by rw [hMdef]; positivity
        have hlam' : lam = 68 * M / y := by rw [hlam, h2y]; ring
        rw [hp2, hlam']
        have e1 : 4608 * M ^ 2 / (2 * (68 * M / y)) = 4608 / 136 * M * y := by
          field_simp; ring
        have e2 : 68 * M / y / 2 * (y * y) = 34 * M * y := by
          field_simp; ring
        rw [e1, e2, hMdef]
        nlinarith [mul_pos hα hy0]

end LongTails.Proofs.StochasticEllSmoothEstimator
