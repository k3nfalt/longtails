import LongTails.Proofs.DistributedNormalizedAdaptive

open MeasureTheory

namespace LongTails.Proofs.DistributedNormalizedDrift

open LongTails.Setups.DistributedHessianLipschitzNonconvex
open DistributedNormalizedAdaptive

noncomputable def disagreement (p : Params) (G : Point p → Point p) (s : State p) : Point p :=
  (p.n : ℝ)⁻¹ • ∑ i, (G (s.2 i) - G s.1)

noncomputable def traceError (p : Params) (s : State p) : ℝ :=
  (p.n : ℝ)⁻¹ * ∑ i, ‖workerError p i s‖ ^ 2

lemma measurable_disagreement (p : Params) (G : Point p → Point p) (hG : Measurable G) :
    Measurable (disagreement p G) := by
  apply Measurable.fun_const_smul
  apply Finset.measurable_sum
  intro i _
  exact (hG.comp ((measurable_pi_apply i).comp measurable_snd)).sub (hG.comp measurable_fst)

lemma measurable_traceError (p : Params) : Measurable (traceError p) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact (measurable_workerError p i).norm.pow_const 2

lemma disagreement_taylor (p : Params) (G : Point p → Point p) (s : State p)
    {L Q : ℝ} (hL : 0 ≤ L) (hQ : 0 ≤ Q) (hdiff : Differentiable ℝ G)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hH : ∀ x y, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ Q * ‖x - y‖) :
    ‖disagreement p G s‖ ≤ L * ‖meanError p s‖ + Q * traceError p s := by
  have hnorm : ‖fderiv ℝ G s.1‖ ≤ L :=
    norm_fderiv_le_of_lip' ℝ hL (Filter.Eventually.of_forall fun x => hlip x s.1)
  have hA (v : Point p) : ‖fderiv ℝ G s.1 v‖ ≤ L * ‖v‖ :=
    ((fderiv ℝ G s.1).le_opNorm v).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg v))
  have ht := DistributedNormalizedConsensus.finite_gradient_linearization_bound
    G s.1 (fun i : Fin p.n => workerError p i s) (a := (p.n : ℝ)⁻¹) (by positivity) hQ hdiff hH hA
  have he (i : Fin p.n) : s.1 + workerError p i s = s.2 i := by unfold workerError; abel
  simp_rw [he] at ht
  convert ht using 1 <;> simp only [disagreement, meanError, traceError, workerError]
  ring

lemma disagreement_lipschitz (p : Params) (G : Point p → Point p) (s : State p)
    {L : ℝ} (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) :
    ‖disagreement p G s‖ ≤ (p.n : ℝ)⁻¹ * L * ∑ i, ‖workerError p i s‖ := by
  unfold disagreement
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (p.n : ℝ)⁻¹ * ∑ i, ‖G (s.2 i) - G s.1‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (p.n : ℝ)⁻¹ * ∑ i, L * ‖workerError p i s‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hlip (s.2 i) s.1) (by positivity)
    _ = _ := by rw [← Finset.mul_sum]; ring

attribute [local irreducible] disagreement traceError meanError workerError

set_option maxHeartbeats 800000 in
lemma expected_disagreement_taylor {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P] (p : Params) (G : Point p → Point p) (X : Z → State p)
    (hX : Measurable X) {L Q M V : ℝ} (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hdiff : Differentiable ℝ G) (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hH : ∀ x y, ‖fderiv ℝ G x - fderiv ℝ G y‖ ≤ Q * ‖x - y‖)
    (hB2 : Integrable (fun z => ‖meanError p (X z)‖ ^ 2) P)
    (hM : (∫ z, ‖meanError p (X z)‖ ^ 2 ∂P) ≤ M)
    (hE2 : ∀ i, Integrable (fun z => ‖workerError p i (X z)‖ ^ 2) P)
    (hV : ∀ i, (∫ z, ‖workerError p i (X z)‖ ^ 2 ∂P) ≤ V) :
    Integrable (fun z => ‖disagreement p G (X z)‖) P ∧
      (∫ z, ‖disagreement p G (X z)‖ ∂P) ≤ L * Real.sqrt M + Q * V := by
  have hGc : LipschitzWith ⟨L, hL⟩ G := lipschitzWith_iff_norm_sub_le.mpr hlip
  have hRm : Measurable (fun z => disagreement p G (X z)) :=
    (measurable_disagreement p G hGc.continuous.measurable).comp hX
  have hBm : Measurable (fun z => meanError p (X z)) := (measurable_meanError p).comp hX
  have hBi : Integrable (fun z => ‖meanError p (X z)‖) P :=
    (((memLp_two_iff_integrable_sq_norm hBm.aestronglyMeasurable).mpr hB2).integrable (by norm_num)).norm
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hE2 i)
  have hTi : Integrable (fun z => traceError p (X z)) P := by
    simpa only [traceError] using hsum.const_mul (p.n : ℝ)⁻¹
  have hTv : (∫ z, traceError p (X z) ∂P) ≤ V := by
    simp only [traceError]
    rw [integral_const_mul, integral_finsetSum _ (fun i _ => hE2 i)]
    calc
      _ ≤ (p.n : ℝ)⁻¹ * ∑ _i : Fin p.n, V :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hV i) (by positivity)
      _ = V := by
        have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
  have hbound : Integrable (fun z => L * ‖meanError p (X z)‖ + Q * traceError p (X z)) P :=
    (hBi.const_mul L).add (hTi.const_mul Q)
  have hp (z : Z) : ‖disagreement p G (X z)‖ ≤ L * ‖meanError p (X z)‖ + Q * traceError p (X z) :=
    disagreement_taylor p G (X z) hL hQ hdiff hlip hH
  have hRi : Integrable (fun z => ‖disagreement p G (X z)‖) P :=
    hbound.mono' hRm.norm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      simpa only [norm_norm] using hp z)
  have hb := integral_mono hRi hbound hp
  rw [integral_add (hBi.const_mul L) (hTi.const_mul Q), integral_const_mul, integral_const_mul] at hb
  have hm : (∫ z, ‖meanError p (X z)‖ ∂P) ≤ Real.sqrt M :=
    (OracleTemplate.NormalizedStorm.integral_norm_le_sqrt hBm.aestronglyMeasurable hB2).trans
      (Real.sqrt_le_sqrt hM)
  exact ⟨hRi, hb.trans (add_le_add (mul_le_mul_of_nonneg_left hm hL)
    (mul_le_mul_of_nonneg_left hTv hQ))⟩

set_option maxHeartbeats 800000 in
lemma expected_disagreement_lipschitz {Z : Type*} [MeasurableSpace Z] (P : Measure Z)
    [IsProbabilityMeasure P] (p : Params) (G : Point p → Point p) (X : Z → State p)
    (hX : Measurable X) {L V : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖)
    (hE2 : ∀ i, Integrable (fun z => ‖workerError p i (X z)‖ ^ 2) P)
    (hV : ∀ i, (∫ z, ‖workerError p i (X z)‖ ^ 2 ∂P) ≤ V) :
    Integrable (fun z => ‖disagreement p G (X z)‖) P ∧
      (∫ z, ‖disagreement p G (X z)‖ ∂P) ≤ L * Real.sqrt V := by
  have hGc : LipschitzWith ⟨L, hL⟩ G := lipschitzWith_iff_norm_sub_le.mpr hlip
  have hRm : Measurable (fun z => disagreement p G (X z)) :=
    (measurable_disagreement p G hGc.continuous.measurable).comp hX
  have hEm (i : Fin p.n) : Measurable (fun z => workerError p i (X z)) :=
    (measurable_workerError p i).comp hX
  have hEi (i : Fin p.n) : Integrable (fun z => ‖workerError p i (X z)‖) P :=
    (((memLp_two_iff_integrable_sq_norm (hEm i).aestronglyMeasurable).mpr (hE2 i)).integrable (by norm_num)).norm
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hEi i)
  have hbound : Integrable (fun z => (p.n : ℝ)⁻¹ * L * ∑ i, ‖workerError p i (X z)‖) P :=
    hsum.const_mul ((p.n : ℝ)⁻¹ * L)
  have hp (z : Z) := disagreement_lipschitz p G (X z) hlip
  have hRi : Integrable (fun z => ‖disagreement p G (X z)‖) P :=
    hbound.mono' hRm.norm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      simpa only [norm_norm] using hp z)
  refine ⟨hRi, ?_⟩
  have hb := integral_mono hRi hbound hp
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hEi i)] at hb
  apply hb.trans
  have he (i : Fin p.n) : (∫ z, ‖workerError p i (X z)‖ ∂P) ≤ Real.sqrt V :=
    (OracleTemplate.NormalizedStorm.integral_norm_le_sqrt (hEm i).aestronglyMeasurable (hE2 i)).trans
      (Real.sqrt_le_sqrt (hV i))
  calc
    _ ≤ (p.n : ℝ)⁻¹ * L * ∑ _i : Fin p.n, Real.sqrt V :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => he i) (mul_nonneg (by positivity) hL)
    _ = L * Real.sqrt V := by
      have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

lemma average_gradient_square (p : Params) (G : Point p → Point p) (s : State p)
    {L : ℝ} (hL : 0 ≤ L) (hlip : ∀ x y, ‖G x - G y‖ ≤ L * ‖x - y‖) :
    (p.n : ℝ)⁻¹ * ∑ i, ‖G (s.2 i)‖ ^ 2 ≤
      2 * ‖G s.1‖ ^ 2 + 2 * L ^ 2 * traceError p s := by
  have hp (i : Fin p.n) : ‖G (s.2 i)‖ ^ 2 ≤
      2 * ‖G s.1‖ ^ 2 + 2 * L ^ 2 * ‖workerError p i s‖ ^ 2 := by
    have he : ‖G (s.2 i)‖ ≤ ‖G s.1‖ + L * ‖workerError p i s‖ := by
      have ht := norm_le_norm_add_norm_sub (G s.1) (G (s.2 i))
      rw [norm_sub_rev (G s.1)] at ht
      have hh := hlip (s.2 i) s.1
      have hh' : ‖G (s.2 i) - G s.1‖ ≤ L * ‖workerError p i s‖ := by
        simpa only [workerError] using hh
      linarith
    have hn : 0 ≤ ‖G s.1‖ + L * ‖workerError p i s‖ := by positivity
    have hs := mul_self_le_mul_self (norm_nonneg _) he
    nlinarith [sq_nonneg (‖G s.1‖ - L * ‖workerError p i s‖)]
  calc
    _ ≤ (p.n : ℝ)⁻¹ * ∑ i, (2 * ‖G s.1‖ ^ 2 + 2 * L ^ 2 * ‖workerError p i s‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hp i) (by positivity)
    _ = _ := by
      have hn : (p.n : ℝ) ≠ 0 := by exact_mod_cast p.n.ne_zero
      simp only [traceError, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      field_simp

end LongTails.Proofs.DistributedNormalizedDrift
