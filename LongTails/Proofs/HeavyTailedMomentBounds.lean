import LongTails.Proofs.HeavyTailedSpectralGeometry
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedMomentBounds

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
lemma integrable_norm_add_rpow {e : Ω → E} (w : E) {p : ℝ} (hp : 0 < p)
    (he : AEStronglyMeasurable e P) (hep : Integrable (fun ω => ‖e ω‖ ^ p) P) :
    Integrable (fun ω => ‖w + e ω‖ ^ p) P := by
  have heLp : MemLp e (ENNReal.ofReal p) P := by
    apply (integrable_norm_rpow_iff he (by simp [hp]) (by simp)).mp
    simpa only [ENNReal.toReal_ofReal hp.le] using hep
  have h : MemLp (fun ω => w + e ω) (ENNReal.ofReal p) P :=
    (memLp_const w).add heLp
  simpa only [ENNReal.toReal_ofReal hp.le] using h.integrable_norm_rpow'

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
lemma integrable_norm_sum_rpow {w e : Ω → E} {p : ℝ} (hp : 0 < p)
    (hw : AEStronglyMeasurable w P) (he : AEStronglyMeasurable e P)
    (hwp : Integrable (fun ω => ‖w ω‖ ^ p) P)
    (hep : Integrable (fun ω => ‖e ω‖ ^ p) P) :
    Integrable (fun ω => ‖w ω + e ω‖ ^ p) P := by
  have hmem {f : Ω → E} (hf : AEStronglyMeasurable f P)
      (hfp : Integrable (fun ω => ‖f ω‖ ^ p) P) : MemLp f (ENNReal.ofReal p) P := by
    apply (integrable_norm_rpow_iff hf (by simp [hp]) (by simp)).mp
    simpa only [ENNReal.toReal_ofReal hp.le] using hfp
  have hh := ((hmem hw hwp).add (hmem he hep)).integrable_norm_rpow'
  simpa only [Pi.add_apply, ENNReal.toReal_ofReal hp.le] using hh

omit [CompleteSpace E] [IsProbabilityMeasure P] in
lemma moment_linear_term_integrable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {w e : Ω → E} {p : ℝ} (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hw : Measurable w) (he : Measurable e)
    (hwp : Integrable (fun ω => ‖w ω‖ ^ p) P)
    (hep : Integrable (fun ω => ‖e ω‖ ^ p) P) :
    Integrable (fun ω => p * ‖w ω‖ ^ (p - 1) * ⟪‖w ω‖⁻¹ • w ω, e ω⟫) P := by
  have hm : Measurable (fun ω => p * ‖w ω‖ ^ (p - 1) * ⟪‖w ω‖⁻¹ • w ω, e ω⟫) := by
    fun_prop
  apply ((hwp.add hep).const_mul 2).mono' hm.aestronglyMeasurable
  filter_upwards with ω
  exact HeavyTailedSpectralGeometry.moment_linear_term_bound (w ω) (e ω) hp hp2

omit [CompleteSpace E] [InnerProductSpace ℝ E] in
lemma integral_norm_le_root_moment {X : Ω → E} {p : ℝ} (hp : 1 < p)
    (hX : AEStronglyMeasurable X P) (hXp : Integrable (fun ω => ‖X ω‖ ^ p) P) :
    (∫ ω, ‖X ω‖ ∂P) ≤ (∫ ω, ‖X ω‖ ^ p ∂P) ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have hLp : MemLp X (ENNReal.ofReal p) P := by
    apply (integrable_norm_rpow_iff hX (by simp [hp0]) (by simp)).mp
    simpa only [ENNReal.toReal_ofReal hp0.le] using hXp
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (Real.HolderConjugate.conjExponent hp)
    (Filter.Eventually.of_forall (fun ω => norm_nonneg (X ω)))
    (Filter.Eventually.of_forall (fun _ : Ω => (zero_le_one : (0 : ℝ) ≤ 1)))
    hLp.norm (memLp_const (1 : ℝ))
  simpa using hh

lemma integral_norm_add_rpow_le {e : Ω → E} {w : E} {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2) (he : Integrable e P)
    (hep : Integrable (fun ω => ‖e ω‖ ^ p) P)
    (hmean : ∫ ω, e ω ∂P = 0) :
    (∫ ω, ‖w + e ω‖ ^ p ∂P) ≤ ‖w‖ ^ p + 6 * ∫ ω, ‖e ω‖ ^ p ∂P := by
  have hp0 : 0 < p := by linarith
  have hwp := integrable_norm_add_rpow w hp0 he.aestronglyMeasurable hep
  have hi : Integrable (fun ω => ⟪‖w‖⁻¹ • w, e ω⟫) P := he.const_inner _
  have hb := integral_mono hwp
    (((integrable_const (‖w‖ ^ p)).add (hi.const_mul (p * ‖w‖ ^ (p - 1)))).add
      (hep.const_mul 6))
    (fun ω => HeavyTailedSpectralGeometry.norm_add_rpow_le (w := w) (e := e ω) hp hp2)
  simp only [Pi.add_apply] at hb
  have hab : Integrable (fun ω => ‖w‖ ^ p + p * ‖w‖ ^ (p - 1) *
      ⟪‖w‖⁻¹ • w, e ω⟫) P := (integrable_const _).add (hi.const_mul _)
  rw [integral_add hab (hep.const_mul 6)] at hb
  have hc : Integrable (fun _ : Ω => ‖w‖ ^ p) P := integrable_const _
  rw [integral_add hc (hi.const_mul (p * ‖w‖ ^ (p - 1))), integral_const,
    integral_const_mul, integral_const_mul, integral_inner he, hmean,
    inner_zero_right] at hb
  simpa using hb

omit [CompleteSpace E] [IsProbabilityMeasure P] in
lemma integral_norm_random_add_rpow_le {w e : Ω → E} {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hw : Integrable (fun ω => ‖w ω‖ ^ p) P)
    (he : Integrable (fun ω => ‖e ω‖ ^ p) P)
    (hwe : Integrable (fun ω => ‖w ω + e ω‖ ^ p) P)
    (hi : Integrable (fun ω => p * ‖w ω‖ ^ (p - 1) *
      ⟪‖w ω‖⁻¹ • w ω, e ω⟫) P)
    (hz : (∫ ω, p * ‖w ω‖ ^ (p - 1) * ⟪‖w ω‖⁻¹ • w ω, e ω⟫ ∂P) = 0) :
    (∫ ω, ‖w ω + e ω‖ ^ p ∂P) ≤
      (∫ ω, ‖w ω‖ ^ p ∂P) + 6 * ∫ ω, ‖e ω‖ ^ p ∂P := by
  have hab : Integrable (fun ω => ‖w ω‖ ^ p + p * ‖w ω‖ ^ (p - 1) *
      ⟪‖w ω‖⁻¹ • w ω, e ω⟫) P := hw.add hi
  have hb := integral_mono hwe (hab.add (he.const_mul 6))
    (fun ω => HeavyTailedSpectralGeometry.norm_add_rpow_le hp hp2)
  simp only [Pi.add_apply] at hb
  rw [integral_add hab (he.const_mul 6), integral_add hw hi,
    integral_const_mul, hz, add_zero] at hb
  exact hb

lemma integral_predictable_inner_eq_zero {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {v e : Ω → E}
    (hv : AEStronglyMeasurable[m] v P) (he : Integrable e P)
    (hi : Integrable (fun ω => ⟪v ω, e ω⟫) P)
    (hz : P[e | m] =ᵐ[P] 0) :
    (∫ ω, ⟪v ω, e ω⟫ ∂P) = 0 := by
  have hc := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ) hv hi he
  rw [← integral_condExp (μ := P) hm (f := fun ω => ⟪v ω, e ω⟫)]
  calc
    _ = ∫ ω, ⟪v ω, P[e | m] ω⟫ ∂P := integral_congr_ae hc
    _ = ∫ _ : Ω, (0 : ℝ) ∂P := by
      apply integral_congr_ae
      filter_upwards [hz] with ω hω
      simp [hω]
    _ = 0 := by simp

omit [CompleteSpace E] [IsProbabilityMeasure P] in
lemma process_moment_bound {X e : ℕ → Ω → E} {p : ℝ}
    (hp : 1 ≤ p) (hp2 : p ≤ 2)
    (hX : ∀ k, Integrable (fun ω => ‖X k ω‖ ^ p) P)
    (he : ∀ k, Integrable (fun ω => ‖e k ω‖ ^ p) P)
    (hi : ∀ k, Integrable (fun ω => p * ‖X k ω‖ ^ (p - 1) *
      ⟪‖X k ω‖⁻¹ • X k ω, e k ω⟫) P)
    (hz : ∀ k, (∫ ω, p * ‖X k ω‖ ^ (p - 1) *
      ⟪‖X k ω‖⁻¹ • X k ω, e k ω⟫ ∂P) = 0)
    (hinit : ∀ ω, X 0 ω = 0)
    (hstep : ∀ k ω, X (k + 1) ω = X k ω + e k ω) (n : ℕ) :
    (∫ ω, ‖X n ω‖ ^ p ∂P) ≤ 6 * ∑ k ∈ Finset.range n, ∫ ω, ‖e k ω‖ ^ p ∂P := by
  induction n with
  | zero =>
      have hp0 : p ≠ 0 := by linarith
      simp [hinit, Real.zero_rpow hp0]
  | succ n ih =>
      have hnext : Integrable (fun ω => ‖X n ω + e n ω‖ ^ p) P := by
        simpa only [hstep] using hX (n + 1)
      have hb := integral_norm_random_add_rpow_le hp hp2 (hX n) (he n) hnext (hi n) (hz n)
      simp only [hstep] at ⊢
      rw [Finset.sum_range_succ]
      linarith

lemma martingale_difference_moment_bound [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {X e : ℕ → Ω → E} {p : ℝ}
    (hp : 1 < p) (hp2 : p ≤ 2) (m : ℕ → MeasurableSpace Ω)
    (hm : ∀ k, m k ≤ mΩ) (hX : ∀ k, @Measurable Ω E (m k) _ (X k))
    (he : ∀ k, Measurable (e k)) (hei : ∀ k, Integrable (e k) P)
    (hep : ∀ k, Integrable (fun ω => ‖e k ω‖ ^ p) P)
    (hzero : ∀ k, P[e k | m k] =ᵐ[P] 0)
    (hinit : ∀ ω, X 0 ω = 0)
    (hstep : ∀ k ω, X (k + 1) ω = X k ω + e k ω) (n : ℕ) :
    (∫ ω, ‖X n ω‖ ^ p ∂P) ≤ 6 * ∑ k ∈ Finset.range n, ∫ ω, ‖e k ω‖ ^ p ∂P := by
  have hXa (k : ℕ) : Measurable (X k) := (hX k).mono (hm k) le_rfl
  have hp0 : 0 < p := by linarith
  have hXp (k : ℕ) : Integrable (fun ω => ‖X k ω‖ ^ p) P := by
    induction k with
    | zero => simpa only [hinit, norm_zero, Real.zero_rpow hp0.ne'] using
        (integrable_const (0 : ℝ) : Integrable (fun _ : Ω => (0 : ℝ)) P)
    | succ k ih =>
        simpa only [hstep] using integrable_norm_sum_rpow hp0
          (hXa k).aestronglyMeasurable (he k).aestronglyMeasurable ih (hep k)
  have hlin (k : ℕ) := moment_linear_term_integrable hp.le hp2 (hXa k) (he k) (hXp k) (hep k)
  apply process_moment_bound hp.le hp2 hXp hep hlin _ hinit hstep n
  intro k
  let v : Ω → E := fun ω => (p * ‖X k ω‖ ^ (p - 1)) • (‖X k ω‖⁻¹ • X k ω)
  have hv : @Measurable Ω E (m k) _ v := by
    dsimp [v]
    fun_prop
  have hi : Integrable (fun ω => ⟪v ω, e k ω⟫) P := by
    simpa only [v, real_inner_smul_left] using hlin k
  have hh := integral_predictable_inner_eq_zero (hm k) hv.aestronglyMeasurable (hei k) hi (hzero k)
  simpa only [v, real_inner_smul_left] using hh

omit [IsProbabilityMeasure P] in
lemma predictable_indicator_centered {m : MeasurableSpace Ω} {A : Set Ω} {e : Ω → E}
    (hA : MeasurableSet[m] A) (he : Integrable e P) (hz : P[e | m] =ᵐ[P] 0) :
    P[A.indicator e | m] =ᵐ[P] 0 := by
  have hh := condExp_indicator he hA
  filter_upwards [hh, hz] with ω hω hzω
  rw [hω]
  by_cases hmem : ω ∈ A <;> simp [hmem, hzω]

omit [CompleteSpace E] [InnerProductSpace ℝ E] [IsProbabilityMeasure P] in
lemma norm_indicator_moment {A : Set Ω} {e : Ω → E} {p : ℝ}
    (hp : 0 < p) (hA : MeasurableSet A)
    (he : Integrable (fun ω => ‖e ω‖ ^ p) P) :
    Integrable (fun ω => ‖A.indicator e ω‖ ^ p) P ∧
      (∫ ω, ‖A.indicator e ω‖ ^ p ∂P) ≤ ∫ ω, ‖e ω‖ ^ p ∂P := by
  have heq : (fun ω => ‖A.indicator e ω‖ ^ p) = A.indicator (fun ω => ‖e ω‖ ^ p) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω, Real.zero_rpow hp.ne']
  rw [heq]
  refine ⟨he.indicator hA, integral_mono (he.indicator hA) he ?_⟩
  intro ω
  by_cases hω : ω ∈ A <;> simp [hω, Real.rpow_nonneg (norm_nonneg _) p]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma mean_le_threshold_add_tail {X : Ω → ℝ} {p q a : ℝ} {A : Set Ω}
    (hpq : p.HolderConjugate q) (hX : MemLp X (ENNReal.ofReal p) P)
    (hXi : Integrable X P) (hX0 : ∀ ω, 0 ≤ X ω) (ha : 0 ≤ a)
    (hA : MeasurableSet A) (hout : ∀ ω ∉ A, X ω ≤ a) :
    (∫ ω, X ω ∂P) ≤ a +
      (∫ ω, X ω ^ p ∂P) ^ (1 / p) * (P.real A) ^ (1 / q) := by
  have hI : MemLp (A.indicator (fun _ : Ω => (1 : ℝ))) (ENNReal.ofReal q) P :=
    (memLp_const 1).indicator hA
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall hX0)
    (Filter.Eventually.of_forall (fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω))
    hX hI
  have heq : (fun ω => X ω * A.indicator (fun _ : Ω => (1 : ℝ)) ω) = A.indicator X := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  have heqpow : (fun ω => (A.indicator (fun _ : Ω => (1 : ℝ)) ω) ^ q) =
      A.indicator (fun _ : Ω => (1 : ℝ)) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω, Real.zero_rpow hpq.symm.pos.ne']
  rw [heq, heqpow, integral_indicator hA, integral_indicator hA, setIntegral_const] at hholder
  have hb := integral_mono hXi ((integrable_const a).add (hXi.indicator hA))
    (fun ω => show X ω ≤ a + A.indicator X ω from by
      by_cases hω : ω ∈ A
      · simpa [hω] using (show X ω ≤ a + X ω by linarith)
      · simpa [hω] using hout ω hω)
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_const a) (hXi.indicator hA), integral_const, integral_indicator hA] at hb
  simp only [probReal_univ, smul_eq_mul, one_mul, mul_one] at hb hholder
  linarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma tail_probability_lower {X : Ω → ℝ} {p q a : ℝ} {A : Set Ω}
    (hpq : p.HolderConjugate q) (hX : MemLp X (ENNReal.ofReal p) P)
    (hXi : Integrable X P) (hX0 : ∀ ω, 0 ≤ X ω) (ha : 0 ≤ a)
    (hA : MeasurableSet A) (hout : ∀ ω ∉ A, X ω ≤ a)
    (hmean : a ≤ ∫ ω, X ω ∂P) (hmom : 0 < ∫ ω, X ω ^ p ∂P) :
    (((∫ ω, X ω ∂P) - a) / (∫ ω, X ω ^ p ∂P) ^ (1 / p)) ^ q ≤ P.real A := by
  have hb := mean_le_threshold_add_tail hpq hX hXi hX0 ha hA hout
  have hm : 0 < (∫ ω, X ω ^ p ∂P) ^ (1 / p) := Real.rpow_pos_of_pos hmom _
  have hd : ((∫ ω, X ω ∂P) - a) / (∫ ω, X ω ^ p ∂P) ^ (1 / p) ≤
      (P.real A) ^ (1 / q) := by
    apply (div_le_iff₀ hm).mpr
    nlinarith
  have hr := Real.rpow_le_rpow
    (div_nonneg (sub_nonneg.mpr hmean) hm.le) hd hpq.symm.nonneg
  rw [← Real.rpow_mul (measureReal_nonneg), one_div_mul_cancel hpq.symm.pos.ne',
    Real.rpow_one] at hr
  exact hr

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma positive_tail_of_moments {X : Ω → ℝ} {p q b : ℝ} {A : Set Ω}
    (hpq : p.HolderConjugate q) (hX : MemLp X (ENNReal.ofReal p) P)
    (hXi : Integrable X P) (hX0 : ∀ ω, 0 ≤ X ω) (hb : 0 < b)
    (hA : MeasurableSet A) (hout : ∀ ω ∉ A, X ω ≤ b / 2)
    (hmean : b ≤ ∫ ω, X ω ∂P)
    (hmom : (∫ ω, X ω ^ p ∂P) ^ (1 / p) ≤ 2 * b) :
    (1 / 4 : ℝ) ^ q ≤ P.real A := by
  have hh := mean_le_threshold_add_tail hpq hX hXi hX0 (by positivity) hA hout
  have hm := mul_le_mul_of_nonneg_right hmom (Real.rpow_nonneg (show 0 ≤ P.real A from measureReal_nonneg) (1 / q))
  have hprob : (1 / 4 : ℝ) ≤ (P.real A) ^ (1 / q) := by
    nlinarith
  have hr := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4) hprob hpq.symm.nonneg
  rw [← Real.rpow_mul (measureReal_nonneg), one_div_mul_cancel hpq.symm.pos.ne',
    Real.rpow_one] at hr
  exact hr

end LongTails.Proofs.HeavyTailedMomentBounds
