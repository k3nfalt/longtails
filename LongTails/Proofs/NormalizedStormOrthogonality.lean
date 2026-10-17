import LongTails.Proofs.HessianNcscProcess
import LongTails.Proofs.TwoSidedPLSampling

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.NormalizedStorm

variable {Ω : Type*} [MeasurableSpace Ω] {Y : Type*} [MeasurableSpace Y]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

lemma integrable_of_lintegral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Measurable f) (hf0 : ∀ a, 0 ≤ f a) (hg : Integrable g μ)
    (hle : ∫⁻ a, ENNReal.ofReal (f a) ∂μ ≤ ∫⁻ a, ENNReal.ofReal (g a) ∂μ) : Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have h1 : ∫⁻ a, ‖f a‖ₑ ∂μ = ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
    congr 1; funext a; rw [Real.enorm_eq_ofReal (hf0 a)]
  rw [h1]
  refine lt_of_le_of_lt hle (lt_of_le_of_lt ?_ hg.2)
  exact lintegral_mono fun a => ENNReal.ofReal_le_of_le_toReal (by simp [le_abs_self])

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma fresh_sq_integrable (p : Measure Ω) [IsProbabilityMeasure p] (k : ℕ)
    (S : (ℕ → Ω) → Y) (hS : Measurable S)
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → S ξ = S ξ')
    (W : Y → Ω → E) (hW : Measurable (Function.uncurry W))
    (hW2 : ∀ y, Integrable (fun ω => ‖W y ω‖ ^ 2) p)
    (w : Y → ℝ) (hw : ∀ y, ∫ ω, ‖W y ω‖ ^ 2 ∂p ≤ w y)
    (hwi : Integrable (fun ξ => w (S ξ)) (Measure.infinitePi fun _ : ℕ => p)) :
    Integrable (fun ξ : ℕ → Ω => ‖W (S ξ) (ξ k)‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p) ∧
      ∫ ξ, ‖W (S ξ) (ξ k)‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        ∫ ξ, w (S ξ) ∂(Measure.infinitePi fun _ : ℕ => p) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  have hΦ : Measurable (Function.uncurry fun (y : Y) (ω : Ω) => ‖W y ω‖ ^ 2) :=
    (hW.norm.pow_const 2)
  have hmeas : Measurable fun ξ : ℕ → Ω => ‖W (S ξ) (ξ k)‖ ^ 2 :=
    hΦ.comp (hS.prodMk (measurable_pi_apply k))
  have hint : Integrable (fun ξ : ℕ → Ω => ‖W (S ξ) (ξ k)‖ ^ 2) P := by
    refine integrable_of_lintegral_le hmeas (fun _ => by positivity) hwi ?_
    have hh : Measurable fun z : Y × Ω => ENNReal.ofReal (‖W z.1 z.2‖ ^ 2) :=
      ENNReal.measurable_ofReal.comp hΦ
    rw [HessianNcsc.fresh_lintegral p k S hS hdep (fun z => ENNReal.ofReal (‖W z.1 z.2‖ ^ 2)) hh]
    refine lintegral_mono fun ξ => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hW2 (S ξ))
      (Filter.Eventually.of_forall fun _ => by positivity)]
    exact ENNReal.ofReal_le_ofReal (hw (S ξ))
  refine ⟨hint, ?_⟩
  rw [TwoSidedPL.integral_prefix_dep p k S hS hdep (fun y ω => ‖W y ω‖ ^ 2) hΦ hint]
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => by positivity)
    hwi (Filter.Eventually.of_forall fun ξ => hw (S ξ))

lemma fresh_step_sq (p : Measure Ω) [IsProbabilityMeasure p] (k : ℕ)
    (S : (ℕ → Ω) → Y) (hS : Measurable S)
    (hdep : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < k → ξ i = ξ' i) → S ξ = S ξ')
    (U : Y → E) (hU : Measurable U)
    (W : Y → Ω → E) (hW : Measurable (Function.uncurry W))
    (hWi : ∀ y, Integrable (W y) p) (hW0 : ∀ y, ∫ ω, W y ω ∂p = 0)
    (hW2 : ∀ y, Integrable (fun ω => ‖W y ω‖ ^ 2) p)
    (w : Y → ℝ) (hw : ∀ y, ∫ ω, ‖W y ω‖ ^ 2 ∂p ≤ w y)
    (hwi : Integrable (fun ξ => w (S ξ)) (Measure.infinitePi fun _ : ℕ => p))
    (hU2 : Integrable (fun ξ => ‖U (S ξ)‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p)) (c : ℝ) :
    Integrable (fun ξ : ℕ → Ω => ‖c • U (S ξ) + W (S ξ) (ξ k)‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => p) ∧
      ∫ ξ, ‖c • U (S ξ) + W (S ξ) (ξ k)‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        c ^ 2 * ∫ ξ, ‖U (S ξ)‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p) +
          ∫ ξ, w (S ξ) ∂(Measure.infinitePi fun _ : ℕ => p) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  obtain ⟨hWk, hWk_le⟩ := fresh_sq_integrable p k S hS hdep W hW hW2 w hw hwi
  have hUm : Measurable fun ξ => U (S ξ) := hU.comp hS
  have hWm : Measurable fun ξ : ℕ → Ω => W (S ξ) (ξ k) := hW.comp (hS.prodMk (measurable_pi_apply k))
  have hUL : MemLp (fun ξ => U (S ξ)) 2 P :=
    (TwoSidedPL.memLp_two_iff_sq hUm.aestronglyMeasurable).mpr hU2
  have hWL : MemLp (fun ξ : ℕ → Ω => W (S ξ) (ξ k)) 2 P :=
    (TwoSidedPL.memLp_two_iff_sq hWm.aestronglyMeasurable).mpr hWk
  have hin : Integrable (fun ξ : ℕ → Ω => ⟪U (S ξ), W (S ξ) (ξ k)⟫) P :=
    TwoSidedPL.integrable_inner_of_memLp hUL hWL
  have hzero : ∫ ξ, ⟪U (S ξ), W (S ξ) (ξ k)⟫ ∂P = 0 := by
    have h := TwoSidedPL.integral_inner_prefix p k S hS hdep U hU W hW (fun _ => (0 : E))
      measurable_const hWi hW0 (by simpa using hin)
    simpa using h
  have hexp : ∀ ξ : ℕ → Ω, ‖c • U (S ξ) + W (S ξ) (ξ k)‖ ^ 2 =
      c ^ 2 * ‖U (S ξ)‖ ^ 2 + (2 * c) * ⟪U (S ξ), W (S ξ) (ξ k)⟫ + ‖W (S ξ) (ξ k)‖ ^ 2 := by
    intro ξ
    rw [norm_add_sq_real, norm_smul, inner_smul_left, mul_pow, Real.norm_eq_abs, sq_abs]
    simp only [conj_trivial]
    ring
  have hi1 : Integrable (fun ξ : ℕ → Ω => c ^ 2 * ‖U (S ξ)‖ ^ 2 + (2 * c) * ⟪U (S ξ), W (S ξ) (ξ k)⟫) P :=
    (hU2.const_mul _).add (hin.const_mul _)
  have hint : Integrable (fun ξ : ℕ → Ω => ‖c • U (S ξ) + W (S ξ) (ξ k)‖ ^ 2) P := by
    simp_rw [hexp]; exact hi1.add hWk
  refine ⟨hint, ?_⟩
  simp_rw [hexp]
  rw [integral_add hi1 hWk, integral_add (hU2.const_mul _) (hin.const_mul _), integral_const_mul,
    integral_const_mul, hzero]
  linarith

end OracleTemplate.NormalizedStorm
