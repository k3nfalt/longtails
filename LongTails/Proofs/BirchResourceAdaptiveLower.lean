import LongTails.Proofs.BirchResourceLower
import LongTails.Proofs.AdaptiveIID

namespace LongTails.Proofs.BirchResourceAdaptiveLower

open Finset MeasureTheory ProbabilityTheory Set
open LongTails.Setups.StochasticGeneralizedSmoothAndConvex (IID)
open LongTails.Proofs.BirchResourceLower

def past {Ω : Type*} (n : ℕ) (ξ : ℕ → Ω) (i : Fin n) : Ω := ξ i.val

lemma measurable_past {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) :
    Measurable (past (Ω := Ω) n) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply i.val

lemma joint_probability {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure (ℕ → Ω)) (hiid : IID (fun i (ξ : ℕ → Ω) => ξ i)
      (μ : Measure Ω) (P : Measure (ℕ → Ω))) (n : ℕ)
    (eligible : Set (Fin n → Ω)) (coin : Set Ω) (he : MeasurableSet eligible)
    (hc : MeasurableSet coin) :
    (P : Measure (ℕ → Ω)).real ((past n ⁻¹' eligible) ∩ ((fun ξ => ξ n) ⁻¹' coin)) =
      (μ : Measure Ω).real coin * (P : Measure (ℕ → Ω)).real (past n ⁻¹' eligible) := by
  have hin := hiid.prefix_tail_independent n
  have h := hin.comp measurable_id (measurable_pi_apply 0)
  have h' : IndepFun (past (Ω := Ω) n) (fun ξ : ℕ → Ω => ξ (n + 0)) (P : Measure (ℕ → Ω)) := h
  rw [Nat.add_zero] at h'
  have hz := h'.measure_inter_preimage_eq_mul eligible coin he hc
  have hcoin : (P : Measure (ℕ → Ω)) ((fun ξ => ξ n) ⁻¹' coin) = (μ : Measure Ω) coin := by
    rw [← Measure.map_apply (measurable_pi_apply n) hc, hiid.marginal n]
  rw [hcoin] at hz
  simpa only [Measure.real, ENNReal.toReal_mul, mul_comm] using congrArg ENNReal.toReal hz

lemma adaptive_reveal {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω)
    (P : ProbabilityMeasure (ℕ → Ω)) (hiid : IID (fun i (ξ : ℕ → Ω) => ξ i)
      (μ : Measure Ω) (P : Measure (ℕ → Ω))) (N : ℕ)
    (eligible : ∀ i, Set (Fin i → Ω)) (coin : Set Ω) (fast : Set (ℕ → Ω))
    (he : ∀ i, MeasurableSet (eligible i)) (hc : MeasurableSet coin) (hf : MeasurableSet fast)
    {R t Φ : ℝ} (hp : 0 < (μ : Measure Ω).real coin) (hR : 0 ≤ R)
    (hΦ : t = Φ / 9) (h : Φ ≤ t + (1 / ((μ : Measure Ω).real coin)) / R)
    (hcount : ∀ ξ, (∑ i ∈ range N, (past i ⁻¹' eligible i).indicator (fun _ => (1 : ℝ)) ξ) ≤ t * R)
    (hcover : fast ⊆ ⋃ i ∈ range N, (past i ⁻¹' eligible i) ∩ ((fun ξ => ξ i) ⁻¹' coin)) :
    (P : Measure (ℕ → Ω)).real fast ≤ 1 / 8 :=
  predictable_reveal (P : Measure (ℕ → Ω)) (range N)
    (fun i => past i ⁻¹' eligible i) (fun i => (fun ξ => ξ i) ⁻¹' coin) fast
    (fun i _ => (measurable_past i) (he i)) (fun i _ => (measurable_pi_apply i) hc) hf hp hR hΦ h
    (fun i _ => joint_probability μ P hiid i (eligible i) coin (he i) hc) hcount hcover

lemma expected_time {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (elapsed error : Ω → ℝ) (reached : Set Ω) (he : MeasurableSet reached)
    (hT : Integrable elapsed P) (herr : Integrable error P)
    (hT₀ : ∀ ω, 0 ≤ elapsed ω) (herr₀ : ∀ ω, 0 ≤ error ω)
    {ε threshold : ℝ} (hε : 0 < ε) (hthreshold : 0 ≤ threshold)
    (hfailed : ∀ ω ∉ reached, 4 * ε ≤ error ω)
    (haccuracy : (∫ ω, error ω ∂P) ≤ ε)
    (hfast : P.real (reached ∩ {ω | elapsed ω ≤ threshold}) ≤ 1 / 4)
    (hm : Measurable elapsed) :
    threshold / 2 ≤ ∫ ω, elapsed ω ∂P := by
  let failed := reachedᶜ
  let quick := reached ∩ {ω | elapsed ω ≤ threshold}
  have hf : MeasurableSet failed := he.compl
  have hq : MeasurableSet quick := he.inter (measurableSet_le hm measurable_const)
  have hm₁ : Integrable (failed.indicator (fun _ : Ω => (1 : ℝ))) P :=
    (integrable_const _).indicator hf
  have hm₂ : Integrable (quick.indicator (fun _ : Ω => (1 : ℝ))) P :=
    (integrable_const _).indicator hq
  have hl (ω : Ω) : failed.indicator (fun _ => 4 * ε) ω ≤ error ω := by
    by_cases h : ω ∈ reached
    · rw [indicator_of_notMem (show ω ∉ failed from fun hn => hn h)]
      exact herr₀ ω
    · rw [indicator_of_mem (show ω ∈ failed from h)]
      exact hfailed ω h
  have hh := integral_mono ((integrable_const (4 * ε)).indicator hf) herr hl
  rw [integral_indicator_const _ hf, smul_eq_mul] at hh
  have hfail : P.real failed ≤ 1 / 4 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    have hmul := hh.trans haccuracy
    apply le_of_mul_le_mul_right _ hε
    nlinarith only [hmul]
  let g := fun ω => threshold *
    (1 - failed.indicator (fun _ => (1 : ℝ)) ω - quick.indicator (fun _ => (1 : ℝ)) ω)
  have hg : Integrable g P := ((integrable_const (1 : ℝ)).sub hm₁ |>.sub hm₂).const_mul _
  have hpoint (ω : Ω) : g ω ≤ elapsed ω := by
    by_cases h : ω ∈ reached
    · have hnf : ω ∉ failed := fun hn => hn h
      by_cases htime : elapsed ω ≤ threshold
      · have hq' : ω ∈ quick := ⟨h, htime⟩
        simp only [g, indicator_of_notMem hnf, indicator_of_mem hq', sub_zero, sub_self, mul_zero]
        exact hT₀ ω
      · have hq' : ω ∉ quick := fun hq => htime hq.2
        simp only [g, indicator_of_notMem hnf, indicator_of_notMem hq', sub_zero, mul_one]
        exact le_of_not_ge htime
    · have hf' : ω ∈ failed := h
      have hq' : ω ∉ quick := fun hq => h hq.1
      simp only [g, indicator_of_mem hf', indicator_of_notMem hq', sub_self, mul_zero]
      exact hT₀ ω
  have hi := integral_mono hg hT hpoint
  change (∫ ω, threshold *
    (1 - failed.indicator (fun _ => (1 : ℝ)) ω - quick.indicator (fun _ => (1 : ℝ)) ω) ∂P) ≤ _ at hi
  rw [integral_const_mul] at hi
  have hsub₁ := integral_sub (integrable_const (1 : ℝ)) hm₁
  have hsub₂ := integral_sub ((integrable_const (1 : ℝ)).sub hm₁) hm₂
  simp only [Pi.sub_apply] at hsub₁ hsub₂
  rw [hsub₂, hsub₁, integral_const, probReal_univ, one_smul,
    integral_indicator_const _ hf, integral_indicator_const _ hq, smul_eq_mul, smul_eq_mul,
    mul_one, mul_one] at hi
  have hh := mul_le_mul_of_nonneg_left
    (show (1 / 2 : ℝ) ≤ 1 - P.real failed - P.real quick by linarith only [hfail, hfast])
    hthreshold
  linarith only [hi, hh]

end LongTails.Proofs.BirchResourceAdaptiveLower
