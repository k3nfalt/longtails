import LongTails.Proofs.HeavyTailedMarkovLaw
import LongTails.Proofs.ScentAnchor
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.MeasureTheory.Measure.Sub

open MeasureTheory ProbabilityTheory Set
namespace LongTails.Proofs.MarkovNonconvexBurnInBatches

variable {Z E : Type} [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

private lemma residual_measures (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {δ : ℝ} (hd : ∀ s, MeasurableSet s → |μ.real s - ν.real s| ≤ δ) :
    ∃ a b c : Measure Z, IsFiniteMeasure a ∧ IsFiniteMeasure b ∧ IsFiniteMeasure c ∧
      a + c = μ ∧ b + c = ν ∧ a.real univ ≤ δ ∧ b.real univ ≤ δ := by
  obtain ⟨s, hs, hp, hn⟩ := hahn_decomposition μ ν
  have h₁ : ν.restrict s ≤ μ.restrict s := by
    refine Measure.le_iff.mpr fun t ht => ?_
    simpa only [Measure.restrict_apply ht] using hp _ (ht.inter hs) inter_subset_right
  have h₂ : μ.restrict sᶜ ≤ ν.restrict sᶜ := by
    refine Measure.le_iff.mpr fun t ht => ?_
    simpa only [Measure.restrict_apply ht] using hn _ (ht.inter hs.compl) inter_subset_right
  let a := μ.restrict s - ν.restrict s
  let b := ν.restrict sᶜ - μ.restrict sᶜ
  let c := ν.restrict s + μ.restrict sᶜ
  have ha : a + ν.restrict s = μ.restrict s := Measure.sub_add_cancel_of_le h₁
  have hb : b + μ.restrict sᶜ = ν.restrict sᶜ := Measure.sub_add_cancel_of_le h₂
  refine ⟨a, b, c, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [show a+c = (a+ν.restrict s)+μ.restrict sᶜ by dsimp [c]; abel, ha,
      Measure.restrict_add_restrict_compl hs]
  · rw [show b+c = ν.restrict s+(b+μ.restrict sᶜ) by dsimp [c]; abel, hb,
      Measure.restrict_add_restrict_compl hs]
  · have h := congrArg (fun ρ : Measure Z => ρ.real univ) ha
    rw [measureReal_add_apply, measureReal_restrict_apply_univ, measureReal_restrict_apply_univ] at h
    linarith [(abs_le.mp (hd s hs)).2]
  · have h := congrArg (fun ρ : Measure Z => ρ.real univ) hb
    rw [measureReal_add_apply, measureReal_restrict_apply_univ, measureReal_restrict_apply_univ] at h
    linarith [(abs_le.mp (hd sᶜ hs.compl)).1]

omit [CompleteSpace E] [SecondCountableTopology E] in
lemma two_measure_square (μ ν : Measure Z) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {δ : ℝ} (hd : ∀ s, MeasurableSet s → |μ.real s - ν.real s| ≤ δ)
    {h : Z → E} (hm : Measurable h) (hμ : Integrable h μ) (hν : Integrable h ν)
    (qμ : Integrable (fun z => ‖h z‖^2) μ) (qν : Integrable (fun z => ‖h z‖^2) ν) :
    ‖(∫ z, h z ∂μ) - ∫ z, h z ∂ν‖^2 ≤
      2*δ*((∫ z, ‖h z‖^2 ∂μ) + ∫ z, ‖h z‖^2 ∂ν) := by
  obtain ⟨a,b,c,ha,hb,hc,ea,eb,ma,mb⟩ := residual_measures μ ν hd
  have la : a ≤ μ := ea ▸ Measure.le_add_right le_rfl
  have lb : b ≤ ν := eb ▸ Measure.le_add_right le_rfl
  have lc : c ≤ μ := ea ▸ Measure.le_add_left le_rfl
  have ia := hμ.mono_measure la
  have ib := hν.mono_measure lb
  have ic := hμ.mono_measure lc
  have qa := qμ.mono_measure la
  have qb := qν.mono_measure lb
  have leab : a + b ≤ μ + ν := add_le_add la lb
  have mass : (a+b).real univ ≤ 2*δ := by rw [measureReal_add_apply]; linarith
  have diff : ‖(∫ z, h z ∂μ) - ∫ z, h z ∂ν‖ ≤ ∫ z, ‖h z‖ ∂(a+b) := by
    rw [← ea, ← eb, integral_add_measure ia ic, integral_add_measure ib ic,
      add_sub_add_right_eq_sub, integral_add_measure ia.norm ib.norm]
    exact (norm_sub_le _ _).trans (add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _))
  have cs := OracleTemplate.Scent.AnchorHyp.integral_mul_le_sqrt
    (μ := a+b) hm.norm (measurable_const (a := (1:ℝ))) (fun z => norm_nonneg (h z))
    (fun _ => zero_le_one) (qa.add_measure qb) (integrable_const _)
  simp only [mul_one, one_pow, integral_const, smul_eq_mul] at cs
  have q := integral_mono_measure leab (.of_forall fun z => sq_nonneg ‖h z‖) (qμ.add_measure qν)
  rw [integral_add_measure qμ qν] at q
  have hh := pow_le_pow_left₀ (norm_nonneg _) (diff.trans cs) 2
  rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),
    Real.sq_sqrt measureReal_nonneg] at hh
  exact hh.trans (by rw [mul_comm]; exact mul_le_mul mass q (integral_nonneg fun _ => sq_nonneg _) (measureReal_nonneg.trans mass))

open Setups.HeavyTailedMarkovSmoothAndConvex OracleTemplate.HeavyTailedMarkovGradient

lemma invariant_power (κ : Kernel Z Z) (π : ProbabilityMeasure Z)
    (hinv : κ ∘ₘ (π : Measure Z) = π) (t : ℕ) : (κ ^ t) ∘ₘ (π : Measure Z) = π := by
  induction t with
  | zero => exact Measure.id_comp
  | succ t ih =>
    rw [pow_succ]
    change ((κ ^ t) ∘ₖ κ) ∘ₘ _ = _
    rw [← Measure.comp_assoc, hinv, ih]

omit [CompleteSpace E] in
set_option maxHeartbeats 600000 in
lemma stationary_square (κ : Kernel Z Z) [IsMarkovKernel κ] (π : ProbabilityMeasure Z)
    (hinv : κ ∘ₘ (π : Measure Z) = π) (t : ℕ) {δ : ℝ} (hd : ∀ z, mixingDistance κ π t z ≤ δ)
    {h : Z → E} (hm : Measurable h) (hi : Integrable h (π : Measure Z))
    (hz : (∫ z, h z ∂(π : Measure Z)) = 0)
    (hq : Integrable (fun z => ‖h z‖^2) (π : Measure Z)) :
    let u := fun z => ‖∫ y, h y ∂(κ ^ t) z‖^2
    Integrable u (π : Measure Z) ∧
      (∫ z, u z ∂(π : Measure Z)) ≤ 4*δ*(∫ z, ‖h z‖^2 ∂(π : Measure Z)) := by
  intro u
  let Q := fun z => ‖h z‖^2
  let m := ∫ z, Q z ∂(π : Measure Z)
  have e := invariant_power κ π hinv t
  have ih : Integrable h ((κ ^ t : Kernel Z Z) ∘ₘ (π : Measure Z)) := by rw [e]; exact hi
  have iq : Integrable Q ((κ ^ t : Kernel Z Z) ∘ₘ (π : Measure Z)) := by rw [e]; exact hq
  have aeq := Measure.ae_integrable_of_integrable_comp iq
  have aeh := Measure.ae_integrable_of_integrable_comp ih
  rw [Measure.comp_eq_comp_const_apply] at iq e
  have iq' : Integrable (fun z => ∫ y, Q y ∂(κ ^ t) z) (π : Measure Z) := iq.integral_comp
  have eqm : (∫ z, ∫ y, Q y ∂(κ ^ t) z ∂(π : Measure Z)) = m := by
    exact (Kernel.integral_comp iq).symm.trans (congrArg (fun ρ => ∫ z, Q z ∂ρ) e)
  have major := (iq'.add (integrable_const m)).const_mul (2*δ)
  have bound : ∀ᵐ z ∂(π : Measure Z), u z ≤ 2*δ*((∫ y, Q y ∂(κ ^ t) z)+m) := by
    filter_upwards [aeh,aeq] with z h1 h2
    have hh := two_measure_square ((κ ^ t) z) (π : Measure Z)
      (fun s hs => (measure_sub_le_mixingDistance κ π t z hs).trans (hd z)) hm h1 hi h2 hq
    simpa only [hz, sub_zero] using hh
  have hm' : Measurable u := (hm.stronglyMeasurable.integral_kernel (κ := κ^t)).measurable.norm.pow_const 2
  have iu := major.mono' hm'.aestronglyMeasurable (bound.mono fun z hle =>
    (Real.norm_of_nonneg (sq_nonneg _)).le.trans hle)
  refine ⟨iu, (integral_mono_ae iu major bound).trans_eq ?_⟩
  change (∫ z, 2*δ*((∫ y, Q y ∂(κ ^ t) z)+m) ∂(π : Measure Z)) = _
  rw [integral_const_mul, integral_add iq' (integrable_const m), eqm, integral_const,
    probReal_univ, one_smul]
  change _ = 4*δ*m
  ring

end LongTails.Proofs.MarkovNonconvexBurnInBatches
