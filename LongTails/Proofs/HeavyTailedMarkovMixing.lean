import LongTails.Setups.HeavyTailedMarkovSmoothAndConvex
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

namespace OracleTemplate.HeavyTailedMarkovGradient

open LongTails.Setups.HeavyTailedMarkovSmoothAndConvex

variable {Ω : Type} [MeasurableSpace Ω]
    (κ : Kernel Ω Ω) [IsMarkovKernel κ] (π : ProbabilityMeasure Ω)

instance isMarkovKernel_pow (t : ℕ) : IsMarkovKernel (κ ^ t) := by
  induction t with
  | zero => exact inferInstanceAs (IsMarkovKernel Kernel.id)
  | succ t ih =>
    let := ih
    rw [pow_succ]
    exact inferInstanceAs (IsMarkovKernel ((κ ^ t) ∘ₖ κ))

lemma mixingDistance_bddAbove (t : ℕ) (z : Ω) :
    BddAbove (Set.range (fun s : {s : Set Ω // MeasurableSet s} =>
      |((κ ^ t) z s.val).toReal - ((π : Measure Ω) s.val).toReal|)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨s, rfl⟩
  have hκ : ((κ ^ t) z s.val).toReal ≤ 1 := measureReal_le_one
  have hπ : ((π : Measure Ω) s.val).toReal ≤ 1 := measureReal_le_one
  rw [abs_le]
  constructor <;> linarith [ENNReal.toReal_nonneg (a := (κ ^ t) z s.val),
    ENNReal.toReal_nonneg (a := (π : Measure Ω) s.val)]

lemma mixingDistance_nonneg (t : ℕ) (z : Ω) : 0 ≤ mixingDistance κ π t z := by
  unfold mixingDistance
  exact (abs_nonneg _).trans (le_ciSup (mixingDistance_bddAbove κ π t z)
    (⟨Set.univ, MeasurableSet.univ⟩ : {s : Set Ω // MeasurableSet s}))

lemma mixingDistance_le_one (t : ℕ) (z : Ω) : mixingDistance κ π t z ≤ 1 := by
  unfold mixingDistance
  apply ciSup_le
  intro s
  have hκ : ((κ ^ t) z s.val).toReal ≤ 1 := measureReal_le_one
  have hπ : ((π : Measure Ω) s.val).toReal ≤ 1 := measureReal_le_one
  rw [abs_le]
  constructor <;> linarith [ENNReal.toReal_nonneg (a := (κ ^ t) z s.val),
    ENNReal.toReal_nonneg (a := (π : Measure Ω) s.val)]

lemma measure_sub_le_mixingDistance (t : ℕ) (z : Ω) {s : Set Ω} (hs : MeasurableSet s) :
    |((κ ^ t) z s).toReal - ((π : Measure Ω) s).toReal| ≤ mixingDistance κ π t z := by
  exact le_ciSup (mixingDistance_bddAbove κ π t z) ⟨s, hs⟩

lemma integral_sub_le_of_set_bound {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {δ B : ℝ} (_hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hset : ∀ s : Set Ω, MeasurableSet s → |μ.real s - ν.real s| ≤ δ)
    {f : Ω → ℝ} (hf : Measurable f) (hbound : ∀ z, |f z| ≤ B) :
    |(∫ z, f z ∂μ) - ∫ z, f z ∂ν| ≤ 2 * B * δ := by
  let h : Ω → ℝ := fun z => f z + B
  have hm : Measurable h := hf.add_const B
  have hnon : ∀ z, 0 ≤ h z := fun z => by
    have := (abs_le.mp (hbound z)).1
    dsimp [h]
    linarith
  have hupper : ∀ z, h z ≤ 2 * B := fun z => by
    have := (abs_le.mp (hbound z)).2
    dsimp [h]
    linarith
  have hint (ρ : Measure Ω) [IsProbabilityMeasure ρ] : Integrable h ρ :=
    Integrable.of_bound hm.aestronglyMeasurable (2 * B) (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnon z)]
      exact hupper z))
  have fint (ρ : Measure Ω) [IsProbabilityMeasure ρ] : Integrable f ρ :=
    Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hbound)
  have htail (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
      IntegrableOn (fun t : ℝ => ρ.real {z | t ≤ h z}) (Set.Ioc 0 (2 * B)) := by
    have hm' : Measurable (fun t : ℝ => ρ {z | t ≤ h z}) :=
      Antitone.measurable (fun _ _ hst => measure_mono (fun _ hz => le_trans hst hz))
    apply Integrable.of_bound hm'.ennreal_toReal.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      exact measureReal_le_one)
  have heq (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
      (∫ z, f z ∂ρ) + B = ∫ t in Set.Ioc 0 (2 * B), ρ.real {z | t ≤ h z} := by
    have hx := (hint ρ).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hnon) (Filter.Eventually.of_forall hupper)
    simpa only [h, integral_add (fint ρ) (integrable_const B), integral_const,
      probReal_univ, smul_eq_mul, one_mul] using hx
  have hh := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Set.Ioc 0 (2 * B)))
    (f := fun t => μ.real {z | t ≤ h z} - ν.real {z | t ≤ h z})
    (Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs]
      exact hset _ (measurableSet_le measurable_const hm)))
  rw [integral_sub (htail μ) (htail ν), ← heq μ, ← heq ν] at hh
  simpa [Real.norm_eq_abs, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * B), ENNReal.toReal_ofReal (by positivity : 0 ≤ B * 2), max_eq_left (by positivity : 0 ≤ 2 * B),
    mul_comm, mul_left_comm, mul_assoc] using hh

lemma integral_sub_le_mixingDistance (t : ℕ) (z : Ω) {B : ℝ} (hB : 0 ≤ B)
    {f : Ω → ℝ} (hf : Measurable f) (hbound : ∀ z, |f z| ≤ B) :
    |(∫ y, f y ∂(κ ^ t) z) - ∫ y, f y ∂(π : Measure Ω)| ≤
      2 * B * mixingDistance κ π t z :=
  integral_sub_le_of_set_bound (mixingDistance_nonneg κ π t z) hB
    (fun _ hs => measure_sub_le_mixingDistance κ π t z hs) hf hbound

lemma averaged_mixing_bound {H : Type*} [MeasurableSpace H] {ρ : Measure H}
    [IsProbabilityMeasure ρ] {z : H → Ω} (hz : Measurable z)
    (hmap : ρ.map z = (π : Measure Ω)) (t : ℕ)
    (hd : Integrable (mixingDistance κ π t) (π : Measure Ω))
    {W : H → Ω → ℝ} (hW : Measurable (Function.uncurry W))
    {B δ : ℝ} (hB : 0 ≤ B) (hbound : ∀ h y, |W h y| ≤ B)
    (hmix : (∫ y, mixingDistance κ π t y ∂(π : Measure Ω)) ≤ δ) :
    |(∫ h, ∫ y, W h y ∂(κ ^ t) (z h) ∂ρ) -
      ∫ h, ∫ y, W h y ∂(π : Measure Ω) ∂ρ| ≤ 2 * B * δ := by
  let K : Kernel H Ω := (κ ^ t).comap z hz
  let h₁ := fun h => ∫ y, W h y ∂(κ ^ t) (z h)
  let h₂ := fun h => ∫ y, W h y ∂(π : Measure Ω)
  have hsm₁ : StronglyMeasurable h₁ :=
    hW.stronglyMeasurable.integral_kernel_prod_right (κ := K)
  have hsm₂ : StronglyMeasurable h₂ :=
    hW.stronglyMeasurable.integral_kernel_prod_right (κ := Kernel.const H (π : Measure Ω))
  have hb₁ : ∀ h, ‖h₁ h‖ ≤ B := fun h => by
    simpa [h₁] using norm_integral_le_of_norm_le_const (μ := (κ ^ t) (z h))
      (f := W h) (Filter.Eventually.of_forall (hbound h))
  have hb₂ : ∀ h, ‖h₂ h‖ ≤ B := fun h => by
    simpa [h₂] using norm_integral_le_of_norm_le_const (μ := (π : Measure Ω))
      (f := W h) (Filter.Eventually.of_forall (hbound h))
  have hi₁ : Integrable h₁ ρ := Integrable.of_bound hsm₁.aestronglyMeasurable B (Filter.Eventually.of_forall hb₁)
  have hi₂ : Integrable h₂ ρ := Integrable.of_bound hsm₂.aestronglyMeasurable B (Filter.Eventually.of_forall hb₂)
  have hmp : MeasurePreserving z ρ (π : Measure Ω) := ⟨hz, hmap⟩
  have hdi := hmp.integrable_comp_of_integrable hd
  have hb := norm_integral_le_of_norm_le (hdi.const_mul (2 * B))
    (f := fun h => h₁ h - h₂ h) (Filter.Eventually.of_forall (fun h => by
      exact integral_sub_le_mixingDistance κ π t (z h) hB
        (hW.comp (measurable_const.prodMk measurable_id)) (hbound h)))
  have hdm : AEStronglyMeasurable (mixingDistance κ π t) (ρ.map z) := by
    rw [hmap]
    exact hd.aestronglyMeasurable
  have he := integral_map hz.aemeasurable hdm
  rw [hmap] at he
  rw [integral_sub hi₁ hi₂, integral_const_mul] at hb
  simp only [Function.comp_apply] at hb
  rw [← he] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hmix (by positivity))

end OracleTemplate.HeavyTailedMarkovGradient
