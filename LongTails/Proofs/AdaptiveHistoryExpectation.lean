import LongTails.Proofs.AdaptiveHistoryField
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace LongTails.Proofs.AdaptiveHistoryExpectation

lemma integral_prod_swap_average {μ : Measure ℝ} [SFinite μ] {f : ℝ × ℝ → ℝ}
    (hf : Integrable f (μ.prod μ)) :
    (∫ z, f z ∂μ.prod μ) = ∫ z, (f z + f z.swap) / 2 ∂μ.prod μ := by
  rw [integral_div]
  erw [integral_add hf hf.swap, integral_prod_swap]
  ring

lemma integral_prod_sign_average {μ : Measure ℝ} [SFinite μ] {f : ℝ × ℝ → ℝ}
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hf : Integrable f (μ.prod μ)) :
    (∫ z, f z ∂μ.prod μ) =
      ∫ z, (f z + f (-z.1, z.2) + f (z.1, -z.2) + f (-z.1, -z.2)) / 4 ∂μ.prod μ := by
  have hn : MeasurePreserving (fun x : ℝ => -x) μ μ := ⟨measurable_neg, hsym⟩
  have hp := hn.prod (MeasurePreserving.id μ)
  have hq := (MeasurePreserving.id μ).prod hn
  have hr := hn.prod hn
  have hfp : Integrable (fun z : ℝ × ℝ => f (-z.1, z.2)) (μ.prod μ) :=
    (hp.integrable_comp hf.aestronglyMeasurable).mpr hf
  have hfq : Integrable (fun z : ℝ × ℝ => f (z.1, -z.2)) (μ.prod μ) :=
    (hq.integrable_comp hf.aestronglyMeasurable).mpr hf
  have hfr : Integrable (fun z : ℝ × ℝ => f (-z.1, -z.2)) (μ.prod μ) :=
    (hr.integrable_comp hf.aestronglyMeasurable).mpr hf
  have hip := hp.integral_comp
    ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)).measurableEmbedding f
  have hiq := hq.integral_comp
    ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)).measurableEmbedding f
  have hir := hr.integral_comp
    ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)).measurableEmbedding f
  change (∫ z, f (-z.1, z.2) ∂μ.prod μ) = _ at hip
  change (∫ z, f (z.1, -z.2) ∂μ.prod μ) = _ at hiq
  change (∫ z, f (-z.1, -z.2) ∂μ.prod μ) = _ at hir
  rw [integral_div]
  erw [integral_add ((hf.add hfp).add hfq) hfr,
    integral_add (hf.add hfp) hfq, integral_add hf hfp, hip, hiq, hir]
  ring

open LongTails.Proofs.AdaptiveHistoryField

lemma integrable_current_field {μ : Measure ℝ} [IsFiniteMeasure μ]
    {δ b g : ℝ} {c : ℝ × ℝ → ℝ} (hδ : 0 < δ)
    (hc : Measurable c) (hm : Integrable (fun x : ℝ => x) μ) :
    Integrable (fun z : ℝ × ℝ => scalarField δ b (c z) (g + z.1)) (μ.prod μ) := by
  have hn : Integrable (fun z : ℝ × ℝ => g + z.1) (μ.prod μ) :=
    (integrable_const g).add (hm.comp_fst μ)
  have hb := hn.abs.div_const δ
  apply hb.mono' (show AEStronglyMeasurable
    (fun z : ℝ × ℝ => scalarField δ b (c z) (g + z.1)) (μ.prod μ) from
      (show Measurable (fun z : ℝ × ℝ => scalarField δ b (c z) (g + z.1)) by
        unfold scalarField
        fun_prop).aestronglyMeasurable)
  filter_upwards [] with z
  rw [Real.norm_eq_abs, scalarField, abs_div,
    abs_of_pos (show 0 < δ + Real.sqrt (b * (g + z.1) ^ 2 + c z) by positivity)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hδ
    (le_add_of_nonneg_right (Real.sqrt_nonneg _))

lemma integral_current_field_eq_twoSampleField {μ : Measure ℝ} [IsFiniteMeasure μ]
    {δ b β S g : ℝ} (hδ : 0 < δ)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ) :
    (∫ z : ℝ × ℝ, scalarField δ b (S + β * b * (g + z.2) ^ 2) (g + z.1) ∂μ.prod μ) =
      ∫ z : ℝ × ℝ, twoSampleField δ b β S g z.1 z.2 ∂μ.prod μ := by
  have hf := integrable_current_field (b := b) (g := g) hδ
    (show Measurable (fun z : ℝ × ℝ => S + β * b * (g + z.2) ^ 2) by fun_prop) hm
  rw [integral_prod_sign_average hsym hf]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [twoSampleField]
  rw [show g + -z.1 = g - z.1 by ring, show g + -z.2 = g - z.2 by ring]

lemma integrable_prod_sign_average {μ : Measure ℝ} [SFinite μ] {f : ℝ × ℝ → ℝ}
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hf : Integrable f (μ.prod μ)) :
    Integrable (fun z =>
      (f z + f (-z.1, z.2) + f (z.1, -z.2) + f (-z.1, -z.2)) / 4) (μ.prod μ) := by
  have hn : MeasurePreserving (fun x : ℝ => -x) μ μ := ⟨measurable_neg, hsym⟩
  have hp := ((hn.prod (MeasurePreserving.id μ)).integrable_comp hf.aestronglyMeasurable).mpr hf
  have hq := (((MeasurePreserving.id μ).prod hn).integrable_comp hf.aestronglyMeasurable).mpr hf
  have hr := ((hn.prod hn).integrable_comp hf.aestronglyMeasurable).mpr hf
  exact (((hf.add hp).add hq).add hr).div_const 4

lemma integrable_twoSampleField {μ : Measure ℝ} [IsFiniteMeasure μ]
    {δ b β S g : ℝ} (hδ : 0 < δ)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ) :
    Integrable (fun z : ℝ × ℝ => twoSampleField δ b β S g z.1 z.2) (μ.prod μ) := by
  have hf := integrable_current_field (b := b) (g := g) hδ
    (show Measurable (fun z : ℝ × ℝ => S + β * b * (g + z.2) ^ 2) by fun_prop) hm
  convert integrable_prod_sign_average hsym hf using 1
  simp only [twoSampleField, sub_eq_add_neg]

lemma integral_current_field_lower_reciprocal {μ : Measure ℝ} [IsFiniteMeasure μ]
    {δ b β S g : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hS : 0 ≤ S) (hg : 0 ≤ g)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ) :
    (∫ z : ℝ × ℝ, β * g /
      (8 * (δ + Real.sqrt (S + b * ((g + |z.1|) ^ 2 + (g + |z.2|) ^ 2)))) ∂μ.prod μ) ≤
      ∫ z : ℝ × ℝ, scalarField δ b (S + β * b * (g + z.2) ^ 2) (g + z.1) ∂μ.prod μ := by
  have hf := integrable_twoSampleField (b := b) (β := β) (S := S) (g := g) hδ hsym hm
  have hi : Integrable (fun z : ℝ × ℝ => β * g /
      (8 * (δ + Real.sqrt (S + b * ((g + |z.1|) ^ 2 + (g + |z.2|) ^ 2))))) (μ.prod μ) := by
    apply (integrable_const (β * g / (8 * δ))).mono'
      (show AEStronglyMeasurable (fun z : ℝ × ℝ => β * g /
        (8 * (δ + Real.sqrt (S + b * ((g + |z.1|) ^ 2 + (g + |z.2|) ^ 2))))) (μ.prod μ) from
        (show Measurable (fun z : ℝ × ℝ => β * g /
          (8 * (δ + Real.sqrt (S + b * ((g + |z.1|) ^ 2 + (g + |z.2|) ^ 2))))) by
          fun_prop).aestronglyMeasurable)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left (mul_nonneg hβ hg) (by positivity)
      (by nlinarith [Real.sqrt_nonneg (S + b * ((g + |z.1|) ^ 2 + (g + |z.2|) ^ 2))])
  rw [integral_current_field_eq_twoSampleField hδ hsym hm, integral_prod_swap_average hf]
  apply integral_mono hi ((hf.add hf.swap).div_const 2)
  intro z
  dsimp only [Pi.add_apply, Function.comp_def, Prod.swap]
  simpa only [twoSampleField_abs] using
    twoSampleField_swap_lower hδ hb hβ hβ1 hS hg (abs_nonneg z.1) (abs_nonneg z.2)

lemma integral_reciprocal_lower {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {U : Ω → ℝ} {D : ℝ}
    (hD : 0 < D) (hpos : ∀ᵐ ω ∂P, 0 < U ω)
    (hU : Integrable U P) (hinv : Integrable (fun ω => 1 / U ω) P)
    (hmean : (∫ ω, U ω ∂P) ≤ D) :
    1 / D ≤ ∫ ω, 1 / U ω ∂P := by
  have hpoint : ∀ᵐ ω ∂P, 2 / D - U ω / D ^ 2 ≤ 1 / U ω := by
    filter_upwards [hpos] with ω hω
    apply (mul_le_mul_iff_of_pos_right (show 0 < U ω * D ^ 2 by positivity)).mp
    field_simp
    nlinarith [sq_nonneg (U ω - D)]
  calc
    1 / D ≤ 2 / D - (∫ ω, U ω ∂P) / D ^ 2 := by
      have hi := div_le_div_of_nonneg_right hmean (sq_nonneg D)
      have he : 2 / D - D / D ^ 2 = 1 / D := by field_simp; ring
      rw [← he]
      linarith
    _ = ∫ ω, 2 / D - U ω / D ^ 2 ∂P := by
      rw [integral_sub (integrable_const _) (hU.div_const _)]
      simp only [integral_div]
      simp
    _ ≤ _ := integral_mono_ae ((integrable_const _).sub (hU.div_const _)) hinv hpoint

lemma twoSampleRoot_le {S b u v : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (S + b * (u ^ 2 + v ^ 2)) ≤ Real.sqrt S + Real.sqrt b * (u + v) := by
  have hz : 0 ≤ S + b * (u ^ 2 + v ^ 2) := by positivity
  have hzsq := Real.sq_sqrt hz
  have hSsq := Real.sq_sqrt hS
  have ht : 0 ≤ Real.sqrt b * (u + v) := by positivity
  have htsq : (Real.sqrt b * (u + v)) ^ 2 = b * (u + v) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hb]
  nlinarith [Real.sqrt_nonneg (S + b * (u ^ 2 + v ^ 2)), Real.sqrt_nonneg S,
    mul_nonneg (Real.sqrt_nonneg S) ht, mul_nonneg hb (mul_nonneg hu hv)]

noncomputable def twoSampleDenominator (δ b S g : ℝ) (z : ℝ × ℝ) : ℝ :=
  δ + Real.sqrt (S + b * ((g + |z.1|) ^ 2 + (g + |z.2|) ^ 2))

lemma twoSampleDenominator_moment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {δ b S g σ : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) (hS : 0 ≤ S) (hg : 0 ≤ g)
    (hm : Integrable (fun x : ℝ => x) μ) (hσ : (∫ x, |x| ∂μ) ≤ σ) :
    Integrable (twoSampleDenominator δ b S g) (μ.prod μ) ∧
      (∫ z, twoSampleDenominator δ b S g z ∂μ.prod μ) ≤
        δ + Real.sqrt S + 2 * Real.sqrt b * (g + σ) := by
  let V := fun z : ℝ × ℝ => δ + Real.sqrt S +
    Real.sqrt b * ((g + |z.1|) + (g + |z.2|))
  have hx := hm.abs.comp_fst μ
  have hy := hm.abs.comp_snd μ
  have hxp : Integrable (fun z : ℝ × ℝ => g + |z.1|) (μ.prod μ) :=
    (integrable_const g).add hx
  have hyp : Integrable (fun z : ℝ × ℝ => g + |z.2|) (μ.prod μ) :=
    (integrable_const g).add hy
  have hV : Integrable V (μ.prod μ) :=
    (integrable_const _).add ((hxp.add hyp).const_mul _)
  have hpoint (z : ℝ × ℝ) : twoSampleDenominator δ b S g z ≤ V z := by
    have hh := twoSampleRoot_le (u := g + |z.1|) (v := g + |z.2|)
      hS hb (by positivity) (by positivity)
    dsimp [twoSampleDenominator, V]
    linarith
  have hi : Integrable (twoSampleDenominator δ b S g) (μ.prod μ) := by
    apply hV.mono' ((show Measurable (twoSampleDenominator δ b S g) by
      unfold twoSampleDenominator
      fun_prop).aestronglyMeasurable)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ twoSampleDenominator δ b S g z by
      unfold twoSampleDenominator; positivity)]
    exact hpoint z
  refine ⟨hi, (integral_mono hi hV hpoint).trans ?_⟩
  have hex : (∫ z : ℝ × ℝ, g + |z.1| ∂μ.prod μ) = g + ∫ x, |x| ∂μ := by
    rw [integral_add (integrable_const _) hx, integral_fun_fst]
    simp
  have hey : (∫ z : ℝ × ℝ, g + |z.2| ∂μ.prod μ) = g + ∫ x, |x| ∂μ := by
    rw [integral_add (integrable_const _) hy, integral_fun_snd]
    simp
  have heV : (∫ z, V z ∂μ.prod μ) =
      δ + Real.sqrt S + Real.sqrt b * ((g + ∫ x, |x| ∂μ) + (g + ∫ x, |x| ∂μ)) := by
    dsimp only [V]
    erw [integral_add (integrable_const _) ((hxp.add hyp).const_mul _),
      integral_const_mul, integral_add hxp hyp, hex, hey]
    simp
  rw [heV]
  nlinarith [mul_le_mul_of_nonneg_left hσ (Real.sqrt_nonneg b)]

lemma integral_current_field_lower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {δ b β S g σ : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hS : 0 ≤ S) (hg : 0 ≤ g)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ)
    (hσ : (∫ x, |x| ∂μ) ≤ σ) :
    β * g / (8 * (δ + Real.sqrt S + 2 * Real.sqrt b * (g + σ))) ≤
      ∫ z : ℝ × ℝ, scalarField δ b (S + β * b * (g + z.2) ^ 2) (g + z.1) ∂μ.prod μ := by
  let U := twoSampleDenominator δ b S g
  let D := δ + Real.sqrt S + 2 * Real.sqrt b * (g + σ)
  have hσ0 : 0 ≤ σ := (integral_nonneg fun x : ℝ => abs_nonneg x).trans hσ
  have hD : 0 < D := by dsimp [D]; positivity
  have hUpos (z : ℝ × ℝ) : 0 < U z := by dsimp [U, twoSampleDenominator]; positivity
  have hUlo (z : ℝ × ℝ) : δ ≤ U z := by
    dsimp [U, twoSampleDenominator]
    linarith [Real.sqrt_nonneg (S + b * ((g + |z.1|) ^ 2 + (g + |z.2|) ^ 2))]
  obtain ⟨hi, hmean⟩ := twoSampleDenominator_moment hδ hb hS hg hm hσ
  have hinv : Integrable (fun z => 1 / U z) (μ.prod μ) := by
    apply (integrable_const (1 / δ)).mono'
      ((show Measurable (fun z => 1 / U z) by
        dsimp [U, twoSampleDenominator]; fun_prop).aestronglyMeasurable)
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (hUpos z))]
    exact one_div_le_one_div_of_le hδ (hUlo z)
  have hrecip := integral_reciprocal_lower hD (Filter.Eventually.of_forall hUpos) hi hinv hmean
  have hscaled := mul_le_mul_of_nonneg_left hrecip
    (show 0 ≤ β * g / 8 by positivity)
  change β * g / (8 * D) ≤ _
  calc
    _ = β * g / 8 * (1 / D) := by ring_nf
    _ ≤ β * g / 8 * (∫ z, 1 / U z ∂μ.prod μ) := hscaled
    _ = ∫ z, β * g / (8 * U z) ∂μ.prod μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    _ ≤ _ := integral_current_field_lower_reciprocal hδ hb hβ hβ1 hS hg hsym hm

lemma integrable_shifted_scalarField {μ : Measure ℝ} [IsFiniteMeasure μ]
    {δ b c g : ℝ} (hδ : 0 < δ) (hm : Integrable (fun x : ℝ => x) μ) :
    Integrable (fun x => scalarField δ b c (g + x)) μ := by
  have hi := ((integrable_const g).add hm).abs.div_const δ
  apply hi.mono' ((show Measurable (fun x => scalarField δ b c (g + x)) by
    unfold scalarField; fun_prop).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, scalarField, abs_div,
    abs_of_pos (show 0 < δ + Real.sqrt (b * (g + x) ^ 2 + c) by positivity)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hδ
    (le_add_of_nonneg_right (Real.sqrt_nonneg _))

lemma integral_shifted_scalarField_nonneg {μ : Measure ℝ} [IsFiniteMeasure μ]
    {δ b c g : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) (hc : 0 ≤ c) (hg : 0 ≤ g)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ) :
    0 ≤ ∫ x, scalarField δ b c (g + x) ∂μ := by
  rw [integral_sign_pair hsym (integrable_shifted_scalarField hδ hm)]
  apply integral_nonneg
  intro x
  change (0 : ℝ) ≤ (scalarField δ b c (g + x) + scalarField δ b c (g + -x)) / 2
  have hh := scalarField_sign_pair (r := |x|) hδ hb hc hg (abs_nonneg x)
  have hpair : 0 ≤ (scalarField δ b c (g + |x|) + scalarField δ b c (g - |x|)) / 2 :=
    (show 0 ≤ g * (δ ^ 2 + c) /
      (δ + Real.sqrt (b * (g + |x|) ^ 2 + c)) ^ 3 by positivity).trans hh
  by_cases hx : 0 ≤ x
  · simpa only [abs_of_nonneg hx, sub_eq_add_neg] using hpair
  · rw [abs_of_neg (lt_of_not_ge hx), show g - -x = g + x by ring] at hpair
    linarith only [hpair]

lemma integrable_current_field_random_residual {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {δ b β g : ℝ} {S : Ω → ℝ} (hδ : 0 < δ) (hS : Measurable S)
    (hm : Integrable (fun x : ℝ => x) μ) :
    Integrable (fun w : Ω × (ℝ × ℝ) =>
      scalarField δ b (S w.1 + β * b * (g + w.2.2) ^ 2) (g + w.2.1))
      (P.prod (μ.prod μ)) := by
  have hn : Integrable (fun z : ℝ × ℝ => g + z.1) (μ.prod μ) :=
    (integrable_const g).add (hm.comp_fst μ)
  have hnp := hn.comp_snd P
  apply (hnp.abs.div_const δ).mono'
    ((show Measurable (fun w : Ω × (ℝ × ℝ) =>
      scalarField δ b (S w.1 + β * b * (g + w.2.2) ^ 2) (g + w.2.1)) by
      unfold scalarField; fun_prop).aestronglyMeasurable)
  filter_upwards [] with w
  rw [Real.norm_eq_abs, scalarField, abs_div,
    abs_of_pos (show 0 < δ + Real.sqrt (b * (g + w.2.1) ^ 2 +
      (S w.1 + β * b * (g + w.2.2) ^ 2)) by positivity)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hδ
    (le_add_of_nonneg_right (Real.sqrt_nonneg _))

lemma integral_current_field_random_residual_lower {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {δ b β g σ ρ : ℝ} {S : Ω → ℝ}
    (hδ : 0 < δ) (hb : 0 ≤ b) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hg : 0 ≤ g)
    (hS : Measurable S) (hS0 : ∀ᵐ ω ∂P, 0 ≤ S ω)
    (hroot : Integrable (fun ω => Real.sqrt (S ω)) P)
    (hρ : (∫ ω, Real.sqrt (S ω) ∂P) ≤ ρ)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ)
    (hσ : (∫ x, |x| ∂μ) ≤ σ) :
    β * g / (8 * (δ + ρ + 2 * Real.sqrt b * (g + σ))) ≤
      ∫ w : Ω × (ℝ × ℝ),
        scalarField δ b (S w.1 + β * b * (g + w.2.2) ^ 2) (g + w.2.1)
        ∂P.prod (μ.prod μ) := by
  let C := 2 * Real.sqrt b * (g + σ)
  let U := fun ω => δ + Real.sqrt (S ω) + C
  let D := δ + ρ + C
  have hσ0 : 0 ≤ σ := (integral_nonneg fun x : ℝ => abs_nonneg x).trans hσ
  have hρ0 : 0 ≤ ρ := (integral_nonneg fun ω => Real.sqrt_nonneg (S ω)).trans hρ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hUpos (ω : Ω) : 0 < U ω := by dsimp [U]; positivity
  have hUlo (ω : Ω) : δ ≤ U ω := by dsimp [U]; linarith [Real.sqrt_nonneg (S ω)]
  have hiU : Integrable U P := ((integrable_const δ).add hroot).add (integrable_const C)
  have hiInv : Integrable (fun ω => 1 / U ω) P := by
    apply (integrable_const (1 / δ)).mono'
      ((show Measurable (fun ω => 1 / U ω) by dsimp [U]; fun_prop).aestronglyMeasurable)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (hUpos ω))]
    exact one_div_le_one_div_of_le hδ (hUlo ω)
  have hmean : (∫ ω, U ω ∂P) ≤ D := by
    dsimp only [U, D]
    erw [integral_add ((integrable_const δ).add hroot) (integrable_const C),
      integral_add (integrable_const δ) hroot]
    simpa using add_le_add (add_le_add (le_refl δ) hρ) (le_refl C)
  have hrecip := integral_reciprocal_lower hD (Filter.Eventually.of_forall hUpos) hiU hiInv hmean
  have hF := integrable_current_field_random_residual (P := P) (b := b) (β := β) (g := g) hδ hS hm
  have hiLower : Integrable (fun ω => β * g / (8 * U ω)) P := by
    convert hiInv.const_mul (β * g / 8) using 1
    funext ω
    ring
  rw [integral_prod _ hF]
  calc
    β * g / (8 * (δ + ρ + 2 * Real.sqrt b * (g + σ))) = β * g / 8 * (1 / D) := by
      change β * g / (8 * D) = β * g / 8 * (1 / D)
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ β * g / 8 * (∫ ω, 1 / U ω ∂P) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ = ∫ ω, β * g / (8 * U ω) ∂P := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ ≤ _ := by
      apply integral_mono_ae hiLower hF.integral_prod_left
      filter_upwards [hS0] with ω hω
      exact integral_current_field_lower hδ hb hβ hβ1 hω hg hsym hm hσ

lemma integral_current_field_random_residual_neg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] {μ : Measure ℝ} [SFinite μ]
    (δ b β g : ℝ) (S : Ω → ℝ) (hsym : μ.map (fun x : ℝ => -x) = μ) :
    (∫ w : Ω × (ℝ × ℝ),
      scalarField δ b (S w.1 + β * b * (-g + w.2.2) ^ 2) (-g + w.2.1)
      ∂P.prod (μ.prod μ)) =
    -(∫ w : Ω × (ℝ × ℝ),
      scalarField δ b (S w.1 + β * b * (g + w.2.2) ^ 2) (g + w.2.1)
      ∂P.prod (μ.prod μ)) := by
  have hn : MeasurePreserving (fun x : ℝ => -x) μ μ := ⟨measurable_neg, hsym⟩
  have hp := (MeasurePreserving.id P).prod (hn.prod hn)
  have hi := hp.integral_comp
    ((MeasurableEquiv.refl Ω).prodCongr
      ((MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ))).measurableEmbedding
    (fun w : Ω × (ℝ × ℝ) =>
      scalarField δ b (S w.1 + β * b * (g + w.2.2) ^ 2) (g + w.2.1))
  change (∫ w : Ω × (ℝ × ℝ),
    scalarField δ b (S w.1 + β * b * (g + -w.2.2) ^ 2) (g + -w.2.1)
    ∂P.prod (μ.prod μ)) = _ at hi
  calc
    _ = ∫ w : Ω × (ℝ × ℝ),
        -scalarField δ b (S w.1 + β * b * (g + -w.2.2) ^ 2) (g + -w.2.1)
        ∂P.prod (μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [show -g + w.2.1 = -(g + -w.2.1) by ring,
        show (-g + w.2.2) ^ 2 = (g + -w.2.2) ^ 2 by ring, scalarField_neg]
    _ = _ := by rw [integral_neg, hi]

lemma integral_current_field_random_residual_coercive {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {δ b β g σ ρ : ℝ} {S : Ω → ℝ}
    (hδ : 0 < δ) (hb : 0 ≤ b) (hβ : 0 ≤ β) (hβ1 : β ≤ 1)
    (hS : Measurable S) (hS0 : ∀ᵐ ω ∂P, 0 ≤ S ω)
    (hroot : Integrable (fun ω => Real.sqrt (S ω)) P)
    (hρ : (∫ ω, Real.sqrt (S ω) ∂P) ≤ ρ)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ)
    (hσ : (∫ x, |x| ∂μ) ≤ σ) :
    β * g ^ 2 / (8 * (δ + ρ + 2 * Real.sqrt b * (|g| + σ))) ≤
      g * (∫ w : Ω × (ℝ × ℝ),
        scalarField δ b (S w.1 + β * b * (g + w.2.2) ^ 2) (g + w.2.1)
        ∂P.prod (μ.prod μ)) := by
  by_cases hg : 0 ≤ g
  · have h := mul_le_mul_of_nonneg_left
      (integral_current_field_random_residual_lower hδ hb hβ hβ1 hg hS hS0 hroot hρ hsym hm hσ) hg
    rw [abs_of_nonneg hg]
    convert h using 1
    all_goals ring
  · have hgn : 0 ≤ -g := by linarith
    have h := mul_le_mul_of_nonneg_left
      (integral_current_field_random_residual_lower hδ hb hβ hβ1 hgn hS hS0 hroot hρ hsym hm hσ) hgn
    rw [integral_current_field_random_residual_neg δ b β g S hsym] at h
    rw [abs_of_neg (lt_of_not_ge hg)]
    convert h using 1
    all_goals ring


lemma integrable_shifted_scalarField_random_residual {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {μ : Measure ℝ} [IsFiniteMeasure μ]
    {δ b g : ℝ} {S : Ω → ℝ} (hδ : 0 < δ) (hS : Measurable S)
    (hm : Integrable (fun x : ℝ => x) μ) :
    Integrable (fun w : Ω × ℝ => scalarField δ b (S w.1) (g + w.2)) (P.prod μ) := by
  have hn : Integrable (fun w : Ω × ℝ => g + w.2) (P.prod μ) :=
    (integrable_const g).add (hm.comp_snd P)
  apply (hn.abs.div_const δ).mono'
    ((show Measurable (fun w : Ω × ℝ => scalarField δ b (S w.1) (g + w.2)) by
      unfold scalarField; fun_prop).aestronglyMeasurable)
  filter_upwards [] with w
  rw [Real.norm_eq_abs, scalarField, abs_div,
    abs_of_pos (show 0 < δ + Real.sqrt (b * (g + w.2) ^ 2 + S w.1) by positivity)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hδ
    (le_add_of_nonneg_right (Real.sqrt_nonneg _))

lemma integral_shifted_scalarField_random_residual_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {μ : Measure ℝ} [IsFiniteMeasure μ]
    {δ b g : ℝ} {S : Ω → ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) (hg : 0 ≤ g)
    (hS : Measurable S) (hS0 : ∀ᵐ ω ∂P, 0 ≤ S ω)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ) :
    0 ≤ ∫ w : Ω × ℝ, scalarField δ b (S w.1) (g + w.2) ∂P.prod μ := by
  have hi := integrable_shifted_scalarField_random_residual (P := P) (b := b) (g := g) hδ hS hm
  rw [integral_prod _ hi]
  apply integral_nonneg_of_ae
  filter_upwards [hS0] with ω hω
  exact integral_shifted_scalarField_nonneg hδ hb hω hg hsym hm

lemma integral_shifted_scalarField_random_residual_neg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P] {μ : Measure ℝ} [SFinite μ]
    (δ b g : ℝ) (S : Ω → ℝ) (hsym : μ.map (fun x : ℝ => -x) = μ) :
    (∫ w : Ω × ℝ, scalarField δ b (S w.1) (-g + w.2) ∂P.prod μ) =
      -(∫ w : Ω × ℝ, scalarField δ b (S w.1) (g + w.2) ∂P.prod μ) := by
  have hn : MeasurePreserving (fun x : ℝ => -x) μ μ := ⟨measurable_neg, hsym⟩
  have hp := (MeasurePreserving.id P).prod hn
  have hi := hp.integral_comp
    ((MeasurableEquiv.refl Ω).prodCongr (MeasurableEquiv.neg ℝ)).measurableEmbedding
    (fun w : Ω × ℝ => scalarField δ b (S w.1) (g + w.2))
  change (∫ w : Ω × ℝ, scalarField δ b (S w.1) (g + -w.2) ∂P.prod μ) = _ at hi
  calc
    _ = ∫ w : Ω × ℝ, -scalarField δ b (S w.1) (g + -w.2) ∂P.prod μ := by
      apply integral_congr_ae
      filter_upwards [] with w
      rw [show -g + w.2 = -(g + -w.2) by ring, scalarField_neg]
    _ = _ := by rw [integral_neg, hi]

lemma integral_shifted_scalarField_random_residual_signed_nonneg {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {μ : Measure ℝ} [IsFiniteMeasure μ]
    {δ b g : ℝ} {S : Ω → ℝ} (hδ : 0 < δ) (hb : 0 ≤ b)
    (hS : Measurable S) (hS0 : ∀ᵐ ω ∂P, 0 ≤ S ω)
    (hsym : μ.map (fun x : ℝ => -x) = μ) (hm : Integrable (fun x : ℝ => x) μ) :
    0 ≤ g * (∫ w : Ω × ℝ, scalarField δ b (S w.1) (g + w.2) ∂P.prod μ) := by
  by_cases hg : 0 ≤ g
  · exact mul_nonneg hg (integral_shifted_scalarField_random_residual_nonneg hδ hb hg hS hS0 hsym hm)
  · have hgn : 0 ≤ -g := by linarith
    have h := mul_nonneg hgn
      (integral_shifted_scalarField_random_residual_nonneg hδ hb hgn hS hS0 hsym hm)
    rw [integral_shifted_scalarField_random_residual_neg δ b g S hsym] at h
    simpa only [neg_mul_neg] using h

end LongTails.Proofs.AdaptiveHistoryExpectation
