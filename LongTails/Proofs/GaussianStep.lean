import LongTails.Proofs.GaussianFacts

namespace LongTails.Proofs.GaussianStep

open MeasureTheory ProbabilityTheory Filter Topology
open LongTails.Proofs.GaussianFacts
open scoped NNReal

noncomputable def step (β a : ℝ) : ℝ := a / Real.sqrt (a ^ 2 + β ^ 2)

lemma measurable_step (β : ℝ) : Measurable (step β) := by
  unfold step; fun_prop

lemma measurable_step₂ : Measurable (fun p : ℝ × ℝ => step p.1 p.2) := by
  unfold step; fun_prop

lemma abs_step_le (β a : ℝ) : |step β a| ≤ 1 := by
  unfold step
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases eq_or_ne (Real.sqrt (a ^ 2 + β ^ 2)) 0 with h | h
  · rw [h, div_zero]; norm_num
  · rw [div_le_one (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm h))]
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg β])

lemma step_neg (β a : ℝ) : step β (-a) = -step β a := by
  simp [step, neg_div]

lemma step_mono (β : ℝ) : Monotone (step β) := by
  intro a b hab
  rcases eq_or_ne β 0 with hβ | hβ
  · subst hβ
    have e (x : ℝ) : step 0 x = x / |x| := by
      rw [step, zero_pow (by norm_num), add_zero, Real.sqrt_sq_eq_abs]
    rcases lt_trichotomy a 0 with ha | ha | ha
    · rw [e a, abs_of_neg ha, div_neg, div_self ha.ne]
      exact (abs_le.mp (abs_step_le 0 b)).1
    · subst ha
      rw [e 0, e b, abs_zero, div_zero]
      exact div_nonneg hab (abs_nonneg b)
    · have hb : 0 < b := ha.trans_le hab
      rw [e a, e b, abs_of_pos ha, abs_of_pos hb, div_self ha.ne', div_self hb.ne']
  · unfold step
    have hpos (x : ℝ) : 0 < x ^ 2 + β ^ 2 := by positivity
    have hd (x : ℝ) : HasDerivAt (fun x => x / Real.sqrt (x ^ 2 + β ^ 2))
        (β ^ 2 / Real.sqrt (x ^ 2 + β ^ 2) ^ 3) x := by
      have hs := HasDerivAt.sqrt (HasDerivAt.add_const (β ^ 2) ((hasDerivAt_id x).pow 2))
        (hpos x).ne'
      have hq := HasDerivAt.div (hasDerivAt_id x) hs (Real.sqrt_pos.mpr (hpos x)).ne'
      convert hq using 1
      · funext y
        simp only [Pi.div_apply, Pi.pow_apply, id_eq]
      · have hsq : Real.sqrt (x ^ 2 + β ^ 2) ^ 2 = x ^ 2 + β ^ 2 := Real.sq_sqrt (hpos x).le
        have hsp : 0 < Real.sqrt (x ^ 2 + β ^ 2) := Real.sqrt_pos.mpr (hpos x)
        simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one,
          one_mul]
        rw [show Real.sqrt (x ^ 2 + β ^ 2) ^ 3 = Real.sqrt (x ^ 2 + β ^ 2) *
          Real.sqrt (x ^ 2 + β ^ 2) ^ 2 by ring, hsq]
        field_simp
        rw [hsq]
        ring
    exact monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt)
      (fun x => by rw [(hd x).deriv]; positivity) hab

lemma abs_step_ge {β a : ℝ} (h : |β| ≤ |a|) (ha : a ≠ 0) : 1 / Real.sqrt 2 ≤ |step β a| := by
  unfold step
  have hpos : 0 < a ^ 2 + β ^ 2 := by positivity
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _), div_le_div_iff₀ (by positivity)
    (Real.sqrt_pos.mpr hpos), one_mul]
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg a)]
  apply Real.sqrt_le_sqrt
  have : β ^ 2 ≤ a ^ 2 := sq_le_sq.mpr h
  nlinarith

lemma step_sq_ge {β a : ℝ} (h : |β| ≤ |a|) (ha : a ≠ 0) : 1 / 2 ≤ step β a ^ 2 := by
  have h1 := abs_step_ge h ha
  have h2 : (1 / Real.sqrt 2) ^ 2 = 1 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [← sq_abs]
  have h3 := pow_le_pow_left₀ (by positivity) h1 2
  linarith

lemma gaussian_step_moments (V : ℝ≥0) (hV : V ≠ 0) (a β b : ℝ) (hβ : |β| ≤ b)
    (hb : b ≤ Real.sqrt V / 4) :
    2 / 5 ≤ (∫ y, step β (a + y) ^ 2 ∂gaussianReal 0 V) ∧
      14 / 25 ≤ ∫ y, |step β (a + y)| ∂gaussianReal 0 V := by
  have hσ : 0 < Real.sqrt V := Real.sqrt_pos.mpr (by positivity)
  have hb0 : 0 ≤ b := (abs_nonneg β).trans hβ
  have hlp := large_prob V hV a b hb0
  have hlp' : 4 / 5 ≤ (gaussianReal 0 V).real {y | b ≤ |a + y|} := by
    have : 4 / 5 * b / Real.sqrt V ≤ 1 / 5 := by
      rw [div_le_iff₀ hσ]; nlinarith
    linarith
  set S := {y : ℝ | b ≤ |a + y|}
  have hS : MeasurableSet S := measurableSet_le measurable_const (by fun_prop)
  have hm : Measurable (fun y => step β (a + y)) := (measurable_step β).comp (by fun_prop)
  have hbdd2 : Integrable (fun y => step β (a + y) ^ 2) (gaussianReal 0 V) :=
    Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable 1
      (Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
        nlinarith [abs_step_le β (a + y), abs_nonneg (step β (a + y))])
  have hbdd1 : Integrable (fun y => |step β (a + y)|) (gaussianReal 0 V) :=
    Integrable.of_bound (continuous_abs.measurable.comp hm).aestronglyMeasurable 1
      (Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (abs_nonneg _)]; exact abs_step_le β (a + y))
  have hae : ∀ᵐ y ∂gaussianReal 0 V, a + y ≠ 0 := by
    apply (gaussianReal_absolutelyContinuous 0 hV).ae_le
    apply ae_iff.mpr
    have hset : {y : ℝ | ¬a + y ≠ 0} = {-a} := by
      ext y
      simp only [ne_eq, not_not, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor <;> intro hy <;> linarith
    rw [hset]
    exact Real.volume_singleton
  constructor
  · have hind : ∀ᵐ y ∂gaussianReal 0 V, S.indicator (fun _ => (1 : ℝ) / 2) y ≤ step β (a + y) ^ 2 := by
      filter_upwards [hae] with y hy0
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy]
        exact step_sq_ge (hβ.trans hy) hy0
      · rw [Set.indicator_of_notMem hy]; positivity
    have := integral_mono_ae ((integrable_const _).indicator hS) hbdd2 hind
    rw [integral_indicator hS, setIntegral_const, smul_eq_mul] at this
    linarith
  · have hind : ∀ᵐ y ∂gaussianReal 0 V,
        S.indicator (fun _ => (7 : ℝ) / 10) y ≤ |step β (a + y)| := by
      filter_upwards [hae] with y hy0
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy]
        refine le_trans ?_ (abs_step_ge (hβ.trans hy) hy0)
        rw [le_div_iff₀ (by positivity)]
        have : Real.sqrt 2 ≤ 10 / 7 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        linarith
      · rw [Set.indicator_of_notMem hy]; positivity
    have := integral_mono_ae ((integrable_const _).indicator hS) hbdd1 hind
    rw [integral_indicator hS, setIntegral_const, smul_eq_mul] at this
    linarith

lemma interval_shift_bound (β a R : ℝ) (ha : 0 ≤ a) :
    (∫ y in (-R)..R, (step β (a + y) - step β y)) ≤ 2 * a := by
  have hi (x z : ℝ) : IntervalIntegrable (step β) volume x z := by
    apply IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const
      (measurable_step β).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs]; exact abs_step_le β y
  have hshift : (∫ y in (-R)..R, step β (a + y)) = ∫ y in (a - R)..(a + R), step β y := by
    rw [intervalIntegral.integral_comp_add_left (step β) a]
    ring_nf
  have hi2 : IntervalIntegrable (fun y => step β (a + y)) volume (-R) R := by
    rw [show (fun y => step β (a + y)) = (fun y => step β (y + a)) by funext y; ring_nf]
    simpa using (hi (-R + a) (R + a)).comp_add_right a
  rw [intervalIntegral.integral_sub hi2 (hi (-R) R), hshift]
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals (hi (a - R) R) (hi R (a + R))
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hi (-R) (a - R)) (hi (a - R) R)
  have hb1 : (∫ y in R..(a + R), step β y) ≤ a := by
    have := intervalIntegral.integral_mono_on (show R ≤ a + R by linarith) (hi R (a + R))
      intervalIntegrable_const (fun y _ => (abs_le.mp (abs_step_le β y)).2)
    simpa using this
  have hb2 : -a ≤ ∫ y in (-R)..(a - R), step β y := by
    have := intervalIntegral.integral_mono_on (show -R ≤ a - R by linarith)
      intervalIntegrable_const (hi (-R) (a - R)) (fun y _ => (abs_le.mp (abs_step_le β y)).1)
    simp at this
    linarith
  linarith

lemma gaussian_step_mean (V : ℝ≥0) (hV : V ≠ 0) (β a : ℝ) :
    |∫ y, step β (a + y) ∂gaussianReal 0 V| ≤ 4 / 5 * |a| / Real.sqrt V := by
  have hσ : 0 < Real.sqrt V := Real.sqrt_pos.mpr (by positivity)
  have hint (c : ℝ) : Integrable (fun y => step β (c + y)) (gaussianReal 0 V) :=
    Integrable.of_bound ((measurable_step β).comp (by fun_prop)).aestronglyMeasurable 1
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact abs_step_le β (c + y))
  have hzero : (∫ y, step β y ∂gaussianReal 0 V) = 0 := by
    have hneg : (gaussianReal 0 V).map (fun y => -y) = gaussianReal 0 V := by
      rw [gaussianReal_map_neg, neg_zero]
    have h := integral_map (μ := gaussianReal 0 V) (f := step β) (measurable_neg.aemeasurable)
      (measurable_step β).aestronglyMeasurable
    rw [hneg] at h
    simp_rw [step_neg, integral_neg] at h
    linarith
  have hpos (c : ℝ) (hc : 0 ≤ c) : (∫ y, step β (c + y) ∂gaussianReal 0 V) ≤ 4 / 5 * c / Real.sqrt V := by
    have hdiff : (∫ y, step β (c + y) ∂gaussianReal 0 V) =
        ∫ y, gaussianPDFReal 0 V y * (step β (c + y) - step β y) := by
      have h0 : (∫ y, step β (c + y) ∂gaussianReal 0 V) =
          (∫ y, step β (c + y) ∂gaussianReal 0 V) - ∫ y, step β y ∂gaussianReal 0 V := by
        rw [hzero, sub_zero]
      rw [h0, ← integral_sub (hint c) (by simpa using hint 0),
        integral_gaussianReal_eq_integral_smul hV]
      simp only [smul_eq_mul]
    rw [hdiff]
    have hF : Integrable (fun y => gaussianPDFReal 0 V y * (step β (c + y) - step β y)) := by
      apply ((integrable_gaussianPDFReal 0 V).mul_const 2).mono'
      · exact ((measurable_gaussianPDFReal 0 V).mul (((measurable_step β).comp
          (by fun_prop)).sub (measurable_step β))).aestronglyMeasurable
      · exact Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
          apply mul_le_mul_of_nonneg_left _ (gaussianPDFReal_nonneg _ _ _)
          have := abs_sub (step β (c + y)) (step β y)
          linarith [abs_step_le β (c + y), abs_step_le β y]
    have hlim := intervalIntegral_tendsto_integral hF tendsto_neg_atTop_atBot tendsto_id
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    have hnn (y : ℝ) : 0 ≤ step β (c + y) - step β y :=
      sub_nonneg.mpr (step_mono β (by linarith))
    have hiF : IntervalIntegrable (fun y => gaussianPDFReal 0 V y * (step β (c + y) - step β y))
        volume (-R) R := hF.intervalIntegrable
    have hiG : IntervalIntegrable (fun y => 2 / 5 / Real.sqrt V * (step β (c + y) - step β y))
        volume (-R) R := by
      apply IntervalIntegrable.const_mul
      apply IntervalIntegrable.mono_fun' (g := fun _ => (2 : ℝ)) intervalIntegrable_const
      · exact (((measurable_step β).comp (by fun_prop)).sub (measurable_step β)).aestronglyMeasurable
      · exact Eventually.of_forall fun y => by
          simp only [Real.norm_eq_abs]
          have := abs_sub (step β (c + y)) (step β y)
          linarith [abs_step_le β (c + y), abs_step_le β y]
    calc (∫ y in (-R)..id R, gaussianPDFReal 0 V y * (step β (c + y) - step β y)) ≤
          ∫ y in (-R)..R, 2 / 5 / Real.sqrt V * (step β (c + y) - step β y) := by
            apply intervalIntegral.integral_mono_on (by linarith) hiF hiG
            intro y _
            exact mul_le_mul_of_nonneg_right (pdf_le V hV y) (hnn y)
      _ = 2 / 5 / Real.sqrt V * ∫ y in (-R)..R, (step β (c + y) - step β y) :=
            intervalIntegral.integral_const_mul _ _
      _ ≤ 2 / 5 / Real.sqrt V * (2 * c) :=
            mul_le_mul_of_nonneg_left (interval_shift_bound β c R hc) (by positivity)
      _ = 4 / 5 * c / Real.sqrt V := by ring
  have hlow (c : ℝ) (hc : 0 ≤ c) : 0 ≤ ∫ y, step β (c + y) ∂gaussianReal 0 V := by
    have hm := integral_mono
      (by simpa using hint 0 : Integrable (fun y => step β y) (gaussianReal 0 V)) (hint c)
      (fun y => step_mono β (by linarith))
    linarith
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg (hlow a ha), abs_of_nonneg ha]
    exact hpos a ha
  · have hsym : (∫ y, step β (a + y) ∂gaussianReal 0 V) = -∫ y, step β (-a + y) ∂gaussianReal 0 V := by
      have hneg : (gaussianReal 0 V).map (fun y => -y) = gaussianReal 0 V := by
        rw [gaussianReal_map_neg, neg_zero]
      have h := integral_map (μ := gaussianReal 0 V) (f := fun y => step β (a + y))
        (measurable_neg.aemeasurable) ((measurable_step β).comp (by fun_prop)).aestronglyMeasurable
      rw [hneg] at h
      rw [h, ← integral_neg]
      congr 1
      funext y
      rw [show a + -y = -(-a + y) by ring, step_neg]
    rw [hsym, abs_neg, abs_of_nonneg (hlow (-a) (by linarith)), abs_of_nonpos ha]
    exact hpos (-a) (by linarith)

end LongTails.Proofs.GaussianStep
