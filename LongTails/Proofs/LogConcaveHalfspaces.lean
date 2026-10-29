import LongTails.Proofs.PrekopaLeindler
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory

noncomputable section

namespace LongTails.Proofs.LogConcaveHalfspaces

abbrev Density (d : ℕ) := (Fin d → ℝ) → ENNReal

def IsLogConcave {E : Type*} [Add E] [SMul ℝ E] (w : E → ENNReal) : Prop :=
  ∀ x y (t : ℝ), 0 < t → t < 1 →
    w x ^ (1 - t) * w y ^ t ≤ w ((1 - t) • x + t • y)

def halfspaceDensity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : E → ENNReal) (ℓ : E →L[ℝ] ℝ) (r : ℝ) (x : E) : ENNReal := if r ≤ ℓ x then w x else 0

def tailMass {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasureSpace E]
    (w : E → ENNReal) (ℓ : E →L[ℝ] ℝ) (r : ℝ) : ENNReal := ∫⁻ x, halfspaceDensity w ℓ r x

lemma measurable_halfspaceDensity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {w : E → ENNReal} (hw : Measurable w)
    (ℓ : E →L[ℝ] ℝ) (r : ℝ) : Measurable (halfspaceDensity w ℓ r) := by
  exact hw.ite (measurableSet_le measurable_const ℓ.continuous.measurable) measurable_const

lemma tailMass_logConcave {d : ℕ} {w : Density (d + 1)}
    (hw : Measurable w) (hlog : IsLogConcave w)
    (ℓ : (Fin (d + 1) → ℝ) →L[ℝ] ℝ) (r s t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    tailMass w ℓ r ^ (1 - t) * tailMass w ℓ s ^ t ≤
      tailMass w ℓ ((1 - t) * r + t * s) := by
  apply PrekopaLeindler.prekopa_leindler_weighted ht ht'
    (measurable_halfspaceDensity hw ℓ r) (measurable_halfspaceDensity hw ℓ s)
    (measurable_halfspaceDensity hw ℓ ((1 - t) * r + t * s))
  intro x y
  have ha : 0 < 1 - t := sub_pos.mpr ht'
  by_cases hx : r ≤ ℓ x
  · by_cases hy : s ≤ ℓ y
    · have hxy : (1 - t) * r + t * s ≤ ℓ ((1 - t) • x + t • y) := by
        simp only [map_add, map_smul, smul_eq_mul]
        nlinarith
      simpa only [halfspaceDensity, ite_eq_left hx, ite_eq_left hy, ite_eq_left hxy] using hlog x y t ht ht'
    · simp [halfspaceDensity, hy, ENNReal.zero_rpow_of_pos ht]
  · simp [halfspaceDensity, hx, ENNReal.zero_rpow_of_pos ha]

lemma measure_le_of_tail_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (s : Set ℝ) (hs : MeasurableSet s) (a : ENNReal)
    (h : ∀ x ∈ s, μ (Set.Ici x) ≤ a) : μ s ≤ a := by
  rw [hs.measure_eq_iSup_isCompact μ]
  refine iSup_le fun K => iSup_le fun hKs => iSup_le fun hK => ?_
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · simp [hKe]
  · have hmin := hK.sInf_mem hKn
    exact (measure_mono (fun x hx => csInf_le hK.bddBelow hx)).trans
      (h (sInf K) (hKs hmin))

lemma tail_superuniform (μ : Measure ℝ) [IsFiniteMeasure μ] (a : ENNReal) :
    μ {x | μ (Set.Ici x) ≤ a} ≤ a := by
  have ht : Antitone (fun x : ℝ => μ (Set.Ici x)) :=
    fun _ _ hxy => measure_mono (Set.Ici_subset_Ici.mpr hxy)
  exact measure_le_of_tail_bound μ _ (measurableSet_le ht.measurable measurable_const)
    a (fun _ hx => hx)

def negLogTail (μ : Measure ℝ) (x : ℝ) : ℝ := -Real.log ((μ (Set.Ici x)).toReal)

lemma measurable_negLogTail (μ : Measure ℝ) : Measurable (negLogTail μ) := by
  have ht : Antitone (fun x : ℝ => μ (Set.Ici x)) :=
    fun _ _ hxy => measure_mono (Set.Ici_subset_Ici.mpr hxy)
  exact ht.measurable.ennreal_toReal.log.neg

lemma negLogTail_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    0 ≤ negLogTail μ x := by
  apply neg_nonneg.mpr
  exact Real.log_nonpos ENNReal.toReal_nonneg
    ((ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr
      (prob_le_one (μ := μ)))

lemma measure_negLogTail_gt (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    μ {x | t < negLogTail μ x} ≤ ENNReal.ofReal (Real.exp (-t)) := by
  apply le_trans (measure_mono ?_) (tail_superuniform μ (ENNReal.ofReal (Real.exp (-t))))
  intro x hx
  by_cases hz : μ (Set.Ici x) = 0
  · simp [hz]
  · have hp : 0 < (μ (Set.Ici x)).toReal := ENNReal.toReal_pos hz (measure_ne_top _ _)
    have hlog : Real.log ((μ (Set.Ici x)).toReal) < -t := by
      change t < -Real.log ((μ (Set.Ici x)).toReal) at hx
      linarith
    have he := (Real.log_lt_iff_lt_exp hp).mp hlog
    change μ (Set.Ici x) ≤ ENNReal.ofReal (Real.exp (-t))
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (Set.Ici x))]
    exact ENNReal.ofReal_le_ofReal he.le

lemma lintegral_negLogTail_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫⁻ x, ENNReal.ofReal (negLogTail μ x) ∂μ) ≤ 1 := by
  rw [lintegral_eq_lintegral_meas_lt μ
    (Filter.Eventually.of_forall (negLogTail_nonneg μ)) (measurable_negLogTail μ).aemeasurable]
  calc
    (∫⁻ t in Set.Ioi 0, μ {x | t < negLogTail μ x}) ≤
        ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (Real.exp (-t)) :=
      lintegral_mono (measure_negLogTail_gt μ)
    _ = 1 := by
      rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
        (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-x)).le)),
        integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]

lemma convex_support_at_interior {s : Set ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hf : ConvexOn ℝ s f) (hx : x ∈ interior s) :
    ∀ y ∈ s, f x + derivWithin f (Set.Ioi x) x * (y - x) ≤ f y := by
  intro y hy
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have h := hf.rightDeriv_le_slope_of_mem_interior hx hy hxy
    rw [slope_def_field] at h
    have := (le_div_iff₀ (sub_pos.mpr hxy)).mp h
    linarith
  · simp
  · have h := (hf.slope_le_leftDeriv_of_mem_interior hy hx hyx).trans
      (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)
    rw [slope_def_field] at h
    have := (div_le_iff₀ (sub_pos.mpr hyx)).mp h
    nlinarith

lemma convex_integral_le_of_mean_interior (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ s f)
    (hmean : (∫ x, x ∂μ) ∈ interior s) (hmem : ∀ᵐ x ∂μ, x ∈ s)
    (hid : Integrable (fun x : ℝ => x) μ) (hfi : Integrable f μ) :
    f (∫ x, x ∂μ) ≤ ∫ x, f x ∂μ := by
  let m := ∫ x, x ∂μ
  let k := derivWithin f (Set.Ioi m) m
  have hlin : Integrable (fun x => k * (x - m)) μ :=
    (hid.sub (integrable_const m)).const_mul k
  have h := integral_mono_ae ((integrable_const (f m)).add hlin) hfi
    (hmem.mono (fun x hx => convex_support_at_interior hf hmean x hx))
  change (∫ x, f m + k * (x - m) ∂μ) ≤ ∫ x, f x ∂μ at h
  rw [integral_add (integrable_const (f m)) hlin, integral_const_mul,
    integral_sub hid (integrable_const m)] at h
  simpa [m] using h

lemma integrable_negLogTail (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Integrable (negLogTail μ) μ := by
  refine ⟨(measurable_negLogTail μ).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simp_rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (negLogTail_nonneg μ _)]
  exact (lintegral_negLogTail_le_one μ).trans_lt ENNReal.one_lt_top

lemma integral_negLogTail_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (∫ x, negLogTail μ x ∂μ) ≤ 1 := by
  have h := lintegral_negLogTail_le_one μ
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_negLogTail μ)
    (Filter.Eventually.of_forall (negLogTail_nonneg μ))] at h
  exact (ENNReal.ofReal_le_one).mp h

lemma scalar_halfspace_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {s : Set ℝ} (hconv : ConvexOn ℝ s (negLogTail μ))
    (hmean : (∫ x, x ∂μ) ∈ interior s) (hmem : ∀ᵐ x ∂μ, x ∈ s)
    (hid : Integrable (fun x : ℝ => x) μ)
    (hpos : 0 < μ (Set.Ici (∫ x, x ∂μ))) :
    ENNReal.ofReal (Real.exp (-1)) ≤ μ (Set.Ici (∫ x, x ∂μ)) := by
  have h := (convex_integral_le_of_mean_interior μ hconv hmean hmem hid
    (integrable_negLogTail μ)).trans (integral_negLogTail_le_one μ)
  have hlog : -1 ≤ Real.log ((μ (Set.Ici (∫ x, x ∂μ))).toReal) := by
    change -Real.log ((μ (Set.Ici (∫ x, x ∂μ))).toReal) ≤ 1 at h
    linarith
  have hp := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ _)
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hp] at he
  simpa only [ENNReal.ofReal_toReal (measure_ne_top μ _)] using ENNReal.ofReal_le_ofReal he

lemma negLog_convex_of_multiplicative {s : Set ℝ} (hs : Convex ℝ s)
    (q : ℝ → ENNReal) (hq : ∀ x ∈ s, 0 < q x ∧ q x ≠ ⊤)
    (hmul : ∀ x ∈ s, ∀ y ∈ s, ∀ t : ℝ, 0 < t → t < 1 →
      q x ^ (1 - t) * q y ^ t ≤ q ((1 - t) * x + t * y)) :
    ConvexOn ℝ s (fun x => -Real.log (q x).toReal) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0, ha1]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hb1 : b < 1 := by linarith
  have hab' : 1 - b = a := by linarith
  have hm := hmul x hx y hy b hbp hb1
  rw [hab'] at hm
  have hz : a * x + b * y ∈ s := by simpa only [smul_eq_mul] using hs hx hy ha hb hab
  have hr := ENNReal.toReal_mono (hq _ hz).2 hm
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hr
  have hxpos := ENNReal.toReal_pos (hq x hx).1.ne' (hq x hx).2
  have hypos := ENNReal.toReal_pos (hq y hy).1.ne' (hq y hy).2
  have hlog := Real.log_le_log
    (mul_pos (Real.rpow_pos_of_pos hxpos a) (Real.rpow_pos_of_pos hypos b)) hr
  rw [Real.log_mul (Real.rpow_pos_of_pos hxpos a).ne'
    (Real.rpow_pos_of_pos hypos b).ne', Real.log_rpow hxpos, Real.log_rpow hypos] at hlog
  simp only [smul_eq_mul]
  linarith

lemma grunbaum_of_logConcave_tails (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hid : Integrable (fun x : ℝ => x) μ)
    (hmul : ∀ x y (t : ℝ), 0 < t → t < 1 →
      μ (Set.Ici x) ^ (1 - t) * μ (Set.Ici y) ^ t ≤
        μ (Set.Ici ((1 - t) * x + t * y))) :
    ENNReal.ofReal (Real.exp (-1)) ≤ μ (Set.Ici (∫ x, x ∂μ)) := by
  let m := ∫ x, x ∂μ
  let s := {x : ℝ | 0 < μ (Set.Ici x)}
  have hsconv : Convex ℝ s := Set.OrdConnected.convex
    ⟨fun _ _ y hy z hz => lt_of_lt_of_le hy
      (measure_mono (Set.Ici_subset_Ici.mpr hz.2))⟩
  have hsmeas : ∀ᵐ x ∂μ, x ∈ s := by
    rw [ae_iff]
    apply le_antisymm ?_ bot_le
    simpa [s] using tail_superuniform μ 0
  have hslog : ConvexOn ℝ s (negLogTail μ) :=
    negLog_convex_of_multiplicative hsconv (fun x => μ (Set.Ici x))
      (fun x hx => ⟨hx, measure_ne_top μ _⟩) (fun x _ y _ t ht ht' => hmul x y t ht ht')
  by_cases hr : ∃ r, m < r ∧ 0 < μ (Set.Ici r)
  · obtain ⟨r, hmr, hpr⟩ := hr
    have hsubset : Set.Iio r ⊆ s := fun x hx =>
      lt_of_lt_of_le hpr (measure_mono (Set.Ici_subset_Ici.mpr hx.le))
    have hmint : m ∈ interior s := interior_mono hsubset (by simpa using hmr)
    exact scalar_halfspace_mass μ hslog hmint hsmeas hid (hsubset hmr)
  · have hnull : μ (Set.Ioi m) = 0 := by
      apply le_antisymm ?_ bot_le
      apply measure_le_of_tail_bound μ _ measurableSet_Ioi 0
      intro x hx
      exact le_of_not_gt (fun hpos => hr ⟨x, hx, hpos⟩)
    have hle : ∀ᵐ x ∂μ, x ≤ m := by
      rw [ae_iff]
      change μ {x : ℝ | m < x} = 0 at hnull
      simpa only [not_le] using hnull
    have hzero : (∫ x, m - x ∂μ) = 0 := by
      rw [integral_sub (integrable_const m) hid]
      simp [m]
    have heq := (integral_eq_zero_iff_of_nonneg_ae
      (hle.mono (fun x hx => sub_nonneg.mpr hx))
      ((integrable_const m).sub hid)).mp hzero
    have htail : μ (Set.Ici m) = 1 := by
      rw [← measure_univ (μ := μ)]
      apply measure_congr
      filter_upwards [heq] with x hx
      simp only [Pi.zero_apply, sub_eq_zero] at hx
      simp [Set.mem_Ici, ← hx]
    change ENNReal.ofReal (Real.exp (-1)) ≤ μ (Set.Ici m)
    rw [htail]
    exact ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr (by norm_num))

lemma map_withDensity_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] (w : E → ENNReal) (ℓ : E →L[ℝ] ℝ) (r : ℝ) :
    (volume.withDensity w).map ℓ (Set.Ici r) = tailMass w ℓ r := by
  have hs : MeasurableSet (ℓ ⁻¹' Set.Ici r) :=
    ℓ.continuous.measurable measurableSet_Ici
  rw [Measure.map_apply ℓ.continuous.measurable measurableSet_Ici, withDensity_apply w hs]
  change (∫⁻ x in ℓ ⁻¹' Set.Ici r, w x) =
    ∫⁻ x, (ℓ ⁻¹' Set.Ici r).indicator w x
  rw [lintegral_indicator hs]

lemma density_halfspace_mass_of_tail {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] (w : E → ENNReal)
    [IsProbabilityMeasure (volume.withDensity w)] (ℓ : E →L[ℝ] ℝ)
    (hi : Integrable ℓ (volume.withDensity w))
    (htails : ∀ x y (t : ℝ), 0 < t → t < 1 →
      tailMass w ℓ x ^ (1 - t) * tailMass w ℓ y ^ t ≤
        tailMass w ℓ ((1 - t) * x + t * y)) :
    ENNReal.ofReal (Real.exp (-1)) ≤
      (volume.withDensity w) {x | (∫ y, ℓ y ∂volume.withDensity w) ≤ ℓ x} := by
  let μ := volume.withDensity w
  have hℓ := ℓ.continuous.measurable
  have hid : Integrable (fun x : ℝ => x) (μ.map ℓ) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable hℓ.aemeasurable).mpr hi
  have h := grunbaum_of_logConcave_tails (μ.map ℓ) hid (by
    intro x y t ht ht'
    simp only [μ, map_withDensity_tail]
    exact htails x y t ht ht')
  rw [integral_map (f := fun x : ℝ => x) hℓ.aemeasurable measurable_id.aestronglyMeasurable,
    Measure.map_apply hℓ measurableSet_Ici] at h
  exact h

lemma euclidean_tailMass_logConcave {d : ℕ} {w : EuclideanSpace ℝ (Fin (d + 1)) → ENNReal}
    (hw : Measurable w) (hlog : IsLogConcave w)
    (ℓ : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] ℝ) (r s t : ℝ) (ht : 0 < t) (ht' : t < 1) :
    tailMass w ℓ r ^ (1 - t) * tailMass w ℓ s ^ t ≤
      tailMass w ℓ ((1 - t) * r + t * s) := by
  apply PrekopaLeindler.prekopa_leindler_euclidean ht ht'
    (measurable_halfspaceDensity hw ℓ r) (measurable_halfspaceDensity hw ℓ s)
    (measurable_halfspaceDensity hw ℓ ((1 - t) * r + t * s))
  intro x y
  have ha : 0 < 1 - t := sub_pos.mpr ht'
  by_cases hx : r ≤ ℓ x
  · by_cases hy : s ≤ ℓ y
    · have hxy : (1 - t) * r + t * s ≤ ℓ ((1 - t) • x + t • y) := by
        simp only [map_add, map_smul, smul_eq_mul]
        nlinarith
      simpa only [halfspaceDensity, ite_eq_left hx, ite_eq_left hy, ite_eq_left hxy] using hlog x y t ht ht'
    · simp [halfspaceDensity, hy, ENNReal.zero_rpow_of_pos ht]
  · simp [halfspaceDensity, hx, ENNReal.zero_rpow_of_pos ha]

lemma density_halfspace_mass {d : ℕ} (w : Density (d + 1)) (hw : Measurable w)
    (hlog : IsLogConcave w) [IsProbabilityMeasure (volume.withDensity w)]
    (ℓ : (Fin (d + 1) → ℝ) →L[ℝ] ℝ) (hi : Integrable ℓ (volume.withDensity w)) :
    ENNReal.ofReal (Real.exp (-1)) ≤
      (volume.withDensity w) {x | (∫ y, ℓ y ∂volume.withDensity w) ≤ ℓ x} :=
  density_halfspace_mass_of_tail w ℓ hi (tailMass_logConcave hw hlog ℓ)

lemma euclidean_density_halfspace_mass {d : ℕ}
    (w : EuclideanSpace ℝ (Fin (d + 1)) → ENNReal) (hw : Measurable w)
    (hlog : IsLogConcave w) [IsProbabilityMeasure (volume.withDensity w)]
    (ℓ : EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] ℝ)
    (hi : Integrable ℓ (volume.withDensity w)) :
    ENNReal.ofReal (Real.exp (-1)) ≤
      (volume.withDensity w) {x | (∫ y, ℓ y ∂volume.withDensity w) ≤ ℓ x} :=
  density_halfspace_mass_of_tail w ℓ hi (euclidean_tailMass_logConcave hw hlog ℓ)

lemma euclidean_density_halfspace_mass_pos {d : ℕ} (hd : 0 < d)
    (w : EuclideanSpace ℝ (Fin d) → ENNReal) (hw : Measurable w)
    (hlog : IsLogConcave w) [IsProbabilityMeasure (volume.withDensity w)]
    (ℓ : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (hi : Integrable ℓ (volume.withDensity w)) :
    ENNReal.ofReal (Real.exp (-1)) ≤
      (volume.withDensity w) {x | (∫ y, ℓ y ∂volume.withDensity w) ≤ ℓ x} := by
  cases d with
  | zero => omega
  | succ d => exact euclidean_density_halfspace_mass w hw hlog ℓ hi

end LongTails.Proofs.LogConcaveHalfspaces
