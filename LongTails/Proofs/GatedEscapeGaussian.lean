import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Real.Pi.Bounds

namespace LongTails.Proofs.GatedEscapeGaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma gaussianPDFReal_le_half (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 / 2 := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  have hpi : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.pi_gt_three])
  have he : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hinv : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hpi
  have hpos : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left he hpos
    _ ≤ 1 / 2 := by rw [mul_one]; exact hinv

lemma gaussianReal_le_of_diam (s : Set ℝ) {D : ℝ}
    (hs : ∀ a ∈ s, ∀ a' ∈ s, |a - a'| ≤ D) : gaussianReal 0 1 s ≤ ENNReal.ofReal (D / 2) := by
  rw [gaussianReal_apply 0 one_ne_zero s]
  have hb : ∀ x, gaussianPDF 0 1 x ≤ ENNReal.ofReal (1 / 2) := fun x => by
    rw [gaussianPDF_def]; exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_half x)
  calc ∫⁻ x in s, gaussianPDF 0 1 x ≤ ∫⁻ _ in s, ENNReal.ofReal (1 / 2) := lintegral_mono hb
    _ = ENNReal.ofReal (1 / 2) * volume s := by rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (1 / 2) * ENNReal.ofReal D := by
      gcongr
      refine (Real.volume_le_diam s).trans ?_
      apply Metric.ediam_le
      intro a ha a' ha'
      rw [edist_dist, Real.dist_eq]
      exact ENNReal.ofReal_le_ofReal (hs a ha a' ha')
    _ = ENNReal.ofReal (D / 2) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]; ring_nf

theorem gauss_slice {n : ℕ} (b : OrthonormalBasis (Fin (n + 1)) ℝ E) (j0 : Fin (n + 1)) (S : Set E)
    (hSm : MeasurableSet S) {D : ℝ}
    (hslice : ∀ u : E, ∀ a a' : ℝ, u + a • b j0 ∈ S → u + a' • b j0 ∈ S → |a - a'| ≤ D) :
    stdGaussian E S ≤ ENNReal.ofReal (D / 2) := by
  have hmeas : Measurable (fun x : Fin (n + 1) → ℝ => ∑ i, x i • b i) := by fun_prop
  rw [stdGaussian_eq_map_pi_orthonormalBasis b, Measure.map_apply hmeas hSm]
  set Pre := (fun x : Fin (n + 1) → ℝ => ∑ i, x i • b i) ⁻¹' S with hPre
  have hPm : MeasurableSet Pre := hmeas hSm
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) j0
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j0 with he
  have hpre : Pre = e ⁻¹' (e.symm ⁻¹' Pre) := by
    ext x; simp
  rw [hpre, hmp.measure_preimage (e.symm.measurable hPm).nullMeasurableSet]
  rw [Measure.prod_apply_symm (e.symm.measurable hPm)]
  have hbound : ∀ y : Fin n → ℝ,
      gaussianReal 0 1 ((fun a => (a, y)) ⁻¹' (e.symm ⁻¹' Pre)) ≤ ENNReal.ofReal (D / 2) := by
    intro y
    apply gaussianReal_le_of_diam _
    intro a ha a' ha'
    simp only [Set.mem_preimage, hPre] at ha ha'
    have hsum : ∀ c : ℝ, ∑ i, (e.symm (c, y)) i • b i =
        (∑ j, y j • b (j0.succAbove j)) + c • b j0 := by
      intro c
      rw [Fin.sum_univ_succAbove _ j0]
      simp [he, MeasurableEquiv.piFinSuccAbove_symm_apply, add_comm]
    rw [hsum] at ha ha'
    exact hslice _ a a' ha ha'
  calc ∫⁻ y, gaussianReal 0 1 ((fun a => (a, y)) ⁻¹' (e.symm ⁻¹' Pre))
        ∂Measure.pi (fun j : Fin n => gaussianReal 0 1) ≤
      ∫⁻ _, ENNReal.ofReal (D / 2) ∂Measure.pi (fun j : Fin n => gaussianReal 0 1) :=
        lintegral_mono hbound
    _ = ENNReal.ofReal (D / 2) := by simp

lemma integral_sq_gaussianReal : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa [integral_id_gaussianReal] using h

theorem integral_norm_sq_stdGaussian :
    ∫ z, ‖z‖ ^ 2 ∂(stdGaussian E) = Module.finrank ℝ E := by
  set b := stdOrthonormalBasis ℝ E
  have hmeas : Measurable (fun x : Fin (Module.finrank ℝ E) → ℝ => ∑ i, x i • b i) := by fun_prop
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    integral_map hmeas.aemeasurable (by fun_prop : Measurable fun z : E => ‖z‖ ^ 2).aestronglyMeasurable]
  have hn : ∀ x : Fin (Module.finrank ℝ E) → ℝ, ‖∑ i, x i • b i‖ ^ 2 = ∑ i, x i ^ 2 := by
    intro x
    rw [← b.sum_sq_inner_right (∑ i, x i • b i)]
    congr 1; funext j
    rw [inner_sum]
    simp_rw [inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
    simp
  simp_rw [hn]
  have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have hint : ∀ i : Fin (Module.finrank ℝ E), Integrable (fun x : Fin (Module.finrank ℝ E) → ℝ => x i ^ 2)
      (Measure.pi fun _ => gaussianReal 0 1) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1) (f := fun x : ℝ => x ^ 2) h2
  rw [integral_finsetSum _ (fun i _ => hint i)]
  have hone : ∀ i : Fin (Module.finrank ℝ E),
      ∫ x : Fin (Module.finrank ℝ E) → ℝ, x i ^ 2 ∂(Measure.pi fun _ => gaussianReal 0 1) = 1 := by
    intro i
    rw [integral_comp_eval (μ := fun _ : Fin (Module.finrank ℝ E) => gaussianReal 0 1)
      (f := fun x : ℝ => x ^ 2) h2.aestronglyMeasurable]
    exact integral_sq_gaussianReal
  simp [hone]

theorem norm_sq_tail (c : ℝ) (hc : 0 < c) :
    ∫ z, (if c * Module.finrank ℝ E < ‖z‖ ^ 2 then (1 : ℝ) else 0) ∂(stdGaussian E) ≤ 1 / c := by
  have hd : 0 < (Module.finrank ℝ E : ℝ) ∨ (Module.finrank ℝ E : ℝ) = 0 := by
    rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with h | h
    · right; simp [h]
    · left; exact_mod_cast h
  rcases hd with hd | hd
  · have hpt : ∀ z : E, (if c * Module.finrank ℝ E < ‖z‖ ^ 2 then (1 : ℝ) else 0) ≤
        ‖z‖ ^ 2 / (c * Module.finrank ℝ E) := by
      intro z
      split_ifs with h
      · rw [le_div_iff₀ (by positivity)]; linarith
      · positivity
    have hi2 : Integrable (fun z : E => ‖z‖ ^ 2) (stdGaussian E) := by
      have := integral_norm_sq_stdGaussian (E := E)
      by_contra hni
      rw [integral_undef hni] at this
      linarith
    have hm : Measurable (fun z : E => if c * Module.finrank ℝ E < ‖z‖ ^ 2 then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) measurable_const measurable_const
    have hi1 : Integrable (fun z : E => if c * Module.finrank ℝ E < ‖z‖ ^ 2 then (1 : ℝ) else 0)
        (stdGaussian E) :=
      Integrable.of_bound (C := 1) hm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
        split_ifs <;> simp)
    refine (integral_mono hi1 (hi2.div_const _) hpt).trans ?_
    rw [integral_div, integral_norm_sq_stdGaussian]
    rw [div_le_div_iff₀ (by positivity) hc]
    nlinarith
  · have : ∀ z : E, ¬ (c * Module.finrank ℝ E < ‖z‖ ^ 2) := by
      intro z
      have hz : z = 0 := by
        have h0 : Module.finrank ℝ E = 0 := by exact_mod_cast hd
        have : Subsingleton E := Module.finrank_zero_iff.mp h0
        exact Subsingleton.elim z 0
      rw [hz, hd]; simp
    simp only [this, ↓reduceIte, integral_zero]
    positivity

end LongTails.Proofs.GatedEscapeGaussian
