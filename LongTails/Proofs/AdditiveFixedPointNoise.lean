import LongTails.Proofs.AdditiveFixedPointGaussian
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LongTails.Proofs.AdditiveFixedPointNoise

open AdditiveFixedPointGaussian

noncomputable abbrev law {d : ℕ} (v : NNReal) (u : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun i => gaussianReal (u i) v

lemma law_density {d : ℕ} {v : NNReal} (hv : v ≠ 0) (u : Fin d → ℝ) :
    law v u = volume.withDensity (weight v u) := by
  classical
  apply Measure.pi_eq
  intro s hs
  have hd : Integrable (density v u) := by
    by_contra hn
    simpa [integral_undef hn] using density_integral hv u
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  unfold weight
  rw [← ofReal_integral_eq_lintegral_ofReal hd.integrableOn (ae_of_all _ (density_nonneg _ _))]
  rw [volume_pi, Measure.restrict_pi_pi]
  simp only [density, integral_fintype_prod_eq_prod, gaussianReal_apply_eq_integral _ hv,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (gaussianPDFReal_nonneg _ _))]

lemma shift_law {d : ℕ} (v : NNReal) (u : Fin d → ℝ) :
    Measure.map (fun z => u + z) (law v 0) = law v u := by
  unfold law
  change Measure.map (fun (x : Fin d → ℝ) i => u i + x i) _ = _
  rw [Measure.pi_map_pi (f := fun i => (u i + ·))
    (fun i => (measurable_const.add measurable_id).aemeasurable)]
  simp_rw [Pi.zero_apply, gaussianReal_map_const_add, zero_add]

set_option maxHeartbeats 600000 in
lemma run_shift {d : ℕ} {v : NNReal} (hv : v ≠ 0) (u : Fin d → ℝ)
    {f : (Fin d → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z, f (u + z) ∂law v 0) = ∫⁻ z, weight v u z * f z := by
  have hm : Measurable (fun z : Fin d → ℝ => u + z) := by fun_prop
  rw [← lintegral_map hf hm, shift_law, law_density hv u]
  apply lintegral_withDensity_eq_lintegral_mul _ _ hf
  unfold weight density
  exact ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun i _ =>
    (measurable_gaussianPDFReal (u i) v).comp (measurable_pi_apply i))

lemma square_tilt {v : NNReal} (hv : v ≠ 0) (z : ℝ) :
    Real.exp (z ^ 2 / (4 * v)) * gaussianPDFReal 0 v z =
      Real.sqrt 2 * gaussianPDFReal 0 (2 * v) z := by
  have hpos : 0 < (v : ℝ) := by positivity
  simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_mul, NNReal.coe_ofNat]
  rw [mul_left_comm, ← Real.exp_add]
  have hid : z ^ 2 / (4 * v) + -(z ^ 2) / (2 * v) = -(z ^ 2) / (2 * (2 * v)) := by
    field_simp
    ring
  have hs : Real.sqrt (2 * Real.pi * (2 * (v : ℝ))) =
      Real.sqrt 2 * Real.sqrt (2 * Real.pi * v) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hid, hs, mul_inv]
  field_simp

lemma exp_square_mean {v : NNReal} (hv : v ≠ 0) :
    ∫ z, Real.exp (z ^ 2 / (4 * v)) ∂gaussianReal 0 v = Real.sqrt 2 := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  simp only [smul_eq_mul]
  simp_rw [mul_comm (gaussianPDFReal _ _ _) _, square_tilt hv]
  rw [integral_const_mul, integral_gaussianPDFReal_eq_one _ (by positivity), mul_one]

lemma law_memLp {d : ℕ} (v : NNReal) (k : NNReal) :
    MemLp (fun z : Fin d → ℝ => z) k (law v 0) := by
  apply MemLp.of_eval
  intro i
  exact (memLp_id_gaussianReal (μ := 0) (v := v) k).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 v) i)

lemma law_centered {d : ℕ} (v : NNReal) :
    ∫ z : Fin d → ℝ, z ∂law v 0 = 0 := by
  have hi := (law_memLp (d := d) v 1).integrable (by simp)
  ext i
  rw [eval_integral (f := fun z : Fin d → ℝ => z) (fun j => hi.eval j) i]
  have hm := measurePreserving_eval (fun _ : Fin d => gaussianReal 0 v) i
  change ∫ z : Fin d → ℝ, id (z i) ∂law v 0 = 0
  rw [← integral_map (φ := fun z : Fin d → ℝ => z i) hm.measurable.aemeasurable
    (by fun_prop : AEStronglyMeasurable id ((law v 0).map (fun z => z i)))]
  rw [show (law v (0 : Fin d → ℝ)).map (fun z => z i) = gaussianReal 0 v from hm.map_eq]
  exact integral_id_gaussianReal

lemma exp_square_integrable {v : NNReal} (hv : v ≠ 0) :
    Integrable (fun z : ℝ => Real.exp (z ^ 2 / (4 * v))) (gaussianReal 0 v) := by
  by_contra hn
  have h := exp_square_mean hv
  rw [integral_undef hn] at h
  linarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]

lemma max_square_bound {d : ℕ} (hd : 0 < d) {v : NNReal} (hv : v ≠ 0)
    (z : Fin d → ℝ) :
    ‖z‖ ^ 2 ≤ 4 * v * (Real.log d + (∑ i, Real.exp (z i ^ 2 / (4 * v))) / d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hv' : (0 : ℝ) < v := by positivity
  let B := 4 * v * (Real.log d + (∑ i, Real.exp (z i ^ 2 / (4 * v))) / d)
  have hb : 0 ≤ B := by
    dsimp [B]
    have hlog := Real.log_nonneg (show 1 ≤ (d : ℝ) by exact_mod_cast hd)
    positivity
  have hs : ‖z‖ ≤ Real.sqrt B := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) hb).mpr
    rw [Real.norm_eq_abs, sq_abs]
    have ht := Real.add_one_le_exp (z i ^ 2 / (4 * v) - Real.log d)
    rw [Real.exp_sub, Real.exp_log hd'] at ht
    have hsum := Finset.single_le_sum (f := fun i : Fin d => Real.exp (z i ^ 2 / (4 * v)))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
    have he : z i ^ 2 / (4 * v) ≤ Real.log d + (∑ i, Real.exp (z i ^ 2 / (4 * v))) / d := by
      linarith [div_le_div_of_nonneg_right hsum hd'.le]
    exact (div_le_iff₀ (show 0 < 4 * (v : ℝ) by positivity)).mp he |>.trans_eq (mul_comm _ _)
  simpa only [Real.sq_sqrt hb] using (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr hs

lemma second_moment {d : ℕ} (hd : 0 < d) {v : NNReal} (hv : v ≠ 0) :
    ∫ z : Fin d → ℝ, ‖z‖ ^ 2 ∂law v 0 ≤ 4 * v * (Real.log d + 2) := by
  have hi := (law_memLp (d := d) v 2).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  let μ := law v (0 : Fin d → ℝ)
  let f (i : Fin d) (z : Fin d → ℝ) := Real.exp (z i ^ 2 / (4 * v))
  have hi' (i : Fin d) : Integrable (f i) μ :=
    (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 v) i).integrable_comp_of_integrable
      (exp_square_integrable hv)
  have he (i : Fin d) : ∫ z, f i z ∂μ = Real.sqrt 2 := by
    have hm : μ.map (fun z => z i) = gaussianReal 0 v :=
      (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 v) i).map_eq
    have h := integral_map (μ := μ) (measurable_pi_apply i).aemeasurable
      (f := fun z : ℝ => Real.exp (z ^ 2 / (4 * v))) (by fun_prop)
    rw [hm, exp_square_mean hv] at h
    exact h.symm
  have hs : Integrable (fun z => ∑ i, f i z) μ := integrable_finsetSum _ fun i _ => hi' i
  have hb := integral_mono (μ := μ) (f := fun z : Fin d → ℝ => ‖z‖ ^ 2)
    (g := fun z => 4 * v * (Real.log d + (∑ i, f i z) / d)) hi
    (((integrable_const _).add (hs.div_const _)).const_mul _) (max_square_bound hd hv)
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [integral_const_mul, integral_add (integrable_const _) (hs.div_const _),
    integral_const, probReal_univ, one_smul, integral_div, integral_finsetSum _ (fun i _ => hi' i)] at hb
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_cancel_left₀ _ hd'] at hb
  exact hb.trans (by gcongr; norm_num)

end LongTails.Proofs.AdditiveFixedPointNoise
