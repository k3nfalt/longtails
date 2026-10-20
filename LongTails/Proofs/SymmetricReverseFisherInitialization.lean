import LongTails.Proofs.SymmetricReverseFisherExecution
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory Set WithLp
open scoped RealInnerProductSpace
open scoped ENNReal
namespace LongTails.Proofs.SymmetricReverseFisherInitialization
open LongTails.Algorithms.SymmetricReverseFisherGD
open LongTails.Setups.SymmetricGaussianReverseFisher
open LongTails.Proofs.SymmetricReverseFisherExecution
lemma coordinateLaw_interval {l u : ℝ} (_hlu : l ≤ u) :
    (coordinateLaw : Measure ℝ) (Icc l u) ≤ ENNReal.ofReal ((u-l)/2) := by
  change ((2:ℝ≥0∞)⁻¹ • volume.restrict (Icc (-1:ℝ) 1)) (Icc l u) ≤ _
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Icc, smul_eq_mul]
  have h : volume (Icc l u ∩ Icc (-1:ℝ) 1) ≤ volume (Icc l u) := measure_mono inter_subset_left
  calc
    _ ≤ (2:ℝ≥0∞)⁻¹ * volume (Icc l u) := by exact mul_le_mul_right h _
    _ = _ := by
      rw [Real.volume_Icc, ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
      norm_num
      rw [div_eq_mul_inv, mul_comm]
lemma coordinateLaw_strip {c b t : ℝ} (hc : c ≠ 0) (ht : 0 ≤ t) :
    (coordinateLaw : Measure ℝ) {z | |c*z+b| ≤ t} ≤ ENNReal.ofReal (t/|c|) := by
  have hpos : 0 < |c| := abs_pos.mpr hc
  have hs : {z : ℝ | |c*z+b| ≤ t} ⊆ Icc (-b/c-t/|c|) (-b/c+t/|c|) := by
    intro z hz
    have hid : z - (-b/c) = (c*z+b)/c := by field_simp; ring
    have h := (div_le_div_of_nonneg_right hz hpos.le)
    rw [← abs_div, ← hid] at h
    exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
  have hi := coordinateLaw_interval (show -b/c-t/|c| ≤ -b/c+t/|c| by linarith [div_nonneg ht hpos.le])
  have he : ((-b/c+t/|c|)-(-b/c-t/|c|))/2 = t/|c| := by ring
  rw [he] at hi
  exact (measure_mono hs).trans hi
lemma cube_linear_strip {n : ℕ} (c : Fin (n+1) → ℝ) (j : Fin (n+1))
    (hc : c j ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin (n+1) => (coordinateLaw : Measure ℝ)))
      {z | |∑ i, c i * z i| ≤ t} ≤ ENNReal.ofReal (t/|c j|) := by
  let μ : Measure ℝ := coordinateLaw
  let S : Set (Fin (n+1) → ℝ) := {z | |∑ i, c i * z i| ≤ t}
  have hS : MeasurableSet S := by
    apply measurableSet_le
    · fun_prop
    · exact measurable_const
  have hpres := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) j).symm
  change (Measure.pi (fun _ : Fin (n+1) => μ)) S ≤ _
  rw [← hpres.measure_preimage hS.nullMeasurableSet, Measure.prod_apply_symm (hpres.measurable hS)]
  calc
    _ ≤ ∫⁻ _ : Fin n → ℝ, ENNReal.ofReal (t/|c j|) ∂Measure.pi (fun _ => μ) := by
      apply lintegral_mono
      intro y
      have he : (fun z => (z,y)) ⁻¹' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) j).symm ⁻¹' S) =
          {z : ℝ | |c j*z + ∑ i : Fin n, c (j.succAbove i) * y i| ≤ t} := by
        ext z
        simp only [mem_preimage, S, mem_ofPred_eq, MeasurableEquiv.piFinSuccAbove_symm_apply]
        rw [Fin.sum_univ_succAbove _ j]
        simp [Fin.insertNthEquiv]
      dsimp only
      rw [he]
      exact coordinateLaw_strip hc ht
    _ = _ := by simp [μ]
lemma coordinateLaw_support : ∀ᵐ z ∂(coordinateLaw : Measure ℝ), |z| ≤ 1 := by
  have h : ∀ᵐ z ∂(volume.restrict (Icc (-1:ℝ) 1)), z ∈ Icc (-1:ℝ) 1 :=
    ae_restrict_mem measurableSet_Icc
  have hs := Measure.ae_smul_measure h ((2:ℝ≥0∞)⁻¹)
  filter_upwards [hs] with z hz
  exact abs_le.mpr hz
lemma cube_support (n : ℕ) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin n => (coordinateLaw : Measure ℝ)), ∀ i, |z i| ≤ 1 := by
  apply ae_all_iff.mpr
  intro i
  apply ae_of_ae_map (μ := Measure.pi (fun _ : Fin n => (coordinateLaw : Measure ℝ)))
    (f := fun z : Fin n → ℝ => z i) (p := fun y : ℝ => |y| ≤ 1)
    (measurable_pi_apply i).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin n => (coordinateLaw : Measure ℝ)) i).map_eq]
  exact coordinateLaw_support
lemma exists_large_coordinate {p : Params} (e : Space p) (he : ‖e‖ = 1) :
    ∃ j, 1 ≤ (p.dimension : ℝ) * (e j)^2 := by
  classical
  have : Nonempty (Fin p.dimension) := ⟨⟨0, p.dimension.pos⟩⟩
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun i => (e i)^2) Finset.univ_nonempty
  refine ⟨j, ?_⟩
  have hs : ∑ i, (e i)^2 ≤ ∑ _ : Fin p.dimension, (e j)^2 :=
    Finset.sum_le_sum (fun i hi => hj i hi)
  rw [← EuclideanSpace.real_norm_sq_eq, he] at hs
  simpa using hs
lemma cube_norm_sq {p : Params} (z : Fin p.dimension → ℝ) (hz : ∀ i, |z i| ≤ 1) :
    ‖(toLp 2 z : Space p)‖^2 ≤ (p.dimension : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change ∑ i, z i ^ 2 ≤ _
  have hs : ∑ i, z i ^ 2 ≤ ∑ _ : Fin p.dimension, (1:ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    exact (sq_le_one_iff_abs_le_one (z i)).mpr (hz i)
  simpa using hs
lemma cube_norm_coordinate {p : Params} (z : Fin p.dimension → ℝ) (e : Space p) (j : Fin p.dimension)
    (hz : ∀ i, |z i| ≤ 1) (hj : 1 ≤ (p.dimension : ℝ)*(e j)^2) :
    ‖(toLp 2 z : Space p)‖ ≤ (p.dimension : ℝ)*|e j| := by
  have hd : 0 ≤ (p.dimension : ℝ) := by positivity
  have hs := cube_norm_sq z hz
  have hh := mul_le_mul_of_nonneg_left hj hd
  have hp : ‖(toLp 2 z : Space p)‖^2 ≤ ((p.dimension : ℝ)*|e j|)^2 := by
    rw [mul_pow, sq_abs]
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hd (abs_nonneg _))).mp hp
lemma initial_inner_lower {p : Params} (z : Fin p.dimension → ℝ) (e : Space p) (j : Fin p.dimension)
    {δ : ℝ} (hδ : 0 < δ) (hz : ∀ i, |z i| ≤ 1)
    (hj : 1 ≤ (p.dimension : ℝ)*(e j)^2)
    (hraw : δ*|e j| ≤ |⟪(toLp 2 z : Space p),e⟫|) :
    δ / (p.dimension : ℝ) ≤ |⟪initial p z,e⟫| := by
  have hc : e j ≠ 0 := by intro h; rw [h] at hj; norm_num at hj
  have hpos : 0 < |⟪(toLp 2 z : Space p),e⟫| := (mul_pos hδ (abs_pos.mpr hc)).trans_le hraw
  have hz0 : (toLp 2 z : Space p) ≠ 0 := by
    intro h
    rw [h, inner_zero_left, abs_zero] at hpos
    exact lt_irrefl _ hpos
  have hn : 0 < ‖(toLp 2 z : Space p)‖ := norm_pos_iff.mpr hz0
  have hd : 0 < (p.dimension : ℝ) := by exact_mod_cast p.dimension.pos
  unfold initial
  dsimp only
  rw [ite_eq_right hz0, real_inner_smul_left, abs_mul, abs_inv, abs_of_pos hn,
    mul_comm, ← div_eq_mul_inv]
  apply (div_le_div_iff₀ hd hn).mpr
  have hh := mul_le_mul_of_nonneg_left (cube_norm_coordinate z e j hz hj) hδ.le
  have hh' := mul_le_mul_of_nonneg_left hraw hd.le
  nlinarith
lemma inner_toLp_sum {p : Params} (z : Fin p.dimension → ℝ) (e : Space p) :
    ⟪(toLp 2 z : Space p),e⟫ = ∑ i, e i * z i := by
  simp [PiLp.inner_apply, mul_comm]
lemma cube_linear_strip_of_pos {n : ℕ} (hn : 0 < n) (c : Fin n → ℝ) (j : Fin n)
    (hc : c j ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin n => (coordinateLaw : Measure ℝ)))
      {z | |∑ i, c i * z i| ≤ t} ≤ ENNReal.ofReal (t/|c j|) := by
  cases n with
  | zero => omega
  | succ n => exact cube_linear_strip c j hc ht
lemma initial_small_projection {p : Params} (e : Space p) (he : ‖e‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    (Measure.pi (fun _ : Fin p.dimension => (coordinateLaw : Measure ℝ)))
      {z | |⟪initial p z,e⟫| < δ/(p.dimension : ℝ)} ≤ ENNReal.ofReal δ := by
  obtain ⟨j,hj⟩ := exists_large_coordinate e he
  have hc : e j ≠ 0 := by intro h; rw [h] at hj; norm_num at hj
  have ht := cube_linear_strip_of_pos p.dimension.pos (fun i => e i) j hc
    (mul_nonneg hδ.le (abs_nonneg (e j)))
  have hcancel : δ*|e j|/|e j| = δ := mul_div_cancel_right₀ δ (abs_ne_zero.mpr hc)
  rw [hcancel] at ht
  apply le_trans _ ht
  apply measure_mono_ae
  filter_upwards [cube_support (p.dimension : ℕ)] with z hz
  intro hbad
  by_contra hraw
  have hraw' : δ*|e j| ≤ |⟪(toLp 2 z : Space p),e⟫| := by
    rw [inner_toLp_sum]
    exact le_of_lt (lt_of_not_ge hraw)
  have h := initial_inner_lower z e j hδ hz hj hraw'
  exact (not_lt_of_ge h) hbad
lemma initial_projection_probability {p : Params} (e : Space p) (he : ‖e‖ = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (1-δ) ≤
      (Measure.pi (fun _ : Fin p.dimension => (coordinateLaw : Measure ℝ)))
        {z | δ/(p.dimension : ℝ) ≤ |⟪initial p z,e⟫|} := by
  have hi := initial_measurable p
  have hmeas : MeasurableSet {z | |⟪initial p z,e⟫| < δ/(p.dimension : ℝ)} := by
    apply measurableSet_lt
    · fun_prop
    · exact measurable_const
  have heq : {z | δ/(p.dimension : ℝ) ≤ |⟪initial p z,e⟫|} =
      {z | |⟪initial p z,e⟫| < δ/(p.dimension : ℝ)}ᶜ := by ext z; simp
  rw [heq, measure_compl hmeas (measure_ne_top _ _), measure_univ,
    ENNReal.ofReal_sub _ hδ.le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left (initial_small_projection e he hδ) 1
end LongTails.Proofs.SymmetricReverseFisherInitialization
