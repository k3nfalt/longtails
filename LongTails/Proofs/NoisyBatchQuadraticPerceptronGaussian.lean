import LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry
import Mathlib.Analysis.Real.Pi.Bounds

namespace LongTails.Proofs.NoisyBatchQuadraticPerceptronGaussian

open LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
lemma gaussian_dual_second (L : StrongDual ℝ E) :
    (∫ x, (L x) ^ 2 ∂stdGaussian E) = ‖L‖ ^ 2 := by
  have h := variance_dual_stdGaussian L
  rw [variance_eq_integral (by fun_prop), integral_strongDual_stdGaussian] at h
  simpa using h
lemma gaussian_norm_second : (∫ x : E, ‖x‖ ^ 2 ∂stdGaussian E) = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  have hp (x : E) : ‖x‖ ^ 2 = ∑ i, (innerSL ℝ (b i) x) ^ 2 := by
    simpa using (b.sum_sq_inner_right x).symm
  simp_rw [hp]
  rw [integral_finsetSum]
  · simp_rw [gaussian_dual_second, innerSL_apply_norm, b.norm_eq_one]
    simp
  · intro i _
    exact (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ (b i)) 2 (by simp)).integrable_sq
lemma gaussian_integral_upper (f : E → ℝ) (hf : Integrable f (stdGaussian E))
    (C K : ℝ) (L : StrongDual ℝ E)
    (h : ∀ x, f x ≤ C + L x + K * ‖x‖ ^ 2) :
    (∫ x, f x ∂stdGaussian E) ≤ C + K * Module.finrank ℝ E := by
  have hL := IsGaussian.integrable_dual (stdGaussian E) L
  have hQ : Integrable (fun x : E => K * ‖x‖ ^ 2) (stdGaussian E) :=
    (IsGaussian.memLp_two_id (μ := stdGaussian E)).norm.integrable_sq.const_mul K
  have hS : Integrable (fun x : E => C + L x) (stdGaussian E) := (integrable_const C).add hL
  have hh := integral_mono hf (((integrable_const C).add hL).add hQ) h
  simp only [Pi.add_apply] at hh
  rw [integral_add hS hQ,
    integral_add (integrable_const C) hL, integral_const,
    integral_strongDual_stdGaussian, integral_const_mul, gaussian_norm_second] at hh
  simpa using hh

open MeasureTheory ProbabilityTheory
open LongTails.Setups.NoisyBatchQuadraticPerceptron
open scoped RealInnerProductSpace
lemma continuous_potential (P : Public) (data : Data P) (η : ℝ) :
    Continuous (fun w : Weights P.dimension => potential data η w.ofLp.1 w.ofLp.2) := by
  unfold potential positive negative
  fun_prop
lemma integrable_potential {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (P : Public) (data : Data P) (η : ℝ) (w : Ω → Weights P.dimension)
    (hw : MemLp w 2 μ) (hη : 0 ≤ η) (hsmall : η * P.radius ≤ 1 / 16)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    Integrable (fun ω => potential data η (w ω).ofLp.1 (w ω).ofLp.2) μ := by
  have hm := (continuous_potential P data η).comp_aestronglyMeasurable hw.aestronglyMeasurable
  have hi := hw.norm.integrable_sq.const_mul 2
  apply hi.mono' hm
  filter_upwards [] with ω
  have h := potential_bounds P data η (w ω).ofLp.1 (w ω).ofLp.2 hη hsmall hR
  have he : ‖w ω‖ ^ 2 = ‖(w ω).ofLp.1‖ ^ 2 + (w ω).ofLp.2 ^ 2 := by
    simpa using WithLp.prod_norm_sq_eq_of_L2 (w ω)
  have hn : 0 ≤ potential data η (w ω).ofLp.1 (w ω).ofLp.2 := by
    nlinarith [sq_nonneg ‖(w ω).ofLp.1‖, sq_nonneg ((w ω).ofLp.2)]
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  simpa only [he] using h.2

open LongTails.Setups.NoisyBatchQuadraticPerceptron
open LongTails.Proofs.NoisyBatchQuadraticPerceptronGeometry
lemma gaussian_potential_upper (P : Public) (data : Data P) (η σ : ℝ)
    (w : Weights P.dimension) (hη : 0 ≤ η) (hsmall : η * P.radius ≤ 1 / 16)
    (hR : ∀ i, ‖data i‖ ≤ P.radius) :
    (∫ z : Weights P.dimension, potential data η (w + σ • z).ofLp.1
      (w + σ • z).ofLp.2 ∂stdGaussian (Weights P.dimension)) ≤
      potential data η w.ofLp.1 w.ofLp.2 +
        6 * σ ^ 2 * Module.finrank ℝ (Weights P.dimension) := by
  let c := w.ofLp.1
  let v := w.ofLp.2
  let bp := max (v - η * positive data c) 0
  let bq := max (-v - η * negative data c) 0
  let a := (2 : ℝ) • c + (η * v) • mean data -
    (4 * η * bp) • positiveVector data c + (4 * η * bq) • positiveVector data (-c)
  let b := -2 * v + η * ⟪mean data, c⟫ + 4 * bp - 4 * bq
  let fst : Weights P.dimension →L[ℝ] Features P.dimension := WithLp.fstL ..
  let snd : Weights P.dimension →L[ℝ] ℝ := WithLp.sndL ..
  let L : StrongDual ℝ (Weights P.dimension) := σ • ((innerSL ℝ a).comp fst + b • snd)
  have hw : MemLp (fun z : Weights P.dimension => w + σ • z) 2
      (stdGaussian (Weights P.dimension)) :=
    (memLp_const w).add (IsGaussian.memLp_two_fun_id.const_smul σ)
  apply gaussian_integral_upper _ (integrable_potential P data η _ hw hη hsmall hR)
    _ (6 * σ ^ 2) L
  intro z
  have hp := potential_perturbation P data η c (σ • z.ofLp.1) v (σ * z.ofLp.2) hη hsmall hR
  have he : ‖z‖ ^ 2 = ‖z.ofLp.1‖ ^ 2 + z.ofLp.2 ^ 2 := by
    simpa using WithLp.prod_norm_sq_eq_of_L2 z
  change potential data η (c + σ • z.ofLp.1) (v + σ * z.ofLp.2) ≤ _
  have hl : L z = σ * (⟪a, z.ofLp.1⟫ + b * z.ofLp.2) := rfl
  rw [hl, he]
  dsimp only [a, b, bp, bq]
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right] at hp
  nlinarith [hp]

lemma weights_finrank (d : ℕ) : Module.finrank ℝ (Weights d) = d + 1 := by
  simpa [Weights, Features, LongTails.Setups.TwoSampleQuadraticPerceptron.Features,
    Module.finrank_prod] using
      (WithLp.linearEquiv 2 ℝ (Features d × ℝ)).finrank_eq

lemma gaussian_dual_fiber_null (L : StrongDual ℝ E) (hL : L ≠ 0) (a : ℝ) :
    stdGaussian E {x | L x = a} = 0 := by
  have hn : 0 < ‖L‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hL)
  have hv : (‖L‖ ^ 2).toNNReal ≠ 0 := by exact ne_of_gt (Real.toNNReal_pos.mpr hn)
  have :=  nullSingletonClass_gaussianReal (μ := 0) hv
  have hm := IsGaussian.map_eq_gaussianReal (μ := stdGaussian E) L
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian] at hm
  have hh := congrArg (fun μ : Measure ℝ => μ {a}) hm
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton a)] at hh
  simpa only [Set.preimage, Set.mem_singleton_iff, measure_singleton] using hh
lemma gaussian_affine_dual_zero (L : StrongDual ℝ E) (hL : L ≠ 0)
    (a σ : ℝ) (hσ : σ ≠ 0) : stdGaussian E {x | a + σ * L x = 0} = 0 := by
  have he : {x | a + σ * L x = 0} = {x | L x = -a / σ} := by
    ext x
    simp only [Set.mem_ofPred_eq, eq_div_iff hσ]
    constructor <;> intro h <;> nlinarith
  rw [he]
  exact gaussian_dual_fiber_null L hL _
lemma independent_gaussian_affine_zero {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → A) (Y : Ω → E)
    (hX : Measurable X) (hY : Measurable Y) (hi : IndepFun X Y μ)
    (hYlaw : μ.map Y = stdGaussian E) (a : A → ℝ) (ha : Measurable a)
    (L : StrongDual ℝ E) (hL : L ≠ 0) (σ : ℝ) (hσ : σ ≠ 0) :
    μ {ω | a (X ω) + σ * L (Y ω) = 0} = 0 := by
  have hm := hi.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  rw [hYlaw] at hm
  have hs : MeasurableSet {z : A × E | a z.1 + σ * L z.2 = 0} := by
    apply measurableSet_eq_fun _ measurable_const
    exact (ha.comp measurable_fst).add ((L.measurable.comp measurable_snd).const_mul σ)
  have hn : ((μ.map X).prod (stdGaussian E)) {z : A × E | a z.1 + σ * L z.2 = 0} = 0 := by
    apply Measure.measure_prod_null_of_ae_null hs
    filter_upwards [] with x
    exact gaussian_affine_dual_zero L hL (a x) σ hσ
  rw [← hm, Measure.map_apply (hX.prodMk hY) hs] at hn
  exact hn

lemma gaussian_energy_shift (w : E) (σ : ℝ) :
    (∫ z : E, ‖w + σ • z‖ ^ 2 ∂stdGaussian E) =
      ‖w‖ ^ 2 + σ ^ 2 * Module.finrank ℝ E := by
  let L : StrongDual ℝ E := (2 * σ) • innerSL ℝ w
  have hL : Integrable (fun z => L z) (stdGaussian E) := IsGaussian.integrable_dual _ L
  have hQ : Integrable (fun z : E => σ ^ 2 * ‖z‖ ^ 2) (stdGaussian E) :=
    IsGaussian.memLp_two_id.norm.integrable_sq.const_mul (σ ^ 2)
  have hS : Integrable (fun z : E => ‖w‖ ^ 2 + L z) (stdGaussian E) :=
    (integrable_const _).add hL
  have he (z : E) : ‖w + σ • z‖ ^ 2 = ‖w‖ ^ 2 + L z + σ ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right]
    change _ = ‖w‖ ^ 2 + (2 * σ) * ⟪w, z⟫ + σ ^ 2 * ‖z‖ ^ 2
    ring
  simp_rw [he]
  rw [integral_add hS hQ, integral_add (integrable_const _) hL, integral_const,
    integral_strongDual_stdGaussian, integral_const_mul, gaussian_norm_second]
  simp

lemma gaussian_density_interval_lower (b r x : ℝ) (hr : 0 ≤ r) (hx : x ∈ Set.Icc (b - r) (b + r)) :
    (1 / 4 : ℝ) * Real.exp (-((|b| + r) ^ 2) / 2) ≤ gaussianPDFReal 0 1 x := by
  rcases hx with ⟨hxl, hxu⟩
  have habs : |x| ≤ |b| + r := abs_le.mpr ⟨by linarith [neg_abs_le b], by linarith [le_abs_self b]⟩
  have hs : x ^ 2 ≤ (|b| + r) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg x) (add_nonneg (abs_nonneg b) hr)).mpr habs
  have he : Real.exp (-((|b| + r) ^ 2) / 2) ≤ Real.exp (-(x ^ 2) / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have hp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hsqrt : Real.sqrt (2 * Real.pi) ≤ 4 := by nlinarith [Real.pi_lt_four]
  have hi : (1 / 4 : ℝ) ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hp hsqrt
  have hh := mul_le_mul hi he (Real.exp_nonneg _) (inv_nonneg.mpr hp.le)
  simpa only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero] using hh
lemma gaussian_interval_lower (b r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal ((r / 2) * Real.exp (-((|b| + r) ^ 2) / 2)) ≤
      gaussianReal 0 1 (Set.Icc (b - r) (b + r)) := by
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0)]
  apply ENNReal.ofReal_le_ofReal
  have hi : IntegrableOn (fun _ : ℝ => (1 / 4 : ℝ) * Real.exp (-((|b| + r) ^ 2) / 2))
      (Set.Icc (b - r) (b + r)) volume := integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hb := setIntegral_mono_on hi (integrable_gaussianPDFReal 0 1).integrableOn
    measurableSet_Icc (fun x hx => gaussian_density_interval_lower b r x hr hx)
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at hb
  nlinarith
lemma gaussian_cube_lower {ι : Type*} [Fintype ι] (b : ι → ℝ) (r : ℝ) (hr : 0 ≤ r) :
    ENNReal.ofReal ((r / 2) ^ Fintype.card ι *
      Real.exp (-(∑ i, (|b i| + r) ^ 2) / 2)) ≤
    (Measure.pi (fun _ : ι => gaussianReal 0 1)) (Set.pi Set.univ (fun i => Set.Icc (b i - r) (b i + r))) := by
  classical
  rw [Measure.pi_pi]
  have hp := Finset.prod_le_prod (s := Finset.univ)
    (fun i _ => gaussian_interval_lower (b i) r hr)
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (by positivity) (Real.exp_nonneg _))] at hp
  have he : (∏ i, (r / 2) * Real.exp (-((|b i| + r) ^ 2) / 2)) =
      (r / 2) ^ Fintype.card ι * Real.exp (-(∑ i, (|b i| + r) ^ 2) / 2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
    congr 2
    rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
  rw [he] at hp
  exact hp
lemma gaussian_coordinate_square_bound {ι : Type*} [Fintype ι] (b : ι → ℝ) (a : ℝ) :
    (∑ i, (|b i| + a) ^ 2) ≤ 2 * (∑ i, b i ^ 2) + 2 * Fintype.card ι * a ^ 2 := by
  calc
    _ ≤ ∑ i, (2 * b i ^ 2 + 2 * a ^ 2) := Finset.sum_le_sum fun i _ => by
      nlinarith [sq_nonneg (|b i| - a), sq_abs (b i)]
    _ = _ := by simp [Finset.sum_add_distrib, Finset.mul_sum]; ring
lemma orthonormal_cube_mem_ball {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E) (c : E) (x : ι → ℝ) (a r : ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (har : Fintype.card ι * a ^ 2 ≤ r ^ 2)
    (hx : x ∈ Set.pi Set.univ (fun i => Set.Icc (b.repr c i - a) (b.repr c i + a))) :
    (∑ i, x i • b i) ∈ Metric.closedBall c r := by
  have hxi (i : ι) : (x i - b.repr c i) ^ 2 ≤ a ^ 2 := by
    have hi := hx i (Set.mem_univ i)
    have habs : |x i - b.repr c i| ≤ a := abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) ha).mpr habs
  have hs : ‖(∑ i, x i • b i) - c‖ ^ 2 ≤ r ^ 2 := by
    rw [b.sum_repr_symm (WithLp.toLp 2 x)]
    rw [← b.repr.symm_apply_apply c, ← map_sub, b.repr.symm.norm_map, EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : ι, a ^ 2 := Finset.sum_le_sum fun i _ => hxi i
      _ ≤ r ^ 2 := by simpa using har
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact (sq_le_sq₀ (norm_nonneg _) hr).mp hs
lemma gaussian_ball_lower_of_cube {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (b : OrthonormalBasis ι ℝ E) (c : E) (a r C : ℝ)
    (ha : 0 ≤ a) (hr : 0 ≤ r) (hC : 0 ≤ C) (hc : ‖c‖ ≤ C)
    (har : Fintype.card ι * a ^ 2 ≤ r ^ 2) :
    ENNReal.ofReal ((a / 2) ^ Fintype.card ι * Real.exp (-C ^ 2 - r ^ 2)) ≤
      stdGaussian E (Metric.closedBall c r) := by
  have hn : (∑ i, (b.repr c i) ^ 2) = ‖c‖ ^ 2 := by
    rw [← EuclideanSpace.real_norm_sq_eq, b.repr.norm_map]
  have hs := gaussian_coordinate_square_bound (fun i => b.repr c i) a
  rw [hn] at hs
  have hc2 : ‖c‖ ^ 2 ≤ C ^ 2 := (sq_le_sq₀ (norm_nonneg _) hC).mpr hc
  have he : Real.exp (-C ^ 2 - r ^ 2) ≤
      Real.exp (-(∑ i, (|b.repr c i| + a) ^ 2) / 2) := Real.exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ ENNReal.ofReal ((a / 2) ^ Fintype.card ι *
        Real.exp (-(∑ i, (|b.repr c i| + a) ^ 2) / 2)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left he (by positivity))
    _ ≤ (Measure.pi (fun _ : ι => gaussianReal 0 1))
        (Set.pi Set.univ (fun i => Set.Icc (b.repr c i - a) (b.repr c i + a))) :=
      gaussian_cube_lower _ a ha
    _ ≤ stdGaussian E (Metric.closedBall c r) := by
      rw [stdGaussian_eq_map_pi_orthonormalBasis b,
        Measure.map_apply (by fun_prop) Metric.isClosed_closedBall.measurableSet]
      exact measure_mono fun x hx => orthonormal_cube_mem_ball b c x a r ha hr har hx
lemma gaussian_ball_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (c : E) (r C : ℝ) (hD : 0 < Module.finrank ℝ E)
    (hr : 0 ≤ r) (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) :
    ENNReal.ofReal ((r / (2 * Real.sqrt (Module.finrank ℝ E))) ^ Module.finrank ℝ E *
      Real.exp (-C ^ 2 - r ^ 2)) ≤ stdGaussian E (Metric.closedBall c r) := by
  have hd : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hD
  have hs : 0 < Real.sqrt (Module.finrank ℝ E) := Real.sqrt_pos.mpr hd
  have hsq := Real.sq_sqrt hd.le
  have har : (Module.finrank ℝ E : ℝ) * (r / Real.sqrt (Module.finrank ℝ E)) ^ 2 ≤ r ^ 2 := by
    rw [div_pow, hsq]
    exact le_of_eq (mul_div_cancel₀ _ (ne_of_gt hd))
  have h := gaussian_ball_lower_of_cube (stdOrthonormalBasis ℝ E) c
    (r / Real.sqrt (Module.finrank ℝ E)) r C (div_nonneg hr hs.le) hr hC hc (by simpa using har)
  simpa only [Fintype.card_fin, div_div, mul_comm (Real.sqrt (Module.finrank ℝ E)) 2] using h

lemma scaled_gaussian_ball_lower {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (b : E) (σ r C : ℝ) (hD : 0 < Module.finrank ℝ E)
    (hσ : 0 < σ) (hr : 0 ≤ r) (hC : 0 ≤ C) (hb : ‖b‖ ≤ σ * C) :
    ENNReal.ofReal ((r / (2 * Real.sqrt (Module.finrank ℝ E))) ^ Module.finrank ℝ E *
      Real.exp (-C ^ 2 - r ^ 2)) ≤ stdGaussian E {z | ‖σ • z - b‖ ≤ σ * r} := by
  have hc : ‖σ⁻¹ • b‖ ≤ C := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hσ)]
    exact (inv_mul_le_iff₀ hσ).mpr hb
  apply (gaussian_ball_lower (σ⁻¹ • b) r C hD hr hC hc).trans
  apply measure_mono
  intro z hz
  have he : σ • z - b = σ • (z - σ⁻¹ • b) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]
  change ‖σ • z - b‖ ≤ σ * r
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hσ]
  exact mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz) hσ.le

end LongTails.Proofs.NoisyBatchQuadraticPerceptronGaussian
