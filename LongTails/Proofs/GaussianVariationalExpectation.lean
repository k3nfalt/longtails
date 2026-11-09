import LongTails.Proofs.GaussianVariationalGeometry
import Mathlib.Topology.Instances.Matrix

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace OracleTemplate.GaussianVariational

open LongTails.Setups.GaussianVariationalInference

variable {d : ℕ}

structure Potential (L μ : ℝ) (V : Point d → ℝ) : Prop where
  grad : ∀ x, HasGradientAt V (gradient V x) x
  lip : ∀ x y, ‖gradient V x - gradient V y‖ ≤ L * ‖x - y‖
  strong : ∀ x y, μ * ‖x - y‖ ^ 2 ≤ ⟪gradient V x - gradient V y, x - y⟫
  pos : 0 < μ
  le : μ ≤ L

namespace Potential

variable {L μ : ℝ} {V : Point d → ℝ}

lemma L_pos (h : Potential L μ V) : 0 < L := lt_of_lt_of_le h.pos h.le

lemma continuous_grad (h : Potential L μ V) : Continuous (gradient V) := by
  refine Metric.continuous_iff.2 fun x ε hε => ⟨ε / (L + 1), by have := h.L_pos; positivity,
    fun y hy => ?_⟩
  rw [dist_eq_norm] at hy ⊢
  have hL := h.L_pos
  have h1 := h.lip y x
  have h2 : L * ‖y - x‖ ≤ L * (ε / (L + 1)) := mul_le_mul_of_nonneg_left hy.le hL.le
  have h3 : L * (ε / (L + 1)) < ε := by
    rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

lemma continuous_fn (h : Potential L μ V) : Continuous V :=
  continuous_iff_continuousAt.2 fun x => (h.grad x).hasFDerivAt.continuousAt

lemma convex (h : Potential L μ V) : ConvexOn ℝ univ V :=
  HiddenDecompositionEnergy.strongly_monotone_gradient_convex h.grad h.strong h.pos.le

lemma support (h : Potential L μ V) (x y : Point d) :
    V x + ⟪gradient V x, y - x⟫ + μ / 2 * ‖y - x‖ ^ 2 ≤ V y :=
  HiddenDecompositionEnergy.strongly_monotone_gradient_support h.grad h.strong x y

lemma upper (h : Potential L μ V) (x y : Point d) :
    V y ≤ V x + ⟪gradient V x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 :=
  Gradient.smooth_upper_bound h.grad h.lip x y

lemma cocoercive (h : Potential L μ V) (a b : Point d) :
    ‖gradient V a - gradient V b‖ ^ 2 ≤ 2 * L * (V a - V b - ⟪gradient V b, a - b⟫) :=
  SampledConvex.cocoercive h.L_pos h.convex h.grad h.lip a b

lemma cocoercive_inner (h : Potential L μ V) (a b : Point d) :
    ‖gradient V a - gradient V b‖ ^ 2 ≤ L * ⟪gradient V a - gradient V b, a - b⟫ := by
  have h1 := h.cocoercive a b
  have h2 := h.cocoercive b a
  rw [norm_sub_rev] at h2
  have he : ⟪gradient V a - gradient V b, a - b⟫ =
      ⟪gradient V a, a - b⟫ - ⟪gradient V b, a - b⟫ := inner_sub_left _ _ _
  have he2 : ⟪gradient V a, b - a⟫ = -⟪gradient V a, a - b⟫ := by
    rw [← inner_neg_right, neg_sub]
  rw [he2] at h2
  rw [he]
  nlinarith

lemma grad_sq_le (h : Potential L μ V) (x : Point d) :
    ‖gradient V x‖ ^ 2 ≤ 2 * ‖gradient V 0‖ ^ 2 + 2 * L ^ 2 * ‖x‖ ^ 2 := by
  have h1 := h.lip x 0
  rw [sub_zero] at h1
  have h2 : ‖gradient V x‖ ≤ ‖gradient V 0‖ + L * ‖x‖ := by
    calc ‖gradient V x‖ = ‖(gradient V x - gradient V 0) + gradient V 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖gradient V x - gradient V 0‖ + ‖gradient V 0‖ := norm_add_le _ _
      _ ≤ L * ‖x‖ + ‖gradient V 0‖ := by linarith
      _ = _ := by ring
  have hn := norm_nonneg (gradient V x)
  have hn0 := norm_nonneg (gradient V 0)
  have hx := norm_nonneg x
  nlinarith [sq_nonneg (‖gradient V 0‖ - L * ‖x‖), h.L_pos]

lemma abs_bound (h : Potential L μ V) (x : Point d) :
    |V x| ≤ (|V 0| + ‖gradient V 0‖ + L) * (1 + ‖x‖ ^ 2) := by
  have hu := h.upper 0 x
  have hl := Gradient.convex_support h.convex h.grad 0 x
  rw [sub_zero] at hu hl
  have hc := real_inner_le_norm (gradient V 0) x
  have hc' := neg_le_of_abs_le (abs_real_inner_le_norm (gradient V 0) x)
  have hx := norm_nonneg x
  have hg := norm_nonneg (gradient V 0)
  have hL := h.L_pos
  have hxx : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  rw [abs_le]
  constructor
  · nlinarith [abs_nonneg (V 0), neg_abs_le (V 0), mul_le_mul_of_nonneg_left hxx hg]
  · nlinarith [abs_nonneg (V 0), le_abs_self (V 0), mul_le_mul_of_nonneg_left hxx hg]

end Potential

lemma continuous_sample : Continuous (fun z : (Location d × Scale d) × (Fin d → ℝ) =>
    sample z.1.1 z.1.2 z.2) := by
  unfold sample
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ)).comp ((continuous_fst.comp continuous_fst).add
    (Continuous.matrix_mulVec (continuous_snd.comp continuous_fst) continuous_snd))

lemma measurable_sample : Measurable (fun z : (Location d × Scale d) × (Fin d → ℝ) =>
    sample z.1.1 z.1.2 z.2) := continuous_sample.measurable

lemma continuous_sample_fixed (m : Location d) (C : Scale d) :
    Continuous (fun ξ : Fin d → ℝ => sample m C ξ) := by
  unfold sample
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ)).comp (continuous_const.add
    (Continuous.matrix_mulVec continuous_const continuous_id))

lemma measurable_sample_fixed (m : Location d) (C : Scale d) :
    Measurable (fun ξ : Fin d → ℝ => sample m C ξ) := (continuous_sample_fixed m C).measurable

lemma norm_sample_sq_le (m : Location d) (C : Scale d) (ξ : Fin d → ℝ) :
    ‖sample m C ξ‖ ^ 2 ≤ 2 * sqDist m 0 C 0 * (1 + sqNorm ξ) := by
  have h := norm_sample_sub_sq_le m 0 C 0 ξ
  have h0 : sample (0 : Location d) (0 : Scale d) ξ = 0 := by
    unfold sample
    rw [mulVec_zero_left, add_zero]
    rfl
  rwa [h0, sub_zero] at h

lemma integral_lin (a : Fin d → ℝ) :
    Integrable (fun ξ : Fin d → ℝ => ∑ j, a j * ξ j) (noiseLaw d) ∧
      ∫ ξ, ∑ j, a j * ξ j ∂noiseLaw d = 0 := by
  have hi : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun ξ : Fin d → ℝ => a j * ξ j) (noiseLaw d) :=
    fun j _ => (integrable_coord j).const_mul (a j)
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  rw [integral_finsetSum _ hi]
  simp [integral_const_mul, integral_coord]

lemma integral_quad (b : Fin d → Fin d → ℝ) :
    Integrable (fun ξ : Fin d → ℝ => ∑ j, ∑ k, b j k * (ξ j * ξ k)) (noiseLaw d) ∧
      ∫ ξ, ∑ j, ∑ k, b j k * (ξ j * ξ k) ∂noiseLaw d = ∑ j, b j j := by
  have hi : ∀ j k, Integrable (fun ξ : Fin d → ℝ => b j k * (ξ j * ξ k)) (noiseLaw d) :=
    fun j k => (integrable_coord_mul j k).const_mul (b j k)
  have hi2 : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun ξ : Fin d → ℝ => ∑ k, b j k * (ξ j * ξ k)) (noiseLaw d) :=
    fun j _ => integrable_finsetSum _ fun k _ => hi j k
  refine ⟨integrable_finsetSum _ hi2, ?_⟩
  rw [integral_finsetSum _ hi2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => hi j k]
  simp only [integral_const_mul, integral_coord_mul, mul_ite, mul_one, mul_zero]
  simp

lemma isotropy (u : Location d) (U : Scale d) :
    Integrable (fun ξ : Fin d → ℝ => ‖(WithLp.toLp 2 (u + Matrix.mulVec U ξ) : Point d)‖ ^ 2)
      (noiseLaw d) ∧
      ∫ ξ, ‖(WithLp.toLp 2 (u + Matrix.mulVec U ξ) : Point d)‖ ^ 2 ∂noiseLaw d =
        (∑ i, u i ^ 2) + ∑ i, ∑ j, U i j ^ 2 := by
  have hexp : ∀ ξ : Fin d → ℝ, ‖(WithLp.toLp 2 (u + Matrix.mulVec U ξ) : Point d)‖ ^ 2 =
      (∑ i, u i ^ 2) + ∑ j, (∑ i, 2 * u i * U i j) * ξ j +
        ∑ j, ∑ k, (∑ i, U i j * U i k) * (ξ j * ξ k) := by
    intro ξ
    rw [norm_sq_eq_sum]
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct]
    have hsq : ∀ i, (u i + ∑ j, U i j * ξ j) ^ 2 =
        u i ^ 2 + ∑ j, 2 * u i * U i j * ξ j + ∑ j, ∑ k, U i j * U i k * (ξ j * ξ k) := by
      intro i
      have h1 : ∑ j, 2 * u i * U i j * ξ j = 2 * u i * ∑ j, U i j * ξ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      have h2 : ∑ j, ∑ k, U i j * U i k * (ξ j * ξ k) = (∑ j, U i j * ξ j) ^ 2 := by
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      rw [h1, h2]
      ring
    simp_rw [hsq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    · congr 1
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_mul]
  simp_rw [hexp]
  have hl := integral_lin (fun j => ∑ i, 2 * u i * U i j)
  have hq := integral_quad (fun j k => ∑ i, U i j * U i k)
  have hc : Integrable (fun _ : Fin d → ℝ => ∑ i, u i ^ 2) (noiseLaw d) := integrable_const _
  refine ⟨(hc.addL hl.1).addL hq.1, ?_⟩
  rw [integral_add (hc.addL hl.1) hq.1, integral_add hc hl.1, hl.2, hq.2]
  simp only [integral_const, probReal_univ, one_smul, add_zero]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma isotropy_sub (m m' : Location d) (C C' : Scale d) :
    Integrable (fun ξ => ‖sample m C ξ - sample m' C' ξ‖ ^ 2) (noiseLaw d) ∧
      ∫ ξ, ‖sample m C ξ - sample m' C' ξ‖ ^ 2 ∂noiseLaw d = sqDist m m' C C' := by
  simp_rw [sample_sub]
  rw [← sqDist_split]
  exact isotropy (m - m') (C - C')

section Instance

variable {L μ : ℝ} {V : Point d → ℝ}

lemma grad_sample_sq_le (h : Potential L μ V) (m : Location d) (C : Scale d) (ξ : Fin d → ℝ) :
    ‖gradient V (sample m C ξ)‖ ^ 2 ≤
      (2 * ‖gradient V 0‖ ^ 2 + 4 * L ^ 2 * sqDist m 0 C 0) * (1 + sqNorm ξ) := by
  have h1 := h.grad_sq_le (sample m C ξ)
  have h2 := norm_sample_sq_le m C ξ
  have hS := sqNorm_nonneg ξ
  have hq := sqDist_nonneg m 0 C 0
  nlinarith [sq_nonneg L, sq_nonneg ‖gradient V 0‖]

lemma measurable_grad_sample (h : Potential L μ V) (m : Location d) (C : Scale d) :
    Measurable (fun ξ : Fin d → ℝ => gradient V (sample m C ξ)) :=
  (h.continuous_grad.comp (continuous_sample_fixed m C)).measurable

lemma integrable_V_sample (h : Potential L μ V) (m : Location d) (C : Scale d) :
    Integrable (fun ξ => V (sample m C ξ)) (noiseLaw d) := by
  refine integrable_poly ((h.continuous_fn.comp (continuous_sample_fixed m C)).measurable
    |>.aestronglyMeasurable) ((|V 0| + ‖gradient V 0‖ + L) * (1 + 2 * sqDist m 0 C 0)) fun ξ => ?_
  have h1 := h.abs_bound (sample m C ξ)
  have h2 := norm_sample_sq_le m C ξ
  have hS := sqNorm_nonneg ξ
  have hq := sqDist_nonneg m 0 C 0
  have hc : 0 ≤ |V 0| + ‖gradient V 0‖ + L := by
    have := h.L_pos
    positivity
  have h3 : 1 + ‖sample m C ξ‖ ^ 2 ≤ (1 + 2 * sqDist m 0 C 0) * (1 + sqNorm ξ) ^ 2 := by
    nlinarith
  calc |V (sample m C ξ)| ≤ (|V 0| + ‖gradient V 0‖ + L) * (1 + ‖sample m C ξ‖ ^ 2) := h1
    _ ≤ (|V 0| + ‖gradient V 0‖ + L) * ((1 + 2 * sqDist m 0 C 0) * (1 + sqNorm ξ) ^ 2) :=
      mul_le_mul_of_nonneg_left h3 hc
    _ = _ := by ring

lemma integrable_grad_bound (h : Potential L μ V) (m : Location d) (C : Scale d)
    {f : (Fin d → ℝ) → ℝ} (hf : AEStronglyMeasurable f (noiseLaw d)) (c : ℝ)
    (hb : ∀ ξ, |f ξ| ≤ c * ((1 + sqNorm ξ) * ‖gradient V (sample m C ξ)‖ ^ 2 + (1 + sqNorm ξ))) :
    Integrable f (noiseLaw d) := by
  refine integrable_poly hf (|c| * ((2 * ‖gradient V 0‖ ^ 2 + 4 * L ^ 2 * sqDist m 0 C 0) + 1))
    fun ξ => ?_
  have hg := grad_sample_sq_le h m C ξ
  have hS := sqNorm_nonneg ξ
  have hq := sqDist_nonneg m 0 C 0
  have hb' := (hb ξ).trans (mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity))
  have hk : 0 ≤ 2 * ‖gradient V 0‖ ^ 2 + 4 * L ^ 2 * sqDist m 0 C 0 := by positivity
  have hin : (1 + sqNorm ξ) * ‖gradient V (sample m C ξ)‖ ^ 2 + (1 + sqNorm ξ) ≤
      ((2 * ‖gradient V 0‖ ^ 2 + 4 * L ^ 2 * sqDist m 0 C 0) + 1) * (1 + sqNorm ξ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hg (by linarith : (0 : ℝ) ≤ 1 + sqNorm ξ)
    nlinarith
  calc |f ξ| ≤ |c| * ((1 + sqNorm ξ) * ‖gradient V (sample m C ξ)‖ ^ 2 + (1 + sqNorm ξ)) := hb'
    _ ≤ |c| * (((2 * ‖gradient V 0‖ ^ 2 + 4 * L ^ 2 * sqDist m 0 C 0) + 1) *
        (1 + sqNorm ξ) ^ 2) := mul_le_mul_of_nonneg_left hin (abs_nonneg c)
    _ = _ := by ring

lemma integrable_grad_coord (h : Potential L μ V) (m : Location d) (C : Scale d) (i : Fin d) :
    Integrable (fun ξ => gradient V (sample m C ξ) i) (noiseLaw d) := by
  refine integrable_grad_bound h m C (((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp
    (measurable_grad_sample h m C)).aestronglyMeasurable) 1 fun ξ => ?_
  have hc : |gradient V (sample m C ξ) i| ≤ ‖gradient V (sample m C ξ)‖ := by
    simpa using PiLp.norm_apply_le (gradient V (sample m C ξ)) i
  have hS := sqNorm_nonneg ξ
  have hn := norm_nonneg (gradient V (sample m C ξ))
  nlinarith [sq_nonneg (‖gradient V (sample m C ξ)‖ - 1)]

lemma integrable_gradScale (h : Potential L μ V) (m : Location d) (C : Scale d) (i j : Fin d) :
    Integrable (fun ξ => gradScale (gradient V (sample m C ξ)) ξ i j) (noiseLaw d) := by
  unfold gradScale
  by_cases hji : j ≤ i
  · simp only [hji, ↓reduceIte]
    refine integrable_grad_bound h m C ((((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).measurable.comp
      (measurable_grad_sample h m C)).mul (measurable_pi_apply j)).aestronglyMeasurable) 1
      fun ξ => ?_
    have hc : |gradient V (sample m C ξ) i| ≤ ‖gradient V (sample m C ξ)‖ := by
      simpa using PiLp.norm_apply_le (gradient V (sample m C ξ)) i
    have hj := coord_sq_le ξ j
    have hS := sqNorm_nonneg ξ
    have hn := norm_nonneg (gradient V (sample m C ξ))
    rw [abs_mul]
    have hab : |ξ j| ^ 2 ≤ sqNorm ξ := by rw [sq_abs]; exact hj
    nlinarith [sq_nonneg (‖gradient V (sample m C ξ)‖ - |ξ j|), abs_nonneg (ξ j),
      mul_le_mul hc (le_refl |ξ j|) (abs_nonneg _) hn]
  · simp only [hji, ↓reduceIte]
    exact integrable_zero _ _ _

noncomputable def meanLoc (V : Point d → ℝ) (m : Location d) (C : Scale d) : Location d :=
  fun i => ∫ ξ, gradient V (sample m C ξ) i ∂noiseLaw d

noncomputable def meanScale (V : Point d → ℝ) (m : Location d) (C : Scale d) : Scale d :=
  fun i j => ∫ ξ, gradScale (gradient V (sample m C ξ)) ξ i j ∂noiseLaw d

lemma integral_pinner_grad (h : Potential L μ V) (m : Location d) (C : Scale d)
    (u : Location d) (U : Scale d) :
    Integrable (fun ξ => pinner (gradLoc (gradient V (sample m C ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ) u U) (noiseLaw d) ∧
    ∫ ξ, pinner (gradLoc (gradient V (sample m C ξ)))
      (gradScale (gradient V (sample m C ξ)) ξ) u U ∂noiseLaw d =
      pinner (meanLoc V m C) (meanScale V m C) u U := by
  have h1 : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun ξ => gradLoc (gradient V (sample m C ξ)) i * u i) (noiseLaw d) :=
    fun i _ => (integrable_grad_coord h m C i).mul_const (u i)
  have h2 : ∀ i j, Integrable (fun ξ => gradScale (gradient V (sample m C ξ)) ξ i j * U i j)
      (noiseLaw d) := fun i j => (integrable_gradScale h m C i j).mul_const (U i j)
  have h2' : ∀ i ∈ (Finset.univ : Finset (Fin d)), Integrable
      (fun ξ => ∑ j, gradScale (gradient V (sample m C ξ)) ξ i j * U i j) (noiseLaw d) :=
    fun i _ => integrable_finsetSum _ fun j _ => h2 i j
  unfold pinner
  refine ⟨(integrable_finsetSum _ h1).addL (integrable_finsetSum _ h2'), ?_⟩
  rw [integral_add (integrable_finsetSum _ h1) (integrable_finsetSum _ h2'),
    integral_finsetSum _ h1, integral_finsetSum _ h2']
  congr 1
  · exact Finset.sum_congr rfl fun i _ => integral_mul_const _ _
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => h2 i j]
    exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _

lemma integral_inner_grad (h : Potential L μ V) (m : Location d) (C : Scale d)
    (u : Location d) {U : Scale d} (hU : IsLower U) :
    Integrable (fun ξ => ⟪gradient V (sample m C ξ),
      (WithLp.toLp 2 (u + Matrix.mulVec U ξ) : Point d)⟫) (noiseLaw d) ∧
    ∫ ξ, ⟪gradient V (sample m C ξ), (WithLp.toLp 2 (u + Matrix.mulVec U ξ) : Point d)⟫ ∂noiseLaw d =
      pinner (meanLoc V m C) (meanScale V m C) u U := by
  have he : ∀ ξ, ⟪gradient V (sample m C ξ), (WithLp.toLp 2 (u + Matrix.mulVec U ξ) : Point d)⟫ =
      pinner (gradLoc (gradient V (sample m C ξ))) (gradScale (gradient V (sample m C ξ)) ξ) u U :=
    fun ξ => (pinner_grad _ ξ u hU).symm
  simp_rw [he]
  exact integral_pinner_grad h m C u U

noncomputable def energy (V : Point d → ℝ) (m : Location d) (C : Scale d) : ℝ :=
  ∫ ξ, V (sample m C ξ) ∂noiseLaw d

lemma energy_upper (h : Potential L μ V) (m m' : Location d) {C C' : Scale d}
    (hC : IsLower (C' - C)) :
    energy V m' C' ≤ energy V m C + pinner (meanLoc V m C) (meanScale V m C) (m' - m) (C' - C) +
      L / 2 * sqDist m' m C' C := by
  have hpt : ∀ ξ, V (sample m' C' ξ) ≤ V (sample m C ξ) +
      ⟪gradient V (sample m C ξ), (WithLp.toLp 2 ((m' - m) + Matrix.mulVec (C' - C) ξ) : Point d)⟫ +
      L / 2 * ‖sample m' C' ξ - sample m C ξ‖ ^ 2 := by
    intro ξ
    have := h.upper (sample m C ξ) (sample m' C' ξ)
    rw [sample_sub] at this ⊢
    exact this
  have hi := integral_inner_grad h m C (m' - m) hC
  have hn := isotropy_sub m' m C' C
  have hA := integrable_V_sample h m C
  have hB := integrable_V_sample h m' C'
  have hR : Integrable (fun ξ => V (sample m C ξ) +
      ⟪gradient V (sample m C ξ), (WithLp.toLp 2 ((m' - m) + Matrix.mulVec (C' - C) ξ) : Point d)⟫ +
      L / 2 * ‖sample m' C' ξ - sample m C ξ‖ ^ 2) (noiseLaw d) :=
    (hA.addL hi.1).addL (hn.1.const_mul _)
  have hm := integral_mono hB hR hpt
  rw [integral_add (hA.addL hi.1) (hn.1.const_mul _), integral_add hA hi.1, hi.2,
    integral_const_mul, hn.2] at hm
  exact hm

lemma energy_lower (h : Potential L μ V) (m m' : Location d) {C C' : Scale d}
    (hC : IsLower (C' - C)) :
    energy V m C + pinner (meanLoc V m C) (meanScale V m C) (m' - m) (C' - C) +
      μ / 2 * sqDist m' m C' C ≤ energy V m' C' := by
  have hpt : ∀ ξ, V (sample m C ξ) +
      ⟪gradient V (sample m C ξ), (WithLp.toLp 2 ((m' - m) + Matrix.mulVec (C' - C) ξ) : Point d)⟫ +
      μ / 2 * ‖sample m' C' ξ - sample m C ξ‖ ^ 2 ≤ V (sample m' C' ξ) := by
    intro ξ
    have := h.support (sample m C ξ) (sample m' C' ξ)
    rw [sample_sub] at this ⊢
    exact this
  have hi := integral_inner_grad h m C (m' - m) hC
  have hn := isotropy_sub m' m C' C
  have hA := integrable_V_sample h m C
  have hB := integrable_V_sample h m' C'
  have hR : Integrable (fun ξ => V (sample m C ξ) +
      ⟪gradient V (sample m C ξ), (WithLp.toLp 2 ((m' - m) + Matrix.mulVec (C' - C) ξ) : Point d)⟫ +
      μ / 2 * ‖sample m' C' ξ - sample m C ξ‖ ^ 2) (noiseLaw d) :=
    (hA.addL hi.1).addL (hn.1.const_mul _)
  have hm := integral_mono hR hB hpt
  rw [integral_add (hA.addL hi.1) (hn.1.const_mul _), integral_add hA hi.1, hi.2,
    integral_const_mul, hn.2] at hm
  exact hm

end Instance

end OracleTemplate.GaussianVariational
