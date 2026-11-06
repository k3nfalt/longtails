import LongTails.Proofs.CovarianceAcceleratedEnergy
import LongTails.Proofs.CovarianceAcceleratedMixedMoments
import LongTails.Proofs.CovarianceAcceleratedGeometry

open MeasureTheory ProbabilityTheory Convexity
open scoped RealInnerProductSpace NNReal
open LongTails.Algorithms.CovarianceAcceleratedMixture
open LongTails.Proofs.CovarianceAcceleratedTilt

namespace LongTails.Proofs.CovarianceAcceleratedConditionalMoments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma density_integral_translation (z : E) {F : E → ℝ} (hF : Measurable F) :
    (∫ u, density z u * F u ∂stdGaussian E) = ∫ u, F (z + u) ∂stdGaussian E := by
  have he : (∫ u, F u ∂(stdGaussian E).tilted (fun u => ⟪z, u⟫)) =
      ∫ u, F (z + u) ∂stdGaussian E := by
    rw [tilted_gaussian_eq_translation, integral_map (by fun_prop) hF.aestronglyMeasurable]
  rw [integral_tilted, integral_exp_inner] at he
  simpa only [density, Real.exp_sub, smul_eq_mul] using he

noncomputable def error (x0 b h v g : E) (a α : ℝ) (u : E) : ℝ :=
  max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫)) - α * ⟪v - h, x0 + a • u - b⟫

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma error_translation (z x0 b h v e u : E) (a α : ℝ) :
    error x0 b h v (v + e) a α (z + u) =
      max (-1) (min 1 ((α * ⟪v - h, x0 + a • z - b⟫ + (α * a) * ⟪v - h, u⟫) +
        (α * ⟪e, x0 + a • z - b⟫ + (α * a) * ⟪e, u⟫))) -
      (α * ⟪v - h, x0 + a • z - b⟫ + (α * a) * ⟪v - h, u⟫) := by
  have he : x0 + a • (z + u) - b = (x0 + a • z - b) + a • u := by rw [smul_add]; abel
  have hv : v + e - h = (v - h) + e := by abel
  have h1 : α * ⟪v - h, (x0 + a • z - b) + a • u⟫ =
      α * ⟪v - h, x0 + a • z - b⟫ + (α * a) * ⟪v - h, u⟫ := by
    rw [inner_add_right, inner_smul_right]
    ring
  have h2 : α * ⟪(v - h) + e, (x0 + a • z - b) + a • u⟫ =
      (α * ⟪v - h, x0 + a • z - b⟫ + (α * a) * ⟪v - h, u⟫) +
      (α * ⟪e, x0 + a • z - b⟫ + (α * a) * ⟪e, u⟫) := by
    simp only [inner_add_left, inner_add_right, inner_smul_right]
    ring
  rw [error, he, hv, h1, h2]

lemma component_clipping_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ξ : Ω → E}
    (hξ : Measurable ξ) (hi : Integrable ξ P)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (hmean : (∫ ω, ξ ω ∂P) = 0)
    (z x0 b h v : E) (a α sign : ℝ) {D V : ℝ} {proxy : ℝ≥0}
    (hD : (∫ ω, ⟪ξ ω, x0 + a • z - b⟫ ^ 2 ∂P) ≤ D)
    (hV : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ V)
    (hm : |α * ⟪v - h, x0 + a • z - b⟫| ≤ 1 / 4)
    (hp : (α * a) ^ 2 * ‖v - h‖ ^ 2 ≤ (proxy : ℝ))
    (hp0 : 0 < (proxy : ℝ)) (hp1 : (proxy : ℝ) ≤ 1 / 4) (hsign : sign = 1 ∨ sign = -1) :
    Integrable (fun ω => ∫ u, density z u * Real.exp (sign * error x0 b h v (v + ξ ω) a α u)
      ∂stdGaussian E) P ∧
    (∫ ω, ∫ u, density z u * Real.exp (sign * error x0 b h v (v + ξ ω) a α u)
      ∂stdGaussian E ∂P) ≤
      1 + 80 * (α ^ 2 * D + (α * a) ^ 2 * V) + 18 * Real.exp (-1 / (32 * (proxy : ℝ))) := by
  have hc := CovarianceAcceleratedMixedMoments.gaussian_clipping_moment P hξ hi h2 hmean
    (v - h) (x0 + a • z - b) α (α * a) sign hD hV hm hp hp0 hp1 hsign
  dsimp only at hc
  have he (ω : Ω) :
      (∫ u, density z u * Real.exp (sign * error x0 b h v (v + ξ ω) a α u) ∂stdGaussian E) =
      ∫ u, Real.exp (sign *
        (max (-1) (min 1 ((α * ⟪v - h, x0 + a • z - b⟫ + (α * a) * ⟪v - h, u⟫) +
          (α * ⟪ξ ω, x0 + a • z - b⟫ + (α * a) * ⟪ξ ω, u⟫))) -
        (α * ⟪v - h, x0 + a • z - b⟫ + (α * a) * ⟪v - h, u⟫))) ∂stdGaussian E := by
    rw [density_integral_translation z (by unfold error; fun_prop)]
    simp_rw [error_translation]
  constructor
  · exact hc.1.integral_prod_right.congr (Filter.Eventually.of_forall fun ω => (he ω).symm)
  · simp_rw [he]
    exact hc.2

lemma component_exp_error_integrable (z x0 b h v g : E) (a α sign : ℝ) :
    Integrable (fun u => density z u * Real.exp (sign * error x0 b h v g a α u)) (stdGaussian E) := by
  have hi := (CovarianceAcceleratedEnergy.component_exp_linear_integrable (fun _ : Fin 1 => z)
    x0 b (v - h) a (-sign * α) 0).const_mul (Real.exp |sign|)
  apply hi.mono' (by unfold density error; fun_prop) (Filter.Eventually.of_forall fun u => ?_)
  have hd : 0 < density z u := Real.exp_pos _
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos hd (Real.exp_pos _))]
  have hc : sign * max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫)) ≤ |sign| := by
    calc
      _ ≤ |sign * max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫))| := le_abs_self _
      _ = |sign| * |max (-1) (min 1 (α * ⟪g - h, x0 + a • u - b⟫))| := abs_mul _ _
      _ ≤ |sign| * 1 := mul_le_mul_of_nonneg_left (CovarianceAcceleratedClipping.clip_abs_le _) (abs_nonneg _)
      _ = |sign| := mul_one _
  have he : sign * error x0 b h v g a α u ≤ |sign| + (-sign * α) * ⟪v - h, x0 + a • u - b⟫ := by
    unfold error
    nlinarith
  have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Real.exp_pos (⟪z, u⟫ - ‖z‖ ^ 2 / 2)).le
  rw [Real.exp_add] at hh
  change density z u * Real.exp (sign * error x0 b h v g a α u) ≤ _
  convert hh using 1 <;> unfold density <;> ring

lemma mixture_clipping_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ξ : Ω → E}
    (hξ : Measurable ξ) (hi : Integrable ξ P)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (hmean : (∫ ω, ξ ω ∂P) = 0)
    {n : ℕ} (z : Fin n → E) (w : StdSimplex ℝ (Fin n))
    (x0 b h v : E) (a α sign : ℝ) {D V : ℝ} {proxy : ℝ≥0}
    (hD : ∀ i, (∫ ω, ⟪ξ ω, x0 + a • z i - b⟫ ^ 2 ∂P) ≤ D)
    (hV : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ V)
    (hm : ∀ i, |α * ⟪v - h, x0 + a • z i - b⟫| ≤ 1 / 4)
    (hp : (α * a) ^ 2 * ‖v - h‖ ^ 2 ≤ (proxy : ℝ))
    (hp0 : 0 < (proxy : ℝ)) (hp1 : (proxy : ℝ) ≤ 1 / 4) (hsign : sign = 1 ∨ sign = -1) :
    Integrable (fun ω => ∫ u, mixture z w u * Real.exp (sign * error x0 b h v (v + ξ ω) a α u)
      ∂stdGaussian E) P ∧
    (∫ ω, ∫ u, mixture z w u * Real.exp (sign * error x0 b h v (v + ξ ω) a α u)
      ∂stdGaussian E ∂P) ≤
      1 + 80 * (α ^ 2 * D + (α * a) ^ 2 * V) + 18 * Real.exp (-1 / (32 * (proxy : ℝ))) := by
  have hc (i : Fin n) := component_clipping_moment P hξ hi h2 hmean
    (z i) x0 b h v a α sign (hD i) hV (hm i) hp hp0 hp1 hsign
  have he (ω : Ω) :
      (∫ u, mixture z w u * Real.exp (sign * error x0 b h v (v + ξ ω) a α u) ∂stdGaussian E) =
      ∑ i, w.weights i * (∫ u, density (z i) u * Real.exp (sign * error x0 b h v (v + ξ ω) a α u)
        ∂stdGaussian E) :=
    CovarianceAcceleratedEnergy.weighted_integral z w _
      (fun i => component_exp_error_integrable (z i) x0 b h v (v + ξ ω) a α sign)
  simp_rw [he]
  constructor
  · exact integrable_finsetSum _ (fun i _ => (hc i).1.const_mul (w.weights i))
  · rw [integral_finsetSum _ (fun i _ => (hc i).1.const_mul (w.weights i))]
    simp_rw [integral_const_mul]
    have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      mul_le_mul_of_nonneg_left (hc i).2 (w.weights_nonneg i))
    simpa only [← Finset.sum_mul, w.total_of_fintype, one_mul] using hb

lemma mixture_exp_error_integrable {n : ℕ} (z : Fin n → E) (w : StdSimplex ℝ (Fin n))
    (x0 b h v g : E) (a α sign : ℝ) :
    Integrable (fun u => mixture z w u * Real.exp (sign * error x0 b h v g a α u)) (stdGaussian E) :=
  CovarianceAcceleratedEnergy.weighted_integrable z w _
    (fun i => component_exp_error_integrable (z i) x0 b h v g a α sign)

lemma mixture_exp_error_positive {n : ℕ} (z : Fin n → E) (w : StdSimplex ℝ (Fin n))
    (x0 b h v g : E) (a α sign : ℝ) :
    0 < ∫ u, mixture z w u * Real.exp (sign * error x0 b h v g a α u) ∂stdGaussian E := by
  have hp (u : E) : 0 < mixture z w u * Real.exp (sign * error x0 b h v g a α u) :=
    mul_pos (CovarianceAcceleratedMixture.mixture_pos z w u) (Real.exp_pos _)
  rw [integral_pos_iff_support_of_nonneg (fun u => (hp u).le)
    (mixture_exp_error_integrable z w x0 b h v g a α sign)]
  have hs : Function.support (fun u => mixture z w u * Real.exp (sign * error x0 b h v g a α u)) =
      Set.univ := by
    ext u
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hp u).ne'
  rw [hs]
  simp

lemma mixture_error_jensen {n : ℕ} (z : Fin n → E) (w : StdSimplex ℝ (Fin n))
    (x0 b h v g : E) (a α : ℝ) :
    Real.exp (∫ u, mixture z w u * error x0 b h v g a α u ∂stdGaussian E) ≤
      ∫ u, mixture z w u * Real.exp (error x0 b h v g a α u) ∂stdGaussian E := by
  have he : (fun u => mixture z w u * Real.log (mixture z w u / mixture z w u)) =
      (fun _ : E => (0 : ℝ)) := by
    funext u
    simp [(CovarianceAcceleratedMixture.mixture_pos z w u).ne']
  have hKL : Integrable (fun u => mixture z w u * Real.log (mixture z w u / mixture z w u))
      (stdGaussian E) := by rw [he]; exact integrable_zero _ _ _
  have hExp : Integrable (fun u => mixture z w u * Real.exp (error x0 b h v g a α u)) (stdGaussian E) := by
    simpa only [one_mul] using mixture_exp_error_integrable z w x0 b h v g a α 1
  have hPos : 0 < ∫ u, mixture z w u * Real.exp (error x0 b h v g a α u) ∂stdGaussian E := by
    simpa only [one_mul] using mixture_exp_error_positive z w x0 b h v g a α 1
  have hb := CovarianceAcceleratedEntropy.integral_entropy_bound (stdGaussian E)
    (mixture z w) (mixture z w) (error x0 b h v g a α)
    (CovarianceAcceleratedMixture.mixture_pos z w) (CovarianceAcceleratedMixture.mixture_pos z w)
    (CovarianceAcceleratedMixture.mixture_integrable z w) (CovarianceAcceleratedMixture.mixture_integral z w)
    (CovarianceAcceleratedEnergy.mixture_error_integrable z w x0 b h g v a α) hKL hExp hPos
  rw [he, integral_zero, sub_zero] at hb
  exact (Real.exp_le_exp.mpr hb).trans_eq (Real.exp_log hPos)

lemma comparator_clipping_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {ξ : Ω → E}
    (hξ : Measurable ξ) (hi : Integrable ξ P)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (hmean : (∫ ω, ξ ω ∂P) = 0)
    {n : ℕ} (z : Fin n → E) (w : StdSimplex ℝ (Fin n))
    (x0 b h v : E) (a α : ℝ) {D V : ℝ} {proxy : ℝ≥0}
    (hD : ∀ i, (∫ ω, ⟪ξ ω, x0 + a • z i - b⟫ ^ 2 ∂P) ≤ D)
    (hV : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ V)
    (hm : ∀ i, |α * ⟪v - h, x0 + a • z i - b⟫| ≤ 1 / 4)
    (hp : (α * a) ^ 2 * ‖v - h‖ ^ 2 ≤ (proxy : ℝ))
    (hp0 : 0 < (proxy : ℝ)) (hp1 : (proxy : ℝ) ≤ 1 / 4) :
    Integrable (fun ω => Real.exp (∫ u, mixture z w u * error x0 b h v (v + ξ ω) a α u
      ∂stdGaussian E)) P ∧
    (∫ ω, Real.exp (∫ u, mixture z w u * error x0 b h v (v + ξ ω) a α u
      ∂stdGaussian E) ∂P) ≤
      1 + 80 * (α ^ 2 * D + (α * a) ^ 2 * V) + 18 * Real.exp (-1 / (32 * (proxy : ℝ))) := by
  have hc := mixture_clipping_moment P hξ hi h2 hmean z w x0 b h v a α 1 hD hV hm hp hp0 hp1 (Or.inl rfl)
  simp only [one_mul] at hc
  have hFm : Measurable (fun q : Ω × E => mixture z w q.2 * error x0 b h v (v + ξ q.1) a α q.2) := by
    unfold mixture density error
    fun_prop
  have hIntm : Measurable (fun ω => ∫ u, mixture z w u * error x0 b h v (v + ξ ω) a α u
      ∂stdGaussian E) := hFm.stronglyMeasurable.integral_prod_right'.measurable
  have hb (ω : Ω) := mixture_error_jensen z w x0 b h v (v + ξ ω) a α
  have hI : Integrable (fun ω => Real.exp (∫ u, mixture z w u * error x0 b h v (v + ξ ω) a α u
      ∂stdGaussian E)) P := by
    apply hc.1.mono' (Real.measurable_exp.comp hIntm).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    dsimp only [Function.comp_def]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hb ω
  exact ⟨hI, (integral_mono hI hc.1 hb).trans hc.2⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma physical_shift_bound {n : ℕ} (z : Fin n → E) (p : StdSimplex ℝ (Fin n))
    (x0 : E) {a M R : ℝ} (hz : ∀ i, ‖z i‖ ≤ M) (ha : |a| * M ≤ R) (i : Fin n) :
    ‖x0 + a • z i - (x0 + a • mean z p)‖ ≤ 2 * R := by
  have hc : ‖x0 + a • z i - x0‖ ≤ R := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hz i) (abs_nonneg a)).trans ha
  have hp : ‖x0 + a • mean z p - x0‖ ≤ R := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (CovarianceAcceleratedGeometry.mean_norm_le z p hz) (abs_nonneg a)).trans ha
  exact CovarianceAcceleratedGeometry.ball_pair_distance hc hp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma covariance_clipping_data {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {ξ : Ω → E} {s : ℝ}
    (hcov : ∀ d, (∫ ω, ⟪ξ ω, d⟫ ^ 2 ∂P) ≤ s ^ 2 * ‖d‖ ^ 2)
    {n : ℕ} (z : Fin n → E) (p : StdSimplex ℝ (Fin n)) (x0 r : E)
    {a α M R B : ℝ} {proxy : ℝ≥0} (hR : 0 ≤ R) (hα : 0 ≤ α)
    (hz : ∀ i, ‖z i‖ ≤ M) (ha : |a| * M ≤ R) (hr : ‖r‖ ≤ B)
    (hsmall : 2 * R * α * B ≤ 1 / 4) (hproxy : (α * a) ^ 2 * B ^ 2 ≤ (proxy : ℝ)) :
    (∀ i, (∫ ω, ⟪ξ ω, x0 + a • z i - (x0 + a • mean z p)⟫ ^ 2 ∂P) ≤ 4 * R ^ 2 * s ^ 2) ∧
    (∀ i, |α * ⟪r, x0 + a • z i - (x0 + a • mean z p)⟫| ≤ 1 / 4) ∧
    (α * a) ^ 2 * ‖r‖ ^ 2 ≤ (proxy : ℝ) := by
  have hB : 0 ≤ B := (norm_nonneg r).trans hr
  have hc (i : Fin n) := physical_shift_bound z p x0 hz ha i
  constructor
  · intro i
    apply (hcov _).trans
    have hn := norm_nonneg (x0 + a • z i - (x0 + a • mean z p))
    have hs : ‖x0 + a • z i - (x0 + a • mean z p)‖ ^ 2 ≤ 4 * R ^ 2 := by nlinarith [hc i]
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg s)]
  constructor
  · intro i
    rw [abs_mul, abs_of_nonneg hα]
    calc
      _ ≤ α * (‖r‖ * ‖x0 + a • z i - (x0 + a • mean z p)‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hα
      _ ≤ α * (B * (2 * R)) := by gcongr; exact hc i
      _ ≤ 1 / 4 := by nlinarith
  · have hs : ‖r‖ ^ 2 ≤ B ^ 2 := by nlinarith [norm_nonneg r]
    exact (mul_le_mul_of_nonneg_left hs (sq_nonneg (α * a))).trans hproxy

end LongTails.Proofs.CovarianceAcceleratedConditionalMoments
