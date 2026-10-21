import LongTails.Proofs.GeneralCovarianceReverseFisherDerivative

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.GeneralCovarianceReverseFisherParts

open LongTails.Proofs.GeneralCovarianceReverseFisherScore
open LongTails.Proofs.GeneralCovarianceReverseFisherDerivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma hasFDerivAt_total (A : E ≃L[ℝ] E) {k : ℕ} (c : Fin k → E) (x : E) :
    HasFDerivAt (fun y => total A c y)
      (∑ j, weight A c x j • innerSL ℝ (precision A (c j - x))) x :=
  HasFDerivAt.fun_sum (fun j _ => hasFDerivAt_weight_point A c x j)

lemma hasFDerivAt_resp (A : E ≃L[ℝ] E) {k : ℕ} [NeZero k] (c : Fin k → E) (x : E) (j : Fin k) :
    HasFDerivAt (fun y => resp A c y j)
      (resp A c x j • innerSL ℝ (precision A (c j - posteriorMean A c x))) x := by
  have hb := total_pos A c x
  have h := (hasFDerivAt_weight_point A c x j).mul
    ((hasDerivAt_inv hb.ne').comp_hasFDerivAt x (hasFDerivAt_total A c x))
  unfold resp
  convert h using 1
  · funext y
    simp [div_eq_mul_inv]
  ext v
  have hb' : ∑ i, weight A c x i = total A c x := rfl
  simp only [add_apply, smul_apply, sum_apply, neg_apply, Function.comp_apply,
    innerSL_apply_apply, smul_eq_mul, neg_smul]
  simp only [posteriorMean, resp, map_sub, map_sum, map_smul, inner_sub_left, sum_inner,
    inner_smul_left, conj_trivial, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hb']
  field_simp
  rw [← Finset.sum_div]
  field_simp
  ring

lemma hasFDerivAt_posteriorMean (A : E ≃L[ℝ] E) {k : ℕ} [NeZero k] (c : Fin k → E) (x : E) :
    HasFDerivAt (fun y => posteriorMean A c y)
      (∑ j, (resp A c x j • innerSL ℝ (precision A (c j - posteriorMean A c x))).smulRight (c j))
      x := by
  unfold posteriorMean
  apply HasFDerivAt.fun_sum
  intro j _
  have := (hasFDerivAt_resp A c x j).smul_const (c j)
  exact this

omit [FiniteDimensional ℝ E] in
lemma sum_resp_smul_sub (A : E ≃L[ℝ] E) {k : ℕ} [NeZero k] (c : Fin k → E) (x : E) :
    ∑ j, resp A c x j • (c j - posteriorMean A c x) = 0 := by
  simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sum_resp, one_smul]
  unfold posteriorMean
  exact sub_self _

lemma sum_resp_mul_inner (A : E ≃L[ℝ] E) {k : ℕ} [NeZero k] (c : Fin k → E) (x : E) (h : E) :
    ∑ j, resp A c x j * ⟪precision A (c j - posteriorMean A c x), h⟫ = 0 := by
  have := congrArg (fun z => ⟪precision A z, h⟫) (sum_resp_smul_sub A c x)
  simp only [map_sum, map_smul, sum_inner, inner_smul_left, conj_trivial, map_zero,
    inner_zero_left] at this
  exact this

noncomputable def gradPsi (A : E ≃L[ℝ] E) (θ : Means E n) (x : E) (i : Fin n) : E :=
  (2 : ℝ) • ∑ j, resp A (fun l => θ l) x j •
    (⟪precision A (θ j - posteriorMean A (fun l => θ l) x),
      precision A (θ i - posteriorMean A (fun l => θ l) x)⟫ •
        precision A (θ j - posteriorMean A (fun l => θ l) x))

lemma hasFDerivAt_psi [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) (i : Fin n) :
    HasFDerivAt (fun y => psi A t θ y i) (innerSL ℝ (gradPsi A θ x i)) x := by
  have hm := hasFDerivAt_posteriorMean A (fun l => θ l) x
  have hc : HasFDerivAt (fun y => precision A (center A t θ y))
      ((precision A).comp (∑ j, (resp A (fun l => θ l) x j • innerSL ℝ
        (precision A (θ j - posteriorMean A (fun l => θ l) x))).smulRight (θ j))) x :=
    (precision A).hasFDerivAt.comp x (hm.sub_const t)
  have h1 := ((innerSL ℝ (precision A (θ i - t))).hasFDerivAt.comp x hc).const_mul (2 : ℝ)
  have h2 := hc.norm_sq
  have h := h1.sub h2
  unfold psi
  convert h using 1
  · funext y
    simp only [Pi.sub_apply, Function.comp_apply, innerSL_apply_apply]
    rw [real_inner_comm]
  ext h'
  set m := posteriorMean A (fun l => θ l) x with hmdef
  set m' : E →L[ℝ] E := ∑ j, (resp A (fun l => θ l) x j • innerSL ℝ
    (precision A (θ j - m))).smulRight (θ j) with hm'def
  have hm'h : m' h' = ∑ j, (resp A (fun l => θ l) x j * ⟪precision A (θ j - m), h'⟫) •
      (θ j - m) := by
    have hz := sum_resp_mul_inner A (fun l => θ l) x h'
    rw [← hmdef] at hz
    simp only [hm'def, sum_apply, ContinuousLinearMap.smulRight_apply, smul_apply,
      innerSL_apply_apply, smul_eq_mul, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hz,
      zero_smul, sub_zero]
  symm
  simp only [sub_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  have hv : precision A (θ i - t) - precision A (center A t θ x) = precision A (θ i - m) := by
    simp only [center, ← hmdef, map_sub]
    abel
  rw [← mul_sub, ← inner_sub_left, hv, hm'h]
  simp only [gradPsi, ← hmdef, map_sum, map_smul, inner_sum, inner_smul_right, sum_inner,
    inner_smul_left, conj_trivial, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [real_inner_comm (precision A (θ i - m)) (precision A (θ j - m))]
  ring

omit [FiniteDimensional ℝ E] in
lemma norm_sub_mean_le [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E) (j : Fin n) :
    ‖θ j - posteriorMean A (fun l => θ l) x‖ ≤ 2 * spread t θ := by
  have h : θ j - posteriorMean A (fun l => θ l) x = (θ j - t) - center A t θ x := by
    simp only [center]; abel
  rw [h]
  refine (norm_sub_le _ _).trans ?_
  linarith [norm_sub_le_spread t θ j, norm_center_le A t θ x]

lemma norm_precision_sub_mean_le [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E)
    (j : Fin n) :
    ‖precision A (θ j - posteriorMean A (fun l => θ l) x)‖ ≤ 2 * ‖precision A‖ * spread t θ := by
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [mul_assoc, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (norm_sub_mean_le A t θ x j) (norm_nonneg _)

lemma abs_inner_gradPsi_le [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E)
    (i : Fin n) (h : E) :
    |⟪gradPsi A θ x i, h⟫| ≤ 16 * ‖precision A‖ ^ 3 * spread t θ ^ 3 * ‖h‖ := by
  set K := 2 * ‖precision A‖ * spread t θ
  have hK : 0 ≤ K := mul_nonneg (by positivity) (spread_nonneg t θ)
  have hb : ∀ j, |resp A (fun l => θ l) x j *
      (⟪precision A (θ j - posteriorMean A (fun l => θ l) x),
        precision A (θ i - posteriorMean A (fun l => θ l) x)⟫ *
        ⟪precision A (θ j - posteriorMean A (fun l => θ l) x), h⟫)| ≤
      resp A (fun l => θ l) x j * (K ^ 3 * ‖h‖) := by
    intro j
    rw [abs_mul, abs_of_nonneg (resp_nonneg A _ x j)]
    refine mul_le_mul_of_nonneg_left ?_ (resp_nonneg A _ x j)
    rw [abs_mul]
    have h1 := (abs_real_inner_le_norm _ _).trans (mul_le_mul
      (norm_precision_sub_mean_le A t θ x j) (norm_precision_sub_mean_le A t θ x i)
      (norm_nonneg _) hK)
    have h2 :=
      (abs_real_inner_le_norm (precision A (θ j - posteriorMean A (fun l => θ l) x)) h).trans
      (mul_le_mul_of_nonneg_right (norm_precision_sub_mean_le A t θ x j) (norm_nonneg h))
    calc _ ≤ (K * K) * (K * ‖h‖) := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = K ^ 3 * ‖h‖ := by ring
  have hsum : ⟪gradPsi A θ x i, h⟫ = 2 * ∑ j, resp A (fun l => θ l) x j *
      (⟪precision A (θ j - posteriorMean A (fun l => θ l) x),
        precision A (θ i - posteriorMean A (fun l => θ l) x)⟫ *
        ⟪precision A (θ j - posteriorMean A (fun l => θ l) x), h⟫) := by
    simp only [gradPsi, inner_smul_left, sum_inner, conj_trivial]
  rw [hsum, abs_mul, abs_two]
  have hS : |∑ j, resp A (fun l => θ l) x j *
      (⟪precision A (θ j - posteriorMean A (fun l => θ l) x),
        precision A (θ i - posteriorMean A (fun l => θ l) x)⟫ *
        ⟪precision A (θ j - posteriorMean A (fun l => θ l) x), h⟫)| ≤ K ^ 3 * ‖h‖ := by
    refine (Finset.abs_sum_le_sum_abs _ Finset.univ).trans ?_
    refine (Finset.sum_le_sum (fun j _ => hb j)).trans ?_
    rw [← Finset.sum_mul, sum_resp, one_mul]
  calc 2 * |_| ≤ 2 * (K ^ 3 * ‖h‖) := by gcongr
    _ = _ := by simp only [K]; ring

lemma continuous_gradPsi [NeZero n] (A : E ≃L[ℝ] E) (θ : Means E n) (i : Fin n) :
    Continuous (fun x => gradPsi A θ x i) := by
  have hv : ∀ j, Continuous (fun x => precision A (θ j - posteriorMean A (fun l => θ l) x)) :=
    fun j => (precision A).continuous.comp (continuous_const.sub (continuous_posteriorMean A _))
  unfold gradPsi
  exact continuous_const.smul (continuous_finsetSum _ (fun j _ =>
    (continuous_resp A _ j).smul (((hv j).inner (hv i)).smul (hv j))))

section Integral

variable [MeasurableSpace E] [BorelSpace E]

open LongTails.Proofs.GeneralCovarianceReverseFisherDensity

lemma integrable_weight_poly (A : E ≃L[ℝ] E) {k : ℕ} (c : Fin k → E) (i : Fin k)
    {F : E → ℝ} (hF : Continuous F) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hFb : ∀ x, |F x| ≤ α + β * ‖x - c i‖) :
    Integrable (fun x => weight A c x i * F x) := by
  have hd := (integrable_exp_quad A (c i) (1 / 8) (by norm_num)).const_mul
    ((α + 2 * β * ‖(A : E →L[ℝ] E)‖) * Real.exp (‖(A.symm : E →L[ℝ] E)‖ ^ 2 / 4))
  refine hd.mono' ((continuous_weight A c i).mul hF).aestronglyMeasurable
    (ae_of_all _ (fun x => ?_))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (weight_pos A c x i)]
  refine le_trans (mul_le_mul_of_nonneg_left (hFb x) (weight_pos A c x i).le) ?_
  exact weight_poly_le A hα hβ x (c i) (c i) (by simp)

lemma integral_parts [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (i : Fin n) (h : E) :
    ∫ x, weight A (fun l => θ l) x i * (psi A t θ x i * ⟪precision A (x - θ i), h⟫) =
      ∫ x, weight A (fun l => θ l) x i * ⟪gradPsi A θ x i, h⟫ := by
  have hs := spread_nonneg t θ
  have hpn := norm_nonneg (precision A)
  have hψ := abs_psi_le A t θ
  have key := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure E))
    (f := fun x => weight A (fun l => θ l) x i)
    (f' := fun x => weight A (fun l => θ l) x i • innerSL ℝ (precision A (θ i - x)))
    (g := fun x => psi A t θ x i) (g' := fun x => innerSL ℝ (gradPsi A θ x i)) (v := h)
    (B := ContinuousLinearMap.mul ℝ ℝ) ?_ ?_ ?_
    (fun x _ => hasFDerivAt_weight_point A _ x i) (fun x _ => hasFDerivAt_psi A t θ x i)
  · simp only [ContinuousLinearMap.mul_apply', smul_apply, innerSL_apply_apply, smul_eq_mul]
      at key
    rw [key, ← integral_neg]
    congr 1
    ext x
    rw [show θ i - x = -(x - θ i) by abel, map_neg, inner_neg_left]
    ring
  · simp only [ContinuousLinearMap.mul_apply', smul_apply, innerSL_apply_apply, smul_eq_mul]
    have hc : Continuous (fun x => ⟪precision A (θ i - x), h⟫ * psi A t θ x i) :=
      ((precision A).continuous.comp (continuous_const.sub continuous_id)).inner continuous_const
        |>.mul (continuous_psi A t θ i)
    have := integrable_weight_poly A (fun l => θ l) i hc (le_refl 0)
      (by positivity : 0 ≤ ‖precision A‖ * ‖h‖ * (3 * ‖precision A‖ ^ 2 * spread t θ ^ 2))
      (fun x => by
        rw [abs_mul, zero_add]
        have h1 : |⟪precision A (θ i - x), h⟫| ≤ ‖precision A‖ * ‖x - θ i‖ * ‖h‖ := by
          refine (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
          rw [norm_sub_rev]
        calc _ ≤ (‖precision A‖ * ‖x - θ i‖ * ‖h‖) * (3 * ‖precision A‖ ^ 2 * spread t θ ^ 2) :=
              mul_le_mul h1 (hψ x i) (abs_nonneg _) (by positivity)
          _ = _ := by ring)
    refine this.congr (ae_of_all _ (fun x => ?_))
    simp only
    ring
  · simp only [ContinuousLinearMap.mul_apply', innerSL_apply_apply]
    exact integrable_weight_mul A _ i ((continuous_gradPsi A θ i).inner continuous_const)
      (fun x => abs_inner_gradPsi_le A t θ x i h)
  · simp only [ContinuousLinearMap.mul_apply']
    exact integrable_weight_mul A _ i (continuous_psi A t θ i) (fun x => hψ x i)

noncomputable def pairing (A : E ≃L[ℝ] E) (t : E) (θ : Means E n) (x : E)
    (h : Means E n) : ℝ :=
  ∑ i, weight A (fun l => θ l) x i *
    (2 * ⟪precision A (precision A (center A t θ x)), h i⟫ + ⟪gradPsi A θ x i, h i⟫)

lemma integral_integrandDeriv_apply [NeZero n] (A : E ≃L[ℝ] E) (t : E) (θ : Means E n)
    (h : Means E n) :
    (∫ x, integrandDeriv A t θ x) h = ∫ x, pairing A t θ x h := by
  have hs := spread_nonneg t θ
  have hpn := norm_nonneg (precision A)
  rw [integral_integrandDeriv_apply_eq]
  simp_rw [integrandDeriv_apply, pairing]
  have hc1 : ∀ i, Integrable (fun x => weight A (fun l => θ l) x i *
      (2 * ⟪precision A (precision A (center A t θ x)), h i⟫)) := fun i =>
    integrable_weight_mul A _ i (C := 2 * (‖precision A‖ ^ 2 * spread t θ * ‖h i‖))
      (continuous_const.mul
      (((precision A).continuous.comp ((precision A).continuous.comp
        (continuous_center A t θ))).inner continuous_const))
      (fun x => by
        rw [abs_mul, abs_two]
        refine mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans ?_) zero_le_two
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        calc ‖precision A (precision A (center A t θ x))‖
            ≤ ‖precision A‖ * ‖precision A (center A t θ x)‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖precision A‖ * (‖precision A‖ * ‖center A t θ x‖) :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) hpn
          _ ≤ ‖precision A‖ * (‖precision A‖ * spread t θ) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (norm_center_le A t θ x) hpn) hpn
          _ = ‖precision A‖ ^ 2 * spread t θ := by ring)
  have hc2 : ∀ i, Integrable (fun x => weight A (fun l => θ l) x i *
      (psi A t θ x i * ⟪precision A (x - θ i), h i⟫)) := fun i => by
    have hc : Continuous (fun x => psi A t θ x i * ⟪precision A (x - θ i), h i⟫) :=
      (continuous_psi A t θ i).mul
        (((precision A).continuous.comp (continuous_id.sub continuous_const)).inner
          continuous_const)
    refine integrable_weight_poly A (fun l => θ l) i hc (le_refl 0)
      (by positivity : 0 ≤ (3 * ‖precision A‖ ^ 2 * spread t θ ^ 2) * (‖precision A‖ * ‖h i‖))
      (fun x => ?_)
    rw [abs_mul, zero_add]
    have h1 : |⟪precision A (x - θ i), h i⟫| ≤ ‖precision A‖ * ‖x - θ i‖ * ‖h i‖ :=
      (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
    calc _ ≤ (3 * ‖precision A‖ ^ 2 * spread t θ ^ 2) * (‖precision A‖ * ‖x - θ i‖ * ‖h i‖) :=
          mul_le_mul (abs_psi_le A t θ x i) h1 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hc3 : ∀ i, Integrable (fun x => weight A (fun l => θ l) x i * ⟪gradPsi A θ x i, h i⟫) :=
    fun i => integrable_weight_mul A _ i ((continuous_gradPsi A θ i).inner continuous_const)
      (fun x => abs_inner_gradPsi_le A t θ x i (h i))
  rw [integral_finsetSum _ (fun i _ => by
      simp_rw [mul_add]; exact (hc1 i).add (hc2 i)),
    integral_finsetSum _ (fun i _ => by
      simp_rw [mul_add]; exact (hc1 i).add (hc3 i))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp_rw [mul_add]
  rw [integral_add (hc1 i) (hc2 i), integral_add (hc1 i) (hc3 i), integral_parts]

end Integral

end LongTails.Proofs.GeneralCovarianceReverseFisherParts
