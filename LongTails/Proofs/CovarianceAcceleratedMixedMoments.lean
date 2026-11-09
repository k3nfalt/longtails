import LongTails.Proofs.CovarianceAcceleratedGaussian

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace LongTails.Proofs.CovarianceAcceleratedMixedMoments

lemma iterated_clipping_bound {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) (Q : Measure Z) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {a : Z → ℝ} {X : Z → Ω → ℝ} {sign V B : ℝ}
    (ha : Measurable a) (hX : Measurable (Function.uncurry X))
    (hi : ∀ z, Integrable (X z) P)
    (h2 : ∀ z, Integrable (fun ω => (X z ω) ^ 2) P)
    (hmean : ∀ z, (∫ ω, X z ω ∂P) = 0)
    (hvariance : Integrable (fun z => ∫ ω, (X z ω) ^ 2 ∂P) Q)
    (htail : Integrable (fun z => if 1 / 2 < |a z| then Real.exp (1 + |a z|) else 0) Q)
    (hV : (∫ z, ∫ ω, (X z ω) ^ 2 ∂P ∂Q) ≤ V)
    (hB : (∫ z, if 1 / 2 < |a z| then Real.exp (1 + |a z|) else 0 ∂Q) ≤ B)
    (hsign : sign = 1 ∨ sign = -1) :
    Integrable (fun q : Z × Ω => Real.exp (sign *
      (max (-1) (min 1 (a q.1 + X q.1 q.2)) - a q.1))) (Q.prod P) ∧
    (∫ ω, ∫ z, Real.exp (sign *
      (max (-1) (min 1 (a z + X z ω)) - a z)) ∂Q ∂P) ≤ 1 + 40 * V + B := by
  let F : Z → Ω → ℝ := fun z ω => Real.exp (sign *
    (max (-1) (min 1 (a z + X z ω)) - a z))
  have hFm : Measurable (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    fun_prop
  have hXm (z : Z) : Measurable (X z) :=
    hX.comp (measurable_const.prodMk measurable_id)
  have hp (z : Z) := CovarianceAcceleratedClipping.clipped_exp_integral_mixed P
    (hXm z) (hi z) (h2 z) (hmean z) hsign (a := a z)
  have hfi (z : Z) : Integrable (F z) P := (hp z).1
  have hbound (z : Z) : (∫ ω, F z ω ∂P) ≤ 1 + 40 * (∫ ω, (X z ω) ^ 2 ∂P) +
      (if 1 / 2 < |a z| then Real.exp (1 + |a z|) else 0) := (hp z).2
  have hfmean : Measurable (fun z => ∫ ω, F z ω ∂P) :=
    hFm.stronglyMeasurable.integral_prod_right'.measurable
  have hlin : Integrable (fun z => 1 + 40 * (∫ ω, (X z ω) ^ 2 ∂P)) Q :=
    (integrable_const 1).add (hvariance.const_mul 40)
  have hmajor : Integrable (fun z => 1 + 40 * (∫ ω, (X z ω) ^ 2 ∂P) +
      (if 1 / 2 < |a z| then Real.exp (1 + |a z|) else 0)) Q := hlin.add htail
  have hint : Integrable (fun z => ∫ ω, F z ω ∂P) Q := hmajor.mono'
    hfmean.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun ω => (Real.exp_pos _).le))]
      exact hbound z)
  have hjoint : Integrable (Function.uncurry F) (Q.prod P) := by
    apply (integrable_prod_iff hFm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall hfi, ?_⟩
    simpa only [Function.uncurry, F, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hint
  refine ⟨hjoint, ?_⟩
  change (∫ ω, ∫ z, F z ω ∂Q ∂P) ≤ _
  rw [← integral_integral_swap hjoint]
  have hb := integral_mono hint hmajor hbound
  rw [integral_add hlin htail,
    integral_add (integrable_const 1) (hvariance.const_mul 40), integral_const_mul] at hb
  simp only [integral_const, probReal_univ, one_smul] at hb
  linarith

lemma covariance_gaussian_second_moment {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ξ : Ω → E}
    (hξ : Measurable ξ) (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P)
    (c : E) (η κ : ℝ) {D V : ℝ}
    (hD : (∫ ω, ⟪ξ ω, c⟫ ^ 2 ∂P) ≤ D) (hV : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ V) :
    Integrable (fun z => ∫ ω, (η * ⟪ξ ω, c⟫ + κ * ⟪ξ ω, z⟫) ^ 2 ∂P)
      (stdGaussian E) ∧
    (∫ z, ∫ ω, (η * ⟪ξ ω, c⟫ + κ * ⟪ξ ω, z⟫) ^ 2 ∂P ∂stdGaussian E) ≤
      2 * η ^ 2 * D + 2 * κ ^ 2 * V := by
  let A : E × Ω → ℝ := fun q => ⟪ξ q.2, c⟫
  let B : E × Ω → ℝ := fun q => ⟪ξ q.2, q.1⟫
  have hLp : MemLp ξ 2 P := (memLp_two_iff_integrable_sq_norm hξ.aestronglyMeasurable).mpr h2
  have hA : MemLp A 2 ((stdGaussian E).prod P) :=
    (hLp.inner_const c).comp_snd (stdGaussian E)
  have hg := CovarianceAcceleratedGaussian.gaussian_noise_energy P hξ h2
  have hBsq : Integrable (fun q => B q ^ 2) ((stdGaussian E).prod P) := hg.1.swap
  have hB : MemLp B 2 ((stdGaussian E).prod P) :=
    (memLp_two_iff_integrable_sq (by dsimp [B]; fun_prop)).mpr hBsq
  have hX : Integrable (fun q => (η * A q + κ * B q) ^ 2) ((stdGaussian E).prod P) :=
    ((hA.const_mul η).add (hB.const_mul κ)).integrable_sq
  have hdom : Integrable (fun q => 2 * η ^ 2 * A q ^ 2 + 2 * κ ^ 2 * B q ^ 2)
      ((stdGaussian E).prod P) :=
    (hA.integrable_sq.const_mul (2 * η ^ 2)).add (hBsq.const_mul (2 * κ ^ 2))
  have hp (q : E × Ω) : (η * A q + κ * B q) ^ 2 ≤
      2 * η ^ 2 * A q ^ 2 + 2 * κ ^ 2 * B q ^ 2 := by
    nlinarith [sq_nonneg (η * A q - κ * B q)]
  have hb := integral_mono hX hdom hp
  rw [integral_add (hA.integrable_sq.const_mul (2 * η ^ 2))
      (hBsq.const_mul (2 * κ ^ 2)), integral_const_mul, integral_const_mul] at hb
  have hIA : (∫ q, A q ^ 2 ∂(stdGaussian E).prod P) = (∫ ω, ⟪ξ ω, c⟫ ^ 2 ∂P) := by
    rw [integral_prod _ hA.integrable_sq]
    simp [A]
  have hIB : (∫ q, B q ^ 2 ∂(stdGaussian E).prod P) = (∫ ω, ‖ξ ω‖ ^ 2 ∂P) := by
    rw [integral_prod _ hBsq]
    exact hg.2
  rw [hIA, hIB, integral_prod _ hX] at hb
  refine ⟨hX.integral_prod_left, ?_⟩
  exact hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left hD (by positivity))
    (mul_le_mul_of_nonneg_left hV (by positivity)))

lemma gaussian_clipping_moment {E Ω : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {ξ : Ω → E}
    (hξ : Measurable ξ) (hi : Integrable ξ P)
    (h2 : Integrable (fun ω => ‖ξ ω‖ ^ 2) P) (hmean : (∫ ω, ξ ω ∂P) = 0)
    (r c : E) (η κ sign : ℝ) {D V : ℝ} {v : ℝ≥0}
    (hD : (∫ ω, ⟪ξ ω, c⟫ ^ 2 ∂P) ≤ D) (hV : (∫ ω, ‖ξ ω‖ ^ 2 ∂P) ≤ V)
    (hm : |η * ⟪r, c⟫| ≤ 1 / 4) (hproxy : κ ^ 2 * ‖r‖ ^ 2 ≤ (v : ℝ))
    (hv : 0 < (v : ℝ)) (hvsmall : (v : ℝ) ≤ 1 / 4) (hsign : sign = 1 ∨ sign = -1) :
    let a := fun z : E => η * ⟪r, c⟫ + κ * ⟪r, z⟫
    let X := fun z ω => η * ⟪ξ ω, c⟫ + κ * ⟪ξ ω, z⟫
    Integrable (fun q : E × Ω => Real.exp (sign *
      (max (-1) (min 1 (a q.1 + X q.1 q.2)) - a q.1))) ((stdGaussian E).prod P) ∧
    (∫ ω, ∫ z, Real.exp (sign *
      (max (-1) (min 1 (a z + X z ω)) - a z)) ∂stdGaussian E ∂P) ≤
      1 + 80 * (η ^ 2 * D + κ ^ 2 * V) + 18 * Real.exp (-1 / (32 * (v : ℝ))) := by
  intro a X
  have hLp : MemLp ξ 2 P := (memLp_two_iff_integrable_sq_norm hξ.aestronglyMeasurable).mpr h2
  have hXi (z : E) : Integrable (X z) P :=
    ((hi.inner_const c).const_mul η).add ((hi.inner_const z).const_mul κ)
  have hX2 (z : E) : Integrable (fun ω => (X z ω) ^ 2) P :=
    (((hLp.inner_const c).const_mul η).add ((hLp.inner_const z).const_mul κ)).integrable_sq
  have hXm (z : E) : (∫ ω, X z ω ∂P) = 0 := by
    dsimp [X]
    rw [integral_add ((hi.inner_const c).const_mul η) ((hi.inner_const z).const_mul κ),
      integral_const_mul, integral_const_mul]
    have hc (w : E) : (∫ ω, ⟪ξ ω, w⟫ ∂P) = 0 := by
      calc
        _ = ∫ ω, ⟪w, ξ ω⟫ ∂P := integral_congr_ae
          (Filter.Eventually.of_forall fun ω => (real_inner_comm (ξ ω) w).symm)
        _ = ⟪w, ∫ ω, ξ ω ∂P⟫ := integral_inner hi w
        _ = 0 := by rw [hmean, inner_zero_right]
    rw [hc c, hc z]
    ring
  have henergy := covariance_gaussian_second_moment P hξ h2 c η κ hD hV
  let L : StrongDual ℝ E := κ • innerSL ℝ r
  have hnorm : ‖L‖ ^ 2 ≤ (v : ℝ) := by
    simpa only [L, norm_smul, Real.norm_eq_abs, innerSL_apply_norm, mul_pow, sq_abs] using hproxy
  have htail := CovarianceAcceleratedGaussian.shifted_subgaussian_tail (stdGaussian E)
    (X := L) (m := η * ⟪r, c⟫) (by fun_prop)
    (CovarianceAcceleratedGaussian.gaussian_dual_subgaussian L hnorm) hv hvsmall hm
  have htail' : Integrable (fun z => if 1 / 2 < |a z| then Real.exp (1 + |a z|) else 0)
      (stdGaussian E) ∧
      (∫ z, if 1 / 2 < |a z| then Real.exp (1 + |a z|) else 0 ∂stdGaussian E) ≤
        18 * Real.exp (-1 / (32 * (v : ℝ))) := by
    simpa only [L, smul_apply, innerSL_apply_apply, smul_eq_mul] using htail
  have h := iterated_clipping_bound P (stdGaussian E)
    (a := a) (X := X) (sign := sign) (by dsimp [a]; fun_prop)
    (by dsimp [X, Function.uncurry]; fun_prop) hXi hX2 hXm henergy.1 htail'.1 henergy.2
    htail'.2 hsign
  refine ⟨h.1, ?_⟩
  linarith [h.2]

end LongTails.Proofs.CovarianceAcceleratedMixedMoments
