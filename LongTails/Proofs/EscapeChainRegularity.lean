import LongTails.Proofs.EscapeChainCertificate

namespace LongTails.Proofs.EscapeChainRegularity

open scoped RealInnerProductSpace BigOperators
open EscapeChainProfiles EscapeChainGates EscapeChainCalculus EscapeChainFunction
open EscapeChainCoordinates EscapeChainCount EscapeChainBounds EscapeChainJets EscapeChainSmooth
open EscapeChainCertificate ThirdOrderJetDifference

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

variable {K : ℕ} {u v : ℕ → E}

lemma cut_bounds (K : ℕ) (x : E) :
    |RelativeHessianCutoffSpatial.value (radius K) x| ≤ 1 ∧
      ‖gradient (RelativeHessianCutoffSpatial.value (radius K)) x‖ ≤ 1 / (2 ^ 98 * Real.sqrt (K + 1)) ∧
      ‖fderiv ℝ (gradient (RelativeHessianCutoffSpatial.value (radius K))) x‖ ≤
        1 / (2 ^ 228 * (K + 1)) ∧
      ‖fderiv ℝ (fderiv ℝ (gradient (RelativeHessianCutoffSpatial.value (radius K)))) x‖ ≤
        1 / (2 ^ 358 * (K + 1) * Real.sqrt (K + 1)) := by
  have hR := radius_pos K
  obtain ⟨b1, b2, b3⟩ := RelativeHessianCutoffBounds.bounds hR x
  obtain ⟨c0, c1⟩ := RelativeHessianCutoff.bounds (RelativeHessianCutoffSpatial.argument (radius K) x)
  have hs := sqrt_succ_ge K
  have hsq : Real.sqrt (K + 1) ^ 2 = K + 1 := Real.sq_sqrt (by positivity)
  refine ⟨?_, ?_, ?_, ?_⟩
  · show |RelativeHessianCutoff.profile _| ≤ 1
    rw [abs_of_nonneg c0]; exact c1
  · refine b1.trans (le_of_eq ?_)
    unfold radius; field_simp
  · refine b2.trans (le_of_eq ?_)
    unfold radius; rw [mul_pow, hsq]; field_simp
  · refine b3.trans (le_of_eq ?_)
    unfold radius
    rw [mul_pow, show Real.sqrt (K + 1) ^ 3 = (K + 1) * Real.sqrt (K + 1) by
      rw [pow_succ, hsq]]
    field_simp

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma product_smooth (K : ℕ) (u v : ℕ → E) :
    ContDiff ℝ 3 (fun y => RelativeHessianCutoffSpatial.value (radius K) y * hidden K u v y) :=
  (RelativeHessianCutoffSpatial.smooth _).mul (hidden_smooth K u v)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma objective_split (K : ℕ) (u v : ℕ → E) :
    objective K (radius K) u v = fun y =>
      (fun y => RelativeHessianCutoffSpatial.value (radius K) y * hidden K u v y) y +
        (1 / 2 : ℝ) * FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E) y := rfl

lemma objective_hessian_bound (fr : Frame K u v) (x : E) :
    ‖fderiv ℝ (gradient (objective K (radius K) u v)) x‖ ≤ 2 ^ 126 := by
  have hq := RelativeHessianGuard.quadratic_smooth (E := E) 2
  rw [objective_split, add_hessian (product_smooth K u v) (contDiff_const.mul hq),
    cmul_hessian hq]
  obtain ⟨c0, c1, c2, -⟩ := cut_bounds K x
  have hH := hidden_hessian_bound fr x
  have hG := hidden_gradient_bound fr x
  have hV := hidden_value_bound fr x
  have hp := product_hessian_norm (RelativeHessianCutoffSpatial.smooth (radius K))
    (hidden_smooth K u v) x
  have hQ : ‖(1 / 2 : ℝ) • fderiv ℝ (gradient (FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E))) x‖
      ≤ 1 := by
    have hg : gradient (FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E)) = fun y => (2 : ℝ) • y :=
      funext (RelativeHessianGuard.quadratic_gradient 2)
    rw [hg, show fderiv ℝ (fun y : E => (2 : ℝ) • y) x = (2 : ℝ) • ContinuousLinearMap.id ℝ E from
      ((hasFDerivAt_id (𝕜 := ℝ) x).const_smul (2 : ℝ)).fderiv, smul_smul]
    norm_num
    exact ContinuousLinearMap.norm_id_le
  have hs := sqrt_succ_ge K
  have hsq : Real.sqrt (K + 1) ^ 2 = K + 1 := Real.sq_sqrt (by positivity)
  have hK1 : (1 : ℝ) ≤ K + 1 := by linarith [Nat.cast_nonneg (α := ℝ) K]
  have t1 : |RelativeHessianCutoffSpatial.value (radius K) x| *
      ‖fderiv ℝ (gradient (hidden K u v)) x‖ ≤ 2 ^ 124 := by
    calc _ ≤ 1 * 2 ^ 124 := mul_le_mul c0 hH (norm_nonneg _) (by norm_num)
      _ = 2 ^ 124 := one_mul _
  have t2 : 2 * ‖gradient (RelativeHessianCutoffSpatial.value (radius K)) x‖ *
      ‖gradient (hidden K u v) x‖ ≤ 2 ^ 26 := by
    calc _ ≤ 2 * (1 / (2 ^ 98 * Real.sqrt (K + 1))) * (2 ^ 123 * Real.sqrt (K + 1)) := by gcongr
      _ = 2 ^ 26 := by field_simp
  have t3 : |hidden K u v x| *
      ‖fderiv ℝ (gradient (RelativeHessianCutoffSpatial.value (radius K))) x‖ ≤ 1 := by
    calc |hidden K u v x| *
          ‖fderiv ℝ (gradient (RelativeHessianCutoffSpatial.value (radius K))) x‖
        ≤ 2 ^ 121 * ((K : ℝ) + 1) * (1 / (2 ^ 228 * ((K : ℝ) + 1))) := by gcongr
      _ = 1 / 2 ^ 107 := by
          rw [mul_one_div, mul_div_mul_right _ _ (by positivity : ((K : ℝ) + 1) ≠ 0)]; norm_num
      _ ≤ 1 := by norm_num
  calc _ ≤ ‖fderiv ℝ (gradient (fun y => RelativeHessianCutoffSpatial.value (radius K) y *
        hidden K u v y)) x‖ + ‖(1 / 2 : ℝ) • fderiv ℝ (gradient
          (FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E))) x‖ := norm_add_le _ _
    _ ≤ (2 ^ 124 + 2 ^ 26 + 1) + 1 := add_le_add (hp.trans (by linarith)) hQ
    _ ≤ 2 ^ 126 := by norm_num

lemma objective_third_bound (fr : Frame K u v) (x : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (objective K (radius K) u v))) x‖ ≤ 2 ^ 126 := by
  have hq := RelativeHessianGuard.quadratic_smooth (E := E) 2
  rw [objective_split, add_third (product_smooth K u v) (contDiff_const.mul hq),
    cmul_third hq, RelativeHessianGuard.quadratic_third, smul_zero, add_zero]
  obtain ⟨c0, c1, c2, c3⟩ := cut_bounds K x
  have hT := hidden_third_bound fr x
  have hH := hidden_hessian_bound fr x
  have hG := hidden_gradient_bound fr x
  have hV := hidden_value_bound fr x
  have hp := ProductCompositionJets.product_third_norm (RelativeHessianCutoffSpatial.smooth (radius K))
    (hidden_smooth K u v) x
  have hs := sqrt_succ_ge K
  have hK1 : (1 : ℝ) ≤ K + 1 := by linarith [Nat.cast_nonneg (α := ℝ) K]
  have t1 : |RelativeHessianCutoffSpatial.value (radius K) x| *
      ‖fderiv ℝ (fderiv ℝ (gradient (hidden K u v))) x‖ ≤ 2 ^ 124 := by
    calc _ ≤ 1 * 2 ^ 124 := mul_le_mul c0 hT (ContinuousLinearMap.opNorm_nonneg _) (by norm_num)
      _ = 2 ^ 124 := one_mul _
  have t2 : |hidden K u v x| *
      ‖fderiv ℝ (fderiv ℝ (gradient (RelativeHessianCutoffSpatial.value (radius K)))) x‖ ≤ 1 := by
    calc _ ≤ 2 ^ 121 * (K + 1) * (1 / (2 ^ 358 * (K + 1) * Real.sqrt (K + 1))) := by gcongr
      _ = 1 / (2 ^ 237 * Real.sqrt (K + 1)) := by field_simp
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith
  have t3 : 3 * ‖gradient (RelativeHessianCutoffSpatial.value (radius K)) x‖ *
      ‖fderiv ℝ (gradient (hidden K u v)) x‖ ≤ 2 ^ 28 := by
    calc _ ≤ 3 * (1 / (2 ^ 98 * Real.sqrt (K + 1))) * 2 ^ 124 := by gcongr
      _ = 3 * 2 ^ 26 / Real.sqrt (K + 1) := by field_simp
      _ ≤ 3 * 2 ^ 26 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      _ ≤ 2 ^ 28 := by norm_num
  have t4 : 3 * ‖gradient (hidden K u v) x‖ *
      ‖fderiv ℝ (gradient (RelativeHessianCutoffSpatial.value (radius K))) x‖ ≤ 1 := by
    calc _ ≤ 3 * (2 ^ 123 * Real.sqrt (K + 1)) * (1 / (2 ^ 228 * (K + 1))) := by gcongr
      _ = 3 * Real.sqrt (K + 1) / (2 ^ 105 * (K + 1)) := by field_simp
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        have : Real.sqrt (K + 1) ≤ K + 1 := by
          nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ K + 1 by positivity), hs]
        nlinarith
  calc _ ≤ _ := hp
    _ ≤ 2 ^ 124 + 1 + 2 ^ 28 + 1 := by linarith
    _ ≤ 2 ^ 126 := by norm_num

lemma objective_gradient_lipschitz (fr : Frame K u v) (x y : E) :
    ‖gradient (objective K (radius K) u v) x - gradient (objective K (radius K) u v) y‖ ≤
      2 ^ 126 * ‖x - y‖ :=
  lipschitz_of_bound (fun z => (GradientDependentLocal.derivative_chain
    (objective_smooth K (radius K) u v)).2.1 z) (fun z => objective_hessian_bound fr z) x y

lemma objective_hessian_lipschitz (fr : Frame K u v) (x y : E) :
    ‖fderiv ℝ (gradient (objective K (radius K) u v)) x -
      fderiv ℝ (gradient (objective K (radius K) u v)) y‖ ≤ 2 ^ 126 * ‖x - y‖ :=
  lipschitz_of_bound (fun z => (GradientDependentLocal.derivative_chain
    (objective_smooth K (radius K) u v)).2.2 z) (fun z => objective_third_bound fr z) x y

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma objective_zero (K : ℕ) (u v : ℕ → E) : objective K (radius K) u v 0 = 0 := by
  have hl : ∀ l, link u v l 0 = 0 := fun l => by
    unfold link; simp [RidgeJets.value, lam, (unit_flat (t := (-4 : ℝ)) (by norm_num)).1]
  have hs : ∀ l, saddle u v l 0 = 0 := fun l => by
    unfold saddle; simp [RidgeJets.value, sad]
  unfold objective EscapeChainFunction.hidden
  simp [hl, hs, FullGeneralizedSmoothZeroQuery.quadratic]

lemma objective_lower (fr : Frame K u v) (x : E) :
    -(2 ^ 121 * (K + 1)) ≤ objective K (radius K) u v x := by
  obtain ⟨c0, -⟩ := cut_bounds K x
  have hV := hidden_value_bound fr x
  have hq : 0 ≤ (1 / 2 : ℝ) * FullGeneralizedSmoothZeroQuery.quadratic 2 (0 : E) x := by
    rw [normsq_eq]; positivity
  have hp : |RelativeHessianCutoffSpatial.value (radius K) x * hidden K u v x| ≤ 2 ^ 121 * (K + 1) := by
    rw [abs_mul]
    calc _ ≤ 1 * (2 ^ 121 * ((K : ℝ) + 1)) := mul_le_mul c0 hV (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  unfold objective
  have := neg_abs_le (RelativeHessianCutoffSpatial.value (radius K) x * hidden K u v x)
  linarith

end LongTails.Proofs.EscapeChainRegularity
