import LongTails.Proofs.TensorFreeModelExecution

namespace LongTails.Proofs.TensorFreeModelTermination

open LongTails.Algorithms.TensorFreeModel LongTails.Algorithms.TaylorCorrectedNewton
open LongTails.Proofs.TensorFreeModel LongTails.Proofs.TensorFreeModelConvergence
open LongTails.Proofs.TensorFreeModelExecution
open LongTails.Setups.FiniteSumSmoothAndConvex
open OracleTemplate OracleTemplate.QueryPlan
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

lemma local_gradient_gap {M : E → ℝ} (hM : ContDiff ℝ 3 M)
    {B ρ r : ℝ} (hB : 0 < B) (hr : 0 ≤ r) (x u : E)
    (hx : ‖x‖ ≤ ρ) (hg : ‖gradient M x‖ ≤ B * r)
    (hH : ∀ y, ‖y‖ ≤ ρ + r → ‖fderiv ℝ (gradient M) y‖ ≤ B)
    (hmin : ∀ y, M u ≤ M y) :
    ‖gradient M x‖ ^ 2 ≤ 2 * B * (M x - M u) := by
  let d := -(B⁻¹) • gradient M x
  have hd : ‖d‖ ≤ r := by
    dsimp [d]
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (inv_pos.mpr hB)]
    exact (inv_mul_le_iff₀ hB).mpr hg
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖x + t • d‖ ≤ ρ + r := by
    calc
      ‖x + t • d‖ ≤ ‖x‖ + ‖t • d‖ := norm_add_le _ _
      _ = ‖x‖ + t * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ ρ + r := by nlinarith [norm_nonneg d, ht.1, ht.2]
  have hh := GuardedMetricSupport.hessian_upper hM (x + d) x (m := B * ‖d‖ ^ 2) (by
    intro t ht
    simp only [add_sub_cancel_left]
    calc
      ⟪fderiv ℝ (gradient M) (x + t • d) d, d⟫ ≤
          ‖fderiv ℝ (gradient M) (x + t • d) d‖ * ‖d‖ := real_inner_le_norm _ _
      _ ≤ (‖fderiv ℝ (gradient M) (x + t • d)‖ * ‖d‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (B * ‖d‖) * ‖d‖ := by gcongr; exact hH _ (hp t ht)
      _ = B * ‖d‖ ^ 2 := by ring)
  simp only [add_sub_cancel_left] at hh
  have hi : ⟪gradient M x, d⟫ = -B⁻¹ * ‖gradient M x‖ ^ 2 := by
    simp only [d, inner_smul_right, real_inner_self_eq_norm_sq]
  have hn : ‖d‖ ^ 2 = B⁻¹ ^ 2 * ‖gradient M x‖ ^ 2 := by
    simp [d, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hi, hn] at hh
  have halg : -B⁻¹ * ‖gradient M x‖ ^ 2 + B * (B⁻¹ ^ 2 * ‖gradient M x‖ ^ 2) / 2 =
      -(‖gradient M x‖ ^ 2 / (2 * B)) := by field_simp; ring
  have hgap : ‖gradient M x‖ ^ 2 / (2 * B) ≤ M x - M u := by
    linarith [hmin (x + d), halg]
  simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 2 * B)).mp hgap

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma acceptance_from_model_gradient {estimate model trueGradient : E} {δ tol : ℝ}
    (herr : ‖estimate - model‖ ≤ δ)
    (hδ : δ ≤ tol / 24) (hm : ‖model‖ ≤ tol / 12) :
    ‖trueGradient‖ ≤ tol ∨ ‖estimate‖ ≤ ‖trueGradient‖ / 6 - δ := by
  by_cases h : ‖trueGradient‖ ≤ tol
  · exact Or.inl h
  · right
    have he := norm_sub_norm_le estimate model
    linarith


lemma modelRound_accepts [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) {L τ ρ δ tol : ℝ} (hL : 0 ≤ L) (hτ : 0 < τ)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (hδ : τ * L * ρ ^ 3 / 6 ≤ δ) (hsmall : δ ≤ tol / 24)
    (z : E) (st : ModelState E) (hst : st.displacement ∈ Metric.closedBall (0 : E) ρ)
    (hm : st.accepted = false →
      ‖exactGradient (gradient (objective f) z) (fderiv ℝ (gradient (objective f)) z)
        (fderiv ℝ (fderiv ℝ (gradient (objective f))) z) L st.displacement‖ ≤ tol / 12) :
    (eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
      (modelRound (gradient (objective f) z) (fderiv ℝ (gradient (objective f)) z)
        L τ ρ δ tol z st)).accepted = true := by
  rw [eval_modelRound f hf]
  by_cases ha : st.accepted = true
  · simp [ha]
  · have hh := acceptance_from_model_gradient
      (trueGradient := gradient (objective f) (z + st.displacement))
      (estimate_error_ball f hf hL hτ hT hδ z st.displacement hst) hsmall
      (hm (Bool.eq_false_of_not_eq_true ha))
    simp [ha, hh]

lemma solveModel_accepts [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) {L τ ρ δ tol : ℝ} (hL : 0 ≤ L) (hτ : 0 < τ) (hρ : 0 ≤ ρ)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (hδ : τ * L * ρ ^ 3 / 6 ≤ δ) (hsmall : δ ≤ tol / 24) (z : E) (K : ℕ)
    (hm : let F := objective f
      let st := eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
        (modelRounds (gradient F z) (fderiv ℝ (gradient F) z) L τ ρ δ tol z K ⟨0, 0, false⟩)
      st.accepted = false → ‖exactGradient (gradient F z) (fderiv ℝ (gradient F) z)
        (fderiv ℝ (fderiv ℝ (gradient F)) z) L st.displacement‖ ≤ tol / 12) :
    (eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
      (solveModel L τ ρ δ tol z K)).accepted = true := by
  have hh := modelRound_accepts f hf hL hτ hT hδ hsmall z _
    (modelRounds_mem _ _ _ L τ δ tol hρ z K _ (by simpa using hρ)) hm
  rw [← eval_modelRounds_succ] at hh
  simpa only [solveModel, eval_bind, snapshot, TaylorCorrectedStep.eval_collect, id_eq,
    meanGradient, meanHessian, FiniteSumThirdSmoothGeometry.objective_gradient f hf,
    FiniteSumThirdSmoothGeometry.objective_hessian f hf] using hh


lemma actual_model_gradient {f : E → ℝ} (hf : ContDiff ℝ 3 f) (z s : E) (L : ℝ) :
    gradient (modelValue (gradient f z) (fderiv ℝ (gradient f) z)
      (fderiv ℝ (fderiv ℝ (gradient f)) z) L) s =
      exactGradient (gradient f z) (fderiv ℝ (gradient f) z)
        (fderiv ℝ (fderiv ℝ (gradient f)) z) L s := by
  apply HasGradientAt.gradient
  apply model_hasGradientAt
  · intro a b
    exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
      (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) z a b).symm
  · exact ThirdOrderObjectiveGeometry.third_swap_first hf z
  · exact ThirdOrderObjectiveGeometry.third_swap_last hf z

omit [FiniteDimensional ℝ E] in
lemma quartic_hessian_norm (x : E) :
    ‖LongTails.Algorithms.QuarticProximal.hess x‖ ≤ 3 * ‖x‖ ^ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  simp only [LongTails.Algorithms.QuarticProximal.hess, add_apply,
    smul_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  simp only [← Nat.cast_smul_eq_nsmul ℝ]
  calc
    ‖‖x‖ ^ 2 • v + (2 : ℝ) • (⟪x, v⟫ • x)‖ ≤
        ‖‖x‖ ^ 2 • v‖ + ‖(2 : ℝ) • (⟪x, v⟫ • x)‖ := norm_add_le _ _
    _ = ‖x‖ ^ 2 * ‖v‖ + 2 * (|⟪x, v⟫| * ‖x‖) := by
      simp [norm_smul, Real.norm_eq_abs]
    _ ≤ ‖x‖ ^ 2 * ‖v‖ + 2 * ((‖x‖ * ‖v‖) * ‖x‖) := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ = 3 * ‖x‖ ^ 2 * ‖v‖ := by ring

lemma actual_model_hessian_norm {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (z s : E) {L : ℝ} (hL : 0 ≤ L) :
    ‖fderiv ℝ (gradient (modelValue (gradient f z) (fderiv ℝ (gradient f) z)
      (fderiv ℝ (fderiv ℝ (gradient f)) z) L)) s‖ ≤
      ‖fderiv ℝ (gradient f) z‖ + ‖fderiv ℝ (fderiv ℝ (gradient f)) z‖ * ‖s‖ + 3 * L * ‖s‖ ^ 2 := by
  have he := funext (fun x => actual_model_gradient hf z x L)
  rw [he, (modelGradient_hasFDerivAt _ _ _ (ThirdOrderObjectiveGeometry.third_swap_first hf z) L s).fderiv]
  calc
    ‖fderiv ℝ (gradient f) z + fderiv ℝ (fderiv ℝ (gradient f)) z s +
        L • LongTails.Algorithms.QuarticProximal.hess s‖ ≤
        ‖fderiv ℝ (gradient f) z‖ + ‖fderiv ℝ (fderiv ℝ (gradient f)) z s‖ +
          ‖L • LongTails.Algorithms.QuarticProximal.hess s‖ := (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ‖fderiv ℝ (gradient f) z‖ + ‖fderiv ℝ (fderiv ℝ (gradient f)) z‖ * ‖s‖ +
        L * (3 * ‖s‖ ^ 2) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hL]
      gcongr
      · exact ContinuousLinearMap.le_opNorm _ _
      · exact quartic_hessian_norm s
    _ = _ := by ring


omit [FiniteDimensional ℝ E] in
lemma exactGradient_norm (g : E) (H : E →L[ℝ] E) (T : E →L[ℝ] E →L[ℝ] E)
    {L : ℝ} (hL : 0 ≤ L) (s : E) :
    ‖exactGradient g H T L s‖ ≤ ‖g‖ + ‖H‖ * ‖s‖ + ‖T‖ * ‖s‖ ^ 2 / 2 + L * ‖s‖ ^ 3 := by
  have hT : ‖T s s‖ ≤ ‖T‖ * ‖s‖ ^ 2 := by
    calc
      ‖T s s‖ ≤ ‖T s‖ * ‖s‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖T‖ * ‖s‖) * ‖s‖ := mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by ring
  unfold exactGradient
  calc
    ‖g + H s + (1 / 2 : ℝ) • T s s + (L * ‖s‖ ^ 2) • s‖ ≤
        ‖g‖ + ‖H s‖ + ‖(1 / 2 : ℝ) • T s s‖ + ‖(L * ‖s‖ ^ 2) • s‖ := by
      have h₁ := norm_add_le (g + H s + (1 / 2 : ℝ) • T s s) ((L * ‖s‖ ^ 2) • s)
      have h₂ := norm_add_le (g + H s) ((1 / 2 : ℝ) • T s s)
      have h₃ := norm_add_le g (H s)
      linarith
    _ = ‖g‖ + ‖H s‖ + ‖T s s‖ / 2 + L * ‖s‖ ^ 3 := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2), abs_of_nonneg (by positivity : 0 ≤ L * ‖s‖ ^ 2)]
      ring
    _ ≤ _ := by gcongr; exact ContinuousLinearMap.le_opNorm _ _

lemma model_gradient_small {f : E → ℝ} (hf : ContDiff ℝ 3 f) (z u s : E)
    {L B ρ r tol : ℝ} (hL : 0 ≤ L) (hB : 0 < B) (hr : 0 ≤ r) (htol : 0 ≤ tol)
    (hs : ‖s‖ ≤ ρ)
    (hg : ‖gradient f z‖ + ‖fderiv ℝ (gradient f) z‖ * ρ +
      ‖fderiv ℝ (fderiv ℝ (gradient f)) z‖ * ρ ^ 2 / 2 + L * ρ ^ 3 ≤ B * r)
    (hH : ‖fderiv ℝ (gradient f) z‖ +
      ‖fderiv ℝ (fderiv ℝ (gradient f)) z‖ * (ρ + r) + 3 * L * (ρ + r) ^ 2 ≤ B)
    (hmin : ∀ y, modelValue (gradient f z) (fderiv ℝ (gradient f) z)
      (fderiv ℝ (fderiv ℝ (gradient f)) z) L u ≤
      modelValue (gradient f z) (fderiv ℝ (gradient f) z)
      (fderiv ℝ (fderiv ℝ (gradient f)) z) L y)
    (hgap : modelValue (gradient f z) (fderiv ℝ (gradient f) z)
      (fderiv ℝ (fderiv ℝ (gradient f)) z) L s -
      modelValue (gradient f z) (fderiv ℝ (gradient f) z)
      (fderiv ℝ (fderiv ℝ (gradient f)) z) L u ≤ tol ^ 2 / (288 * B)) :
    ‖exactGradient (gradient f z) (fderiv ℝ (gradient f) z)
      (fderiv ℝ (fderiv ℝ (gradient f)) z) L s‖ ≤ tol / 12 := by
  let M := modelValue (gradient f z) (fderiv ℝ (gradient f) z)
    (fderiv ℝ (fderiv ℝ (gradient f)) z) L
  have hgrad : ‖gradient M s‖ ≤ B * r := by
    rw [actual_model_gradient hf]
    apply (exactGradient_norm _ _ _ hL s).trans
    apply le_trans _ hg
    gcongr
  have hhess (y : E) (hy : ‖y‖ ≤ ρ + r) : ‖fderiv ℝ (gradient M) y‖ ≤ B := by
    apply (actual_model_hessian_norm hf z y hL).trans
    apply le_trans _ hH
    gcongr
  have hh := local_gradient_gap ((model_contDiff _ _ _ _).of_le (by simp)) hB hr s u hs hgrad hhess hmin
  rw [actual_model_gradient hf] at hh
  have hb := (le_div_iff₀ (by positivity : 0 < 288 * B)).mp hgap
  nlinarith [norm_nonneg (exactGradient (gradient f z) (fderiv ℝ (gradient f) z)
    (fderiv ℝ (fderiv ℝ (gradient f)) z) L s)]


lemma solveModel_terminates [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L τ ρ δ tol t B r : ℝ} (hL : 0 ≤ L) (hτ : 0 < τ) (hρ : 0 ≤ ρ)
    (ht : 0 ≤ t) (hB : 0 < B) (hr : 0 ≤ r) (htol : 0 ≤ tol)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (hδ : τ * L * ρ ^ 3 / 6 ≤ δ) (hδt : δ ≤ L * t ^ 3) (hsmall : δ ≤ tol / 24)
    (z u : E) (hu : u ∈ Metric.closedBall (0 : E) ρ) (k : ℕ)
    (hg : ‖gradient (objective f) z‖ + ‖fderiv ℝ (gradient (objective f)) z‖ * ρ +
      ‖fderiv ℝ (fderiv ℝ (gradient (objective f))) z‖ * ρ ^ 2 / 2 + L * ρ ^ 3 ≤ B * r)
    (hH : ‖fderiv ℝ (gradient (objective f)) z‖ +
      ‖fderiv ℝ (fderiv ℝ (gradient (objective f))) z‖ * (ρ + r) + 3 * L * (ρ + r) ^ 2 ≤ B)
    (hmin : ∀ y, modelValue (gradient (objective f) z) (fderiv ℝ (gradient (objective f)) z)
      (fderiv ℝ (fderiv ℝ (gradient (objective f))) z) L u ≤
      modelValue (gradient (objective f) z) (fderiv ℝ (gradient (objective f)) z)
      (fderiv ℝ (fderiv ℝ (gradient (objective f))) z) L y)
    (hbudget : (2 * (1 + 1 / Real.sqrt 2)) * (23 / 24 : ℝ) ^ (k + 1) *
      kernelBregman (fderiv ℝ (gradient (objective f)) z) L 0 u +
      24 * (2 * (1 + 1 / Real.sqrt 2)) * (3 * L * t ^ 4) ≤ tol ^ 2 / (288 * B)) :
    (eval (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
      (solveModel L τ ρ δ tol z (k + 1))).accepted = true := by
  apply solveModel_accepts f hf hL hτ hρ hT hδ hsmall z (k + 1)
  dsimp only
  intro ha
  have hmem := modelRounds_mem
    (fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2))
    (gradient (objective f) z) (fderiv ℝ (gradient (objective f)) z) L τ δ tol hρ z (k + 1)
    (⟨0, 0, false⟩ : ModelState E) (by simpa using hρ)
  have hgap := modelRounds_masked_gap f hf hc (tol := tol) hL hτ hρ ht hT hδ hδt z u hu
    (⟨0, 0, false⟩ : ModelState E) (by simpa using hρ) hmin k
  dsimp only at hgap
  simp only [maskedGap, maskedEnergy, ha, Bool.false_eq_true, ↓reduceIte] at hgap
  exact model_gradient_small (FiniteSumThirdSmoothGeometry.objective_contDiff f hf) z u _
    hL hB hr htol (by simpa only [Metric.mem_closedBall, dist_zero_right] using hmem)
    hg hH hmin (hgap.trans hbudget)

end LongTails.Proofs.TensorFreeModelTermination
