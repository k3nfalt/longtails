import LongTails.Setups.FiniteSumThirdSmoothConvex
import LongTails.Proofs.ThirdSmoothJensen
import LongTails.Proofs.SvrgConvex
import LongTails.Algorithms.TaylorCorrectedNewton
import LongTails.Proofs.TaylorCorrectedStep

namespace LongTails.Proofs.FiniteSumThirdSmoothGeometry

open LongTails.Setups.FiniteSumSmoothAndConvex
open LongTails.Algorithms.TaylorCorrectedNewton
open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ}

omit [FiniteDimensional ℝ E] in
lemma objective_contDiff (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) :
    ContDiff ℝ 3 (objective f) := by
  exact contDiff_const.mul (ContDiff.sum (fun i _ => hf i))

lemma objective_gradient (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) (x : E) :
    gradient (objective f) x = (n : ℝ)⁻¹ • ∑ i, gradient (f i) x := by
  exact (OracleTemplate.FiniteSum.objective_gradient
    (oracle := fun ix => gradient (f ix.1) ix.2)
    (fun i y => ((hf i).differentiable (by norm_num) y).hasGradientAt) x).gradient

lemma objective_hessian (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) (x : E) :
    fderiv ℝ (gradient (objective f)) x = (n : ℝ)⁻¹ • ∑ i, fderiv ℝ (gradient (f i)) x := by
  have hg : gradient (objective f) = fun y => (n : ℝ)⁻¹ • ∑ i, gradient (f i) y :=
    funext (objective_gradient f hf)
  rw [hg]
  have hd : HasFDerivAt (fun y => (n : ℝ)⁻¹ • ∑ i, gradient (f i) y)
      ((n : ℝ)⁻¹ • ∑ i, fderiv ℝ (gradient (f i)) x) x := by
    convert ((HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
      (GradientDependentLocal.derivative_chain (hf i)).2.1 x)).const_smul ((n : ℝ)⁻¹)) using 1
    funext y
    simp
  exact hd.fderiv

lemma objective_third (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) (x : E) :
    fderiv ℝ (fderiv ℝ (gradient (objective f))) x =
      (n : ℝ)⁻¹ • ∑ i, fderiv ℝ (fderiv ℝ (gradient (f i))) x := by
  have he : fderiv ℝ (gradient (objective f)) =
      fun y => (n : ℝ)⁻¹ • ∑ i, fderiv ℝ (gradient (f i)) y :=
    funext (objective_hessian f hf)
  rw [he]
  have hd := (HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
    (GradientDependentLocal.derivative_chain (hf i)).2.2 x)).const_smul ((n : ℝ)⁻¹)
  have he' : (fun y => (n : ℝ)⁻¹ • ∑ i, fderiv ℝ (gradient (f i)) y) =
      (n : ℝ)⁻¹ • ∑ i, fderiv ℝ (gradient (f i)) := by
    funext y
    simp
  rw [he']
  exact hd.fderiv

lemma objective_third_lipschitz [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) {L : ℝ}
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖) (x y : E) :
    ‖fderiv ℝ (fderiv ℝ (gradient (objective f))) x -
      fderiv ℝ (fderiv ℝ (gradient (objective f))) y‖ ≤ L * ‖x - y‖ := by
  rw [objective_third f hf, objective_third f hf]
  have he : (n : ℝ)⁻¹ • (∑ i, fderiv ℝ (fderiv ℝ (gradient (f i))) x) -
      (n : ℝ)⁻¹ • (∑ i, fderiv ℝ (fderiv ℝ (gradient (f i))) y) =
      (n : ℝ)⁻¹ • ∑ i, (fderiv ℝ (fderiv ℝ (gradient (f i))) x -
        fderiv ℝ (fderiv ℝ (gradient (f i))) y) := by
    ext a b
    simp [Finset.sum_sub_distrib, smul_sub]
  rw [he]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  calc
    _ ≤ ‖(n : ℝ)⁻¹‖ * ‖∑ i, (fderiv ℝ (fderiv ℝ (gradient (f i))) x -
        fderiv ℝ (fderiv ℝ (gradient (f i))) y)‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ (n : ℝ)⁻¹ * ∑ i, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
        fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)⁻¹)]
      exact mul_le_mul_of_nonneg_left
        (norm_sum_le Finset.univ (fun i : Fin n =>
          fderiv ℝ (fderiv ℝ (gradient (f i))) x - fderiv ℝ (fderiv ℝ (gradient (f i))) y))
        (by positivity)
    _ ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, L * ‖x - y‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hT i x y)) (by positivity)
    _ = _ := by simp [← mul_assoc, hn]

lemma average_remainder (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) (v w : E) :
    (n : ℝ)⁻¹ • ∑ i, (gradient (f i) v - gradient (f i) w -
      fderiv ℝ (gradient (f i)) w (v - w)) =
      gradient (objective f) v - gradient (objective f) w -
        fderiv ℝ (gradient (objective f)) w (v - w) := by
  rw [objective_gradient f hf v, objective_gradient f hf w, objective_hessian f hf w]
  simp only [Finset.sum_sub_distrib, smul_sub, smul_apply,
    sum_apply]

lemma remainder_sum [NeZero n] (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) (v w : E) :
    ∑ i, (gradient (f i) v - gradient (f i) w - fderiv ℝ (gradient (f i)) w (v - w)) =
      (n : ℝ) • (gradient (objective f) v - gradient (objective f) w -
        fderiv ℝ (gradient (objective f)) w (v - w)) := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hh := congrArg (fun a : E => (n : ℝ) • a) (average_remainder f hf v w)
  simpa only [smul_smul, mul_inv_cancel₀ hn, one_smul] using hh

lemma average_bregman (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i)) (v w : E) :
    (n : ℝ)⁻¹ * ∑ i, (f i v - f i w - ⟪gradient (f i) w, v - w⟫) =
      objective f v - objective f w - ⟪gradient (objective f) w, v - w⟫ := by
  rw [objective_gradient f hf]
  simp only [objective, Finset.sum_sub_distrib, real_inner_smul_left, sum_inner, mul_sub]

lemma bregman_nonneg (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    (hc : ∀ i, ConvexOn ℝ Set.univ (f i)) (v w : E) :
    0 ≤ objective f v - objective f w - ⟪gradient (objective f) w, v - w⟫ := by
  rw [← average_bregman f hf]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  exact sub_nonneg.mpr (OracleTemplate.Gradient.convex_support (hc i)
    (fun y => ((hf i).differentiable (by norm_num) y).hasGradientAt) w v)

lemma remainder_variance (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L : ℝ} (hL : 0 < L)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖) (w v : E) :
    (n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) v - gradient (f i) w -
      fderiv ℝ (gradient (f i)) w (v - w)‖ ^ 2 ≤
      2 * L * ‖v - w‖ ^ 2 *
        (objective f v - objective f w - ⟪gradient (objective f) w, v - w⟫) := by
  simpa only [average_bregman f hf] using
    ThirdSmoothJensen.finite_sum_remainder_bound f hf hc hL hT w v

lemma ball_remainder_variance (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L ρ : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c w v : E) (hw : w ∈ Metric.closedBall c ρ) (hv : v ∈ Metric.closedBall c ρ) :
    (n : ℝ)⁻¹ * ∑ i, ‖gradient (f i) v - gradient (f i) w -
      fderiv ℝ (gradient (f i)) w (v - w)‖ ^ 2 ≤
      8 * L * ρ ^ 2 *
        (objective f v - objective f w - ⟪gradient (objective f) w, v - w⟫) := by
  have hd : ‖v - w‖ ≤ 2 * ρ := by
    have hh := dist_triangle v c w
    rw [dist_comm c w] at hh
    calc
      ‖v - w‖ ≤ ‖v - c‖ + ‖w - c‖ := by simpa [dist_eq_norm] using hh
      _ ≤ 2 * ρ := by
        have hw' : ‖w - c‖ ≤ ρ := by simpa [dist_eq_norm] using hw
        have hv' : ‖v - c‖ ≤ ρ := by simpa [dist_eq_norm] using hv
        linarith
  apply (remainder_variance f hf hc hL hT w v).trans
  apply mul_le_mul_of_nonneg_right _ (bregman_nonneg f hf hc v w)
  have hs : ‖v - w‖ ^ 2 ≤ (2 * ρ) ^ 2 := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr hd
  nlinarith [mul_le_mul_of_nonneg_left hs hL.le]

lemma local_potential [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L ρ η : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ) (hη : 0 ≤ η)
    (hstep : 32 * η * L * ρ ^ 2 ≤ 1)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c z w u : E) (hw : w ∈ Metric.closedBall c ρ) (hu : u ∈ Metric.closedBall c ρ) :
    let F := objective f
    let v := modelPoint η ρ c z w (gradient F w) (fderiv ℝ (gradient F) w)
    let e := fun i => gradient (f i) v - gradient (f i) w - fderiv ℝ (gradient (f i)) w (v - w)
    (n : ℝ)⁻¹ * (∑ i, ‖v - (2 * η) • e i - u‖ ^ 2) / 2 +
      η * (F v - F u + 2 * (F u - F v - ⟪gradient F v, u - v⟫)) ≤
        ‖z - u‖ ^ 2 / 2 + η * (F u - F w - ⟪gradient F w, u - w⟫) := by
  dsimp only
  let F := objective f
  let v := modelPoint η ρ c z w (gradient F w) (fderiv ℝ (gradient F) w)
  let e := fun i => gradient (f i) v - gradient (f i) w - fderiv ℝ (gradient (f i)) w (v - w)
  have hH : ∀ a b, ⟪a, fderiv ℝ (gradient F) w b⟫ = ⟪fderiv ℝ (gradient F) w a, b⟫ := by
    intro a b
    exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
      ((objective_contDiff f hf).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) w a b).symm
  have hv := (TaylorCorrectedStep.modelPoint_optimal hρ η c z w
    (gradient F w) (fderiv ℝ (gradient F) w)).1
  have hm := TaylorCorrectedStep.modelPoint_variational hρ η c z w
    (gradient F w) (fderiv ℝ (gradient F) w) hH u hu
  have hh := TaylorCorrectedStep.averaged_descent F (gradient F) z v u w
    (fderiv ℝ (gradient F) w (v - w)) e hη (by simpa only [v, two_smul] using hm)
    (remainder_sum f hf v w) (bregman_nonneg f hf hc v w)
    (ball_remainder_variance f hf hc hL hρ hT c w v hw hv)
    (show 4 * η * (8 * L * ρ ^ 2) ≤ 1 by nlinarith [hstep])
  have hd := mul_nonneg (show 0 ≤ η / 2 by positivity) (bregman_nonneg f hf hc v w)
  have hn := sq_nonneg ‖z - v‖
  change (n : ℝ)⁻¹ * (∑ i, ‖v - (2 * η) • e i - u‖ ^ 2) / 2 +
    η * (F v - F u + 2 * (F u - F v - ⟪gradient F v, u - v⟫)) ≤
      ‖z - u‖ ^ 2 / 2 + η * (F u - F w - ⟪gradient F w, u - w⟫)
  dsimp only [F] at hh hd ⊢
  nlinarith

lemma eval_step (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    (η ρ : ℝ) (c z w : E) (i : Fin n) :
    let answer := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
    let v := modelPoint η ρ c z w (gradient (objective f) w) (fderiv ℝ (gradient (objective f)) w)
    OracleTemplate.QueryPlan.eval answer (step η ρ c z w (fun j => answer (j, w)) i) =
      (v - (2 * η) • (gradient (f i) v - gradient (f i) w -
        fderiv ℝ (gradient (f i)) w (v - w)), v) := by
  dsimp only
  rw [objective_gradient f hf w, objective_hessian f hf w]
  rfl

lemma step_potential [NeZero n] (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L ρ η : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ) (hη : 0 ≤ η)
    (hstep : 32 * η * L * ρ ^ 2 ≤ 1)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c z w u : E) (hw : w ∈ Metric.closedBall c ρ) (hu : u ∈ Metric.closedBall c ρ) :
    let F := objective f
    let answer := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
    (𝔼 i : Fin n,
      let result := OracleTemplate.QueryPlan.eval answer (step η ρ c z w (fun j => answer (j, w)) i)
      ‖result.1 - u‖ ^ 2 / 2 + η * (F result.2 - F u) +
        2 * (η * (F u - F result.2 - ⟪gradient F result.2, u - result.2⟫))) ≤
      ‖z - u‖ ^ 2 / 2 + η * (F u - F w - ⟪gradient F w, u - w⟫) := by
  dsimp only
  simp only [eval_step f hf]
  have hh := local_potential f hf hc hL hρ hη hstep hT c z w u hw hu
  dsimp only at hh
  simp only [Finset.expect_add_distrib, Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    ← Finset.sum_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp at hh ⊢
  nlinarith only [hh]

end LongTails.Proofs.FiniteSumThirdSmoothGeometry
