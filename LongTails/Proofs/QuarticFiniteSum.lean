import LongTails.Proofs.QuarticProximalGeometry
import LongTails.Proofs.FiniteSumThirdSmoothGeometry
import LongTails.Proofs.TaylorCorrectedConvergence

namespace LongTails.Proofs.QuarticFiniteSum

open LongTails.Algorithms.QuarticProximal
open LongTails.Setups.FiniteSumSmoothAndConvex
open scoped RealInnerProductSpace BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ} [NeZero n]

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] in
lemma objective_penalty (f : Fin n → E → ℝ) (γ μ : ℝ) (c y0 x : E) :
    objective (fun i z => f i z + penalty γ μ c y0 z) x =
      objective f x + penalty γ μ c y0 x := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp only [objective, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_add, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

omit [FiniteDimensional ℝ E] [NeZero n] in
lemma component_contDiff (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    (γ μ : ℝ) (c y0 : E) (i : Fin n) :
    ContDiff ℝ 3 (fun x => f i x + penalty γ μ c y0 x) :=
  (hf i).add ((QuarticProximalGeometry.penalty_contDiff γ μ c y0).of_le le_top)

omit [NeZero n] in
lemma component_gradient (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    (γ μ : ℝ) (c y0 x : E) (i : Fin n) :
    gradient (fun z => f i z + penalty γ μ c y0 z) x =
      gradient (f i) x + penaltyGrad γ μ c y0 x :=
  (QuarticProximalGeometry.add_penalty_hasGradientAt
    (fun z => ((hf i).differentiable (by norm_num) z).hasGradientAt) γ μ c y0 x).gradient

omit [NeZero n] in
lemma component_hessian (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    (γ μ : ℝ) (c y0 x : E) (i : Fin n) :
    fderiv ℝ (gradient (fun z => f i z + penalty γ μ c y0 z)) x =
      fderiv ℝ (gradient (f i)) x + penaltyHess γ μ c x := by
  have he : gradient (fun z => f i z + penalty γ μ c y0 z) =
      fun z => gradient (f i) z + penaltyGrad γ μ c y0 z :=
    funext (fun z => component_gradient f hf γ μ c y0 z i)
  rw [he]
  exact ((GradientDependentLocal.derivative_chain (hf i)).2.1 x |>.add
    (QuarticProximalGeometry.penaltyGrad_hasFDerivAt γ μ c y0 x)).fderiv

omit [NeZero n] in
lemma component_third (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    (γ μ : ℝ) (c y0 x : E) (i : Fin n) :
    fderiv ℝ (fderiv ℝ (gradient (fun z => f i z + penalty γ μ c y0 z))) x =
      fderiv ℝ (fderiv ℝ (gradient (f i))) x +
        fderiv ℝ (fderiv ℝ (gradient (penalty γ μ c y0))) x := by
  have hp : fderiv ℝ (gradient (penalty γ μ c y0)) = penaltyHess γ μ c := by
    rw [gradient_eq (QuarticProximalGeometry.penalty_hasGradientAt γ μ c y0)]
    exact funext (fun z => (QuarticProximalGeometry.penaltyGrad_hasFDerivAt γ μ c y0 z).fderiv)
  have he : fderiv ℝ (gradient (fun z => f i z + penalty γ μ c y0 z)) =
      fun z => fderiv ℝ (gradient (f i)) z + fderiv ℝ (gradient (penalty γ μ c y0)) z := by
    funext z
    rw [component_hessian f hf, hp]
  rw [he]
  exact ((GradientDependentLocal.derivative_chain (hf i)).2.2 x |>.add
    ((GradientDependentLocal.derivative_chain
      ((QuarticProximalGeometry.penalty_contDiff γ μ c y0).of_le le_top)).2.2 x)).fderiv

omit [NeZero n] in
lemma component_third_lipschitz (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    {L γ μ : ℝ} (hγ : 0 ≤ γ)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c y0 x y : E) (i : Fin n) :
    ‖fderiv ℝ (fderiv ℝ (gradient (fun z => f i z + penalty γ μ c y0 z))) x -
      fderiv ℝ (fderiv ℝ (gradient (fun z => f i z + penalty γ μ c y0 z))) y‖ ≤
        (L + 6 * γ) * ‖x - y‖ := by
  rw [component_third f hf, component_third f hf]
  have he :
      (fderiv ℝ (fderiv ℝ (gradient (f i))) x + fderiv ℝ (fderiv ℝ (gradient (penalty γ μ c y0))) x) -
        (fderiv ℝ (fderiv ℝ (gradient (f i))) y + fderiv ℝ (fderiv ℝ (gradient (penalty γ μ c y0))) y) =
      (fderiv ℝ (fderiv ℝ (gradient (f i))) x - fderiv ℝ (fderiv ℝ (gradient (f i))) y) +
        (fderiv ℝ (fderiv ℝ (gradient (penalty γ μ c y0))) x -
          fderiv ℝ (fderiv ℝ (gradient (penalty γ μ c y0))) y) := by abel
  rw [he]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x - fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ +
        ‖fderiv ℝ (fderiv ℝ (gradient (penalty γ μ c y0))) x -
          fderiv ℝ (fderiv ℝ (gradient (penalty γ μ c y0))) y‖ := ContinuousLinearMap.opNorm_add_le _ _
    _ ≤ L * ‖x - y‖ + 6 * γ * ‖x - y‖ := add_le_add (hT i x y)
      (QuarticProximalGeometry.penalty_third_lipschitz (μ := μ) hγ c y0 x y)
    _ = _ := by ring

omit [NeZero n] in
lemma component_convex (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    (hc : ∀ i, ConvexOn ℝ Set.univ (f i)) {γ μ : ℝ} (hγ : 0 ≤ γ) (hμ : 0 ≤ μ)
    (c y0 : E) (i : Fin n) : ConvexOn ℝ Set.univ (fun z => f i z + penalty γ μ c y0 z) := by
  apply LoraObjective.support_convex (g := fun z => gradient (f i) z + penaltyGrad γ μ c y0 z)
  intro x y
  have hh := QuarticProximalGeometry.add_penalty_support
    (fun z => ((hf i).differentiable (by norm_num) z).hasGradientAt) (hc i) (μ := μ) hγ c y0 x y
  have hq : 0 ≤ γ * ‖y - x‖ ^ 4 / 12 := by positivity
  have hm : 0 ≤ μ * ‖y - x‖ ^ 2 / 2 := by positivity
  linarith

omit [NeZero n] in
lemma augment_answer (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    (γ μ : ℝ) (c y0 x : E) (i : Fin n) :
    augment γ μ c y0 x (gradient (f i) x, fderiv ℝ (gradient (f i)) x) =
      (gradient (fun z => f i z + penalty γ μ c y0 z) x,
        fderiv ℝ (gradient (fun z => f i z + penalty γ μ c y0 z)) x) := by
  rw [component_gradient f hf, component_hessian f hf]
  rfl

lemma objective_gradient (f : Fin n → E → ℝ) (hf : ∀ i, ContDiff ℝ 3 (f i))
    (γ μ : ℝ) (c y0 x : E) :
    gradient (objective (fun i z => f i z + penalty γ μ c y0 z)) x =
      gradient (objective f) x + penaltyGrad γ μ c y0 x := by
  have he : objective (fun i z => f i z + penalty γ μ c y0 z) =
      fun z => objective f z + penalty γ μ c y0 z := funext (objective_penalty f γ μ c y0)
  rw [he]
  exact (QuarticProximalGeometry.add_penalty_hasGradientAt
    (fun z => ((FiniteSumThirdSmoothGeometry.objective_contDiff f hf).differentiable
      (by norm_num) z).hasGradientAt) γ μ c y0 x).gradient

lemma objective_strong_support (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {γ μ : ℝ} (hγ : 0 ≤ γ) (c y0 x y : E) :
    μ * ‖y - x‖ ^ 2 / 2 ≤
      objective (fun i z => f i z + penalty γ μ c y0 z) y -
        objective (fun i z => f i z + penalty γ μ c y0 z) x -
          ⟪gradient (objective (fun i z => f i z + penalty γ μ c y0 z)) x, y - x⟫ := by
  rw [objective_gradient f hf, objective_penalty, objective_penalty, inner_add_left]
  have hb := FiniteSumThirdSmoothGeometry.bregman_nonneg f hf hc y x
  have hp := QuarticProximalGeometry.penalty_support (μ := μ) hγ c y0 x y
  have hq : 0 ≤ γ * ‖y - x‖ ^ 4 / 12 := by positivity
  linarith

lemma regularized_restart_contraction (f : Fin n → E → ℝ)
    (hf : ∀ i, ContDiff ℝ 3 (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    {L γ μ ρ η : ℝ} (hL : 0 ≤ L) (hγ : 0 < γ) (hμ : 0 < μ) (hρ : 0 ≤ ρ) (hη : 0 < η)
    (hstep : 32 * η * (L + 6 * γ) * ρ ^ 2 ≤ 1)
    (hT : ∀ i x y, ‖fderiv ℝ (fderiv ℝ (gradient (f i))) x -
      fderiv ℝ (fderiv ℝ (gradient (f i))) y‖ ≤ L * ‖x - y‖)
    (c y0 y u : E) (hy : y ∈ Metric.closedBall y0 ρ) (hu : u ∈ Metric.closedBall y0 ρ)
    (hmin : IsMinOn (objective (fun i z => f i z + penalty γ μ c y0 z)) (Metric.closedBall y0 ρ) u)
    (m : ℕ) :
    let F := objective (fun i z => f i z + penalty γ μ c y0 z)
    let Φ := fun v => ‖v - u‖ ^ 2 / 2 + (n : ℝ) *
      (η * (F u - F v - ⟪gradient F v, u - v⟫))
    let answer := fun q : Fin n × E => (gradient (f q.1) q.2, fderiv ℝ (gradient (f q.1)) q.2)
    (𝔼 seeds : Fin m → LongTails.Algorithms.TaylorCorrectedNewton.EpochSeed n,
      𝔼 selection : Fin (n * m),
        Φ (OracleTemplate.QueryPlan.eval answer
          (LongTails.Algorithms.TaylorCorrectedNewton.augmentPlan (augment γ μ c y0)
            (LongTails.Algorithms.TaylorCorrectedNewton.restart η ρ y0 y m seeds selection)))) ≤
      ((n : ℝ) + 1 / (η * μ)) / (n * m : ℕ) * Φ y := by
  have hh := TaylorCorrectedConvergence.restart_contraction
    (fun i z => f i z + penalty γ μ c y0 z)
    (component_contDiff f hf γ μ c y0) (component_convex f hf hc hγ.le hμ.le c y0)
    (show 0 < L + 6 * γ by positivity) hρ hη hμ hstep
    (fun i x y => component_third_lipschitz f hf hγ.le hT c y0 x y i)
    y0 y u hy hu hmin (fun v _ => objective_strong_support f hf hc hγ.le c y0 v u) m
  dsimp only at hh ⊢
  simpa only [TaylorCorrectedStep.eval_augmentPlan, augment_answer f hf] using hh

end LongTails.Proofs.QuarticFiniteSum
