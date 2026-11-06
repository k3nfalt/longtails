import LongTails.Proofs.SurjectiveProxLinearExactModel
import LongTails.Proofs.ProxLinearEnvelope

open scoped RealInnerProductSpace

namespace LongTails.Proofs.SurjectiveProxLinearGeometry

open LongTails.Setups.StochasticSurjectiveInequalities
open LongTails.Algorithms.SurjectiveProxLinear
open LongTails.Proofs.ProxLinearDualSensitivity
open LongTails.Proofs.SurjectiveProxLinearModel
open LongTails.Proofs.SurjectiveProxLinearExactModel

lemma exact_direction_identity (p : Params) (I : Problem p) (x : p.E) (d : Constraint p) :
    ⟪quadraticGradient (transposeContinuous p (I.J x)) (gradient I.f x)
      (I.c x) (eta p) 0 (exactDualPoint p I x), d⟫ =
      ⟪-linearizedConstraints p I x (exactModelStep p I x), d⟫ := by
  rw [quadraticGradient_direction, inner_neg_left, linearized_pairing]
  simp only [exactModelStep, real_inner_smul_right, transposeContinuous_apply,
    zero_mul, add_zero]
  rw [real_inner_comm (transposeAction p (I.J x) d)]
  ring

lemma exact_support (p : Params) (I : Problem p) (x : p.E) (hρ : 0 ≤ rho p) :
    ⟪linearizedConstraints p I x (exactModelStep p I x), exactDualPoint p I x⟫ =
      rho p * ∑ i, max (linearizedConstraints p I x (exactModelStep p I x) i) 0 := by
  apply box_support_equality p _ hρ (exactDualPoint_spec p I x hρ).1
  intro z hz
  rw [← exact_direction_identity]
  exact exactDualPoint_vi p I x hρ hz

lemma linearModel_subgradient (p : Params) (I : Problem p) (x y : p.E)
    (hρ : 0 ≤ rho p) :
    linearModel p I x (x + exactModelStep p I x) +
      ⟪gradient I.f x + transposeAction p (I.J x) (exactDualPoint p I x),
        y - (x + exactModelStep p I x)⟫ ≤ linearModel p I x y := by
  have hs := exact_support p I x hρ
  have hy := box_pairing_le_hinge p (linearizedConstraints p I x (y - x))
    (exactDualPoint_spec p I x hρ).1
  rw [linearized_pairing] at hs hy
  simp only [linearModel, add_sub_cancel_left]
  change I.f x + ⟪gradient I.f x, exactModelStep p I x⟫ +
    rho p * ∑ i, max (linearizedConstraints p I x (exactModelStep p I x) i) 0 + _ ≤ _
  rw [← hs]
  have hd : y - (x + exactModelStep p I x) = y - x - exactModelStep p I x := by abel
  rw [hd]
  dsimp only [linearizedConstraints] at hy
  simp only [inner_add_left, inner_sub_right] at hy ⊢
  linarith

lemma linearModel_strong_growth (p : Params) (I : Problem p) (hp : spec.valid p)
    (x y : p.E) :
    linearModel p I x (x + exactModelStep p I x) +
      2 * gamma p * ‖exactModelStep p I x‖ ^ 2 +
      2 * gamma p * ‖x + exactModelStep p I x - y‖ ^ 2 ≤
      linearModel p I x y + 2 * gamma p * ‖y - x‖ ^ 2 := by
  have hρ := (valid_tuning_positive p hp).1.le
  have hγ := (valid_tuning_positive p hp).2.1
  have hγ0 : gamma p ≠ 0 := ne_of_gt hγ
  let s := exactModelStep p I x
  let a := gradient I.f x + transposeAction p (I.J x) (exactDualPoint p I x)
  let d := y - (x + s)
  have hs : 4 * gamma p * ⟪s, d⟫ = -⟪a, d⟫ := by
    dsimp [s, a, exactModelStep, eta]
    rw [real_inner_smul_left]
    field_simp
  have hsub := linearModel_subgradient p I x y hρ
  change linearModel p I x (x + s) + ⟪a, d⟫ ≤ linearModel p I x y at hsub
  have hsum : s + d = y - x := by dsimp [d]; abel
  have hn := norm_add_sq_real s d
  rw [hsum] at hn
  have hnγ := congrArg (fun z : ℝ => 2 * gamma p * z) hn
  have hd : ‖x + s - y‖ = ‖d‖ := by dsimp [d]; exact norm_sub_rev _ _
  change linearModel p I x (x + s) + 2 * gamma p * ‖s‖ ^ 2 +
    2 * gamma p * ‖x + s - y‖ ^ 2 ≤ _
  rw [hd]
  nlinarith

lemma constraint_model_error (p : Params) (I : Problem p) (H : Regularity p I)
    (x y : p.E) (i : Fin p.m) :
    |I.c y i - (I.c x i + ⟪I.J x i, y - x⟫)| ≤ p.H / 2 * ‖y - x‖ ^ 2 := by
  have hlip : ∀ u v, ‖I.J u i - I.J v i‖ ≤ p.H * ‖u - v‖ := by
    intro u v
    exact (PiLp.norm_apply_le (I.J u - I.J v) i).trans (H.jacobianLipschitz u v)
  have h := ProxLinearEnvelope.smooth_model_abs_error
    (fun u => H.constraintGradient u i) hlip x y
  simpa only [sub_add_eq_sub_sub] using h

lemma penalty_model_abs_error (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x y : p.E) :
    |penalty p I y - linearModel p I x y| ≤ gamma p / 2 * ‖y - x‖ ^ 2 := by
  have hρ := (valid_tuning_positive p hp).1.le
  have hf := ProxLinearEnvelope.smooth_model_abs_error H.hasGradient H.gradientLipschitz x y
  have hc : ∀ i : Fin p.m,
      |max (I.c y i) 0 - max (I.c x i + ⟪I.J x i, y - x⟫) 0| ≤
        p.H / 2 * ‖y - x‖ ^ 2 := by
    intro i
    exact (abs_max_sub_max_le_abs _ _ _).trans (constraint_model_error p I H x y i)
  have hsum : |∑ i : Fin p.m,
      (max (I.c y i) 0 - max (I.c x i + ⟪I.J x i, y - x⟫) 0)| ≤
      p.m * (p.H / 2 * ‖y - x‖ ^ 2) := by
    calc
      _ ≤ ∑ i : Fin p.m, |max (I.c y i) 0 - max (I.c x i + ⟪I.J x i, y - x⟫) 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin p.m, p.H / 2 * ‖y - x‖ ^ 2 := Finset.sum_le_sum fun i _ => hc i
      _ = _ := by simp
  have heq : penalty p I y - linearModel p I x y =
      (I.f y - I.f x - ⟪gradient I.f x, y - x⟫) +
      rho p * ∑ i : Fin p.m,
        (max (I.c y i) 0 - max (I.c x i + ⟪I.J x i, y - x⟫) 0) := by
    simp only [penalty, linearModel, rho, Finset.sum_sub_distrib]
    ring
  rw [heq]
  have h := abs_add_le (I.f y - I.f x - ⟪gradient I.f x, y - x⟫)
    (rho p * ∑ i : Fin p.m,
      (max (I.c y i) 0 - max (I.c x i + ⟪I.J x i, y - x⟫) 0))
  rw [abs_mul, abs_of_nonneg hρ] at h
  have hh := mul_le_mul_of_nonneg_left hsum hρ
  dsimp [gamma]
  nlinarith [sq_nonneg ‖y - x‖]

noncomputable def hingeMultiplier (p : Params) (I : Problem p) (x : p.E) : Constraint p :=
  WithLp.toLp 2 (fun i => if 0 < I.c x i then rho p else 0)

noncomputable def penaltySubgradient (p : Params) (I : Problem p) (x : p.E) : p.E :=
  gradient I.f x + transposeAction p (I.J x) (hingeMultiplier p I x)

lemma hingeMultiplier_mem (p : Params) (I : Problem p) (x : p.E) (hρ : 0 ≤ rho p) :
    hingeMultiplier p I x ∈ dualBox p := by
  intro i
  change 0 ≤ (if 0 < I.c x i then rho p else 0) ∧
    (if 0 < I.c x i then rho p else 0) ≤ rho p
  split_ifs <;> exact ⟨by positivity, by simp_all⟩

lemma hingeMultiplier_support (p : Params) (I : Problem p) (x : p.E) :
    ⟪I.c x, hingeMultiplier p I x⟫ = rho p * ∑ i, max (I.c x i) 0 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (if 0 < I.c x i then rho p else 0) * I.c x i = rho p * max (I.c x i) 0
  split_ifs with hi
  · rw [max_eq_left hi.le]
  · rw [max_eq_right (le_of_not_gt hi)]
    ring

lemma linearModel_support_at_base (p : Params) (I : Problem p) (x y : p.E)
    (hρ : 0 ≤ rho p) :
    penalty p I x + ⟪penaltySubgradient p I x, y - x⟫ ≤ linearModel p I x y := by
  have h := box_pairing_le_hinge p (linearizedConstraints p I x (y - x))
    (hingeMultiplier_mem p I x hρ)
  rw [linearized_pairing, hingeMultiplier_support] at h
  simp only [penaltySubgradient, inner_add_left, linearModel, penalty]
  change I.f x + rho p * ∑ i, max (I.c x i) 0 +
    (⟪gradient I.f x, y - x⟫ + ⟪transposeAction p (I.J x) (hingeMultiplier p I x), y - x⟫) ≤ _
  change _ ≤ I.f x + ⟪gradient I.f x, y - x⟫ +
    rho p * ∑ i, max (linearizedConstraints p I x (y - x) i) 0
  linarith

lemma penalty_weak_subgradient (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) :
    OracleTemplate.WeaklyConvexHeavyTailed.WeakSubgradientOn Set.univ (gamma p)
      (penalty p I) (penaltySubgradient p I) := by
  intro x _ y _
  have h := linearModel_support_at_base p I x y (valid_tuning_positive p hp).1.le
  have he := (abs_le.mp (penalty_model_abs_error p I hp H x y)).1
  linarith

lemma penaltySubgradient_bound (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) :
    ‖penaltySubgradient p I x‖ ≤ p.H + p.H * (rho p * p.m) := by
  have hρ := (valid_tuning_positive p hp).1.le
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.2.1
  have hℓ := norm_mem_dualBox_le p hp.1 hρ (hingeMultiplier_mem p I x hρ)
  have hT := norm_transposeAction_le p (I.J x) (hingeMultiplier p I x)
  have hbound := mul_le_mul hℓ (H.jacobianBound x) (norm_nonneg _) (by positivity : 0 ≤ rho p * p.m)
  rw [mul_comm (rho p * p.m) p.H] at hbound
  exact (norm_add_le _ _).trans (add_le_add (H.gradientBound x) (hT.trans hbound))

end LongTails.Proofs.SurjectiveProxLinearGeometry
