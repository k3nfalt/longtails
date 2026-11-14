import LongTails.Proofs.StochasticMfcqTuning
import LongTails.Proofs.FiniteHullDirection
import LongTails.Proofs.ActiveDirectionCertificates
import LongTails.Proofs.ProxLinearEnvelope

open scoped RealInnerProductSpace

namespace LongTails.Proofs.StochasticMfcqGeometry

open LongTails.Setups.StochasticMfcqInequalities
open LongTails.Algorithms.StochasticMfcqDirection

lemma coefficients_simplex (p : Params) (hp : spec.valid p) (v : Primitive p) :
    (∀ i, 0 ≤ coefficients p v i) ∧ ∑ i, coefficients p v i = 1 := by
  exact FiniteHullDirection.secondPhase_simplex (vectors p v) (hullSteps p)
    (StochasticMfcqTuning.hullSteps_sufficient p hp).1 _

lemma vectors_bound (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (hx : feasible p I x) (v : Primitive p)
    (hg : ‖v.1 - gradient I.f x‖ ≤ precision p)
    (hJ : ∀ i, ‖v.2.2 i - I.J x i‖ ≤ precision p) :
    ∀ i, ‖vectors p v i‖ ≤ p.H + 1 := by
  have hd := (StochasticMfcqTuning.precision_bounds p hp).2.1
  have hgb : ‖v.1‖ ≤ p.H + 1 := by
    have ht := norm_le_norm_sub_add v.1 (gradient I.f x)
    linarith [H.gradientBound x hx]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [vectors] using hgb
  · classical
    simp only [vectors, Fin.cases_succ]
    split_ifs
    · have ht := norm_le_norm_sub_add (v.2.2 j) (I.J x j)
      linarith [hJ j, H.jacobianBound x hx j]
    · exact hgb

lemma residual_projection (p : Params) (hp : spec.valid p) (v : Primitive p)
    (hv : ∀ i, ‖vectors p v i‖ ≤ p.H + 1) (i : Fin (p.m + 1)) :
    ‖residual p v‖ ^ 2 - precision p ^ 2 ≤ ⟪vectors p v i, residual p v⟫ := by
  apply FiniteHullDirection.projection_of_gap
  exact (FiniteHullDirection.weights_gap_bound (vectors p v) (p.H + 1) (hullSteps p)
    (StochasticMfcqTuning.hullSteps_sufficient p hp).1 hv).trans
      (StochasticMfcqTuning.hullSteps_sufficient p hp).2

lemma direction_norm_le (p : Params) (v : Primitive p) : ‖direction p v‖ ≤ 1 := by
  by_cases hv : residual p v = 0
  · simp [direction, hv]
  · simp [direction, norm_smul, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

lemma objective_direction (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (hx : feasible p I x) (v : Primitive p)
    (hg : ‖v.1 - gradient I.f x‖ ≤ precision p)
    (hJ : ∀ i, ‖v.2.2 i - I.J x i‖ ≤ precision p)
    (hr : 4 * precision p ≤ ‖residual p v‖) :
    ⟪gradient I.f x, direction p v⟫ ≤ -(5 / 2 : ℝ) * precision p := by
  have hproj := residual_projection p hp v (vectors_bound p I hp H x hx v hg hJ) 0
  simp only [vectors, Fin.cases_zero] at hproj
  exact ActiveDirectionCertificates.approximate_direction_descent _ _ _ _
    (StochasticMfcqTuning.precision_bounds p hp).1 (by simpa [norm_sub_rev] using hg) hr hproj

lemma active_direction (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (hx : feasible p I x) (v : Primitive p)
    (hg : ‖v.1 - gradient I.f x‖ ≤ precision p)
    (hJ : ∀ i, ‖v.2.2 i - I.J x i‖ ≤ precision p)
    (hr : 4 * precision p ≤ ‖residual p v‖) (i : Fin p.m) (hi : active p v i) :
    ⟪I.J x i, direction p v⟫ ≤ -(5 / 2 : ℝ) * precision p := by
  have hproj := residual_projection p hp v (vectors_bound p I hp H x hx v hg hJ) i.succ
  simp only [vectors, Fin.cases_succ, ite_eq_left hi] at hproj
  exact ActiveDirectionCertificates.approximate_direction_descent _ _ _ _
    (StochasticMfcqTuning.precision_bounds p hp).1 (by simpa [norm_sub_rev] using hJ i) hr hproj

lemma objective_model (p : Params) (I : Problem p) (H : Regularity p I) (x y : p.E) :
    I.f y ≤ I.f x + ⟪gradient I.f x, y - x⟫ + p.H / 2 * ‖y - x‖ ^ 2 := by
  have h := (abs_le.mp (ProxLinearEnvelope.smooth_model_abs_error
    H.hasGradient H.gradientLipschitz x y)).2
  linarith

lemma constraint_model (p : Params) (I : Problem p) (H : Regularity p I)
    (x y : p.E) (i : Fin p.m) :
    I.c y i ≤ I.c x i + ⟪I.J x i, y - x⟫ + p.H / 2 * ‖y - x‖ ^ 2 := by
  have h := (abs_le.mp (ProxLinearEnvelope.smooth_model_abs_error
    (fun u => H.constraintGradient u i) (fun u v => H.jacobianLipschitz u v i) x y)).2
  linarith

lemma step_algebra (p : Params) (hp : spec.valid p) :
    p.H * stepSize p + p.H / 2 * stepSize p ^ 2 ≤ precision p / 2 ∧
      stepSize p * (-(5 / 2 : ℝ) * precision p) + p.H / 2 * stepSize p ^ 2 ≤
        -(precision p ^ 2 / (2 * p.H)) := by
  have hH := hp.2.1
  have hH0 : 0 < p.H := by linarith
  have hd := (StochasticMfcqTuning.precision_bounds p hp).1
  have hd1 := (StochasticMfcqTuning.precision_bounds p hp).2.1
  constructor
  · unfold stepSize
    field_simp
    nlinarith [sq_nonneg (precision p), mul_nonneg hd.le (sub_nonneg.mpr hH)]
  · unfold stepSize
    field_simp
    nlinarith [sq_nonneg (precision p)]

lemma step_model_bound (p : Params) (hp : spec.valid p) (x d g : p.E) (a b : ℝ)
    (hd : ‖d‖ ≤ 1)
    (hm : b ≤ a + ⟪g, x + stepSize p • d - x⟫ +
      p.H / 2 * ‖x + stepSize p • d - x‖ ^ 2) :
    b ≤ a + stepSize p * ⟪g, d⟫ + p.H / 2 * stepSize p ^ 2 := by
  have hη := StochasticMfcqTuning.stepSize_pos p hp
  have hn : ‖stepSize p • d‖ ≤ stepSize p := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    nlinarith
  have hn2 := (sq_le_sq₀ (norm_nonneg _) hη.le).2 hn
  have hH : 0 ≤ p.H / 2 := by linarith [hp.2.1]
  have hc := mul_le_mul_of_nonneg_left hn2 hH
  simp only [add_sub_cancel_left, real_inner_smul_right] at hm
  linarith

lemma objective_decrease (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (hx : feasible p I x) (v : Primitive p)
    (hg : ‖v.1 - gradient I.f x‖ ≤ precision p)
    (hJ : ∀ i, ‖v.2.2 i - I.J x i‖ ≤ precision p)
    (hr : 4 * precision p ≤ ‖residual p v‖) :
    I.f (x + stepSize p • direction p v) ≤ I.f x - precision p ^ 2 / (2 * p.H) := by
  have hm := step_model_bound p hp x (direction p v) (gradient I.f x) _ _
    (direction_norm_le p v) (objective_model p I H x _)
  have hd := mul_le_mul_of_nonneg_left (objective_direction p I hp H x hx v hg hJ hr)
    (StochasticMfcqTuning.stepSize_pos p hp).le
  have ha := (step_algebra p hp).2
  linarith

lemma step_feasible (p : Params) (I : Problem p) (hp : spec.valid p)
    (H : Regularity p I) (x : p.E) (hx : feasible p I x) (v : Primitive p)
    (hg : ‖v.1 - gradient I.f x‖ ≤ precision p)
    (hc : ∀ i, |v.2.1 i - I.c x i| ≤ precision p)
    (hJ : ∀ i, ‖v.2.2 i - I.J x i‖ ≤ precision p)
    (hr : 4 * precision p ≤ ‖residual p v‖) :
    feasible p I (x + stepSize p • direction p v) := by
  intro i
  have hm := step_model_bound p hp x (direction p v) (I.J x i) _ _
    (direction_norm_le p v) (constraint_model p I H x _ i)
  by_cases hi : active p v i
  · have hd := mul_le_mul_of_nonneg_left (active_direction p I hp H x hx v hg hJ hr i hi)
      (StochasticMfcqTuning.stepSize_pos p hp).le
    have ha := (step_algebra p hp).2
    have hn : 0 ≤ precision p ^ 2 / (2 * p.H) := by
      have := hp.2.1
      positivity
    linarith [hx i]
  · have hi' : v.2.1 i < -4 * precision p := lt_of_not_ge hi
    have hvalue := (abs_le.mp (hc i)).1
    have hbound : ⟪I.J x i, direction p v⟫ ≤ p.H := by
      calc
        _ ≤ ‖I.J x i‖ * ‖direction p v‖ := real_inner_le_norm _ _
        _ ≤ ‖I.J x i‖ * 1 :=
          mul_le_mul_of_nonneg_left (direction_norm_le p v) (norm_nonneg _)
        _ ≤ p.H := by simpa using H.jacobianBound x hx i
    have hd := mul_le_mul_of_nonneg_left hbound (StochasticMfcqTuning.stepSize_pos p hp).le
    have ha := (step_algebra p hp).1
    have hδ := (StochasticMfcqTuning.precision_bounds p hp).1
    nlinarith

end LongTails.Proofs.StochasticMfcqGeometry
