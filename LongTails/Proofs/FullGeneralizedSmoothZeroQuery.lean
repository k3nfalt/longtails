import LongTails.Setups.GeneralizedSmoothConvexFull
import LongTails.Proofs.SmoothConvexMollification
import LongTails.Proofs.SmoothConvexFiniteLowerBound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory OracleTemplate Set
open scoped RealInnerProductSpace

namespace LongTails.Proofs.FullGeneralizedSmoothZeroQuery

open LongTails.Setups.GeneralizedSmoothConvexFull

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def quadratic (L : ℝ) (z x : E) : ℝ := L / 2 * ‖x - z‖ ^ 2
noncomputable def field (L : ℝ) (z x : E) : E := L • (x - z)

lemma quadratic_gradient (L : ℝ) (z x : E) : HasGradientAt (quadratic L z) (field L z x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := ((hasFDerivAt_id x).sub_const z).norm_sq.const_mul (L / 2)
  convert h using 1
  · funext v
    simp only [quadratic, id_eq]
  · ext v
    simp [field, InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
    ring

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma quadratic_nonneg (L : ℝ) (hL : 0 ≤ L) (z x : E) : 0 ≤ quadratic L z x := by
  unfold quadratic
  positivity

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma quadratic_zero (L : ℝ) (z : E) : quadratic L z z = 0 := by simp [quadratic]

omit [CompleteSpace E] in
lemma quadratic_convex (L : ℝ) (hL : 0 ≤ L) (z : E) : ConvexOn ℝ univ (quadratic L z) := by
  unfold quadratic
  apply SmoothConvexFiniteLowerBound.convex_translate z (fun y : E => L / 2 * ‖y‖ ^ 2)
  exact ((convexOn_norm (E := E) convex_univ).pow (fun x _ => norm_nonneg x) 2).smul
    (by positivity : 0 ≤ L / 2)

omit [CompleteSpace E] in
lemma field_lipschitz (L : ℝ) (hL : 0 ≤ L) (z x y : E) :
    ‖field L z x - field L z y‖ ≤ L * ‖x - y‖ := by
  simp only [field, ← smul_sub, sub_sub_sub_cancel_right, norm_smul,
    Real.norm_of_nonneg hL, le_refl]

omit [CompleteSpace E] in
lemma quadratic_pair (L : ℝ) (hL : 0 ≤ L) (u x : E) :
    L * ‖u‖ ^ 2 ≤ quadratic L u x + quadratic L (-u) x := by
  have h := norm_add_sq_real x u
  have h' := norm_sub_sq_real x u
  unfold quadratic
  rw [sub_neg_eq_add, h, h']
  nlinarith [mul_nonneg hL (sq_nonneg ‖x‖)]

lemma admissible (p : Params) (hp : spec.valid p) (u : EuclideanSpace ℝ (Fin p.d)) (hu : ‖u‖ ≤ p.R) :
    spec.admissible p (fun x : EuclideanSpace ℝ (Fin p.d) => quadratic p.L0 u (x - p.x0))
      (SmoothConvexFiniteLowerBound.oracle p.x0 (field p.L0 u)) := by
  rcases hp with ⟨h0, h1, hR, hε, hεu, hd⟩
  refine ⟨SmoothConvexFiniteLowerBound.convex_translate p.x0 _ (quadratic_convex p.L0 h0.le u),
    ?_, ?_, ?_, p.x0 + u, ?_, ?_⟩
  · intro history seed x
    exact SmoothConvexFiniteLowerBound.gradient_translate p.x0 _ _ (quadratic_gradient p.L0 u) x
  · intro history seed
    exact (differentiable_id.sub_const p.x0 |>.sub_const u).const_smul p.L0
  · intro history seed x
    have hf : Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin p.d) => field p.L0 u (x - p.x0)) :=
      (differentiable_id.sub_const p.x0 |>.sub_const u).const_smul p.L0
    have hb := GeneralizedSmoothMollification.derivative_bound_of_quadratic_increment
      (fun x : EuclideanSpace ℝ (Fin p.d) => field p.L0 u (x - p.x0)) x _ p.L0 0
      (hf x).hasFDerivAt h0.le (by norm_num) (fun y => by
        simpa only [zero_mul, add_zero, sub_sub_sub_cancel_right] using
          field_lipschitz p.L0 h0.le u (y - p.x0) (x - p.x0))
    exact hb.trans (le_add_of_nonneg_right (mul_nonneg h1 (norm_nonneg _)))
  · intro x _
    change quadratic p.L0 u (p.x0 + u - p.x0) ≤ quadratic p.L0 u (x - p.x0)
    simp only [add_sub_cancel_left, quadratic_zero]
    exact quadratic_nonneg p.L0 h0.le u (x - p.x0)
  · simpa only [sub_add_cancel_left, norm_neg] using hu

lemma zero_success (p : Params) (hp : spec.valid p) (u : EuclideanSpace ℝ (Fin p.d))
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)))
    (h : spec.successful p (fun x : EuclideanSpace ℝ (Fin p.d) => quadratic p.L0 u (x - p.x0))
      (fun w : A.Seed × (ℕ → Unit) => execute
        (SmoothConvexFiniteLowerBound.oracle p.x0 (field p.L0 u)) A (fun _ => 0) w.1 w.2)
      ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩) :
    Integrable (fun w : A.Seed × (ℕ → Unit) => quadratic p.L0 u (A.output (A.initial w.1) - p.x0))
      ((A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ()))) ∧
    (∫ w : A.Seed × (ℕ → Unit), quadratic p.L0 u (A.output (A.initial w.1) - p.x0)
      ∂((A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())))) ≤ p.ε := by
  obtain ⟨z, hm, hi, he⟩ := h
  change EuclideanSpace ℝ (Fin p.d) at z
  have hz : quadratic p.L0 u (z - p.x0) = 0 := by
    apply le_antisymm
    · have hh := hm (mem_univ (p.x0 + u))
      change quadratic p.L0 u (z - p.x0) ≤ quadratic p.L0 u (p.x0 + u - p.x0) at hh
      simpa only [add_sub_cancel_left, quadratic_zero] using hh
    · exact quadratic_nonneg p.L0 hp.1.le u _
  simp only [hz, sub_zero, SmoothConvexFiniteLowerBound.execute_translated,
    Function.iterate_zero, id_eq] at hi he
  exact ⟨hi, he⟩

lemma exists_failure (p : Params) (hp : spec.valid p) (hd : 0 < p.d)
    (A : Algorithm (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))) :
    ∃ (f : EuclideanSpace ℝ (Fin p.d) → ℝ)
      (O : Oracle (EuclideanSpace ℝ (Fin p.d)) (EuclideanSpace ℝ (Fin p.d))),
      spec.admissible p f O ∧
        ¬ spec.successful p f
          (fun w : A.Seed × ((k : ℕ) → O.Seed k) => execute O A (fun _ => 0) w.1 w.2)
          ⟨(A.law : Measure _).prod (O.law : Measure _), inferInstance⟩ := by
  classical
  by_contra h
  push Not at h
  let u : EuclideanSpace ℝ (Fin p.d) := PiLp.single 2 ⟨0, hd⟩ p.R
  have hu : ‖u‖ = p.R := by
    simp only [u, PiLp.norm_single, Real.norm_of_nonneg hp.2.2.1.le]
  have hp' := h _ _ (admissible p hp u hu.le)
  have hm' := h _ _ (admissible p hp (-u) (by simpa only [norm_neg] using hu.le))
  obtain ⟨hip, hep⟩ := zero_success p hp u A hp'
  obtain ⟨him, hem⟩ := zero_success p hp (-u) A hm'
  let P : ProbabilityMeasure (A.Seed × (ℕ → Unit)) :=
    ⟨(A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())), inferInstance⟩
  have hpair (w : A.Seed × (ℕ → Unit)) : p.L0 * p.R ^ 2 ≤
      quadratic p.L0 u (A.output (A.initial w.1) - p.x0) +
      quadratic p.L0 (-u) (A.output (A.initial w.1) - p.x0) := by
    simpa only [hu] using quadratic_pair p.L0 hp.1.le u (A.output (A.initial w.1) - p.x0)
  have hh := integral_mono (μ := (P : Measure _)) (integrable_const (p.L0 * p.R ^ 2))
    (hip.add him) hpair
  have hipP : Integrable (fun w : A.Seed × (ℕ → Unit) => quadratic p.L0 u (A.output (A.initial w.1) - p.x0))
      (P : Measure (A.Seed × (ℕ → Unit))) := hip
  have himP : Integrable (fun w : A.Seed × (ℕ → Unit) => quadratic p.L0 (-u) (A.output (A.initial w.1) - p.x0))
      (P : Measure (A.Seed × (ℕ → Unit))) := him
  rw [integral_add hipP himP] at hh
  simp only [integral_const, probReal_univ, one_smul] at hh
  have hε := hp.2.2.2.1
  have huε := hp.2.2.2.2.1
  change _ ≤ (∫ w : A.Seed × (ℕ → Unit), quadratic p.L0 u (A.output (A.initial w.1) - p.x0)
    ∂((A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())))) +
    (∫ w : A.Seed × (ℕ → Unit), quadratic p.L0 (-u) (A.output (A.initial w.1) - p.x0)
    ∂((A.law : Measure _).prod (Measure.dirac (fun _ : ℕ => ())))) at hh
  linarith

end LongTails.Proofs.FullGeneralizedSmoothZeroQuery
