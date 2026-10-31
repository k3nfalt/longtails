import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import LongTails.Proofs.SmoothBanachAnchoring
import Mathlib.Tactic

open MeasureTheory

namespace LongTails.Proofs.SmoothBanachNoise

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

lemma centered_second_moment (C : ℝ) (J : E → E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + C * ‖y‖ ^ 2)
    {X : Ω → E} (hX : Measurable X) (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    (hzero : (∫ ω, X ω ∂P) = 0) (y : E) :
    Integrable (fun ω => ‖y + X ω‖ ^ 2) P ∧
    (∫ ω, ‖y + X ω‖ ^ 2 ∂P) ≤ ‖y‖ ^ 2 + C * ∫ ω, ‖X ω‖ ^ 2 ∂P := by
  have hJi : Integrable (fun ω => J y (X ω)) P := (J y).integrable_comp hXi
  have hfirst : Integrable (fun ω => ‖y‖ ^ 2 + 2 * J y (X ω)) P :=
    (integrable_const _).add (hJi.const_mul 2)
  have hu : Integrable (fun ω => ‖y‖ ^ 2 + 2 * J y (X ω) + C * ‖X ω‖ ^ 2) P :=
    hfirst.add (hX2.const_mul C)
  have hi : Integrable (fun ω => ‖y + X ω‖ ^ 2) P := by
    apply hu.mono' ((measurable_const.add hX).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖y + X ω‖)] using
        hsmooth y (X ω))
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, ‖y‖ ^ 2 + 2 * J y (X ω) + C * ‖X ω‖ ^ 2 ∂P :=
      integral_mono hi hu (fun ω => hsmooth y (X ω))
    _ = _ := by
      rw [integral_add hfirst (hX2.const_mul C),
        integral_add (integrable_const _) (hJi.const_mul 2), integral_const_mul,
        (J y).integral_comp_comm hXi, hzero, integral_const_mul]
      simp

lemma picard_second_moment (C : ℝ) (hC : 0 ≤ C) (J : E → E →L[ℝ] ℝ)
    (hsmooth : ∀ x y, ‖x + y‖ ^ 2 ≤ ‖x‖ ^ 2 + 2 * J x y + C * ‖y‖ ^ 2)
    (T : E → E) (hT : ∀ x y, ‖T x - T y‖ ≤ ‖x - y‖)
    (a η σ : ℝ) (hη : 0 ≤ η) (hstep : η * (1 + a) ≤ 1)
    (b x u : E) (hu : (1 + a) • u - T u - b = 0)
    (g : Ω → E) (hg : Measurable g) (hgi : Integrable g P)
    (hg2 : Integrable (fun ω => ‖g ω - T x‖ ^ 2) P)
    (hmean : (∫ ω, g ω ∂P) = T x)
    (hvar : (∫ ω, ‖g ω - T x‖ ^ 2 ∂P) ≤ σ ^ 2) :
    Integrable (fun ω =>
      ‖(1 - η * (1 + a)) • x + η • g ω + η • b - u‖ ^ 2) P ∧
    (∫ ω, ‖(1 - η * (1 + a)) • x + η • g ω + η • b - u‖ ^ 2 ∂P) ≤
      (1 - η * a) ^ 2 * ‖x - u‖ ^ 2 + C * η ^ 2 * σ ^ 2 := by
  let X : Ω → E := fun ω => η • (g ω - T x)
  let y := (1 - η * (1 + a)) • x + η • T x + η • b - u
  have hX : Measurable X := by dsimp [X]; fun_prop
  have hXi : Integrable X P := (hgi.sub (integrable_const _)).smul η
  have hsq (ω : Ω) : ‖X ω‖ ^ 2 = η ^ 2 * ‖g ω - T x‖ ^ 2 := by
    simp only [X, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P := by
    simp_rw [hsq]
    exact hg2.const_mul _
  have hzero : (∫ ω, X ω ∂P) = 0 := by
    dsimp [X]
    rw [integral_smul, integral_sub hgi (integrable_const _), hmean]
    simp
  have hn := centered_second_moment C J hsmooth hX hXi hX2 hzero y
  have he (ω : Ω) :
      (1 - η * (1 + a)) • x + η • g ω + η • b - u = y + X ω := by
    dsimp [y, X]
    module
  simp_rw [he]
  refine ⟨hn.1, hn.2.trans ?_⟩
  have hfix : (1 - η * (1 + a)) • u + η • T u + η • b = u := by
    have hb : (1 + a) • u - T u = b := sub_eq_zero.mp hu
    rw [← hb]
    module
  have hy : ‖y‖ ≤ (1 - η * a) * ‖x - u‖ := by
    simpa only [hfix, y] using
      SmoothBanachAnchoring.damped_picard_contraction T hT a η hη hstep b x u
  have hcoef : 0 ≤ 1 - η * a := by nlinarith
  have hy2 : ‖y‖ ^ 2 ≤ (1 - η * a) ^ 2 * ‖x - u‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hcoef (norm_nonneg _))).mpr hy
  have hv : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ η ^ 2 * σ ^ 2 := by
    simp_rw [hsq]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hvar (sq_nonneg η)
  nlinarith

end LongTails.Proofs.SmoothBanachNoise
