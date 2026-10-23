import LongTails.Proofs.ManySampleConvolutionalPerceptronStability
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

namespace LongTails.Proofs.ManySampleConvolutionalPerceptronDynamics

open LongTails.Proofs.ManySampleConvolutionalPerceptronStability

@[ext] structure State (E : Type*) where
  a : ℝ
  q : ℝ
  t : ℝ
  z : E

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def positive (c σ : ℝ) (x : State E) : State E :=
  ⟨x.a + c * x.q + escapeKick σ (x.a + x.q), x.q + c * x.a, x.t, x.z⟩

noncomputable def negative (c δ : ℝ) (p r : E) (x : State E) : State E :=
  ⟨x.a - c * x.q - δ * ⟪p, x.z⟫, x.q - c * x.a,
    x.t - δ * ⟪r, x.z⟫, x.z - (x.a • p + x.t • r)⟩

lemma residual_step_norm {a t : ℝ} {p r : E} (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1) :
    ‖a • p + t • r‖ ≤ |a| + |t| := by
  calc
    _ ≤ ‖a • p‖ + ‖t • r‖ := norm_add_le _ _
    _ = |a| * ‖p‖ + |t| * ‖r‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ _ := by nlinarith [abs_nonneg a, abs_nonneg t]

lemma negative_projection {c δ κ : ℝ} {p r w : E} {x : State E}
    (hp : ‖p‖ ≤ 1) (hw : ‖w‖ = 1) (hr : κ ≤ -⟪r, w⟫) (ht : 0 ≤ x.t) :
    ⟪x.z, w⟫ + x.t * κ - |x.a| ≤ ⟪(negative c δ p r x).z, w⟫ := by
  have hip : |⟪p, w⟫| ≤ 1 := by
    have h := abs_real_inner_le_norm p w
    rw [hw, mul_one] at h
    exact h.trans hp
  have ha : x.a * ⟪p, w⟫ ≤ |x.a| := by
    calc
      _ ≤ |x.a * ⟪p, w⟫| := le_abs_self _
      _ = |x.a| * |⟪p, w⟫| := abs_mul _ _
      _ ≤ _ := by nlinarith [abs_nonneg x.a]
  change _ ≤ ⟪x.z - (x.a • p + x.t • r), w⟫
  simp only [inner_sub_left, inner_add_left, real_inner_smul_left]
  nlinarith

lemma negative_norm_sq {c δ : ℝ} {p r : E} {x : State E}
    (hδ : 0 < δ) (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    (hwrong : 0 ≤ c * x.a * x.q + δ * (x.a * ⟪p, x.z⟫ + x.t * ⟪r, x.z⟫)) :
    ‖(negative c δ p r x).z‖ ^ 2 ≤
      ‖x.z‖ ^ 2 + 2 * c * x.a * x.q / δ + (|x.a| + |x.t|) ^ 2 := by
  have hstep := residual_step_norm (a := x.a) (t := x.t) hp hr
  have hsq : ‖x.a • p + x.t • r‖ ^ 2 ≤ (|x.a| + |x.t|) ^ 2 := by
    nlinarith [norm_nonneg (x.a • p + x.t • r), abs_nonneg x.a, abs_nonneg x.t]
  have hi : -2 * (x.a * ⟪p, x.z⟫ + x.t * ⟪r, x.z⟫) ≤
      2 * c * x.a * x.q / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  change ‖x.z - (x.a • p + x.t • r)‖ ^ 2 ≤ _
  rw [norm_sub_sq_real]
  simp only [inner_add_right, real_inner_smul_right]
  rw [← real_inner_comm x.z p, ← real_inner_comm x.z r]
  linarith

lemma negative_signal_drift {c δ : ℝ} {p r : E} {x : State E}
    (hδ : 0 ≤ δ) (hr : ‖r‖ ≤ 1) :
    |(negative c δ p r x).t - x.t| ≤ δ * ‖x.z‖ := by
  have hi := abs_real_inner_le_norm r x.z
  have hi' : |⟪r, x.z⟫| ≤ ‖x.z‖ := by nlinarith [norm_nonneg x.z]
  change |x.t - δ * ⟪r, x.z⟫ - x.t| ≤ _
  rw [show x.t - δ * ⟪r, x.z⟫ - x.t = -(δ * ⟪r, x.z⟫) by ring,
    abs_neg, abs_mul, abs_of_nonneg hδ]
  exact mul_le_mul_of_nonneg_left hi' hδ

noncomputable def coordinates (x : State E) : ℝ × ℝ := (x.a + x.q, x.a - x.q)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma positive_coordinates {c σ : ℝ} {x : State E} (hx : x.a * x.q ≤ 0) :
    coordinates (positive c σ x) =
      ((scalarStep c (coordinates x).1 (coordinates x).2).1 + escapeKick σ (x.a + x.q),
       (scalarStep c (coordinates x).1 (coordinates x).2).2 + escapeKick σ (x.a + x.q)) := by
  have h := (switch_criterion x.a x.q).mpr hx
  ext <;> simp [coordinates, positive, scalarStep, h] <;> ring

lemma negative_coordinates {c δ : ℝ} {p r : E} {x : State E} (hx : 0 < x.a * x.q) :
    coordinates (negative c δ p r x) =
      ((scalarStep c (coordinates x).1 (coordinates x).2).1 - δ * ⟪p, x.z⟫,
       (scalarStep c (coordinates x).1 (coordinates x).2).2 - δ * ⟪p, x.z⟫) := by
  have h : ¬|x.a + x.q| ≤ |x.a - x.q| := by
    rw [switch_criterion]
    exact not_le.mpr hx
  ext <;> simp [coordinates, negative, scalarStep, h] <;> ring

lemma negative_forcing {δ : ℝ} {p : E} {x : State E}
    (hδ : 0 ≤ δ) (hp : ‖p‖ ≤ 1) : |-(δ * ⟪p, x.z⟫)| ≤ δ * ‖x.z‖ := by
  have hi := abs_real_inner_le_norm p x.z
  have hi' : |⟪p, x.z⟫| ≤ ‖x.z‖ := by nlinarith [norm_nonneg x.z]
  rw [abs_neg, abs_mul, abs_of_nonneg hδ]
  exact mul_le_mul_of_nonneg_left hi' hδ

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
lemma coordinates_control (x : State E) :
    2 * |x.a| ≤ |(coordinates x).1| + |(coordinates x).2| ∧
    2 * |x.q| ≤ |(coordinates x).1| + |(coordinates x).2| := by
  have ha := abs_add_le (x.a + x.q) (x.a - x.q)
  have hq := abs_add_le (x.a + x.q) (-(x.a - x.q))
  rw [abs_neg] at hq
  rw [show x.a + x.q + (x.a - x.q) = 2 * x.a by ring, abs_mul] at ha
  rw [show x.a + x.q + -(x.a - x.q) = 2 * x.q by ring, abs_mul] at hq
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ha hq
  exact ⟨ha, hq⟩

lemma negative_norm_increment {c δ A T : ℝ} {p r : E} {x : State E}
    (hδ : 0 < δ) (hc : c ≤ 1 / 2) (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    (ha : |x.a| ≤ A) (hq : |x.q| ≤ A) (ht : |x.t| ≤ T)
    (haq : 0 ≤ x.a * x.q)
    (hwrong : 0 ≤ c * x.a * x.q + δ * (x.a * ⟪p, x.z⟫ + x.t * ⟪r, x.z⟫)) :
    ‖(negative c δ p r x).z‖ ^ 2 ≤ ‖x.z‖ ^ 2 + A ^ 2 / δ + (A + T) ^ 2 := by
  have hA : 0 ≤ A := (abs_nonneg _).trans ha
  have hT : 0 ≤ T := (abs_nonneg _).trans ht
  have hprod : x.a * x.q ≤ A ^ 2 := by
    calc
      _ ≤ |x.a * x.q| := le_abs_self _
      _ = |x.a| * |x.q| := abs_mul _ _
      _ ≤ A * A := mul_le_mul ha hq (abs_nonneg _) hA
      _ = A ^ 2 := by ring
  have hnum : 2 * c * x.a * x.q ≤ A ^ 2 := by nlinarith
  have hdiv := div_le_div_of_nonneg_right hnum hδ.le
  have hsq : (|x.a| + |x.t|) ^ 2 ≤ (A + T) ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mpr
    linarith
  have hn := negative_norm_sq hδ hp hr hwrong
  linarith

end LongTails.Proofs.ManySampleConvolutionalPerceptronDynamics
