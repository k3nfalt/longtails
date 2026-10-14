import LongTails.Proofs.HeavyTailedClipping
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.TerminalClipping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma projection_distance {y z u : E} (h : ⟪y - z, u - z⟫ ≤ 0) :
    ‖z - u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
  have he : y - u = (y - z) - (u - z) := by module
  rw [he, norm_sub_sq_real (y - z) (u - z)]
  rw [norm_sub_rev z u]
  nlinarith [sq_nonneg ‖y - z‖]

lemma projection_step {η : ℝ} (hη : 0 ≤ η) {x z c : E}
    (h : ⟪x - η • c - z, x - z⟫ ≤ 0) : ‖z - x‖ ≤ η * ‖c‖ := by
  have he : x - η • c - z = (x - z) - η • c := by module
  rw [he, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
  have hi := real_inner_le_norm c (x - z)
  have hm := mul_le_mul_of_nonneg_left hi hη
  have hn := norm_nonneg (x - z)
  rw [norm_sub_rev z x]
  nlinarith [mul_nonneg hη (norm_nonneg c)]

lemma projected_objective_step {f : E → ℝ} {η M : ℝ} (hη : 0 < η) (hM : 0 ≤ M)
    {x z u h c : E}
    (hproj : ‖z - u‖ ^ 2 ≤ ‖x - η • c - u‖ ^ 2)
    (hstep : ‖z - x‖ ≤ η * ‖c‖)
    (hsub : f x - f u ≤ ⟪h, x - u⟫)
    (hupper : f z - f x ≤ M * ‖z - x‖) :
    η * (f z - f u) ≤ (‖x - u‖ ^ 2 - ‖z - u‖ ^ 2) / 2 +
      η ^ 2 * (M ^ 2 / 2 + ‖c‖ ^ 2) + η * ⟪h - c, x - u⟫ := by
  have heq : x - η • c - u = (x - u) - η • c := by module
  rw [heq, norm_sub_sq_real (x - u) (η • c), real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hη, mul_pow] at hproj
  rw [real_inner_comm c] at hproj
  rw [inner_sub_left]
  have hup : f z - f x ≤ M * (η * ‖c‖) :=
    hupper.trans (mul_le_mul_of_nonneg_left hstep hM)
  have hsum := mul_le_mul_of_nonneg_left (add_le_add hsub hup) hη.le
  nlinarith [sq_nonneg (η * (M - ‖c‖))]

lemma influence_bias_bound {A K : ℝ} (_hA : 0 ≤ A) (hK : 0 < K)
    {b U V q : E} (hV : U = V + q) (hb : ‖b‖ ≤ A + K * ‖U‖) :
    ⟪b, V⟫ ≤ 2 * K * ‖V‖ ^ 2 + A ^ 2 / (2 * K) + K * ‖q‖ ^ 2 / 2 := by
  have hU : ‖U‖ ≤ ‖V‖ + ‖q‖ := by rw [hV]; exact norm_add_le V q
  have hb' : ‖b‖ ≤ A + K * (‖V‖ + ‖q‖) :=
    hb.trans (add_le_add_right (mul_le_mul_of_nonneg_left hU hK.le) A)
  have hi : ⟪b, V⟫ ≤ (A + K * (‖V‖ + ‖q‖)) * ‖V‖ :=
    (real_inner_le_norm b V).trans (mul_le_mul_of_nonneg_right hb' (norm_nonneg V))
  have hden : 0 < 2 * K := by positivity
  have hfrac : A ^ 2 / (2 * K) * (2 * K) = A ^ 2 :=
    div_mul_cancel₀ _ (ne_of_gt hden)
  have hv := mul_le_mul_of_nonneg_left hi hden.le
  have hs := sq_nonneg (A - K * ‖V‖)
  have ht := mul_nonneg (sq_nonneg K) (sq_nonneg (‖q‖ - ‖V‖))
  nlinarith

lemma full_moment_clip_residual {C : ℝ} (hC : 0 < C) (v : E) :
    ‖v - clip C v‖ ≤ ‖v‖ ^ 2 / C := by
  rw [clip_residual_norm hC.le, max_le_iff]
  constructor
  · positivity
  · apply (le_div_iff₀ hC).mpr
    nlinarith [sq_nonneg (‖v‖ - C), mul_nonneg (norm_nonneg v) hC.le]

variable {Ω : Type*} [MeasurableSpace Ω] [CompleteSpace E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {P : Measure Ω} [IsProbabilityMeasure P]

omit [CompleteSpace E] in
lemma full_moment_clip_bias {g : Ω → E} (hg : Measurable g)
    (hgi : Integrable g P) (hmi : Integrable (fun ω => ‖g ω‖ ^ 2) P)
    {C M : ℝ} (hC : 0 < C) (hm : (∫ ω, ‖g ω‖ ^ 2 ∂P) ≤ M) :
    ‖(∫ ω, g ω ∂P) - (∫ ω, clip C (g ω) ∂P)‖ ≤ M / C := by
  have hi := integrable_clip (P := P) hg hC.le
  have hb := norm_integral_le_of_norm_le (hmi.div_const C)
    (f := fun ω => g ω - clip C (g ω))
    (Filter.Eventually.of_forall (fun ω => full_moment_clip_residual hC (g ω)))
  rw [integral_sub hgi hi, integral_div] at hb
  exact hb.trans (div_le_div_of_nonneg_right hm hC.le)

omit [CompleteSpace E] [SecondCountableTopology E] [IsProbabilityMeasure P] in
lemma full_moment_clip_second {g : Ω → E} (hg : Measurable g)
    (hmi : Integrable (fun ω => ‖g ω‖ ^ 2) P) {C : ℝ} (hC : 0 ≤ C) :
    Integrable (fun ω => ‖clip C (g ω)‖ ^ 2) P ∧
    (∫ ω, ‖clip C (g ω)‖ ^ 2 ∂P) ≤ ∫ ω, ‖g ω‖ ^ 2 ∂P := by
  have hp (ω : Ω) : ‖clip C (g ω)‖ ^ 2 ≤ ‖g ω‖ ^ 2 := by
    have h := norm_clip_sub_le hC (u := (0 : E)) (by simpa using hC) (g ω)
    simp only [sub_zero] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  have hi : Integrable (fun ω => ‖clip C (g ω)‖ ^ 2) P := by
    apply hmi.mono' (((measurable_clip C).comp hg).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      change |‖clip C (g ω)‖ ^ 2| ≤ ‖g ω‖ ^ 2
      rw [abs_of_nonneg (sq_nonneg _)]
      exact hp ω)
  exact ⟨hi, integral_mono hi hmi hp⟩

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma centered_second_identity {X : Ω → E} (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) :
    Integrable (fun ω => ‖X ω - ∫ u, X u ∂P‖ ^ 2) P ∧
      (∫ ω, ‖X ω - ∫ u, X u ∂P‖ ^ 2 ∂P) =
        (∫ ω, ‖X ω‖ ^ 2 ∂P) - ‖∫ u, X u ∂P‖ ^ 2 := by
  let m := ∫ u, X u ∂P
  have hi : Integrable (fun ω => ⟪m, X ω⟫) P := hXi.const_inner m
  have he : (fun ω => ‖X ω - m‖ ^ 2) =
      fun ω => (‖X ω‖ ^ 2 - 2 * ⟪m, X ω⟫) + ‖m‖ ^ 2 := by
    funext ω
    rw [norm_sub_sq_real, real_inner_comm m]
  have hs : Integrable (fun ω => ‖X ω‖ ^ 2 - 2 * ⟪m, X ω⟫) P :=
    hX2.sub (hi.const_mul 2)
  change Integrable (fun ω => ‖X ω - m‖ ^ 2) P ∧ _
  rw [he]
  refine ⟨hs.add (integrable_const _), ?_⟩
  rw [integral_add hs (integrable_const _), integral_sub hX2 (hi.const_mul 2),
    integral_const_mul, integral_inner hXi m]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  change (∫ ω, ‖X ω‖ ^ 2 ∂P) - 2 * ⟪m, m⟫ + ‖m‖ ^ 2 =
    (∫ ω, ‖X ω‖ ^ 2 ∂P) - ‖m‖ ^ 2
  rw [real_inner_self_eq_norm_sq]
  ring

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma centered_second_moment {X : Ω → E} (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) :
    Integrable (fun ω => ‖X ω - ∫ u, X u ∂P‖ ^ 2) P ∧
      (∫ ω, ‖X ω - ∫ u, X u ∂P‖ ^ 2 ∂P) ≤ ∫ ω, ‖X ω‖ ^ 2 ∂P := by
  have h := centered_second_identity hXi hX2
  refine ⟨h.1, ?_⟩
  rw [h.2]
  exact sub_le_self _ (sq_nonneg _)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma mean_norm_bound {X : Ω → E} (hXi : Integrable X P)
    (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P) {M : ℝ} (hM : 0 ≤ M)
    (hbound : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ M ^ 2) : ‖∫ ω, X ω ∂P‖ ≤ M := by
  have h := (centered_second_identity hXi hX2).2
  have hn : 0 ≤ ∫ ω, ‖X ω - ∫ u, X u ∂P‖ ^ 2 ∂P :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hs : ‖∫ ω, X ω ∂P‖ ^ 2 ≤ M ^ 2 := by linarith
  exact (sq_le_sq₀ (norm_nonneg _) hM).mp hs

omit [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma objective_difference_from_moment {f : E → ℝ} {x y : E} {X : Ω → E}
    (hXi : Integrable X P) (hX2 : Integrable (fun ω => ‖X ω‖ ^ 2) P)
    {M : ℝ} (hM : 0 ≤ M) (hmoment : (∫ ω, ‖X ω‖ ^ 2 ∂P) ≤ M ^ 2)
    (hsub : f y - f x ≤ ⟪∫ ω, X ω ∂P, y - x⟫) :
    f y - f x ≤ M * ‖y - x‖ :=
  hsub.trans ((real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (mean_norm_bound hXi hX2 hM hmoment) (norm_nonneg _)))

omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma radius_geometry {D R : ℝ} (hD : 0 ≤ D) (hR : 0 ≤ R) (hRD : R ^ 2 ≤ D)
    {x xstar x0 : E} (hstart : ‖x0 - xstar‖ ≤ R)
    (hx : ‖x - xstar‖ ^ 2 ≤ 16 * D) : ‖x - x0‖ ≤ 5 * Real.sqrt D := by
  have hs := Real.sq_sqrt hD
  have hr : R ≤ Real.sqrt D := by nlinarith [Real.sqrt_nonneg D]
  have hd : ‖x - xstar‖ ≤ 4 * Real.sqrt D := by
    nlinarith [norm_nonneg (x - xstar), Real.sqrt_nonneg D]
  have ht := norm_add_le (x - xstar) (xstar - x0)
  rw [show (x - xstar) + (xstar - x0) = x - x0 by module, norm_sub_rev xstar x0] at ht
  linarith

end OracleTemplate.TerminalClipping
