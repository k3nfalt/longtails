import LongTails.Proofs.ScentScalar
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod


namespace OracleTemplate.Scent

open MeasureTheory Real
open scoped RealInnerProductSpace

section Anchor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {Ξ : Type*} [MeasurableSpace Ξ]

structure AnchorHyp (μ : Measure Ξ) (s : E → Ξ → ℝ) (g : E → Ξ → E) (W : Set E)
    (c0 c1 G κ σ : ℝ) : Prop where
  meas_s : Measurable (Function.uncurry s)
  meas_g : Measurable (Function.uncurry g)
  subgrad : ∀ ξ, ∀ x ∈ W, ∀ y ∈ W, s x ξ + ⟪g x ξ, y - x⟫ ≤ s y ξ
  bound : ∀ ξ, ∀ x ∈ W, c0 ≤ s x ξ ∧ s x ξ ≤ c1
  grad_int : ∀ x ∈ W, Integrable (fun ξ => ‖g x ξ‖ ^ 2) μ
  grad_sq : ∀ x ∈ W, (∫ ξ, ‖g x ξ‖ ^ 2 ∂μ) ≤ G ^ 2
  kappa : ∀ x ∈ W, (∫ ξ, exp (2 * s x ξ) ∂μ) ≤ κ * (∫ ξ, exp (s x ξ) ∂μ) ^ 2
  sigma : ∀ x ∈ W, (∫ ξ, exp (2 * s x ξ) * ‖g x ξ‖ ^ 2 ∂μ) ≤ σ ^ 2 * (∫ ξ, exp (s x ξ) ∂μ) ^ 2

variable {μ : Measure Ξ} [IsProbabilityMeasure μ] {s : E → Ξ → ℝ} {g : E → Ξ → E} {W : Set E}
  {c0 c1 G κ σ : ℝ}

noncomputable def mass (μ : Measure Ξ) (s : E → Ξ → ℝ) (x : E) : ℝ := ∫ ξ, exp (s x ξ) ∂μ

noncomputable def dualObj (μ : Measure Ξ) (s : E → Ξ → ℝ) (x : E) (ν : ℝ) : ℝ :=
  mass μ s x * exp (-ν) + ν

noncomputable def gradW (μ : Measure Ξ) (s : E → Ξ → ℝ) (g : E → Ξ → E) (x : E) (ν : ℝ) : E :=
  ∫ ξ, exp (s x ξ - ν) • g x ξ ∂μ

noncomputable def anchorGap (μ : Measure Ξ) (s : E → Ξ → ℝ) (x : E) (ν : ℝ) : ℝ :=
  psi (log (mass μ s x) - ν)

namespace AnchorHyp

variable (h : AnchorHyp μ s g W c0 c1 G κ σ)
include h

omit [IsProbabilityMeasure μ] in
lemma meas_s_x (x : E) : Measurable (s x) :=
  h.meas_s.comp (measurable_const.prodMk measurable_id)

omit [IsProbabilityMeasure μ] in
lemma meas_g_x (x : E) : Measurable (g x) :=
  h.meas_g.comp (measurable_const.prodMk measurable_id)

lemma exp_s_int {x : E} (hx : x ∈ W) : Integrable (fun ξ => exp (s x ξ)) μ := by
  refine Integrable.of_bound ((measurable_exp.comp (h.meas_s_x x)).aestronglyMeasurable) (exp c1) ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]; exact exp_le_exp.mpr (h.bound ξ x hx).2

lemma exp2_s_int {x : E} (hx : x ∈ W) : Integrable (fun ξ => exp (2 * s x ξ)) μ := by
  refine Integrable.of_bound ((measurable_exp.comp ((h.meas_s_x x).const_mul 2)).aestronglyMeasurable)
    (exp (2 * c1)) ?_
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr (by linarith [(h.bound ξ x hx).2])

lemma mass_bounds {x : E} (hx : x ∈ W) : exp c0 ≤ mass μ s x ∧ mass μ s x ≤ exp c1 := by
  unfold mass
  constructor
  · have := integral_mono (integrable_const (exp c0)) (h.exp_s_int hx)
      (fun ξ => exp_le_exp.mpr (h.bound ξ x hx).1)
    simpa using this
  · have := integral_mono (h.exp_s_int hx) (integrable_const (exp c1))
      (fun ξ => exp_le_exp.mpr (h.bound ξ x hx).2)
    simpa using this

lemma mass_pos {x : E} (hx : x ∈ W) : 0 < mass μ s x :=
  lt_of_lt_of_le (exp_pos c0) (h.mass_bounds hx).1

lemma log_mass_mem {x : E} (hx : x ∈ W) : log (mass μ s x) ∈ Set.Icc c0 c1 := by
  obtain ⟨h1, h2⟩ := h.mass_bounds hx
  constructor
  · rw [← log_exp c0]; exact log_le_log (exp_pos c0) h1
  · rw [← log_exp c1]; exact log_le_log (h.mass_pos hx) h2

lemma grad_int1 [BorelSpace E] [SecondCountableTopology E] {x : E} (hx : x ∈ W) : Integrable (g x) μ := by
  have hm : AEStronglyMeasurable (g x) μ := (h.meas_g_x x).aestronglyMeasurable
  exact ((memLp_two_iff_integrable_sq_norm hm).2 (h.grad_int x hx)).integrable one_le_two

lemma weighted_grad_int [BorelSpace E] [SecondCountableTopology E] {x : E} (hx : x ∈ W) (ν : ℝ) :
    Integrable (fun ξ => exp (s x ξ - ν) • g x ξ) μ := by
  refine Integrable.mono' ((h.grad_int1 hx).norm.const_mul (exp (c1 - ν))) ?_ ?_
  · exact ((measurable_exp.comp ((h.meas_s_x x).sub measurable_const)).smul (h.meas_g_x x)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith [(h.bound ξ x hx).2])) (norm_nonneg _)

omit [IsProbabilityMeasure μ] in
lemma weighted_grad_sq_int [BorelSpace E] [SecondCountableTopology E] {x : E} (hx : x ∈ W) (ν : ℝ) :
    Integrable (fun ξ => ‖exp (s x ξ - ν) • g x ξ‖ ^ 2) μ := by
  refine Integrable.mono' ((h.grad_int x hx).const_mul (exp (c1 - ν) ^ 2)) ?_ ?_
  · exact (((measurable_exp.comp ((h.meas_s_x x).sub measurable_const)).smul (h.meas_g_x x)).norm.pow_const 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_smul, Real.norm_eq_abs,
        abs_of_pos (exp_pos _), mul_pow]
      have := exp_le_exp.mpr (show s x ξ - ν ≤ c1 - ν by linarith [(h.bound ξ x hx).2])
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (exp_pos _).le this 2) (sq_nonneg _)

omit [IsProbabilityMeasure μ] in
lemma exp2_grad_sq_int [BorelSpace E] {x : E} (hx : x ∈ W) :
    Integrable (fun ξ => exp (2 * s x ξ) * ‖g x ξ‖ ^ 2) μ := by
  refine Integrable.mono' ((h.grad_int x hx).const_mul (exp (2 * c1))) ?_ ?_
  · exact ((measurable_exp.comp ((h.meas_s_x x).const_mul 2)).mul ((h.meas_g_x x).norm.pow_const 2)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exp_pos _).le (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr (by linarith [(h.bound ξ x hx).2])) (sq_nonneg _)

omit [IsProbabilityMeasure μ] h [MeasurableSpace E] in
lemma gradW_eq (x : E) (ν : ℝ) :
    gradW μ s g x ν = exp (-ν) • ∫ ξ, exp (s x ξ) • g x ξ ∂μ := by
  unfold gradW
  rw [← integral_smul]
  congr 1
  funext ξ
  rw [smul_smul, ← exp_add]
  ring_nf


lemma dual_shift {x : E} (hx : x ∈ W) (ν : ℝ) :
    mass μ s x * exp (-ν) = exp (log (mass μ s x) - ν) := by
  rw [exp_sub, exp_log (h.mass_pos hx), exp_neg, div_eq_mul_inv]

lemma gap_eq {x : E} (hx : x ∈ W) (ν : ℝ) :
    dualObj μ s x ν - dualObj μ s x (log (mass μ s x)) = anchorGap μ s x ν := by
  have hm : mass μ s x * exp (-(log (mass μ s x))) = 1 := by
    rw [exp_neg, exp_log (h.mass_pos hx), mul_inv_cancel₀ (h.mass_pos hx).ne']
  unfold dualObj anchorGap psi
  rw [h.dual_shift hx ν, hm]
  ring

omit [IsProbabilityMeasure μ] h [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] in
lemma gap_nonneg (x : E) (ν : ℝ) : 0 ≤ anchorGap μ s x ν := psi_nonneg _

lemma mass_exp_neg_le_gap {x : E} (hx : x ∈ W) (ν : ℝ) :
    mass μ s x * exp (-ν) ≤ 2 * (1 + anchorGap μ s x ν) := by
  rw [h.dual_shift hx ν]; exact exp_le_two_mul_one_add_psi _

lemma log_mass_sub_le {x : E} (hx : x ∈ W) {ν : ℝ} (hν : c0 ≤ ν) :
    log (mass μ s x) - ν ≤ c1 - c0 := by
  have := (h.log_mass_mem hx).2; linarith

lemma mass_exp_neg_le_exp {x : E} (hx : x ∈ W) {ν : ℝ} (hν : c0 ≤ ν) :
    mass μ s x * exp (-ν) ≤ exp (c1 - c0) := by
  rw [h.dual_shift hx ν]; exact exp_le_exp.mpr (h.log_mass_sub_le hx hν)

lemma variance_le {x : E} (hx : x ∈ W) :
    (∫ ξ, (exp (s x ξ) - mass μ s x) ^ 2 ∂μ) ≤ (κ - 1) * mass μ s x ^ 2 := by
  have hz := h.exp_s_int hx
  have hz2 := h.exp2_s_int hx
  have hexp2 : ∀ ξ, exp (2 * s x ξ) = exp (s x ξ) ^ 2 := fun ξ => by
    rw [sq, ← exp_add]; ring_nf
  have heq : (∫ ξ, (exp (s x ξ) - mass μ s x) ^ 2 ∂μ) =
      (∫ ξ, exp (2 * s x ξ) ∂μ) - mass μ s x ^ 2 := by
    have h1 : (fun ξ => (exp (s x ξ) - mass μ s x) ^ 2) =
        fun ξ => exp (2 * s x ξ) - (2 * mass μ s x) * exp (s x ξ) + mass μ s x ^ 2 := by
      funext ξ; rw [hexp2]; ring
    have hi1 : Integrable (fun ξ => exp (2 * s x ξ) - 2 * mass μ s x * exp (s x ξ)) μ :=
      hz2.sub (hz.const_mul _)
    rw [h1, integral_add hi1 (integrable_const _), integral_sub hz2 (hz.const_mul _),
      integral_const_mul, integral_const]
    simp only [probReal_univ, smul_eq_mul]
    unfold mass; ring
  rw [heq]
  have := h.kappa x hx
  unfold mass at this ⊢
  nlinarith

lemma integral_exp_sq_shift {x : E} (hx : x ∈ W) :
    (∫ ξ, exp (2 * (s x ξ - log (mass μ s x))) ∂μ) ≤ κ := by
  have hm := h.mass_pos hx
  have h1 : (fun ξ => exp (2 * (s x ξ - log (mass μ s x)))) =
      fun ξ => (mass μ s x ^ 2)⁻¹ * exp (2 * s x ξ) := by
    funext ξ
    have h2 : exp (2 * log (mass μ s x)) = mass μ s x ^ 2 := by
      rw [show (2 : ℝ) * log (mass μ s x) = log (mass μ s x) + log (mass μ s x) by ring, exp_add,
        exp_log hm, sq]
    rw [mul_sub, exp_sub, h2, div_eq_inv_mul]
  rw [h1, integral_const_mul]
  have hk := h.kappa x hx
  have hpos : 0 < mass μ s x ^ 2 := by positivity
  rw [inv_mul_le_iff₀ hpos]
  unfold mass at hk ⊢
  linarith

omit [IsProbabilityMeasure μ] h in
lemma integral_mul_le_sqrt {F G' : Ξ → ℝ} (hF : Measurable F) (hG : Measurable G')
    (hF0 : ∀ ξ, 0 ≤ F ξ) (hG0 : ∀ ξ, 0 ≤ G' ξ)
    (hiF : Integrable (fun ξ => F ξ ^ 2) μ) (hiG : Integrable (fun ξ => G' ξ ^ 2) μ) :
    (∫ ξ, F ξ * G' ξ ∂μ) ≤ Real.sqrt (∫ ξ, F ξ ^ 2 ∂μ) * Real.sqrt (∫ ξ, G' ξ ^ 2 ∂μ) := by
  have hf : MemLp F (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).2 hiF
  have hg : MemLp G' (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).2 hiG
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    (Filter.Eventually.of_forall hF0) (Filter.Eventually.of_forall hG0) hf hg
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using hh

omit h in
lemma sq_sqrt_sq (a : ℝ) : Real.sqrt (a ^ 2) = |a| := Real.sqrt_sq_eq_abs a

lemma gradW_center_norm_le [BorelSpace E] [SecondCountableTopology E] {x : E} (hx : x ∈ W) (_hκ : 0 ≤ κ) (hG : 0 ≤ G) :
    ‖gradW μ s g x (log (mass μ s x))‖ ≤ Real.sqrt κ * G := by
  unfold gradW
  have hint := h.weighted_grad_int hx (log (mass μ s x))
  calc ‖∫ ξ, exp (s x ξ - log (mass μ s x)) • g x ξ ∂μ‖
      ≤ ∫ ξ, ‖exp (s x ξ - log (mass μ s x)) • g x ξ‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ ξ, exp (s x ξ - log (mass μ s x)) * ‖g x ξ‖ ∂μ := by
        congr 1; funext ξ; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    _ ≤ Real.sqrt (∫ ξ, exp (s x ξ - log (mass μ s x)) ^ 2 ∂μ) *
          Real.sqrt (∫ ξ, ‖g x ξ‖ ^ 2 ∂μ) := by
        have hF : Measurable (fun ξ => exp (s x ξ - log (mass μ s x))) :=
          measurable_exp.comp ((h.meas_s_x x).sub measurable_const)
        have hG' : Measurable (fun ξ => ‖g x ξ‖) := (h.meas_g_x x).norm
        apply integral_mul_le_sqrt hF hG' (fun ξ => (exp_pos _).le) (fun ξ => norm_nonneg _)
        · have : (fun ξ => exp (s x ξ - log (mass μ s x)) ^ 2) =
              fun ξ => exp (2 * (s x ξ - log (mass μ s x))) := by
            funext ξ; rw [sq, ← exp_add]; ring_nf
          rw [this]
          have hm := h.mass_pos hx
          have h1 : (fun ξ => exp (2 * (s x ξ - log (mass μ s x)))) =
              fun ξ => (mass μ s x ^ 2)⁻¹ * exp (2 * s x ξ) := by
            funext ξ
            have h2 : exp (2 * log (mass μ s x)) = mass μ s x ^ 2 := by
              rw [show (2 : ℝ) * log (mass μ s x) = log (mass μ s x) + log (mass μ s x) by ring,
                exp_add, exp_log hm, sq]
            rw [mul_sub, exp_sub, h2, div_eq_inv_mul]
          rw [h1]; exact (h.exp2_s_int hx).const_mul _
        · exact h.grad_int x hx
    _ ≤ Real.sqrt κ * G := by
        apply mul_le_mul
        · apply Real.sqrt_le_sqrt
          have : (fun ξ => exp (s x ξ - log (mass μ s x)) ^ 2) =
              fun ξ => exp (2 * (s x ξ - log (mass μ s x))) := by
            funext ξ; rw [sq, ← exp_add]; ring_nf
          rw [this]; exact h.integral_exp_sq_shift hx
        · calc Real.sqrt (∫ ξ, ‖g x ξ‖ ^ 2 ∂μ) ≤ Real.sqrt (G ^ 2) :=
                Real.sqrt_le_sqrt (h.grad_sq x hx)
            _ = G := by rw [Real.sqrt_sq hG]
        · exact Real.sqrt_nonneg _
        · exact Real.sqrt_nonneg _

lemma gradW_scale {x : E} (hx : x ∈ W) (ν : ℝ) :
    gradW μ s g x ν = (mass μ s x * exp (-ν)) • gradW μ s g x (log (mass μ s x)) := by
  rw [gradW_eq x ν, gradW_eq x (log (mass μ s x)), smul_smul]
  congr 1
  rw [mul_comm (mass μ s x) (exp (-ν)), mul_assoc, exp_neg (log _), exp_log (h.mass_pos hx),
    mul_inv_cancel₀ (h.mass_pos hx).ne', mul_one]

lemma gradW_sub_center_sq [BorelSpace E] [SecondCountableTopology E] {x : E} (hx : x ∈ W) {ν : ℝ} (hν : c0 ≤ ν) (hc : c0 ≤ c1)
    (hκ : 0 ≤ κ) (hG : 0 ≤ G) :
    ‖gradW μ s g x ν - gradW μ s g x (log (mass μ s x))‖ ^ 2 ≤
      2 * exp (c1 - c0) * κ * G ^ 2 * anchorGap μ s x ν := by
  rw [h.gradW_scale hx ν]
  have hsub : (mass μ s x * exp (-ν)) • gradW μ s g x (log (mass μ s x)) -
      gradW μ s g x (log (mass μ s x)) =
      (mass μ s x * exp (-ν) - 1) • gradW μ s g x (log (mass μ s x)) := by
    rw [sub_smul, one_smul]
  rw [hsub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h1 : (mass μ s x * exp (-ν) - 1) ^ 2 ≤ 2 * exp (c1 - c0) * anchorGap μ s x ν := by
    rw [h.dual_shift hx ν]
    unfold anchorGap
    exact sq_exp_sub_one_le_of_le (h.log_mass_sub_le hx hν) (by linarith)
  have h2 : ‖gradW μ s g x (log (mass μ s x))‖ ^ 2 ≤ κ * G ^ 2 := by
    have := h.gradW_center_norm_le hx hκ hG
    calc ‖gradW μ s g x (log (mass μ s x))‖ ^ 2 ≤ (Real.sqrt κ * G) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = κ * G ^ 2 := by rw [mul_pow, Real.sq_sqrt hκ]
  calc (mass μ s x * exp (-ν) - 1) ^ 2 * ‖gradW μ s g x (log (mass μ s x))‖ ^ 2
      ≤ (2 * exp (c1 - c0) * anchorGap μ s x ν) * (κ * G ^ 2) :=
        mul_le_mul h1 h2 (sq_nonneg _) (by have : 0 ≤ anchorGap μ s x ν := gap_nonneg x ν; positivity)
    _ = 2 * exp (c1 - c0) * κ * G ^ 2 * anchorGap μ s x ν := by ring

omit [IsProbabilityMeasure μ] in
lemma second_moment_le_sigma {x : E} (hx : x ∈ W) (ν : ℝ) :
    (∫ ξ, ‖exp (s x ξ - ν) • g x ξ‖ ^ 2 ∂μ) ≤ σ ^ 2 * (mass μ s x * exp (-ν)) ^ 2 := by
  have h1 : (fun ξ => ‖exp (s x ξ - ν) • g x ξ‖ ^ 2) =
      fun ξ => exp (-ν) ^ 2 * (exp (2 * s x ξ) * ‖g x ξ‖ ^ 2) := by
    funext ξ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _), mul_pow]
    have : exp (s x ξ - ν) ^ 2 = exp (-ν) ^ 2 * exp (2 * s x ξ) := by
      rw [sq, sq, ← exp_add, ← exp_add, ← exp_add]; congr 1; ring
    rw [this]
    ring
  rw [h1, integral_const_mul]
  have := h.sigma x hx
  unfold mass at this ⊢
  have hp : 0 ≤ exp (-ν) ^ 2 := sq_nonneg _
  calc exp (-ν) ^ 2 * ∫ ξ, exp (2 * s x ξ) * ‖g x ξ‖ ^ 2 ∂μ
      ≤ exp (-ν) ^ 2 * (σ ^ 2 * (∫ ξ, exp (s x ξ) ∂μ) ^ 2) := mul_le_mul_of_nonneg_left this hp
    _ = σ ^ 2 * ((∫ ξ, exp (s x ξ) ∂μ) * exp (-ν)) ^ 2 := by ring

omit [IsProbabilityMeasure μ] in
lemma second_moment_le_G [BorelSpace E] [SecondCountableTopology E] {x : E} (hx : x ∈ W) {ν : ℝ} (hν : c0 ≤ ν) :
    (∫ ξ, ‖exp (s x ξ - ν) • g x ξ‖ ^ 2 ∂μ) ≤ exp (2 * (c1 - c0)) * G ^ 2 := by
  have hpt : ∀ ξ, ‖exp (s x ξ - ν) • g x ξ‖ ^ 2 ≤ exp (2 * (c1 - c0)) * ‖g x ξ‖ ^ 2 := by
    intro ξ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _), mul_pow]
    have : exp (s x ξ - ν) ^ 2 ≤ exp (2 * (c1 - c0)) := by
      rw [sq, ← exp_add]
      exact exp_le_exp.mpr (by linarith [(h.bound ξ x hx).2])
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  calc (∫ ξ, ‖exp (s x ξ - ν) • g x ξ‖ ^ 2 ∂μ)
      ≤ ∫ ξ, exp (2 * (c1 - c0)) * ‖g x ξ‖ ^ 2 ∂μ :=
        integral_mono (h.weighted_grad_sq_int hx ν) ((h.grad_int x hx).const_mul _) hpt
    _ = exp (2 * (c1 - c0)) * ∫ ξ, ‖g x ξ‖ ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ exp (2 * (c1 - c0)) * G ^ 2 :=
        mul_le_mul_of_nonneg_left (h.grad_sq x hx) (exp_pos _).le


omit [IsProbabilityMeasure μ] in
lemma spmd_s_mem {x : E} (hx : x ∈ W) {ν α : ℝ} (hα : 0 ≤ α) (hν : ν ∈ Set.Icc c0 c1) (ξ : Ξ) :
    spmd α ν (s x ξ) ∈ Set.Icc c0 c1 :=
  spmd_mem_Icc hα hν (h.bound ξ x hx)

omit [IsProbabilityMeasure μ] in
lemma exp_neg_spmd_mem {x : E} (hx : x ∈ W) {ν α : ℝ} (hα : 0 ≤ α) (hν : ν ∈ Set.Icc c0 c1) (ξ : Ξ) :
    exp (-(spmd α ν (s x ξ))) ∈ Set.Icc (exp (-c1)) (exp (-c0)) := by
  have := h.spmd_s_mem hx hα hν ξ
  exact ⟨exp_le_exp.mpr (by linarith [this.2]), exp_le_exp.mpr (by linarith [this.1])⟩

omit h in
lemma kernel_lipschitz {ν α z z' : ℝ} (hα : 0 ≤ α) (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    |(exp (-ν) + α) / (1 + α * z) - (exp (-ν) + α) / (1 + α * z')| ≤
      α * (exp (-ν) + α) * |z - z'| := by
  have h1 : 0 < 1 + α * z := by positivity
  have h2 : 0 < 1 + α * z' := by positivity
  have heq : (exp (-ν) + α) / (1 + α * z) - (exp (-ν) + α) / (1 + α * z') =
      (exp (-ν) + α) * (α * (z' - z)) / ((1 + α * z) * (1 + α * z')) := by
    field_simp
    ring
  rw [heq, abs_div, abs_mul, abs_mul, abs_of_pos (mul_pos h1 h2),
    abs_of_nonneg (by positivity : 0 ≤ exp (-ν) + α), abs_of_nonneg hα, abs_sub_comm z' z]
  rw [div_le_iff₀ (by positivity)]
  have hprod : 1 ≤ (1 + α * z) * (1 + α * z') := by nlinarith [mul_nonneg hα hz, mul_nonneg hα hz']
  have hnn : 0 ≤ α * (exp (-ν) + α) * |z - z'| := by positivity
  calc (exp (-ν) + α) * (α * |z - z'|) = α * (exp (-ν) + α) * |z - z'| * 1 := by ring
    _ ≤ α * (exp (-ν) + α) * |z - z'| * ((1 + α * z) * (1 + α * z')) :=
        mul_le_mul_of_nonneg_left hprod hnn

lemma bias_bound {x : E} (hx : x ∈ W) {ν u α ρ : ℝ} (hν : ν ∈ Set.Icc c0 c1)
    (hu : u ∈ Set.Icc c0 c1) (hα : 0 ≤ α) (hρ : α * exp c1 ≤ ρ) :
    |∫ ξ, (exp (s x ξ) - mass μ s x) *
        (exp (-(spmd α ν (s x ξ))) * (spmd α ν (s x ξ) - u)) ∂μ| ≤
      (1 + ρ) * (1 + (c1 - c0)) * α * exp (-ν) *
        ∫ ξ, (exp (s x ξ) - mass μ s x) ^ 2 ∂μ := by
  set m := mass μ s x with hm_def
  have hm := h.mass_pos hx
  have hmI := h.mass_bounds hx
  set L := (1 + ρ) * (1 + (c1 - c0)) * α * exp (-ν) with hL
  let p : ℝ → ℝ := fun z => (exp (-ν) + α) / (1 + α * z)
  let H : ℝ → ℝ := fun r => -(r * log r) - u * r
  have hp_eq : ∀ ξ, exp (-(spmd α ν (s x ξ))) = p (exp (s x ξ)) := fun ξ => exp_neg_spmd hα
  have hH_eq : ∀ ξ, exp (-(spmd α ν (s x ξ))) * (spmd α ν (s x ξ) - u) =
      H (p (exp (s x ξ))) := by
    intro ξ
    have hpos : 0 < p (exp (s x ξ)) := by rw [← hp_eq]; exact exp_pos _
    have hlog : log (p (exp (s x ξ))) = -(spmd α ν (s x ξ)) := by rw [← hp_eq, log_exp]
    simp only [H]
    rw [hlog, ← hp_eq]
    ring
  have hpm : p m = exp (-(spmd α ν (log m))) := by rw [exp_neg_spmd hα, exp_log hm]
  have hνm : spmd α ν (log m) ∈ Set.Icc c0 c1 := spmd_mem_Icc hα hν (h.log_mass_mem hx)
  have hpm_mem : p m ∈ Set.Icc (exp (-c1)) (exp (-c0)) := by
    rw [hpm]; exact ⟨exp_le_exp.mpr (by linarith [hνm.2]), exp_le_exp.mpr (by linarith [hνm.1])⟩
  have hC : ∀ r ∈ Set.Icc (exp (-c1)) (exp (-c0)), |-(log r + 1) - u| ≤ 1 + (c1 - c0) := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le (exp_pos _) hr.1
    have h1 : -c1 ≤ log r := by rw [← log_exp (-c1)]; exact log_le_log (exp_pos _) hr.1
    have h2 : log r ≤ -c0 := by rw [← log_exp (-c0)]; exact log_le_log hr0 hr.2
    rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
  have hpt : ∀ ξ, |(exp (s x ξ) - m) * (H (p (exp (s x ξ))) - H (p m))| ≤
      L * (exp (s x ξ) - m) ^ 2 := by
    intro ξ
    have hpz_mem : p (exp (s x ξ)) ∈ Set.Icc (exp (-c1)) (exp (-c0)) := by
      rw [← hp_eq]; exact h.exp_neg_spmd_mem hx hα hν ξ
    have hHlip := mul_log_lipschitz (exp_pos (-c1)) u hC hpz_mem hpm_mem
    have hplip := kernel_lipschitz (ν := ν) hα (exp_pos (s x ξ)).le hm.le
    have hαν : exp (-ν) + α ≤ (1 + ρ) * exp (-ν) := by
      have : α ≤ ρ * exp (-ν) := by
        have h1 : α * exp c1 ≤ ρ := hρ
        have h2 : exp (-ν) * exp c1 ≥ 1 := by
          rw [← exp_add]; exact one_le_exp_iff.mpr (by linarith [hν.2])
        nlinarith [exp_pos (-ν), exp_pos c1]
      linarith
    have hchain : |H (p (exp (s x ξ))) - H (p m)| ≤ L * |exp (s x ξ) - m| := by
      calc |H (p (exp (s x ξ))) - H (p m)|
          ≤ (1 + (c1 - c0)) * |p (exp (s x ξ)) - p m| := hHlip
        _ ≤ (1 + (c1 - c0)) * (α * (exp (-ν) + α) * |exp (s x ξ) - m|) :=
            mul_le_mul_of_nonneg_left hplip (by linarith [hν.1, hν.2])
        _ ≤ (1 + (c1 - c0)) * (α * ((1 + ρ) * exp (-ν)) * |exp (s x ξ) - m|) := by
            apply mul_le_mul_of_nonneg_left _ (by linarith [hν.1, hν.2])
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            exact mul_le_mul_of_nonneg_left hαν hα
        _ = L * |exp (s x ξ) - m| := by rw [hL]; ring
    rw [abs_mul]
    calc |exp (s x ξ) - m| * |H (p (exp (s x ξ))) - H (p m)|
        ≤ |exp (s x ξ) - m| * (L * |exp (s x ξ) - m|) :=
          mul_le_mul_of_nonneg_left hchain (abs_nonneg _)
      _ = L * (exp (s x ξ) - m) ^ 2 := by rw [← sq_abs]; ring
  have hz := h.exp_s_int hx
  have hzm : Integrable (fun ξ => exp (s x ξ) - m) μ := hz.sub (integrable_const _)
  have hcenter : ∫ ξ, (exp (s x ξ) - m) * H (p m) ∂μ = 0 := by
    rw [integral_mul_const, integral_sub hz (integrable_const _), integral_const]
    simp [hm_def, mass]
  have hmeasH : Measurable (fun ξ => H (p (exp (s x ξ)))) := by
    have hp : Measurable (fun ξ => p (exp (s x ξ))) := by
      simp only [p]
      exact measurable_const.div (measurable_const.add (measurable_const.mul
        (measurable_exp.comp (h.meas_s_x x))))
    simp only [H]
    exact (hp.mul (measurable_log.comp hp)).neg.sub (hp.const_mul u)
  have hsq : Integrable (fun ξ => (exp (s x ξ) - m) ^ 2) μ := by
    refine Integrable.of_bound (((measurable_exp.comp (h.meas_s_x x)).sub measurable_const).pow_const 2
      |>.aestronglyMeasurable) (exp c1 ^ 2) ?_
    exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb := h.bound ξ x hx
      have hz1 := exp_le_exp.mpr hb.2
      have hz0 := exp_le_exp.mpr hb.1
      have : |exp (s x ξ) - m| ≤ exp c1 := by
        rw [abs_le]; constructor <;> nlinarith [exp_pos c0, exp_pos c1, hmI.1, hmI.2]
      calc (exp (s x ξ) - m) ^ 2 = |exp (s x ξ) - m| ^ 2 := (sq_abs _).symm
        _ ≤ exp c1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hbdd : Integrable (fun ξ => (exp (s x ξ) - m) * (H (p (exp (s x ξ))) - H (p m))) μ := by
    refine Integrable.mono' (hsq.const_mul L) ?_ ?_
    · exact ((measurable_exp.comp (h.meas_s_x x)).sub measurable_const).mul
        (hmeasH.sub measurable_const) |>.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ξ => by rw [Real.norm_eq_abs]; exact hpt ξ
  have hsplit : (fun ξ => (exp (s x ξ) - m) * (exp (-(spmd α ν (s x ξ))) * (spmd α ν (s x ξ) - u))) =
      fun ξ => (exp (s x ξ) - m) * (H (p (exp (s x ξ))) - H (p m)) + (exp (s x ξ) - m) * H (p m) := by
    funext ξ; rw [hH_eq]; ring
  rw [hsplit, integral_add hbdd (hzm.mul_const _), hcenter, add_zero]
  calc |∫ ξ, (exp (s x ξ) - m) * (H (p (exp (s x ξ))) - H (p m)) ∂μ|
      ≤ ∫ ξ, |(exp (s x ξ) - m) * (H (p (exp (s x ξ))) - H (p m))| ∂μ := by
        have := norm_integral_le_integral_norm
          (fun ξ => (exp (s x ξ) - m) * (H (p (exp (s x ξ))) - H (p m))) (μ := μ)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∫ ξ, L * (exp (s x ξ) - m) ^ 2 ∂μ :=
        integral_mono hbdd.abs (hsq.const_mul L) hpt
    _ = L * ∫ ξ, (exp (s x ξ) - m) ^ 2 ∂μ := integral_const_mul _ _


lemma spmd_int {x : E} (hx : x ∈ W) {ν α : ℝ} (hα : 0 ≤ α) (hν : ν ∈ Set.Icc c0 c1)
    (F : ℝ → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ r ∈ Set.Icc c0 c1, |F r| ≤ C) :
    Integrable (fun ξ => F (spmd α ν (s x ξ))) μ := by
  refine Integrable.of_bound ?_ C ?_
  · have hm : Measurable (fun ξ => spmd α ν (s x ξ)) := by
      unfold spmd
      exact ((measurable_const.add (measurable_log.comp (measurable_const.add
        (measurable_const.mul (measurable_exp.comp (h.meas_s_x x)))))).sub measurable_const)
    exact (hF.comp hm).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs]; exact hC _ (h.spmd_s_mem hx hα hν ξ)

omit [IsProbabilityMeasure μ] in
lemma meas_spmd {x : E} (ν α : ℝ) : Measurable (fun ξ => spmd α ν (s x ξ)) := by
  unfold spmd
  exact ((measurable_const.add (measurable_log.comp (measurable_const.add
    (measurable_const.mul (measurable_exp.comp (h.meas_s_x x)))))).sub measurable_const)

lemma anchor_regret {x : E} (hx : x ∈ W) {ν u α ρ : ℝ} (hν : ν ∈ Set.Icc c0 c1)
    (hu : u ∈ Set.Icc c0 c1) (hα : 0 ≤ α) (hρ : α * exp c1 ≤ ρ) :
    α * ∫ ξ, (1 - mass μ s x * exp (-(spmd α ν (s x ξ)))) * (spmd α ν (s x ξ) - u) ∂μ ≤
      breg u ν - (∫ ξ, breg u (spmd α ν (s x ξ)) ∂μ) +
        (1 + ρ) * (1 + (c1 - c0)) * α ^ 2 * exp (-ν) *
          ∫ ξ, (exp (s x ξ) - mass μ s x) ^ 2 ∂μ := by
  set m := mass μ s x
  have hbias := h.bias_bound hx hν hu hα hρ
  have hmeasν := h.meas_spmd (x := x) ν α
  have hbdd_spmd : ∀ ξ, |spmd α ν (s x ξ)| ≤ |c0| + |c1| := by
    intro ξ
    have := h.spmd_s_mem hx hα hν ξ
    rw [abs_le]; constructor <;> cases abs_cases c0 <;> cases abs_cases c1 <;> linarith [this.1, this.2]
  have hi_pt : Integrable (fun ξ => (1 - exp (s x ξ) * exp (-(spmd α ν (s x ξ)))) *
      (spmd α ν (s x ξ) - u)) μ := by
    refine Integrable.of_bound ?_ ((1 + exp c1 * exp (-c0)) * (|c0| + |c1| + |u|)) ?_
    · exact (((measurable_const.sub ((measurable_exp.comp (h.meas_s_x x)).mul
        (measurable_exp.comp hmeasν.neg)))).mul (hmeasν.sub measurable_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 := h.exp_neg_spmd_mem hx hα hν ξ
        have h2 := h.bound ξ x hx
        have ha : |1 - exp (s x ξ) * exp (-(spmd α ν (s x ξ)))| ≤ 1 + exp c1 * exp (-c0) := by
          rw [abs_le]
          have := mul_le_mul (exp_le_exp.mpr h2.2) h1.2 (exp_pos _).le (exp_pos _).le
          constructor <;> nlinarith [exp_pos (s x ξ), exp_pos (-(spmd α ν (s x ξ)))]
        have hb : |spmd α ν (s x ξ) - u| ≤ |c0| + |c1| + |u| := by
          have := hbdd_spmd ξ
          calc |spmd α ν (s x ξ) - u| ≤ |spmd α ν (s x ξ)| + |u| := abs_sub _ _
            _ ≤ |c0| + |c1| + |u| := by linarith
        exact mul_le_mul ha hb (abs_nonneg _) (by positivity)
  have hi_bias : Integrable (fun ξ => (exp (s x ξ) - m) *
      (exp (-(spmd α ν (s x ξ))) * (spmd α ν (s x ξ) - u))) μ := by
    refine Integrable.of_bound ?_ ((exp c1 + exp c1) * (exp (-c0) * (|c0| + |c1| + |u|))) ?_
    · exact (((measurable_exp.comp (h.meas_s_x x)).sub measurable_const).mul
        ((measurable_exp.comp hmeasν.neg).mul (hmeasν.sub measurable_const))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ξ => by
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 := h.exp_neg_spmd_mem hx hα hν ξ
        have h2 := h.bound ξ x hx
        have hmI := h.mass_bounds hx
        have ha : |exp (s x ξ) - m| ≤ exp c1 + exp c1 := by
          rw [abs_le]
          have := exp_le_exp.mpr h2.2
          constructor <;> nlinarith [exp_pos (s x ξ), exp_pos c0, hmI.1, hmI.2]
        have hb : |exp (-(spmd α ν (s x ξ)))| ≤ exp (-c0) := by
          rw [abs_of_pos (exp_pos _)]; exact h1.2
        have hc : |spmd α ν (s x ξ) - u| ≤ |c0| + |c1| + |u| := by
          have := hbdd_spmd ξ
          calc |spmd α ν (s x ξ) - u| ≤ |spmd α ν (s x ξ)| + |u| := abs_sub _ _
            _ ≤ |c0| + |c1| + |u| := by linarith
        exact mul_le_mul ha (mul_le_mul hb hc (abs_nonneg _) (exp_pos _).le) (by positivity)
          (by positivity)
  have hi_breg : Integrable (fun ξ => breg u (spmd α ν (s x ξ))) μ := by
    refine h.spmd_int hx hα hν (fun r => breg u r) ?_ (exp (-c0) + exp (-c0) + exp (-c0) * (|c0| + |c1| + |u|)) ?_
    · unfold breg
      exact ((measurable_const.sub (measurable_exp.comp measurable_neg)).add
        ((measurable_exp.comp measurable_neg).mul (measurable_const.sub measurable_id)))
    · intro r hr
      unfold breg
      have h1 : exp (-r) ≤ exp (-c0) := exp_le_exp.mpr (by linarith [hr.1])
      have h2 : exp (-u) ≤ exp (-c0) := exp_le_exp.mpr (by linarith [hu.1])
      have h3 : |u - r| ≤ |c0| + |c1| + |u| := by
        calc |u - r| ≤ |u| + |r| := abs_sub _ _
          _ ≤ |u| + (|c0| + |c1|) := by
              have : |r| ≤ |c0| + |c1| := by
                rw [abs_le]; constructor <;> cases abs_cases c0 <;> cases abs_cases c1 <;>
                  linarith [hr.1, hr.2]
              linarith
          _ = |c0| + |c1| + |u| := by ring
      have h4 : |exp (-r) * (u - r)| ≤ exp (-c0) * (|c0| + |c1| + |u|) := by
        rw [abs_mul, abs_of_pos (exp_pos _)]
        exact mul_le_mul h1 h3 (abs_nonneg _) (exp_pos _).le
      calc |exp (-u) - exp (-r) + exp (-r) * (u - r)|
          ≤ |exp (-u) - exp (-r)| + |exp (-r) * (u - r)| := abs_add_le _ _
        _ ≤ (exp (-c0) + exp (-c0)) + exp (-c0) * (|c0| + |c1| + |u|) := by
            gcongr
            rw [abs_le]; constructor <;> linarith [exp_pos (-u), exp_pos (-r)]
        _ = _ := by ring
  have hpt : ∀ ξ, α * ((1 - exp (s x ξ) * exp (-(spmd α ν (s x ξ)))) * (spmd α ν (s x ξ) - u)) ≤
      breg u ν - breg u (spmd α ν (s x ξ)) := fun ξ => by
    have := spmd_regret (ν := ν) (s := s x ξ) hα u
    linarith [this]
  have hint1 : α * ∫ ξ, (1 - exp (s x ξ) * exp (-(spmd α ν (s x ξ)))) * (spmd α ν (s x ξ) - u) ∂μ ≤
      breg u ν - ∫ ξ, breg u (spmd α ν (s x ξ)) ∂μ := by
    rw [← integral_const_mul]
    have hi : Integrable (fun ξ => breg u ν - breg u (spmd α ν (s x ξ))) μ :=
      (integrable_const _).sub hi_breg
    have := integral_mono (hi_pt.const_mul α) hi hpt
    rwa [integral_sub (integrable_const _) hi_breg, integral_const, probReal_univ, one_smul] at this
  have hdecomp : ∀ ξ, (1 - m * exp (-(spmd α ν (s x ξ)))) * (spmd α ν (s x ξ) - u) =
      (1 - exp (s x ξ) * exp (-(spmd α ν (s x ξ)))) * (spmd α ν (s x ξ) - u) +
      (exp (s x ξ) - m) * (exp (-(spmd α ν (s x ξ))) * (spmd α ν (s x ξ) - u)) := fun ξ => by ring
  have hsum : ∫ ξ, (1 - m * exp (-(spmd α ν (s x ξ)))) * (spmd α ν (s x ξ) - u) ∂μ =
      (∫ ξ, (1 - exp (s x ξ) * exp (-(spmd α ν (s x ξ)))) * (spmd α ν (s x ξ) - u) ∂μ) +
      ∫ ξ, (exp (s x ξ) - m) * (exp (-(spmd α ν (s x ξ))) * (spmd α ν (s x ξ) - u)) ∂μ := by
    rw [← integral_add hi_pt hi_bias]
    congr 1; funext ξ; exact hdecomp ξ
  rw [hsum, mul_add]
  have hb := (abs_le.mp hbias).2
  have hαb : α * ∫ ξ, (exp (s x ξ) - m) * (exp (-(spmd α ν (s x ξ))) * (spmd α ν (s x ξ) - u)) ∂μ ≤
      α * ((1 + ρ) * (1 + (c1 - c0)) * α * exp (-ν) * ∫ ξ, (exp (s x ξ) - m) ^ 2 ∂μ) :=
    mul_le_mul_of_nonneg_left hb hα
  calc _ ≤ (breg u ν - ∫ ξ, breg u (spmd α ν (s x ξ)) ∂μ) +
        α * ((1 + ρ) * (1 + (c1 - c0)) * α * exp (-ν) * ∫ ξ, (exp (s x ξ) - m) ^ 2 ∂μ) :=
        add_le_add hint1 hαb
    _ = _ := by ring

lemma joint_convex [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] {x y : E} (hx : x ∈ W) (hy : y ∈ W) (ν ν' : ℝ) :
    dualObj μ s x ν + ⟪gradW μ s g x ν, y - x⟫ + (1 - mass μ s x * exp (-ν)) * (ν' - ν) ≤
      dualObj μ s y ν' := by
  have hpt : ∀ ξ, exp (s x ξ - ν) + exp (s x ξ - ν) * ⟪g x ξ, y - x⟫ -
      exp (s x ξ - ν) * (ν' - ν) ≤ exp (s y ξ - ν') := by
    intro ξ
    have hsub := h.subgrad ξ x hx y hy
    set d := ⟪g x ξ, y - x⟫ - (ν' - ν)
    have h1 : exp (s x ξ - ν) * exp d ≤ exp (s y ξ - ν') := by
      rw [← exp_add]; exact exp_le_exp.mpr (by simp only [d]; linarith)
    have h2 : exp (s x ξ - ν) * (1 + d) ≤ exp (s x ξ - ν) * exp d :=
      mul_le_mul_of_nonneg_left (by linarith [add_one_le_exp d]) (exp_pos _).le
    calc exp (s x ξ - ν) + exp (s x ξ - ν) * ⟪g x ξ, y - x⟫ - exp (s x ξ - ν) * (ν' - ν)
        = exp (s x ξ - ν) * (1 + d) := by simp only [d]; ring
      _ ≤ exp (s y ξ - ν') := h2.trans h1
  have hiw : Integrable (fun ξ => exp (s x ξ - ν)) μ := by
    have := h.exp_s_int hx
    have h1 : (fun ξ => exp (s x ξ - ν)) = fun ξ => exp (-ν) * exp (s x ξ) := by
      funext ξ; rw [← exp_add]; ring_nf
    rw [h1]; exact this.const_mul _
  have hig : Integrable (fun ξ => exp (s x ξ - ν) * ⟪g x ξ, y - x⟫) μ := by
    have := Integrable.inner_const (𝕜 := ℝ) (h.weighted_grad_int hx ν) (y - x)
    convert this using 1
    funext ξ; rw [real_inner_smul_left]
  have hiy : Integrable (fun ξ => exp (s y ξ - ν')) μ := by
    have := h.exp_s_int hy
    have h1 : (fun ξ => exp (s y ξ - ν')) = fun ξ => exp (-ν') * exp (s y ξ) := by
      funext ξ; rw [← exp_add]; ring_nf
    rw [h1]; exact this.const_mul _
  have hi1 : Integrable (fun ξ => exp (s x ξ - ν) + exp (s x ξ - ν) * ⟪g x ξ, y - x⟫) μ := hiw.add hig
  have hi2 : Integrable (fun ξ => exp (s x ξ - ν) * (ν' - ν)) μ := hiw.mul_const _
  have hi_lhs : Integrable (fun ξ => exp (s x ξ - ν) + exp (s x ξ - ν) * ⟪g x ξ, y - x⟫ -
      exp (s x ξ - ν) * (ν' - ν)) μ := hi1.sub hi2
  have hint := integral_mono hi_lhs hiy hpt
  rw [integral_sub hi1 hi2, integral_add hiw hig, integral_mul_const] at hint
  have e1 : ∫ ξ, exp (s x ξ - ν) ∂μ = mass μ s x * exp (-ν) := by
    have h1 : (fun ξ => exp (s x ξ - ν)) = fun ξ => exp (-ν) * exp (s x ξ) := by
      funext ξ; rw [← exp_add]; ring_nf
    rw [h1, integral_const_mul]; unfold mass; ring
  have e2 : ∫ ξ, exp (s x ξ - ν) * ⟪g x ξ, y - x⟫ ∂μ = ⟪gradW μ s g x ν, y - x⟫ := by
    unfold gradW
    rw [real_inner_comm, ← integral_inner (h.weighted_grad_int hx ν)]
    congr 1; funext ξ; rw [real_inner_smul_right, real_inner_comm]
  have e3 : ∫ ξ, exp (s y ξ - ν') ∂μ = mass μ s y * exp (-ν') := by
    have h1 : (fun ξ => exp (s y ξ - ν')) = fun ξ => exp (-ν') * exp (s y ξ) := by
      funext ξ; rw [← exp_add]; ring_nf
    rw [h1, integral_const_mul]; unfold mass; ring
  rw [e1, e2, e3] at hint
  unfold dualObj
  linarith


lemma gap_bound {x : E} (hx : x ∈ W) {r : ℝ} (hr : r ∈ Set.Icc c0 c1) :
    anchorGap μ s x r ≤ exp (c1 - c0) := by
  unfold anchorGap
  have h1 : log (mass μ s x) - r ≤ c1 - c0 := h.log_mass_sub_le hx hr.1
  have h2 : -(c1 - c0) ≤ log (mass μ s x) - r := by linarith [(h.log_mass_mem hx).1, hr.2]
  rcases le_or_gt 0 (log (mass μ s x) - r) with hu | hu
  · exact (psi_le_exp_of_nonneg hu).trans (exp_le_exp.mpr h1)
  · have := psi_neg_le_half_sq (x := -(log (mass μ s x) - r)) (by linarith)
    rw [neg_neg] at this
    have hc : 0 ≤ c1 - c0 := by linarith
    calc psi (log (mass μ s x) - r) ≤ (-(log (mass μ s x) - r)) ^ 2 / 2 := this
      _ ≤ (c1 - c0) ^ 2 / 2 := by
          have : -(log (mass μ s x) - r) ≤ c1 - c0 := by linarith
          have h0 : 0 ≤ -(log (mass μ s x) - r) := by linarith
          nlinarith [pow_le_pow_left₀ h0 this 2]
      _ ≤ exp (c1 - c0) := by
          have := quadratic_le_exp_of_nonneg hc
          nlinarith

lemma gap_virtual_int {x : E} (hx : x ∈ W) {ν α : ℝ} (hα : 0 ≤ α) (hν : ν ∈ Set.Icc c0 c1) :
    Integrable (fun ξ => anchorGap μ s x (spmd α ν (s x ξ))) μ := by
  refine h.spmd_int hx hα hν (fun r => anchorGap μ s x r) ?_ (exp (c1 - c0)) ?_
  · unfold anchorGap psi
    exact ((measurable_exp.comp (measurable_const.sub measurable_id)).sub measurable_const).sub
      (measurable_const.sub measurable_id)
  · intro r hr
    rw [abs_of_nonneg (gap_nonneg (μ := μ) (s := s) x r)]
    exact h.gap_bound hx hr

lemma virtual_variance_bound {x : E} (hx : x ∈ W) {ν α ρ : ℝ} (hα : 0 ≤ α) (hν : ν ∈ Set.Icc c0 c1)
    (hρ : α * exp c1 ≤ ρ) (hκ : 1 ≤ κ) :
    exp (-ν) * (∫ ξ, (exp (s x ξ) - mass μ s x) ^ 2 ∂μ) ≤
      2 * (1 + ρ) * (κ - 1) * exp c1 *
        ∫ ξ, (1 + anchorGap μ s x (spmd α ν (s x ξ))) ∂μ := by
  have hvar := h.variance_le hx
  have hm := h.mass_pos hx
  have hmI := h.mass_bounds hx
  have hpt : ∀ ξ, mass μ s x * exp (-ν) ≤ 2 * (1 + ρ) * (1 + anchorGap μ s x (spmd α ν (s x ξ))) := by
    intro ξ
    have h1 : exp (-ν) ≤ (1 + ρ) * exp (-(spmd α ν (s x ξ))) :=
      exp_neg_le_of_spmd hα (ρ := ρ) (by
        have := exp_le_exp.mpr (h.bound ξ x hx).2
        nlinarith)
    have h2 := h.mass_exp_neg_le_gap hx (spmd α ν (s x ξ))
    have hρ0 : 0 ≤ 1 + ρ := by nlinarith [exp_pos c1]
    calc mass μ s x * exp (-ν) ≤ mass μ s x * ((1 + ρ) * exp (-(spmd α ν (s x ξ)))) :=
          mul_le_mul_of_nonneg_left h1 hm.le
      _ = (1 + ρ) * (mass μ s x * exp (-(spmd α ν (s x ξ)))) := by ring
      _ ≤ (1 + ρ) * (2 * (1 + anchorGap μ s x (spmd α ν (s x ξ)))) :=
          mul_le_mul_of_nonneg_left h2 hρ0
      _ = _ := by ring
  have hint : mass μ s x * exp (-ν) ≤
      ∫ ξ, 2 * (1 + ρ) * (1 + anchorGap μ s x (spmd α ν (s x ξ))) ∂μ := by
    have := integral_mono (integrable_const (mass μ s x * exp (-ν)))
      (((integrable_const _).add (h.gap_virtual_int hx hα hν)).const_mul _) hpt
    simpa using this
  rw [integral_const_mul] at hint
  have hk : 0 ≤ κ - 1 := by linarith
  calc exp (-ν) * ∫ ξ, (exp (s x ξ) - mass μ s x) ^ 2 ∂μ
      ≤ exp (-ν) * ((κ - 1) * mass μ s x ^ 2) := mul_le_mul_of_nonneg_left hvar (exp_pos _).le
    _ = (κ - 1) * mass μ s x * (mass μ s x * exp (-ν)) := by ring
    _ ≤ (κ - 1) * exp c1 * (2 * (1 + ρ) * ∫ ξ, (1 + anchorGap μ s x (spmd α ν (s x ξ))) ∂μ) := by
        apply mul_le_mul _ hint (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hmI.2 hk
    _ = _ := by ring

lemma second_moment_gap {x : E} (hx : x ∈ W) {ν : ℝ} (hν : c0 ≤ ν) (_hσ : 0 ≤ σ) :
    (∫ ξ, ‖exp (s x ξ - ν) • g x ξ‖ ^ 2 ∂μ) ≤
      2 * exp (c1 - c0) * σ ^ 2 * (1 + anchorGap μ s x ν) := by
  have h1 := h.second_moment_le_sigma hx ν
  have h2 := h.mass_exp_neg_le_exp hx hν
  have h3 := h.mass_exp_neg_le_gap hx ν
  have h0 : 0 ≤ mass μ s x * exp (-ν) := mul_nonneg (h.mass_pos hx).le (exp_pos _).le
  calc (∫ ξ, ‖exp (s x ξ - ν) • g x ξ‖ ^ 2 ∂μ) ≤ σ ^ 2 * (mass μ s x * exp (-ν)) ^ 2 := h1
    _ ≤ σ ^ 2 * (exp (c1 - c0) * (2 * (1 + anchorGap μ s x ν))) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg σ)
        rw [sq]; exact mul_le_mul h2 h3 h0 (exp_pos _).le
    _ = _ := by ring

lemma gradW_sq_bound [BorelSpace E] [SecondCountableTopology E] {x : E} (hx : x ∈ W) {ν : ℝ} (hν : c0 ≤ ν) (hc : c0 ≤ c1)
    (hκ : 0 ≤ κ) (hG : 0 ≤ G) :
    ‖gradW μ s g x ν‖ ^ 2 ≤ 2 * κ * G ^ 2 + 4 * exp (c1 - c0) * κ * G ^ 2 * anchorGap μ s x ν := by
  have h1 := h.gradW_sub_center_sq hx hν hc hκ hG
  have h2 : ‖gradW μ s g x (log (mass μ s x))‖ ^ 2 ≤ κ * G ^ 2 := by
    have := h.gradW_center_norm_le hx hκ hG
    calc ‖gradW μ s g x (log (mass μ s x))‖ ^ 2 ≤ (Real.sqrt κ * G) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = κ * G ^ 2 := by rw [mul_pow, Real.sq_sqrt hκ]
  have htri : ‖gradW μ s g x ν‖ ^ 2 ≤ 2 * ‖gradW μ s g x ν - gradW μ s g x (log (mass μ s x))‖ ^ 2 +
      2 * ‖gradW μ s g x (log (mass μ s x))‖ ^ 2 := by
    have := norm_add_le (gradW μ s g x ν - gradW μ s g x (log (mass μ s x)))
      (gradW μ s g x (log (mass μ s x)))
    rw [sub_add_cancel] at this
    nlinarith [sq_nonneg (‖gradW μ s g x ν - gradW μ s g x (log (mass μ s x))‖ -
      ‖gradW μ s g x (log (mass μ s x))‖), norm_nonneg (gradW μ s g x ν),
      norm_nonneg (gradW μ s g x ν - gradW μ s g x (log (mass μ s x))),
      norm_nonneg (gradW μ s g x (log (mass μ s x)))]
  nlinarith

end AnchorHyp

end Anchor

end OracleTemplate.Scent
