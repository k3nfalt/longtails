import LongTails.Proofs.ManyConstraintNoise

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintRegularity

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintPenalty
  LongTails.Proofs.ManyConstraintFinite LongTails.Proofs.ManyConstraintStochastic
  LongTails.Proofs.ManyConstraintStep LongTails.Proofs.ManyConstraintBall
  LongTails.Proofs.ManyConstraintCoupling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {m : ℕ} [NeZero m]
variable {law : Measure Ξ} {loss : Ξ → E → ℝ} {grad : Ξ → E → E} {L σ : ℝ} {xs : E}
  {K : Fin m → Set E} {P : Fin m → E → E}

lemma _root_.LongTails.Proofs.ManyConstraintStochastic.Regular.meanGrad_lip (h : Regular law loss grad L σ xs) (x y : E) :
    ‖meanGrad law grad y - meanGrad law grad x‖ ≤ L * ‖y - x‖ := by
  have := h.prob
  unfold meanGrad
  rw [← integral_sub (h.gradInt y) (h.gradInt x)]
  have hb := norm_integral_le_of_norm_le_const (μ := law) (C := L * ‖y - x‖)
    (Filter.Eventually.of_forall fun ξ => h.lip ξ y x)
  simpa using hb

lemma _root_.LongTails.Proofs.ManyConstraintStochastic.Regular.objective_continuous (h : Regular law loss grad L σ xs) (hL : 0 < L) :
    Continuous (objective law loss) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  set g := ‖meanGrad law grad x‖
  refine ⟨min 1 (ε / (g + 2 * L + 1)), by positivity, fun y hy => ?_⟩
  rw [dist_eq_norm] at hy ⊢
  rw [Real.norm_eq_abs]
  set d := ‖y - x‖
  have hd1 : d ≤ 1 := hy.le.trans (min_le_left _ _)
  have hd2 : d * (g + 2 * L + 1) < ε := by
    have := lt_of_lt_of_le hy (min_le_right _ _)
    rwa [lt_div_iff₀ (by positivity)] at this
  have hup := h.model x y
  have hup2 := h.model y x
  have hi1 : ⟪meanGrad law grad x, y - x⟫ ≤ g * d := real_inner_le_norm _ _
  have hgy : ‖meanGrad law grad y‖ ≤ g + L * d := by
    have hl := h.meanGrad_lip x y
    have hn := norm_add_le (meanGrad law grad x) (meanGrad law grad y - meanGrad law grad x)
    rw [add_sub_cancel] at hn
    linarith
  have hxy : ‖x - y‖ = d := norm_sub_rev _ _
  have hi2 : ⟪meanGrad law grad y, x - y⟫ ≤ (g + L * d) * d := by
    have := real_inner_le_norm (meanGrad law grad y) (x - y)
    rw [hxy] at this
    nlinarith [mul_le_mul_of_nonneg_right hgy (norm_nonneg (y - x))]
  rw [hxy] at hup2
  have hd0 : 0 ≤ d := norm_nonneg _
  have hg0 : 0 ≤ g := norm_nonneg _
  have hdd : d * d ≤ d := by nlinarith
  rw [abs_lt]
  constructor <;> nlinarith

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NeZero m] in
lemma hpen_continuous (hP : ∀ j z, IsProj (K j) z (P j z)) (β : ℝ) :
    Continuous (hpen β P) := by
  have : hpen β P = fun x => 𝔼 j, β / 2 * Metric.infDist x (K j) ^ 2 := by
    funext x; simp only [hpen, pen_eq_infDist (hP _)]
  rw [this]
  simp only [Finset.expect, Finset.card_univ]
  fun_prop

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma reg_continuous (μ : ℝ) (x0 : E) : Continuous (reg μ x0) := by
  unfold reg; fun_prop

omit [NeZero m] in
lemma Phi_measurable (h : Regular law loss grad L σ xs) (hL : 0 < L)
    (hP : ∀ j z, IsProj (K j) z (P j z)) (β μ : ℝ) (x0 : E) :
    Measurable (Phi law loss β P μ x0) := by
  unfold Phi Fsm
  exact ((h.objective_continuous hL).add (hpen_continuous hP β)).add
    (reg_continuous μ x0) |>.measurable

omit [CompleteSpace E] in
lemma projBall_measurable (x0 : E) (ρ : ℝ) : Measurable (projBall x0 ρ) := by
  unfold projBall
  refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) measurable_id ?_
  fun_prop

omit [CompleteSpace E] in
lemma proxBall_measurable (μ : ℝ) (x0 : E) (ρ a : ℝ) (z : E) :
    Measurable (proxBall μ x0 ρ a z) := by
  unfold proxBall ManyConstraintBall.center
  exact (projBall_measurable x0 ρ).comp (by fun_prop)

lemma Phi_abs_le (h : Regular law loss grad L σ xs) (hL : 0 < L)
    (hP : ∀ j z, IsProj (K j) z (P j z)) {β μ ρ : ℝ} (hβ : 0 ≤ β) (hμ : 0 ≤ μ) {x0 : E}
    (hxs : xs ∈ closedBall x0 ρ) {y : E} (hy : y ∈ closedBall x0 ρ) :
    |Phi law loss β P μ x0 y| ≤ |objective law loss xs| + ‖meanGrad law grad xs‖ * (2 * ρ) +
      L / 2 * (2 * ρ) ^ 2 + (hpen β P xs + ‖hgrad β P xs‖ * (2 * ρ) + β / 2 * (2 * ρ) ^ 2) +
      μ / 2 * ρ ^ 2 := by
  rw [mem_closedBall, dist_eq_norm] at hxs hy
  have hd : ‖y - xs‖ ≤ 2 * ρ := by
    calc ‖y - xs‖ = ‖(y - x0) - (xs - x0)‖ := by congr 1; abel
      _ ≤ ‖y - x0‖ + ‖xs - x0‖ := norm_sub_le _ _
      _ ≤ 2 * ρ := by linarith
  have hd0 : 0 ≤ ‖y - xs‖ := norm_nonneg _
  have hsq : ‖y - xs‖ ^ 2 ≤ (2 * ρ) ^ 2 := pow_le_pow_left₀ hd0 hd 2
  have hup := h.model xs y
  have hlow := h.support hL xs y
  have hnn : 0 ≤ (1 / (2 * L)) * ∫ ξ, ‖grad ξ y - grad ξ xs‖ ^ 2 ∂law := by
    have : 0 ≤ ∫ ξ, ‖grad ξ y - grad ξ xs‖ ^ 2 ∂law := integral_nonneg fun _ => sq_nonneg _
    positivity
  have hi := abs_real_inner_le_norm (meanGrad law grad xs) (y - xs)
  have hi' : ‖meanGrad law grad xs‖ * ‖y - xs‖ ≤ ‖meanGrad law grad xs‖ * (2 * ρ) :=
    mul_le_mul_of_nonneg_left hd (norm_nonneg _)
  have hpu := hpen_upper hP hβ xs y
  have hpn := hpen_nonneg (P := P) hβ y
  have hpi := abs_real_inner_le_norm (hgrad β P xs) (y - xs)
  have hpi' : ‖hgrad β P xs‖ * ‖y - xs‖ ≤ ‖hgrad β P xs‖ * (2 * ρ) :=
    mul_le_mul_of_nonneg_left hd (norm_nonneg _)
  have hr0 : 0 ≤ reg μ x0 y := by unfold reg; positivity
  have hr1 : reg μ x0 y ≤ μ / 2 * ρ ^ 2 := by
    unfold reg
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy 2) (by positivity)
  have hpxs := hpen_nonneg (P := P) hβ xs
  unfold Phi Fsm
  rw [abs_le]
  constructor
  · have hA : -(‖meanGrad law grad xs‖ * (2 * ρ)) ≤ ⟪meanGrad law grad xs, y - xs⟫ := by
      linarith [neg_abs_le ⟪meanGrad law grad xs, y - xs⟫]
    have hB := neg_abs_le (objective law loss xs)
    have hC : 0 ≤ L / 2 * (2 * ρ) ^ 2 := by positivity
    have hD : 0 ≤ hpen β P xs + ‖hgrad β P xs‖ * (2 * ρ) + β / 2 * (2 * ρ) ^ 2 := by
      have : 0 ≤ ‖hgrad β P xs‖ * (2 * ρ) := by
        have : 0 ≤ ρ := le_trans (norm_nonneg _) hy
        positivity
      have : 0 ≤ β / 2 * (2 * ρ) ^ 2 := by positivity
      linarith
    have hE : 0 ≤ μ / 2 * ρ ^ 2 := by positivity
    have hG0 : 0 ≤ ‖meanGrad law grad xs‖ * (2 * ρ) := by
      have : 0 ≤ ρ := le_trans (norm_nonneg _) hy
      positivity
    linarith
  · nlinarith [le_abs_self (objective law loss xs), le_abs_self ⟪meanGrad law grad xs, y - xs⟫,
      le_abs_self ⟪hgrad β P xs, y - xs⟫, mul_le_mul_of_nonneg_left hsq hL.le,
      mul_le_mul_of_nonneg_left hsq hβ]

end LongTails.Proofs.ManyConstraintRegularity
