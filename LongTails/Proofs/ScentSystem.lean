import LongTails.Proofs.ScentAnchor
import LongTails.Proofs.ScentProduct
import Mathlib.Algebra.Order.Chebyshev


namespace OracleTemplate.Scent

open MeasureTheory Real
open LongTails.Setups.CompositionalEntropicRisk
open scoped RealInnerProductSpace BigOperators

variable {q : Params} (I : Instance q)

structure SysHyp (I : Instance q) (projection : q.E → q.E) (wstar : q.E) : Prop where
  convex : Convex ℝ I.domain
  closed : IsClosed I.domain
  w0_mem : q.w0 ∈ I.domain
  proj_meas : Measurable projection
  proj_mem : ∀ x, projection x ∈ I.domain
  proj_ineq : ∀ x, ∀ u ∈ I.domain, ⟪x - projection x, u - projection x⟫ ≤ 0
  anchor : ∀ i, AnchorHyp (I.law i : Measure q.Ξ) (I.score i) (I.grad i) I.domain q.c0 q.c1 q.G q.κ q.σ
  hB : 0 < q.B
  hc : q.c0 ≤ q.c1
  hG : 0 ≤ q.G
  hκ : 1 ≤ q.κ
  hσ : 0 ≤ q.σ
  wstar_mem : wstar ∈ I.domain
  wstar_min : IsMinOn (objective I) I.domain wstar

noncomputable def jointObj (w : q.E) (ν : Fin q.n → ℝ) : ℝ :=
  (q.n : ℝ)⁻¹ * ∑ i, dualObj (I.law i : Measure q.Ξ) (I.score i) w (ν i)

noncomputable def virtualObj (α : ℝ) (w : q.E) (ν : Fin q.n → ℝ) : ℝ :=
  (q.n : ℝ)⁻¹ * ∑ i, ∫ ζ, dualObj (I.law i : Measure q.Ξ) (I.score i) w
    (spmd α (ν i) (I.score i w ζ)) ∂(I.law i : Measure q.Ξ)

noncomputable def virtualGap (α : ℝ) (w : q.E) (ν : Fin q.n → ℝ) : ℝ :=
  (q.n : ℝ)⁻¹ * ∑ i, ∫ ζ, anchorGap (I.law i : Measure q.Ξ) (I.score i) w
    (spmd α (ν i) (I.score i w ζ)) ∂(I.law i : Measure q.Ξ)

noncomputable def meanGrad (α : ℝ) (w : q.E) (ν : Fin q.n → ℝ) : q.E :=
  (q.n : ℝ)⁻¹ • ∑ i, ∫ ζ, gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i) w
    (spmd α (ν i) (I.score i w ζ)) ∂(I.law i : Measure q.Ξ)

noncomputable def dualPot (νstar ν : Fin q.n → ℝ) : ℝ := ∑ i, breg (νstar i) (ν i)

noncomputable def dualNoise (w : q.E) (ν : Fin q.n → ℝ) : ℝ :=
  (q.n : ℝ)⁻¹ * ∑ i, exp (-(ν i)) *
    ∫ ζ, (exp (I.score i w ζ) - mass (I.law i : Measure q.Ξ) (I.score i) w) ^ 2 ∂(I.law i : Measure q.Ξ)

noncomputable def piece (α : ℝ) (w : q.E) (ν : Fin q.n → ℝ) (ω : Seed q) : q.E :=
  exp (I.score ω.1 w (ω.2.2 ω.1) - spmd α (ν ω.1) (I.score ω.1 w (ω.2.1 ω.1))) •
    I.grad ω.1 w (ω.2.2 ω.1)

noncomputable def newDual (α : ℝ) (w : q.E) (ν : Fin q.n → ℝ) (ω : Seed q) : Fin q.n → ℝ :=
  Function.update ν ω.1 (spmd α (ν ω.1) (I.score ω.1 w (ω.2.1 ω.1)))

noncomputable def pieceF (α : ℝ) (w : q.E) (ν : Fin q.n → ℝ) (i : Fin q.n) (y : q.Ξ × q.Ξ) : q.E :=
  exp (-(spmd α (ν i) (I.score i w y.1))) • (exp (I.score i w y.2) • I.grad i w y.2)

noncomputable def nuStar (wstar : q.E) : Fin q.n → ℝ :=
  fun i => log (mass (I.law i : Measure q.Ξ) (I.score i) wstar)

noncomputable def dualRegret (α : ℝ) (w : q.E) (ν νstar : Fin q.n → ℝ) : ℝ :=
  (q.n : ℝ)⁻¹ * ∑ i, ∫ ζ, (1 - mass (I.law i : Measure q.Ξ) (I.score i) w *
    exp (-(spmd α (ν i) (I.score i w ζ)))) * (spmd α (ν i) (I.score i w ζ) - νstar i)
    ∂(I.law i : Measure q.Ξ)


namespace AnchorHyp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
  {s : E → Ξ → ℝ} {g : E → Ξ → E} {W : Set E} {c0 c1 G κ σ : ℝ}
  (h : AnchorHyp μ s g W c0 c1 G κ σ)
include h

lemma exp_neg_virtual_int {x : E} (hx : x ∈ W) {ν α : ℝ} (hα : 0 ≤ α) (hν : ν ∈ Set.Icc c0 c1) :
    Integrable (fun ξ => exp (-(spmd α ν (s x ξ)))) μ := by
  refine h.spmd_int hx hα hν (fun r => exp (-r)) (measurable_exp.comp measurable_neg) (exp (-c0)) ?_
  intro r hr
  rw [abs_of_pos (exp_pos _)]
  exact exp_le_exp.mpr (by linarith [hr.1])

lemma exp_neg_two_virtual_int {x : E} (hx : x ∈ W) {ν α : ℝ} (hα : 0 ≤ α) (hν : ν ∈ Set.Icc c0 c1) :
    Integrable (fun ξ => exp (-(spmd α ν (s x ξ))) ^ 2) μ := by
  refine h.spmd_int hx hα hν (fun r => exp (-r) ^ 2)
    ((measurable_exp.comp measurable_neg).pow_const 2) (exp (-c0) ^ 2) ?_
  intro r hr
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (exp_pos _).le (exp_le_exp.mpr (by linarith [hr.1])) 2

omit [IsProbabilityMeasure μ] h [MeasurableSpace E] in
lemma gradVirt_eq (x : E) (α ν : ℝ) (ξ : Ξ) :
    gradW μ s g x (spmd α ν (s x ξ)) =
      exp (-(spmd α ν (s x ξ))) • ∫ ξ', exp (s x ξ') • g x ξ' ∂μ :=
  AnchorHyp.gradW_eq x _

lemma gradVirt_int {x : E} (hx : x ∈ W) {ν α : ℝ} (hα : 0 ≤ α) (hν : ν ∈ Set.Icc c0 c1) :
    Integrable (fun ξ => gradW μ s g x (spmd α ν (s x ξ))) μ := by
  simp_rw [gradVirt_eq x α ν]
  exact (h.exp_neg_virtual_int hx hα hν).smul_const _

omit [IsProbabilityMeasure μ] h [MeasurableSpace E] in
lemma integral_gradVirt [CompleteSpace E] (x : E) (α ν : ℝ) :
    ∫ ξ, gradW μ s g x (spmd α ν (s x ξ)) ∂μ =
      (∫ ξ, exp (-(spmd α ν (s x ξ))) ∂μ) • ∫ ξ', exp (s x ξ') • g x ξ' ∂μ := by
  simp_rw [gradVirt_eq x α ν]
  exact integral_smul_const _ _

lemma regret_integrand_int {x : E} (hx : x ∈ W) {ν α : ℝ} (hα : 0 ≤ α) (hν : ν ∈ Set.Icc c0 c1)
    {u : ℝ} (_hu : u ∈ Set.Icc c0 c1) :
    Integrable (fun ξ => (1 - mass μ s x * exp (-(spmd α ν (s x ξ)))) *
      (spmd α ν (s x ξ) - u)) μ := by
  refine h.spmd_int hx hα hν (fun r => (1 - mass μ s x * exp (-r)) * (r - u))
    ((measurable_const.sub (measurable_const.mul (measurable_exp.comp measurable_neg))).mul
      (measurable_id.sub measurable_const)) ((1 + exp c1 * exp (-c0)) * (|c0| + |c1| + |u|)) ?_
  intro r hr
  rw [abs_mul]
  have hm := h.mass_bounds hx
  have h1 : |1 - mass μ s x * exp (-r)| ≤ 1 + exp c1 * exp (-c0) := by
    rw [abs_le]
    have := mul_le_mul hm.2 (exp_le_exp.mpr (show -r ≤ -c0 by linarith [hr.1])) (exp_pos _).le
      (exp_pos _).le
    have h0 : 0 ≤ mass μ s x * exp (-r) := mul_nonneg (h.mass_pos hx).le (exp_pos _).le
    constructor <;> linarith
  have h2 : |r - u| ≤ |c0| + |c1| + |u| := by
    calc |r - u| ≤ |r| + |u| := abs_sub _ _
      _ ≤ (|c0| + |c1|) + |u| := by
          have : |r| ≤ |c0| + |c1| := by
            rw [abs_le]; constructor <;> cases abs_cases c0 <;> cases abs_cases c1 <;>
              linarith [hr.1, hr.2]
          linarith
  exact mul_le_mul h1 h2 (abs_nonneg _) (by positivity)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] h in
lemma sq_integral_le_integral_sq {f : Ξ → ℝ} (hf : Measurable f) (hf0 : ∀ ξ, 0 ≤ f ξ)
    (hi : Integrable (fun ξ => f ξ ^ 2) μ) :
    (∫ ξ, f ξ ∂μ) ^ 2 ≤ ∫ ξ, f ξ ^ 2 ∂μ := by
  have h1 : Integrable (fun _ : Ξ => (1 : ℝ) ^ 2) μ := by simp
  have := AnchorHyp.integral_mul_le_sqrt hf measurable_const hf0 (fun _ => zero_le_one) hi h1
  simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul, Real.sqrt_one] at this
  have hnn : 0 ≤ ∫ ξ, f ξ ∂μ := integral_nonneg hf0
  calc (∫ ξ, f ξ ∂μ) ^ 2 ≤ (Real.sqrt (∫ ξ, f ξ ^ 2 ∂μ)) ^ 2 := pow_le_pow_left₀ hnn this 2
    _ = ∫ ξ, f ξ ^ 2 ∂μ := Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)

lemma virtual_second_moment_bounds [BorelSpace E] [SecondCountableTopology E] {x : E} (hx : x ∈ W) {ν α : ℝ} (hα : 0 ≤ α)
    (hν : ν ∈ Set.Icc c0 c1) (hσ : 0 ≤ σ) (_hc : c0 ≤ c1) (_hκ : 0 ≤ κ) (_hG : 0 ≤ G) :
    Integrable (fun y : Ξ × Ξ => ‖exp (s x y.2 - spmd α ν (s x y.1)) • g x y.2‖ ^ 2) (μ.prod μ) ∧
    (∫ y : Ξ × Ξ, ‖exp (s x y.2 - spmd α ν (s x y.1)) • g x y.2‖ ^ 2 ∂(μ.prod μ)) ≤
      2 * exp (c1 - c0) * σ ^ 2 * (1 + ∫ ξ, anchorGap μ s x (spmd α ν (s x ξ)) ∂μ) ∧
    (∫ y : Ξ × Ξ, ‖exp (s x y.2 - spmd α ν (s x y.1)) • g x y.2‖ ^ 2 ∂(μ.prod μ)) ≤
      exp (2 * (c1 - c0)) * G ^ 2 := by
  have hrepr : ∀ y : Ξ × Ξ, ‖exp (s x y.2 - spmd α ν (s x y.1)) • g x y.2‖ ^ 2 =
      exp (-(spmd α ν (s x y.1))) ^ 2 * (exp (2 * s x y.2) * ‖g x y.2‖ ^ 2) := by
    intro y
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _), mul_pow]
    have : exp (s x y.2 - spmd α ν (s x y.1)) ^ 2 =
        exp (-(spmd α ν (s x y.1))) ^ 2 * exp (2 * s x y.2) := by
      rw [sq, sq, ← exp_add, ← exp_add, ← exp_add]; congr 1; ring
    rw [this]; ring
  have hint : Integrable (fun y : Ξ × Ξ => ‖exp (s x y.2 - spmd α ν (s x y.1)) • g x y.2‖ ^ 2)
      (μ.prod μ) := by
    simp_rw [hrepr]
    exact (h.exp_neg_two_virtual_int hx hα hν).mul_prod (h.exp2_grad_sq_int hx)
  refine ⟨hint, ?_, ?_⟩
  · rw [integral_prod _ hint]
    have hpt : ∀ ξ, (∫ ξ', ‖exp (s x ξ' - spmd α ν (s x ξ)) • g x ξ'‖ ^ 2 ∂μ) ≤
        2 * exp (c1 - c0) * σ ^ 2 * (1 + anchorGap μ s x (spmd α ν (s x ξ))) := fun ξ =>
      h.second_moment_gap hx (h.spmd_s_mem hx hα hν ξ).1 hσ
    have hi1 := hint.integral_prod_left
    have hi2 : Integrable (fun ξ => 2 * exp (c1 - c0) * σ ^ 2 *
        (1 + anchorGap μ s x (spmd α ν (s x ξ)))) μ :=
      ((integrable_const _).add (h.gap_virtual_int hx hα hν)).const_mul _
    calc (∫ ξ, ∫ ξ', ‖exp (s x ξ' - spmd α ν (s x ξ)) • g x ξ'‖ ^ 2 ∂μ ∂μ)
        ≤ ∫ ξ, 2 * exp (c1 - c0) * σ ^ 2 * (1 + anchorGap μ s x (spmd α ν (s x ξ))) ∂μ :=
          integral_mono hi1 hi2 hpt
      _ = 2 * exp (c1 - c0) * σ ^ 2 * (1 + ∫ ξ, anchorGap μ s x (spmd α ν (s x ξ)) ∂μ) := by
          rw [integral_const_mul, integral_add (integrable_const _) (h.gap_virtual_int hx hα hν)]
          simp
  · rw [integral_prod _ hint]
    have hpt : ∀ ξ, (∫ ξ', ‖exp (s x ξ' - spmd α ν (s x ξ)) • g x ξ'‖ ^ 2 ∂μ) ≤
        exp (2 * (c1 - c0)) * G ^ 2 := fun ξ =>
      h.second_moment_le_G hx (h.spmd_s_mem hx hα hν ξ).1
    calc (∫ ξ, ∫ ξ', ‖exp (s x ξ' - spmd α ν (s x ξ)) • g x ξ'‖ ^ 2 ∂μ ∂μ)
        ≤ ∫ _ξ, exp (2 * (c1 - c0)) * G ^ 2 ∂μ :=
          integral_mono hint.integral_prod_left (integrable_const _) hpt
      _ = exp (2 * (c1 - c0)) * G ^ 2 := by simp

lemma virtual_grad_sq_le [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] {x : E} (hx : x ∈ W) {ν α : ℝ} (hα : 0 ≤ α) (hν : ν ∈ Set.Icc c0 c1)
    (hc : c0 ≤ c1) (hκ : 0 ≤ κ) (hG : 0 ≤ G) :
    ‖∫ ξ, gradW μ s g x (spmd α ν (s x ξ)) ∂μ‖ ^ 2 ≤
      2 * κ * G ^ 2 + 4 * exp (c1 - c0) * κ * G ^ 2 *
        ∫ ξ, anchorGap μ s x (spmd α ν (s x ξ)) ∂μ := by
  rw [integral_gradVirt x α ν, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg fun _ => (exp_pos _).le), mul_pow]
  have hj := sq_integral_le_integral_sq (f := fun ξ => exp (-(spmd α ν (s x ξ))))
    (measurable_exp.comp ((h.meas_spmd ν α).neg)) (fun _ => (exp_pos _).le)
    (h.exp_neg_two_virtual_int hx hα hν)
  have hC : 0 ≤ ‖∫ ξ', exp (s x ξ') • g x ξ' ∂μ‖ ^ 2 := sq_nonneg _
  have hsq : (∫ ξ, exp (-(spmd α ν (s x ξ))) ∂μ) ^ 2 * ‖∫ ξ', exp (s x ξ') • g x ξ' ∂μ‖ ^ 2 ≤
      ∫ ξ, ‖gradW μ s g x (spmd α ν (s x ξ))‖ ^ 2 ∂μ := by
    have heq : (fun ξ => ‖gradW μ s g x (spmd α ν (s x ξ))‖ ^ 2) =
        fun ξ => exp (-(spmd α ν (s x ξ))) ^ 2 * ‖∫ ξ', exp (s x ξ') • g x ξ' ∂μ‖ ^ 2 := by
      funext ξ
      rw [gradVirt_eq x α ν, norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _), mul_pow]
    rw [heq, integral_mul_const]
    exact mul_le_mul_of_nonneg_right hj hC
  have hpt : ∀ ξ, ‖gradW μ s g x (spmd α ν (s x ξ))‖ ^ 2 ≤
      2 * κ * G ^ 2 + 4 * exp (c1 - c0) * κ * G ^ 2 * anchorGap μ s x (spmd α ν (s x ξ)) :=
    fun ξ => h.gradW_sq_bound hx (h.spmd_s_mem hx hα hν ξ).1 hc hκ hG
  have hi1 : Integrable (fun ξ => ‖gradW μ s g x (spmd α ν (s x ξ))‖ ^ 2) μ := by
    have heq : (fun ξ => ‖gradW μ s g x (spmd α ν (s x ξ))‖ ^ 2) =
        fun ξ => exp (-(spmd α ν (s x ξ))) ^ 2 * ‖∫ ξ', exp (s x ξ') • g x ξ' ∂μ‖ ^ 2 := by
      funext ξ
      rw [gradVirt_eq x α ν, norm_smul, Real.norm_eq_abs, abs_of_pos (exp_pos _), mul_pow]
    rw [heq]; exact (h.exp_neg_two_virtual_int hx hα hν).mul_const _
  have hi2 : Integrable (fun ξ => 2 * κ * G ^ 2 + 4 * exp (c1 - c0) * κ * G ^ 2 *
      anchorGap μ s x (spmd α ν (s x ξ))) μ :=
    (integrable_const _).add ((h.gap_virtual_int hx hα hν).const_mul _)
  calc (∫ ξ, exp (-(spmd α ν (s x ξ))) ∂μ) ^ 2 * ‖∫ ξ', exp (s x ξ') • g x ξ' ∂μ‖ ^ 2
      ≤ ∫ ξ, ‖gradW μ s g x (spmd α ν (s x ξ))‖ ^ 2 ∂μ := hsq
    _ ≤ ∫ ξ, (2 * κ * G ^ 2 + 4 * exp (c1 - c0) * κ * G ^ 2 *
        anchorGap μ s x (spmd α ν (s x ξ))) ∂μ := integral_mono hi1 hi2 hpt
    _ = _ := by
        rw [integral_add (integrable_const _) ((h.gap_virtual_int hx hα hν).const_mul _),
          integral_const, integral_const_mul]
        simp

end AnchorHyp

namespace SysHyp

variable {I} {projection : q.E → q.E} {wstar : q.E} (h : SysHyp I projection wstar)
include h

omit h in
lemma n_pos : (0 : ℝ) < q.n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q.n)

lemma nuStar_mem (i : Fin q.n) : nuStar I wstar i ∈ Set.Icc q.c0 q.c1 :=
  (h.anchor i).log_mass_mem h.wstar_mem

omit h in
lemma objective_eq (w : q.E) :
    objective I w = (q.n : ℝ)⁻¹ * ∑ i, log (mass (I.law i : Measure q.Ξ) (I.score i) w) := rfl

omit h in
lemma sum_const_one : (q.n : ℝ)⁻¹ * ∑ _i : Fin q.n, (1 : ℝ) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast NeZero.ne q.n)

lemma fstar_eq : jointObj I wstar (nuStar I wstar) = 1 + objective I wstar := by
  unfold jointObj nuStar dualObj
  rw [objective_eq]
  have hone : ∀ i, mass (I.law i : Measure q.Ξ) (I.score i) wstar *
      exp (-(log (mass (I.law i : Measure q.Ξ) (I.score i) wstar))) = 1 := by
    intro i
    rw [exp_neg, exp_log ((h.anchor i).mass_pos h.wstar_mem),
      mul_inv_cancel₀ ((h.anchor i).mass_pos h.wstar_mem).ne']
  simp only [hone]
  rw [Finset.sum_add_distrib, mul_add, sum_const_one (q := q)]

lemma dualObj_int {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : Fin q.n → ℝ}
    (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) (i : Fin q.n) :
    Integrable (fun ζ => dualObj (I.law i : Measure q.Ξ) (I.score i) w
      (spmd α (ν i) (I.score i w ζ))) (I.law i : Measure q.Ξ) := by
  have hA := h.anchor i
  refine hA.spmd_int hw hα (hν i) (fun r => dualObj (I.law i : Measure q.Ξ) (I.score i) w r)
    ?_ (exp q.c1 * exp (-q.c0) + (|q.c0| + |q.c1|)) ?_
  · unfold dualObj
    exact (measurable_const.mul (measurable_exp.comp measurable_neg)).add measurable_id
  · intro r hr
    unfold dualObj
    have hm := hA.mass_bounds hw
    have h1 : 0 ≤ mass (I.law i : Measure q.Ξ) (I.score i) w * exp (-r) :=
      mul_nonneg (hA.mass_pos hw).le (exp_pos _).le
    have h2 : mass (I.law i : Measure q.Ξ) (I.score i) w * exp (-r) ≤ exp q.c1 * exp (-q.c0) :=
      mul_le_mul hm.2 (exp_le_exp.mpr (by linarith [hr.1])) (exp_pos _).le (exp_pos _).le
    have h3 : |r| ≤ |q.c0| + |q.c1| := by
      rw [abs_le]; constructor <;> cases abs_cases q.c0 <;> cases abs_cases q.c1 <;>
        linarith [hr.1, hr.2]
    calc |mass (I.law i : Measure q.Ξ) (I.score i) w * exp (-r) + r|
        ≤ |mass (I.law i : Measure q.Ξ) (I.score i) w * exp (-r)| + |r| := abs_add_le _ _
      _ ≤ exp q.c1 * exp (-q.c0) + (|q.c0| + |q.c1|) := by
          rw [abs_of_nonneg h1]; exact add_le_add h2 h3

lemma gap_int_eq {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : Fin q.n → ℝ}
    (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) (i : Fin q.n) :
    ∫ ζ, anchorGap (I.law i : Measure q.Ξ) (I.score i) w (spmd α (ν i) (I.score i w ζ))
      ∂(I.law i : Measure q.Ξ) =
    (∫ ζ, dualObj (I.law i : Measure q.Ξ) (I.score i) w (spmd α (ν i) (I.score i w ζ))
      ∂(I.law i : Measure q.Ξ)) - (1 + log (mass (I.law i : Measure q.Ξ) (I.score i) w)) := by
  have hA := h.anchor i
  rw [show (1 + log (mass (I.law i : Measure q.Ξ) (I.score i) w)) =
      ∫ _ζ, (1 + log (mass (I.law i : Measure q.Ξ) (I.score i) w)) ∂(I.law i : Measure q.Ξ) by simp]
  rw [← integral_sub (h.dualObj_int hw hα hν i) (integrable_const _)]
  congr 1
  funext ζ
  rw [← hA.gap_eq hw (spmd α (ν i) (I.score i w ζ))]
  congr 1
  unfold dualObj
  rw [exp_neg, exp_log (hA.mass_pos hw), mul_inv_cancel₀ (hA.mass_pos hw).ne']

lemma virtualGap_eq {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : Fin q.n → ℝ}
    (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) :
    virtualGap I α w ν = virtualObj I α w ν - (1 + objective I w) := by
  unfold virtualGap virtualObj
  rw [objective_eq]
  have hsum : ∑ i, ∫ ζ, anchorGap (I.law i : Measure q.Ξ) (I.score i) w
      (spmd α (ν i) (I.score i w ζ)) ∂(I.law i : Measure q.Ξ) =
      ∑ i, ((∫ ζ, dualObj (I.law i : Measure q.Ξ) (I.score i) w (spmd α (ν i) (I.score i w ζ))
        ∂(I.law i : Measure q.Ξ)) - (1 + log (mass (I.law i : Measure q.Ξ) (I.score i) w))) :=
    Finset.sum_congr rfl fun i _ => h.gap_int_eq hw hα hν i
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hn : (q.n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q.n
  rw [mul_sub, mul_add, inv_mul_cancel₀ hn]

lemma one_add_objective_ge {w : q.E} (hw : w ∈ I.domain) :
    jointObj I wstar (nuStar I wstar) ≤ 1 + objective I w := by
  rw [h.fstar_eq]
  have : objective I wstar ≤ objective I w := h.wstar_min hw
  linarith

lemma virtualGap_le {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : Fin q.n → ℝ}
    (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) :
    virtualGap I α w ν ≤ virtualObj I α w ν - jointObj I wstar (nuStar I wstar) := by
  rw [h.virtualGap_eq hw hα hν]
  linarith [h.one_add_objective_ge hw]

omit h in
lemma virtualGap_nonneg (α : ℝ) (w : q.E) (ν : Fin q.n → ℝ) : 0 ≤ virtualGap I α w ν := by
  unfold virtualGap
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_nonneg
  intro i _
  exact integral_nonneg fun ζ => psi_nonneg _


omit h in
lemma breg_bounded {u : ℝ} (hu : u ∈ Set.Icc q.c0 q.c1) {r : ℝ} (hr : r ∈ Set.Icc q.c0 q.c1) :
    |breg u r| ≤ 3 * exp (-q.c0) * (1 + |q.c0| + |q.c1|) := by
  unfold breg
  have h1 : exp (-r) ≤ exp (-q.c0) := exp_le_exp.mpr (by linarith [hr.1])
  have h2 : exp (-u) ≤ exp (-q.c0) := exp_le_exp.mpr (by linarith [hu.1])
  have h3 : |u - r| ≤ |q.c0| + |q.c1| := by
    rw [abs_le]; constructor <;> cases abs_cases q.c0 <;> cases abs_cases q.c1 <;>
      linarith [hr.1, hr.2, hu.1, hu.2]
  have h4 : |exp (-r) * (u - r)| ≤ exp (-q.c0) * (|q.c0| + |q.c1|) := by
    rw [abs_mul, abs_of_pos (exp_pos _)]
    exact mul_le_mul h1 h3 (abs_nonneg _) (exp_pos _).le
  have h5 : |exp (-u) - exp (-r)| ≤ exp (-q.c0) + exp (-q.c0) := by
    rw [abs_le]; constructor <;> linarith [exp_pos (-u), exp_pos (-r)]
  calc |exp (-u) - exp (-r) + exp (-r) * (u - r)|
      ≤ |exp (-u) - exp (-r)| + |exp (-r) * (u - r)| := abs_add_le _ _
    _ ≤ (exp (-q.c0) + exp (-q.c0)) + exp (-q.c0) * (|q.c0| + |q.c1|) := add_le_add h5 h4
    _ ≤ 3 * exp (-q.c0) * (1 + |q.c0| + |q.c1|) := by
        nlinarith [exp_pos (-q.c0), abs_nonneg q.c0, abs_nonneg q.c1]

lemma breg_virtual_int {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : Fin q.n → ℝ}
    (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) {u : ℝ} (hu : u ∈ Set.Icc q.c0 q.c1) (i : Fin q.n) :
    Integrable (fun ζ => breg u (spmd α (ν i) (I.score i w ζ))) (I.law i : Measure q.Ξ) := by
  refine (h.anchor i).spmd_int hw hα (hν i) (fun r => breg u r) ?_
    (3 * exp (-q.c0) * (1 + |q.c0| + |q.c1|)) ?_
  · unfold breg
    exact ((measurable_const.sub (measurable_exp.comp measurable_neg)).add
      ((measurable_exp.comp measurable_neg).mul (measurable_const.sub measurable_id)))
  · intro r hr; exact breg_bounded hu hr

omit h in
lemma dualPot_update (νstar ν : Fin q.n → ℝ) (i : Fin q.n) (v : ℝ) :
    dualPot νstar (Function.update ν i v) =
      dualPot νstar ν + (breg (νstar i) v - breg (νstar i) (ν i)) := by
  unfold dualPot
  have hpt : ∀ j, breg (νstar j) (Function.update ν i v j) =
      breg (νstar j) (ν j) + if j = i then breg (νstar i) v - breg (νstar i) (ν i) else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i]
  simp

lemma meas_breg_virtual (w : q.E) (α : ℝ) (ν : Fin q.n → ℝ) (u : ℝ) (i : Fin q.n) :
    Measurable (fun ζ => breg u (spmd α (ν i) (I.score i w ζ))) := by
  have hm := (h.anchor i).meas_spmd (x := w) (ν i) α
  unfold breg
  exact ((measurable_const.sub (measurable_exp.comp hm.neg)).add
    ((measurable_exp.comp hm.neg).mul (measurable_const.sub hm)))

lemma expected_dualPot {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : Fin q.n → ℝ}
    (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) :
    ∫ ω, dualPot (nuStar I wstar) (newDual I α w ν ω) ∂(sampleLaw I) =
      dualPot (nuStar I wstar) ν - (q.n : ℝ)⁻¹ * ∑ i, (breg (nuStar I wstar i) (ν i) -
        ∫ ζ, breg (nuStar I wstar i) (spmd α (ν i) (I.score i w ζ)) ∂(I.law i : Measure q.Ξ)) := by
  set F : Fin q.n → q.Ξ × q.Ξ → ℝ := fun i y => dualPot (nuStar I wstar) ν +
    (breg (nuStar I wstar i) (spmd α (ν i) (I.score i w y.1)) - breg (nuStar I wstar i) (ν i)) with hFdef
  have hF : ∀ ω : Seed q, dualPot (nuStar I wstar) (newDual I α w ν ω) = F ω.1 (ω.2.1 ω.1, ω.2.2 ω.1) := by
    intro ω; unfold newDual; rw [dualPot_update]
  have hmeas : ∀ i, Measurable (F i) := fun i =>
    measurable_const.add (((h.meas_breg_virtual w α ν (nuStar I wstar i) i).comp measurable_fst).sub
      measurable_const)
  have hint : ∀ i, Integrable (F i) ((I.law i : Measure q.Ξ).prod (I.law i)) := fun i =>
    (integrable_const _).add ((integrable_fst_real (h.breg_virtual_int hw hα hν (h.nuStar_mem i) i)).sub
      (integrable_const _))
  simp_rw [hF]
  rw [mixture_integral I F hmeas hint]
  have hsum : ∀ i, (∫ y, F i y ∂((I.law i : Measure q.Ξ).prod (I.law i))) =
      dualPot (nuStar I wstar) ν - (breg (nuStar I wstar i) (ν i) -
        ∫ ζ, breg (nuStar I wstar i) (spmd α (ν i) (I.score i w ζ)) ∂(I.law i : Measure q.Ξ)) := by
    intro i
    have hb := h.breg_virtual_int hw hα hν (h.nuStar_mem i) i
    have hb2 : Integrable (fun y : q.Ξ × q.Ξ => breg (nuStar I wstar i)
        (spmd α (ν i) (I.score i w y.1)) - breg (nuStar I wstar i) (ν i))
        ((I.law i : Measure q.Ξ).prod (I.law i)) := (integrable_fst_real hb).sub (integrable_const _)
    rw [hFdef]
    simp only
    rw [integral_add (integrable_const _) hb2,
      integral_sub (integrable_fst_real hb) (integrable_const _), integral_const, integral_const]
    have hfst : ∫ y : q.Ξ × q.Ξ, breg (nuStar I wstar i) (spmd α (ν i) (I.score i w y.1))
        ∂((I.law i : Measure q.Ξ).prod (I.law i)) =
        ∫ ζ, breg (nuStar I wstar i) (spmd α (ν i) (I.score i w ζ)) ∂(I.law i : Measure q.Ξ) := by
      have := integral_fun_fst (μ := (I.law i : Measure q.Ξ)) (ν := (I.law i : Measure q.Ξ))
        (fun ζ => breg (nuStar I wstar i) (spmd α (ν i) (I.score i w ζ)))
      simpa [probReal_univ] using this
    rw [hfst]
    simp only [probReal_univ, smul_eq_mul]
    ring
  simp_rw [hsum]
  rw [Finset.sum_sub_distrib, smul_eq_mul, mul_sub, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ ((n_pos (q := q)).ne'), one_mul]

lemma dual_regret_bound {w : q.E} (hw : w ∈ I.domain) {α ρ : ℝ} (hα : 0 ≤ α)
    (hρ : α * exp q.c1 ≤ ρ) {ν : Fin q.n → ℝ} (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) :
    α * dualRegret I α w ν (nuStar I wstar) ≤
      dualPot (nuStar I wstar) ν - (∫ ω, dualPot (nuStar I wstar) (newDual I α w ν ω) ∂(sampleLaw I)) +
        (1 + ρ) * (1 + (q.c1 - q.c0)) * α ^ 2 * dualNoise I w ν := by
  rw [h.expected_dualPot hw hα hν]
  unfold dualRegret dualNoise
  have hper : ∀ i, α * ∫ ζ, (1 - mass (I.law i : Measure q.Ξ) (I.score i) w *
      exp (-(spmd α (ν i) (I.score i w ζ)))) * (spmd α (ν i) (I.score i w ζ) - nuStar I wstar i)
      ∂(I.law i : Measure q.Ξ) ≤
      (breg (nuStar I wstar i) (ν i) - ∫ ζ, breg (nuStar I wstar i) (spmd α (ν i) (I.score i w ζ))
        ∂(I.law i : Measure q.Ξ)) +
      (1 + ρ) * (1 + (q.c1 - q.c0)) * α ^ 2 * (exp (-(ν i)) *
        ∫ ζ, (exp (I.score i w ζ) - mass (I.law i : Measure q.Ξ) (I.score i) w) ^ 2
          ∂(I.law i : Measure q.Ξ)) := by
    intro i
    have := (h.anchor i).anchor_regret hw (hν i) (h.nuStar_mem i) hα hρ
    linarith [this]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hper i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hn : 0 ≤ (q.n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have := mul_le_mul_of_nonneg_left hsum hn
  calc α * ((q.n : ℝ)⁻¹ * ∑ i, ∫ ζ, (1 - mass (I.law i : Measure q.Ξ) (I.score i) w *
        exp (-(spmd α (ν i) (I.score i w ζ)))) * (spmd α (ν i) (I.score i w ζ) - nuStar I wstar i)
        ∂(I.law i : Measure q.Ξ))
      = (q.n : ℝ)⁻¹ * (α * ∑ i, ∫ ζ, (1 - mass (I.law i : Measure q.Ξ) (I.score i) w *
        exp (-(spmd α (ν i) (I.score i w ζ)))) * (spmd α (ν i) (I.score i w ζ) - nuStar I wstar i)
        ∂(I.law i : Measure q.Ξ)) := by ring
    _ ≤ (q.n : ℝ)⁻¹ * (∑ i, (breg (nuStar I wstar i) (ν i) -
        ∫ ζ, breg (nuStar I wstar i) (spmd α (ν i) (I.score i w ζ)) ∂(I.law i : Measure q.Ξ)) +
        (1 + ρ) * (1 + (q.c1 - q.c0)) * α ^ 2 * ∑ i, exp (-(ν i)) *
        ∫ ζ, (exp (I.score i w ζ) - mass (I.law i : Measure q.Ξ) (I.score i) w) ^ 2
          ∂(I.law i : Measure q.Ξ)) := this
    _ = _ := by ring

lemma dualNoise_le {w : q.E} (hw : w ∈ I.domain) {α ρ : ℝ} (hα : 0 ≤ α)
    (hρ : α * exp q.c1 ≤ ρ) {ν : Fin q.n → ℝ} (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) :
    dualNoise I w ν ≤ 2 * (1 + ρ) * (q.κ - 1) * exp q.c1 * (1 + virtualGap I α w ν) := by
  unfold dualNoise virtualGap
  have hper : ∀ i, exp (-(ν i)) * ∫ ζ, (exp (I.score i w ζ) - mass (I.law i : Measure q.Ξ)
      (I.score i) w) ^ 2 ∂(I.law i : Measure q.Ξ) ≤
      2 * (1 + ρ) * (q.κ - 1) * exp q.c1 * (1 + ∫ ζ, anchorGap (I.law i : Measure q.Ξ) (I.score i) w
        (spmd α (ν i) (I.score i w ζ)) ∂(I.law i : Measure q.Ξ)) := by
    intro i
    have := (h.anchor i).virtual_variance_bound hw hα (hν i) hρ h.hκ
    rw [integral_add (integrable_const _) ((h.anchor i).gap_virtual_int hw hα (hν i))] at this
    simp only [integral_const, probReal_univ, one_smul] at this
    exact this
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hper i
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  have hn : 0 ≤ (q.n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  calc (q.n : ℝ)⁻¹ * ∑ i, exp (-(ν i)) * ∫ ζ, (exp (I.score i w ζ) -
        mass (I.law i : Measure q.Ξ) (I.score i) w) ^ 2 ∂(I.law i : Measure q.Ξ)
      ≤ (q.n : ℝ)⁻¹ * (2 * (1 + ρ) * (q.κ - 1) * exp q.c1 * ((q.n : ℝ) + ∑ i, ∫ ζ,
        anchorGap (I.law i : Measure q.Ξ) (I.score i) w (spmd α (ν i) (I.score i w ζ))
        ∂(I.law i : Measure q.Ξ))) := mul_le_mul_of_nonneg_left hsum hn
    _ = 2 * (1 + ρ) * (q.κ - 1) * exp q.c1 * ((q.n : ℝ)⁻¹ * (q.n : ℝ) + (q.n : ℝ)⁻¹ * ∑ i, ∫ ζ,
        anchorGap (I.law i : Measure q.Ξ) (I.score i) w (spmd α (ν i) (I.score i w ζ))
        ∂(I.law i : Measure q.Ξ)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (n_pos (q := q)).ne']


lemma virtual_joint_convex {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : Fin q.n → ℝ}
    (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) :
    virtualObj I α w ν - jointObj I wstar (nuStar I wstar) ≤
      ⟪meanGrad I α w ν, w - wstar⟫ + dualRegret I α w ν (nuStar I wstar) := by
  unfold virtualObj jointObj meanGrad dualRegret
  have hper : ∀ i, (∫ ζ, dualObj (I.law i : Measure q.Ξ) (I.score i) w
      (spmd α (ν i) (I.score i w ζ)) ∂(I.law i : Measure q.Ξ)) -
      dualObj (I.law i : Measure q.Ξ) (I.score i) wstar (nuStar I wstar i) ≤
      ⟪w - wstar, ∫ ζ, gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i) w
        (spmd α (ν i) (I.score i w ζ)) ∂(I.law i : Measure q.Ξ)⟫ +
      ∫ ζ, (1 - mass (I.law i : Measure q.Ξ) (I.score i) w * exp (-(spmd α (ν i) (I.score i w ζ)))) *
        (spmd α (ν i) (I.score i w ζ) - nuStar I wstar i) ∂(I.law i : Measure q.Ξ) := by
    intro i
    have hA := h.anchor i
    have hpt : ∀ ζ, dualObj (I.law i : Measure q.Ξ) (I.score i) w (spmd α (ν i) (I.score i w ζ)) -
        dualObj (I.law i : Measure q.Ξ) (I.score i) wstar (nuStar I wstar i) ≤
        ⟪w - wstar, gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i) w (spmd α (ν i) (I.score i w ζ))⟫ +
        (1 - mass (I.law i : Measure q.Ξ) (I.score i) w * exp (-(spmd α (ν i) (I.score i w ζ)))) *
          (spmd α (ν i) (I.score i w ζ) - nuStar I wstar i) := by
      intro ζ
      have := hA.joint_convex hw h.wstar_mem (spmd α (ν i) (I.score i w ζ)) (nuStar I wstar i)
      have hinner : ⟪gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i) w
          (spmd α (ν i) (I.score i w ζ)), wstar - w⟫ =
          -⟪w - wstar, gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i) w
            (spmd α (ν i) (I.score i w ζ))⟫ := by
        rw [real_inner_comm, ← inner_neg_left, neg_sub]
      rw [hinner] at this
      nlinarith [this]
    have hi_obj := h.dualObj_int hw hα hν i
    have hi_grad : Integrable (fun ζ => ⟪w - wstar, gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i) w
        (spmd α (ν i) (I.score i w ζ))⟫) (I.law i : Measure q.Ξ) :=
      Integrable.const_inner (𝕜 := ℝ) (w - wstar) (hA.gradVirt_int hw hα (hν i))
    have hi_reg := hA.regret_integrand_int hw hα (hν i) (h.nuStar_mem i)
    have hi_lhs : Integrable (fun ζ => dualObj (I.law i : Measure q.Ξ) (I.score i) w
        (spmd α (ν i) (I.score i w ζ)) - dualObj (I.law i : Measure q.Ξ) (I.score i) wstar
        (nuStar I wstar i)) (I.law i : Measure q.Ξ) := hi_obj.sub (integrable_const _)
    have hi_rhs : Integrable (fun ζ => ⟪w - wstar, gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i) w
        (spmd α (ν i) (I.score i w ζ))⟫ +
        (1 - mass (I.law i : Measure q.Ξ) (I.score i) w * exp (-(spmd α (ν i) (I.score i w ζ)))) *
          (spmd α (ν i) (I.score i w ζ) - nuStar I wstar i)) (I.law i : Measure q.Ξ) :=
      hi_grad.add hi_reg
    have := integral_mono hi_lhs hi_rhs hpt
    rw [integral_sub hi_obj (integrable_const _), integral_add hi_grad hi_reg, integral_const,
      probReal_univ, one_smul, integral_inner (hA.gradVirt_int hw hα (hν i))] at this
    exact this
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hper i
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← inner_sum] at hsum
  have hn : 0 ≤ (q.n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have := mul_le_mul_of_nonneg_left hsum hn
  rw [mul_sub, mul_add, ← real_inner_smul_right, real_inner_comm] at this
  exact this

omit h in
lemma piece_repr (α : ℝ) (w : q.E) (ν : Fin q.n → ℝ) :
    piece I α w ν = fun ω : Seed q => pieceF I α w ν ω.1 (ω.2.1 ω.1, ω.2.2 ω.1) := by
  funext ω
  unfold piece pieceF
  rw [smul_smul, ← exp_add]
  congr 2
  ring

lemma piece_meas (α : ℝ) (w : q.E) (ν : Fin q.n → ℝ) (i : Fin q.n) :
    Measurable (pieceF I α w ν i) := by
  have hA := h.anchor i
  unfold pieceF
  exact ((measurable_exp.comp ((hA.meas_spmd (x := w) (ν i) α).comp measurable_fst).neg)).smul
    (((measurable_exp.comp ((hA.meas_s_x w).comp measurable_snd))).smul
      ((hA.meas_g_x w).comp measurable_snd))

lemma piece_prod_int {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : Fin q.n → ℝ}
    (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) (i : Fin q.n) :
    Integrable (pieceF I α w ν i) ((I.law i : Measure q.Ξ).prod (I.law i)) := by
  have hA := h.anchor i
  have hg : Integrable (fun ζ => exp (I.score i w ζ) • I.grad i w ζ) (I.law i : Measure q.Ξ) := by
    simpa using hA.weighted_grad_int hw 0
  unfold pieceF
  exact (hA.exp_neg_virtual_int hw hα (hν i)).smul_prod hg

lemma piece_int {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : Fin q.n → ℝ}
    (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) :
    Integrable (piece I α w ν) (sampleLaw I) := by
  rw [piece_repr]
  exact mixture_integrable I _ (h.piece_meas α w ν) (h.piece_prod_int hw hα hν)

lemma expected_piece {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : Fin q.n → ℝ}
    (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) :
    ∫ ω, piece I α w ν ω ∂(sampleLaw I) = meanGrad I α w ν := by
  rw [piece_repr, mixture_integral I _ (h.piece_meas α w ν) (h.piece_prod_int hw hα hν)]
  unfold meanGrad
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hA := h.anchor i
  unfold pieceF
  have := integral_prod_smul (μ := (I.law i : Measure q.Ξ)) (ν := (I.law i : Measure q.Ξ))
    (fun ζ => exp (-(spmd α (ν i) (I.score i w ζ)))) (fun ζ' => exp (I.score i w ζ') • I.grad i w ζ')
  rw [this, AnchorHyp.integral_gradVirt w α (ν i)]

lemma expected_piece_sq {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : Fin q.n → ℝ}
    (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) :
    Integrable (fun ω => ‖piece I α w ν ω‖ ^ 2) (sampleLaw I) ∧
    (∫ ω, ‖piece I α w ν ω‖ ^ 2 ∂(sampleLaw I)) ≤
      2 * exp (q.c1 - q.c0) * q.σ ^ 2 * (1 + virtualGap I α w ν) ∧
    (∫ ω, ‖piece I α w ν ω‖ ^ 2 ∂(sampleLaw I)) ≤ exp (2 * (q.c1 - q.c0)) * q.G ^ 2 := by
  have hrepr : ∀ ω : Seed q, ‖piece I α w ν ω‖ ^ 2 = (fun i (y : q.Ξ × q.Ξ) =>
      ‖exp (I.score i w y.2 - spmd α (ν i) (I.score i w y.1)) • I.grad i w y.2‖ ^ 2)
        ω.1 (ω.2.1 ω.1, ω.2.2 ω.1) := fun ω => rfl
  have hmeas : ∀ i, Measurable (fun y : q.Ξ × q.Ξ =>
      ‖exp (I.score i w y.2 - spmd α (ν i) (I.score i w y.1)) • I.grad i w y.2‖ ^ 2) := by
    intro i
    have hA := h.anchor i
    exact (((measurable_exp.comp (((hA.meas_s_x w).comp measurable_snd).sub
      ((hA.meas_spmd (x := w) (ν i) α).comp measurable_fst))).smul
      ((hA.meas_g_x w).comp measurable_snd)).norm.pow_const 2)
  have hb := fun i => (h.anchor i).virtual_second_moment_bounds hw hα (hν i) h.hσ h.hc
    (by linarith [h.hκ]) h.hG
  simp_rw [hrepr]
  refine ⟨mixture_integrable I _ hmeas (fun i => (hb i).1), ?_, ?_⟩
  · rw [mixture_integral I _ hmeas (fun i => (hb i).1)]
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hb i).2.1
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
    have hn : 0 ≤ (q.n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have := mul_le_mul_of_nonneg_left hsum hn
    rw [smul_eq_mul]
    unfold virtualGap
    calc _ ≤ _ := this
      _ = 2 * exp (q.c1 - q.c0) * q.σ ^ 2 * ((q.n : ℝ)⁻¹ * (q.n : ℝ) + (q.n : ℝ)⁻¹ * ∑ i, ∫ ζ,
          anchorGap (I.law i : Measure q.Ξ) (I.score i) w (spmd α (ν i) (I.score i w ζ))
          ∂(I.law i : Measure q.Ξ)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ (n_pos (q := q)).ne']
  · rw [mixture_integral I _ hmeas (fun i => (hb i).1)]
    have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (hb i).2.2
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hn : 0 ≤ (q.n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have := mul_le_mul_of_nonneg_left hsum hn
    rw [smul_eq_mul]
    calc _ ≤ _ := this
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (n_pos (q := q)).ne', one_mul]

lemma meanGrad_sq_le {w : q.E} (hw : w ∈ I.domain) {α : ℝ} (hα : 0 ≤ α) {ν : Fin q.n → ℝ}
    (hν : ∀ i, ν i ∈ Set.Icc q.c0 q.c1) :
    ‖meanGrad I α w ν‖ ^ 2 ≤ 2 * q.κ * q.G ^ 2 +
      4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 * virtualGap I α w ν := by
  unfold meanGrad virtualGap
  set v : Fin q.n → q.E := fun i => ∫ ζ, gradW (I.law i : Measure q.Ξ) (I.score i) (I.grad i) w
    (spmd α (ν i) (I.score i w ζ)) ∂(I.law i : Measure q.Ξ) with hv
  have hper : ∀ i, ‖v i‖ ^ 2 ≤ 2 * q.κ * q.G ^ 2 + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 *
      ∫ ζ, anchorGap (I.law i : Measure q.Ξ) (I.score i) w (spmd α (ν i) (I.score i w ζ))
        ∂(I.law i : Measure q.Ξ) := fun i =>
    (h.anchor i).virtual_grad_sq_le hw hα (hν i) h.hc (by linarith [h.hκ]) h.hG
  have hjensen : ‖(q.n : ℝ)⁻¹ • ∑ i, v i‖ ^ 2 ≤ (q.n : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)), mul_pow]
    have h1 : ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    have h2 : (∑ i, ‖v i‖) ^ 2 ≤ (Finset.univ : Finset (Fin q.n)).card * ∑ i, ‖v i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    rw [Finset.card_univ, Fintype.card_fin] at h2
    have hn := (n_pos (q := q))
    calc ((q.n : ℝ)⁻¹) ^ 2 * ‖∑ i, v i‖ ^ 2 ≤ ((q.n : ℝ)⁻¹) ^ 2 * ((q.n : ℝ) * ∑ i, ‖v i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (sq_nonneg _)
      _ = (q.n : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 := by field_simp
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hper i
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum] at hsum
  have hn : 0 ≤ (q.n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  calc ‖(q.n : ℝ)⁻¹ • ∑ i, v i‖ ^ 2 ≤ (q.n : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 := hjensen
    _ ≤ (q.n : ℝ)⁻¹ * ((q.n : ℝ) * (2 * q.κ * q.G ^ 2) + 4 * exp (q.c1 - q.c0) * q.κ * q.G ^ 2 *
        ∑ i, ∫ ζ, anchorGap (I.law i : Measure q.Ξ) (I.score i) w (spmd α (ν i) (I.score i w ζ))
          ∂(I.law i : Measure q.Ξ)) := mul_le_mul_of_nonneg_left hsum hn
    _ = _ := by
        rw [mul_add, ← mul_assoc, inv_mul_cancel₀ (n_pos (q := q)).ne', one_mul]
        ring

end SysHyp

end OracleTemplate.Scent
