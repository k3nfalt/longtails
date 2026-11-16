import LongTails.Proofs.ManyConstraintRegularity

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintExpected

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintPenalty
  LongTails.Proofs.ManyConstraintFinite LongTails.Proofs.ManyConstraintStochastic
  LongTails.Proofs.ManyConstraintStep LongTails.Proofs.ManyConstraintBall
  LongTails.Proofs.ManyConstraintCoupling LongTails.Proofs.ManyConstraintNoise
  LongTails.Proofs.ManyConstraintRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {m : ℕ} [NeZero m]
variable {law : Measure Ξ} {loss : Ξ → E → ℝ} {grad : Ξ → E → E} {L σ : ℝ} {xs : E}
  {K : Fin m → Set E} {P : Fin m → E → E}

noncomputable def stepY (grad : Ξ → E → E) (β : ℝ) (P : Fin m → E → E) (L μ ρ τ : ℝ) (x0 s y z : E)
    {b : ℕ} (j : Fin m) (ω : Fin b → Ξ) : E :=
  proxBall μ x0 ρ (1 / (3 * (L + β))) (mix τ s y z)
    (batch grad ω (mix τ s y z) + hest β P s (mix τ s y z) j)

noncomputable def stepZ (grad : Ξ → E → E) (β : ℝ) (P : Fin m → E → E) (μ ρ τ α : ℝ) (x0 s y z : E)
    {b : ℕ} (j : Fin m) (ω : Fin b → Ξ) : E :=
  proxBall μ x0 ρ α z (batch grad ω (mix τ s y z) + hest β P s (mix τ s y z) j)

lemma expected_step (h : Regular law loss grad L σ xs) (hP : ∀ j z, IsProj (K j) z (P j z))
    {β μ ρ τ α : ℝ} {x0 : E} (hL : 0 < L) (hβ : 0 < β) (hμ : 0 ≤ μ) (hρ : 0 ≤ ρ)
    (hα : 0 < α) (hτ : 0 < τ) (hτh : τ ≤ 1 / 2) (htune : 3 * α * (L + β) * τ ≤ 1)
    {b : ℕ} (hb : 0 < b) (habs : L ≤ τ * ((L + β) * b))
    {s y z : E} (hs : s ∈ closedBall x0 ρ) (hy : y ∈ closedBall x0 ρ)
    (hxs : xs ∈ closedBall x0 ρ) :
    let Y := stepY grad β P L μ ρ τ x0 s y z (b := b)
    let Z := stepZ grad β P μ ρ τ α x0 s y z (b := b)
    let Φ := Phi law loss β P μ x0
    (∀ j, Integrable (fun ω => Φ (Y j ω) + τ / (2 * α) * (1 + α * μ) * ‖Z j ω - xs‖ ^ 2)
      (Measure.pi fun _ => law)) ∧
    (𝔼 j, ∫ ω, (Φ (Y j ω) + τ / (2 * α) * (1 + α * μ) * ‖Z j ω - xs‖ ^ 2)
        ∂(Measure.pi fun _ => law)) ≤
      (1 / 2 - τ) * Φ y + 1 / 2 * Φ s + τ * Φ xs + τ / (2 * α) * ‖z - xs‖ ^ 2 +
        σ ^ 2 / (2 * (L + β) * b) := by
  intro Y Z Φ
  have := h.prob
  set x := mix τ s y z with hx
  set G := Fgrad law grad β P x with hG
  set v := fun (j : Fin m) (ω : Fin b → Ξ) => batch grad ω x + hest β P s x j with hv
  set c := 1 / (4 * (L + β)) with hc
  have hLt : 0 < L + β := by linarith
  have hc0 : 0 ≤ c := by positivity
  set I := ∫ ξ, ‖grad ξ xs - grad ξ x‖ ^ 2 ∂law with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => sq_nonneg _
  obtain ⟨hNint, hNle⟩ := noise_bound (K := K) h hP hβ hc0 hb s x (τ • (z - xs))
  have hpt : ∀ j ω, Φ (Y j ω) + τ / (2 * α) * (1 + α * μ) * ‖Z j ω - xs‖ ^ 2 ≤
      ((1 / 2 - τ) * Φ y + 1 / 2 * Φ s + τ * Φ xs + τ / (2 * α) * ‖z - xs‖ ^ 2 -
        τ * ((1 / (2 * L)) * I) - 1 / 2 * (Fsm law loss β P s - Fsm law loss β P x -
          ⟪G, s - x⟫)) +
      (⟪G - v j ω, τ • (z - xs)⟫ + c * ‖G - v j ω‖ ^ 2) := by
    intro j ω
    have hp := pointwise_step (z := z) (v := v j ω) h hP hL hβ hμ hρ hα hτ hτh htune hs hy hxs
    have hp' : Φ (Y j ω) + τ / (2 * α) * (1 + α * μ) * ‖Z j ω - xs‖ ^ 2 ≤
        (1 / 2 - τ) * Φ y + 1 / 2 * Φ s + τ * Φ xs + τ / (2 * α) * ‖z - xs‖ ^ 2 +
        τ * ⟪G - v j ω, z - xs⟫ + ‖G - v j ω‖ ^ 2 / (4 * (L + β)) -
        τ * ((1 / (2 * L)) * I) -
        1 / 2 * (Fsm law loss β P s - Fsm law loss β P x - ⟪G, s - x⟫) := hp
    have hdiv : ‖G - v j ω‖ ^ 2 / (4 * (L + β)) = c * ‖G - v j ω‖ ^ 2 := by
      rw [hc]; ring
    rw [inner_smul_right]
    linarith [hp', hdiv]
  have hYm : ∀ j, Measurable (Y j) := fun j =>
    (proxBall_measurable μ x0 ρ _ x).comp ((batch_measurable h b x).add measurable_const)
  have hZm : ∀ j, Measurable (Z j) := fun j =>
    (proxBall_measurable μ x0 ρ α z).comp ((batch_measurable h b x).add measurable_const)
  have hLint : ∀ j, Integrable (fun ω => Φ (Y j ω) + τ / (2 * α) * (1 + α * μ) *
      ‖Z j ω - xs‖ ^ 2) (Measure.pi fun _ => law) := by
    intro j
    refine Integrable.add ?_ ?_
    · refine Integrable.of_bound (((Phi_measurable h hL hP β μ x0).comp (hYm j)).aestronglyMeasurable)
        (|objective law loss xs| + ‖meanGrad law grad xs‖ * (2 * ρ) + L / 2 * (2 * ρ) ^ 2 +
          (hpen β P xs + ‖hgrad β P xs‖ * (2 * ρ) + β / 2 * (2 * ρ) ^ 2) + μ / 2 * ρ ^ 2)
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs]
      exact Phi_abs_le h hL hP hβ.le hμ hxs (proxBall_mem hρ _ _)
    · refine Integrable.const_mul ?_ _
      refine Integrable.of_bound ((((hZm j).sub measurable_const).norm.pow_const 2).aestronglyMeasurable)
        ((2 * ρ) ^ 2) (Filter.Eventually.of_forall fun ω => ?_)
      have hz := proxBall_mem (μ := μ) (x0 := x0) (a := α) hρ z (v j ω)
      rw [mem_closedBall, dist_eq_norm] at hz hxs
      have hd : ‖Z j ω - xs‖ ≤ 2 * ρ := by
        calc ‖Z j ω - xs‖ = ‖(Z j ω - x0) - (xs - x0)‖ := by congr 1; abel
          _ ≤ ‖Z j ω - x0‖ + ‖xs - x0‖ := norm_sub_le _ _
          _ ≤ 2 * ρ := by change ‖proxBall μ x0 ρ α z (v j ω) - x0‖ + _ ≤ _; linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hd 2
  refine ⟨hLint, ?_⟩
  set A := (1 / 2 - τ) * Φ y + 1 / 2 * Φ s + τ * Φ xs + τ / (2 * α) * ‖z - xs‖ ^ 2 -
      τ * ((1 / (2 * L)) * I) - 1 / 2 * (Fsm law loss β P s - Fsm law loss β P x - ⟪G, s - x⟫)
    with hA
  have hj : ∀ j, ∫ ω, (Φ (Y j ω) + τ / (2 * α) * (1 + α * μ) * ‖Z j ω - xs‖ ^ 2)
      ∂(Measure.pi fun _ => law) ≤
      A + ∫ ω, (⟪G - v j ω, τ • (z - xs)⟫ + c * ‖G - v j ω‖ ^ 2) ∂(Measure.pi fun _ => law) := by
    intro j
    have hR : Integrable (fun ω => A + (⟪G - v j ω, τ • (z - xs)⟫ + c * ‖G - v j ω‖ ^ 2))
        (Measure.pi fun _ => law) := (integrable_const A).add (hNint j)
    have hm := integral_mono (hLint j) hR (hpt j)
    rw [integral_add (integrable_const A) (hNint j), integral_const] at hm
    simpa using hm
  have hE := Finset.expect_le_expect (s := Finset.univ) fun j _ => hj j
  simp only [Finset.expect_add_distrib, Fintype.expect_const] at hE
  have hDobj : 0 ≤ objective law loss s - objective law loss x - ⟪meanGrad law grad x, s - x⟫ := by
    have := h.support hL x s
    have : 0 ≤ (1 / (2 * L)) * ∫ ξ, ‖grad ξ s - grad ξ x‖ ^ 2 ∂law := by
      have : 0 ≤ ∫ ξ, ‖grad ξ s - grad ξ x‖ ^ 2 ∂law := integral_nonneg fun _ => sq_nonneg _
      positivity
    linarith
  have hDh : 0 ≤ hpen β P s - hpen β P x - ⟪hgrad β P x, s - x⟫ := by
    have := hpen_support hP hβ.le x s; linarith
  have hDF : Fsm law loss β P s - Fsm law loss β P x - ⟪G, s - x⟫ =
      (objective law loss s - objective law loss x - ⟪meanGrad law grad x, s - x⟫) +
      (hpen β P s - hpen β P x - ⟪hgrad β P x, s - x⟫) := by
    simp only [Fsm, hG, Fgrad, inner_add_left]; ring
  have hcβ : c * (2 * β) ≤ 1 / 2 := by
    rw [hc, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; linarith
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have habs' : c * (2 * I / b) ≤ τ * ((1 / (2 * L)) * I) := by
    rw [hc]
    have : 1 / (4 * (L + β)) * (2 * I / b) = I / (2 * ((L + β) * b)) := by field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    have : τ * (1 / (2 * L) * I) * (2 * ((L + β) * b)) = I * (τ * ((L + β) * b)) / L := by
      field_simp
    rw [this, le_div_iff₀ hL]
    nlinarith [mul_le_mul_of_nonneg_left habs hI0]
  have hσ : c * (2 * σ ^ 2 / b) = σ ^ 2 / (2 * (L + β) * b) := by rw [hc]; field_simp; ring
  have hsplit : c * (2 * β * (hpen β P s - hpen β P x - ⟪hgrad β P x, s - x⟫) +
      (2 * I + 2 * σ ^ 2) / b) = c * (2 * β) * (hpen β P s - hpen β P x - ⟪hgrad β P x, s - x⟫) +
      c * (2 * I / b) + c * (2 * σ ^ 2 / b) := by ring
  rw [hsplit] at hNle
  have hD := mul_le_mul_of_nonneg_right hcβ hDh
  rw [hDF] at hA
  nlinarith [hE, hNle, hD, habs', hσ, hDobj]

end LongTails.Proofs.ManyConstraintExpected
