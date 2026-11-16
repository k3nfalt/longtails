import LongTails.Proofs.ManyConstraintRegularity

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintLower

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintPenalty
  LongTails.Proofs.ManyConstraintFinite LongTails.Proofs.ManyConstraintStochastic
  LongTails.Proofs.ManyConstraintStep LongTails.Proofs.ManyConstraintBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ]
variable {m : ℕ} [NeZero m]
variable {law : Measure Ξ} {loss : Ξ → E → ℝ} {grad : Ξ → E → E} {L σ : ℝ} {xs : E}

lemma first_order (h : Regular law loss grad L σ xs) (hL : 0 < L) {C : Set E} (hC : Convex ℝ C)
    (hxs : xs ∈ C) (hmin : IsMinOn (objective law loss) C xs) {w : E} (hw : w ∈ C) :
    0 ≤ ⟪meanGrad law grad xs, w - xs⟫ := by
  by_contra hneg
  push Not at hneg
  set g := ⟪meanGrad law grad xs, w - xs⟫
  set q := ‖w - xs‖ ^ 2
  have hq : 0 ≤ q := sq_nonneg _
  have hden : 0 < L * q + 1 := by positivity
  set t := min 1 (-g / (L * q + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos (by linarith) hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ -g / (L * q + 1) := min_le_right _ _
  have hmem : xs + t • (w - xs) ∈ C := hC.add_smul_sub_mem hxs hw ⟨ht0.le, ht1⟩
  have hmod := h.model xs (xs + t • (w - xs))
  have hm := hmin hmem
  simp only [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos ht0, mul_pow] at hmod
  change objective law loss xs ≤ objective law loss (xs + t • (w - xs)) at hm
  have key2 : 0 ≤ g + L / 2 * (t * q) := by
    have : 0 ≤ t * (g + L / 2 * (t * q)) := by nlinarith
    exact nonneg_of_mul_nonneg_right (by linarith) ht0
  have h3 : L * q * t ≤ L * q * (-g / (L * q + 1)) := mul_le_mul_of_nonneg_left ht2 (by positivity)
  have h4 : L * q * (-g / (L * q + 1)) < -g := by
    rw [mul_div_assoc', div_lt_iff₀ hden]; nlinarith
  nlinarith

lemma meanGrad_norm_le (h : Regular law loss grad L σ xs) (hσ : 0 ≤ σ) :
    ‖meanGrad law grad xs‖ ≤ σ := by
  have := h.prob
  have hint := h.gradInt xs
  have h2 : Integrable (fun ξ => ‖grad ξ xs‖ ^ 2) law := h.sqInt
  have hexp : ∀ ξ, ‖grad ξ xs - meanGrad law grad xs‖ ^ 2 =
      ‖grad ξ xs‖ ^ 2 - 2 * ⟪grad ξ xs, meanGrad law grad xs⟫ + ‖meanGrad law grad xs‖ ^ 2 := by
    intro ξ; rw [norm_sub_sq_real]
  have hnn : 0 ≤ ∫ ξ, ‖grad ξ xs - meanGrad law grad xs‖ ^ 2 ∂law :=
    integral_nonneg fun _ => sq_nonneg _
  simp_rw [hexp] at hnn
  have hI : Integrable (fun ξ => 2 * ⟪grad ξ xs, meanGrad law grad xs⟫) law :=
    (hint.inner_const _).const_mul 2
  have hD : Integrable (fun ξ => ‖grad ξ xs‖ ^ 2 - 2 * ⟪grad ξ xs, meanGrad law grad xs⟫) law :=
    h2.sub hI
  rw [integral_add hD (integrable_const _), integral_sub h2 hI, integral_const_mul,
    int_inner hint, integral_const] at hnn
  simp only [meanGrad, real_inner_self_eq_norm_sq, probReal_univ, one_smul] at hnn
  have hsq : ‖meanGrad law grad xs‖ ^ 2 ≤ σ ^ 2 := by
    simp only [meanGrad]; linarith [h.second]
  exact (sq_le_sq₀ (norm_nonneg _) hσ).1 hsq

variable {K : Fin m → Set E} {P : Fin m → E → E}

omit [NeZero m] in
lemma Phi_lower (h : Regular law loss grad L σ xs) (hL : 0 < L) (hσ : 0 ≤ σ)
    (hP : ∀ j z, IsProj (K j) z (P j z)) (hK : ∀ j, Convex ℝ (K j))
    (hxs : xs ∈ ⋂ j, K j) (hmin : IsMinOn (objective law loss) (⋂ j, K j) xs)
    {κ β μ R : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hμ : 0 ≤ μ) {x0 : E} (hR : ‖x0 - xs‖ ≤ R)
    (x : E) (hreg : Metric.infDist x (⋂ j, K j) ^ 2 ≤
      κ * ((1 / (m : ℝ)) * ∑ j, Metric.infDist x (K j) ^ 2)) :
    -(κ * σ ^ 2 / (2 * β) + μ / 2 * R ^ 2) ≤ Phi law loss β P μ x0 x - Phi law loss β P μ x0 xs := by
  set C := ⋂ j, K j
  have hC : Convex ℝ C := convex_iInter hK
  set G := ‖meanGrad law grad xs‖
  set d := Metric.infDist x C
  have hd0 : 0 ≤ d := Metric.infDist_nonneg
  have hG0 : 0 ≤ G := norm_nonneg _
  have hf : objective law loss xs - G * d ≤ objective law loss x := by
    have hsupp : objective law loss xs + ⟪meanGrad law grad xs, x - xs⟫ ≤ objective law loss x := by
      have := h.support hL xs x
      have : 0 ≤ (1 / (2 * L)) * ∫ ξ, ‖grad ξ x - grad ξ xs‖ ^ 2 ∂law := by
        have : 0 ≤ ∫ ξ, ‖grad ξ x - grad ξ xs‖ ^ 2 ∂law := integral_nonneg fun _ => sq_nonneg _
        positivity
      linarith
    have hall : ∀ w ∈ C, objective law loss xs - G * ‖x - w‖ ≤ objective law loss x := fun w hw =>
      value_lower_bound hsupp rfl (first_order h hL hC hxs hmin hw)
    apply le_of_forall_pos_le_add
    intro η hη
    have hne : C.Nonempty := ⟨xs, hxs⟩
    obtain ⟨w, hw, hlt⟩ := (Metric.infDist_lt_iff hne).mp (lt_add_of_pos_right d
      (show 0 < η / (G + 1) by positivity))
    rw [dist_eq_norm] at hlt
    have h1 := hall w hw
    have h2 : G * ‖x - w‖ ≤ G * d + G * (η / (G + 1)) := by nlinarith
    have h3 : G * (η / (G + 1)) ≤ η := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hpenx : β / (2 * κ) * d ^ 2 ≤ hpen β P x := by
    have hval : hpen β P x = β / 2 * ((1 / (m : ℝ)) * ∑ j, Metric.infDist x (K j) ^ 2) := by
      simp only [hpen, pen_eq_infDist (hP _), Finset.expect_eq_sum_div_card, Finset.card_univ,
        Fintype.card_fin, ← Finset.mul_sum]
      ring
    rw [hval]
    have h1 : d ^ 2 / κ ≤ (1 / (m : ℝ)) * ∑ j, Metric.infDist x (K j) ^ 2 := by
      rw [div_le_iff₀ hκ]; linarith
    have hb : 0 ≤ β / 2 := by positivity
    calc β / (2 * κ) * d ^ 2 = β / 2 * (d ^ 2 / κ) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hb
  have hpen0 : ManyConstraintFinite.hpen β P xs = 0 := by
    have hz : ∀ j, pen β (P j) xs = 0 := fun j => pen_zero_of_mem (hP j) (mem_iInter.mp hxs j)
    simp [ManyConstraintFinite.hpen, hz]
  have hr0 : 0 ≤ reg μ x0 x := by unfold reg; positivity
  have hr1 : reg μ x0 xs ≤ μ / 2 * R ^ 2 := by
    unfold reg
    have : ‖xs - x0‖ ≤ R := by rw [norm_sub_rev]; exact hR
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) this 2) (by positivity)
  have hGσ : G ≤ σ := meanGrad_norm_le h hσ
  have hamgm : -(κ * G ^ 2 / (2 * β)) ≤ -(G * d) + β / (2 * κ) * d ^ 2 := by
    have h2 : 0 ≤ (β * d - κ * G) ^ 2 := sq_nonneg _
    have h3 : -(κ * G ^ 2 / (2 * β)) - (-(G * d) + β / (2 * κ) * d ^ 2) =
        -((β * d - κ * G) ^ 2) / (2 * κ * β) := by field_simp; ring
    have h4 : -((β * d - κ * G) ^ 2) / (2 * κ * β) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith
  have hG2 : κ * G ^ 2 / (2 * β) ≤ κ * σ ^ 2 / (2 * β) := by
    have : G ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hG0 hGσ 2
    gcongr
  simp only [Phi, Fsm]
  linarith

omit [NeZero m] in
lemma Phi_lower_dist (h : Regular law loss grad L σ xs) (hL : 0 < L) (hσ : 0 ≤ σ)
    (hP : ∀ j z, IsProj (K j) z (P j z)) (hK : ∀ j, Convex ℝ (K j))
    (hxs : xs ∈ ⋂ j, K j) (hmin : IsMinOn (objective law loss) (⋂ j, K j) xs)
    {κ β μ R : ℝ} (hκ : 0 < κ) (hβ : 0 < β) (hμ : 0 ≤ μ) {x0 : E} (hR : ‖x0 - xs‖ ≤ R)
    (x : E) (hreg : Metric.infDist x (⋂ j, K j) ^ 2 ≤
      κ * ((1 / (m : ℝ)) * ∑ j, Metric.infDist x (K j) ^ 2)) :
    -(σ * Metric.infDist x (⋂ j, K j)) + β / (2 * κ) * Metric.infDist x (⋂ j, K j) ^ 2 -
      μ / 2 * R ^ 2 ≤ Phi law loss β P μ x0 x - Phi law loss β P μ x0 xs := by
  set C := ⋂ j, K j
  have hC : Convex ℝ C := convex_iInter hK
  set G := ‖meanGrad law grad xs‖
  set d := Metric.infDist x C
  have hd0 : 0 ≤ d := Metric.infDist_nonneg
  have hG0 : 0 ≤ G := norm_nonneg _
  have hf : objective law loss xs - G * d ≤ objective law loss x := by
    have hsupp : objective law loss xs + ⟪meanGrad law grad xs, x - xs⟫ ≤ objective law loss x := by
      have := h.support hL xs x
      have : 0 ≤ (1 / (2 * L)) * ∫ ξ, ‖grad ξ x - grad ξ xs‖ ^ 2 ∂law := by
        have : 0 ≤ ∫ ξ, ‖grad ξ x - grad ξ xs‖ ^ 2 ∂law := integral_nonneg fun _ => sq_nonneg _
        positivity
      linarith
    have hall : ∀ w ∈ C, objective law loss xs - G * ‖x - w‖ ≤ objective law loss x := fun w hw =>
      value_lower_bound hsupp rfl (first_order h hL hC hxs hmin hw)
    apply le_of_forall_pos_le_add
    intro η hη
    have hne : C.Nonempty := ⟨xs, hxs⟩
    obtain ⟨w, hw, hlt⟩ := (Metric.infDist_lt_iff hne).mp (lt_add_of_pos_right d
      (show 0 < η / (G + 1) by positivity))
    rw [dist_eq_norm] at hlt
    have h1 := hall w hw
    have h2 : G * ‖x - w‖ ≤ G * d + G * (η / (G + 1)) := by nlinarith
    have h3 : G * (η / (G + 1)) ≤ η := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hpenx : β / (2 * κ) * d ^ 2 ≤ hpen β P x := by
    have hval : hpen β P x = β / 2 * ((1 / (m : ℝ)) * ∑ j, Metric.infDist x (K j) ^ 2) := by
      simp only [hpen, pen_eq_infDist (hP _), Finset.expect_eq_sum_div_card, Finset.card_univ,
        Fintype.card_fin, ← Finset.mul_sum]
      ring
    rw [hval]
    have h1 : d ^ 2 / κ ≤ (1 / (m : ℝ)) * ∑ j, Metric.infDist x (K j) ^ 2 := by
      rw [div_le_iff₀ hκ]; linarith
    have hb : 0 ≤ β / 2 := by positivity
    calc β / (2 * κ) * d ^ 2 = β / 2 * (d ^ 2 / κ) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 hb
  have hpen0 : ManyConstraintFinite.hpen β P xs = 0 := by
    have hz : ∀ j, pen β (P j) xs = 0 := fun j => pen_zero_of_mem (hP j) (mem_iInter.mp hxs j)
    simp [ManyConstraintFinite.hpen, hz]
  have hr0 : 0 ≤ reg μ x0 x := by unfold reg; positivity
  have hr1 : reg μ x0 xs ≤ μ / 2 * R ^ 2 := by
    unfold reg
    have : ‖xs - x0‖ ≤ R := by rw [norm_sub_rev]; exact hR
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) this 2) (by positivity)
  have hGσ : G ≤ σ := meanGrad_norm_le h hσ
  have hGd : G * d ≤ σ * d := mul_le_mul_of_nonneg_right hGσ hd0
  simp only [Phi, Fsm]
  linarith

end LongTails.Proofs.ManyConstraintLower
