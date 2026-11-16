import LongTails.Proofs.ManyConstraintLower
import LongTails.Proofs.ManyConstraintRun
import LongTails.Proofs.RecursiveGradientEnergy

open MeasureTheory Set Metric
open scoped RealInnerProductSpace BigOperators

namespace LongTails.Proofs.ManyConstraintCleanup

open LongTails.Proofs.ManyConstraintGeometry LongTails.Proofs.ManyConstraintStochastic
  LongTails.Proofs.ManyConstraintLower LongTails.Proofs.ManyConstraintRun

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ} [NeZero m] {K : Fin m → Set E} {P : Fin m → E → E}

lemma cleanup_feasibility (hP : ∀ j z, IsProj (K j) z (P j z)) (hne : (⋂ j, K j).Nonempty)
    {κ : ℝ} (hκ : 0 < κ) (hκ1 : 1 ≤ κ)
    (hreg : ∀ x, Metric.infDist x (⋂ j, K j) ^ 2 ≤
      κ * ((1 / (m : ℝ)) * ∑ j, Metric.infDist x (K j) ^ 2)) :
    ∀ (Q : ℕ) (p : E), (𝔼 js : Fin Q → Fin m,
      Metric.infDist (cleanup P Q p js) (⋂ j, K j) ^ 2) ≤
        (1 - 1 / κ) ^ Q * Metric.infDist p (⋂ j, K j) ^ 2 := by
  intro Q
  induction Q with
  | zero => intro p; simp [cleanup]
  | succ Q ih =>
    intro p
    rw [OracleTemplate.NonconvexFiniteSum.expect_function_succ]
    simp only [cleanup, Fin.cons_zero, Fin.cons_succ]
    have hstep : ∀ j : Fin m, (𝔼 js : Fin Q → Fin m,
        Metric.infDist (cleanup P Q (P j p) (fun i => (Fin.cons j js : Fin (Q + 1) → Fin m) i.succ))
          (⋂ j, K j) ^ 2) ≤ (1 - 1 / κ) ^ Q * Metric.infDist (P j p) (⋂ j, K j) ^ 2 := by
      intro j
      simp only [Fin.cons_succ]
      exact ih (P j p)
    have h1 := Finset.expect_le_expect (s := Finset.univ) fun j _ => hstep j
    rw [← Finset.mul_expect] at h1
    have hc := avg_contraction (Nat.pos_of_ne_zero (NeZero.ne m)) K
      (fun j => iInter_subset K j) hne hκ p (fun j => P j p) (fun j => hP j p) (hreg p)
    have hexp : (𝔼 j, Metric.infDist (P j p) (⋂ j, K j) ^ 2) =
        (1 / (m : ℝ)) * ∑ j, Metric.infDist (P j p) (⋂ j, K j) ^ 2 := by
      rw [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_fin]; ring
    have hq : 0 ≤ (1 - 1 / κ) ^ Q := by
      have : 1 / κ ≤ 1 := by rw [div_le_one hκ]; exact hκ1
      exact pow_nonneg (by linarith) Q
    calc _ ≤ _ := h1
      _ = (1 - 1 / κ) ^ Q * ((1 / (m : ℝ)) * ∑ j, Metric.infDist (P j p) (⋂ j, K j) ^ 2) := by
          rw [hexp]
      _ ≤ (1 - 1 / κ) ^ Q * ((1 - 1 / κ) * Metric.infDist p (⋂ j, K j) ^ 2) :=
          mul_le_mul_of_nonneg_left hc hq
      _ = _ := by ring

omit [NeZero m] in
lemma cleanup_fejer (hP : ∀ j z, IsProj (K j) z (P j z)) {w : E} (hw : w ∈ ⋂ j, K j) :
    ∀ (Q : ℕ) (p : E) (js : Fin Q → Fin m), ‖cleanup P Q p js - w‖ ≤ ‖p - w‖ := by
  intro Q
  induction Q with
  | zero => intro p js; simp [cleanup]
  | succ Q ih =>
    intro p js
    simp only [cleanup]
    exact (ih _ _).trans (proj_dist_le (iInter_subset K (js 0)) (hP (js 0) p) hw)

omit [NeZero m] in
lemma cleanup_move (hP : ∀ j z, IsProj (K j) z (P j z)) (hne : (⋂ j, K j).Nonempty)
    (Q : ℕ) (p : E) (js : Fin Q → Fin m) :
    ‖cleanup P Q p js - p‖ ≤ 2 * Metric.infDist p (⋂ j, K j) := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨w, hw, hlt⟩ := (Metric.infDist_lt_iff hne).mp
    (lt_add_of_pos_right (Metric.infDist p (⋂ j, K j)) (half_pos hη))
  rw [dist_eq_norm] at hlt
  have h1 := cleanup_fejer hP hw Q p js
  calc ‖cleanup P Q p js - p‖ = ‖(cleanup P Q p js - w) - (p - w)‖ := by congr 1; abel
    _ ≤ ‖cleanup P Q p js - w‖ + ‖p - w‖ := norm_sub_le _ _
    _ ≤ 2 * ‖p - w‖ := by linarith
    _ ≤ _ := by linarith

section Damage

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ξ : Type*} [MeasurableSpace Ξ] {law : Measure Ξ} {loss : Ξ → E → ℝ}
  {grad : Ξ → E → E} {L σ : ℝ} {xs : E}

omit [NeZero m] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma sq_integral_le {f : Ξ → ℝ} [IsProbabilityMeasure law] (hf : Integrable f law)
    (hf2 : Integrable (fun ξ => f ξ ^ 2) law) :
    (∫ ξ, f ξ ∂law) ^ 2 ≤ ∫ ξ, f ξ ^ 2 ∂law := by
  set a := ∫ ξ, f ξ ∂law
  have h0 : 0 ≤ ∫ ξ, (f ξ - a) ^ 2 ∂law := integral_nonneg fun _ => sq_nonneg _
  have hexp : ∀ ξ, (f ξ - a) ^ 2 = f ξ ^ 2 - 2 * a * f ξ + a ^ 2 := fun ξ => by ring
  simp_rw [hexp] at h0
  have hA : Integrable (fun ξ => f ξ ^ 2 - 2 * a * f ξ) law := hf2.sub (hf.const_mul _)
  rw [integral_add hA (integrable_const _), integral_sub hf2 (hf.const_mul _),
    integral_const_mul, integral_const] at h0
  simp only [probReal_univ, one_smul] at h0
  nlinarith

omit [NeZero m] in
lemma cleanup_objective (h : Regular law loss grad L σ xs) (hL : 0 < L) (hσ : 0 ≤ σ)
    (hK : ∀ j, Convex ℝ (K j)) (hxs : xs ∈ ⋂ j, K j)
    (hmin : IsMinOn (objective law loss) (⋂ j, K j) xs) {s p : E}
    (hmove : ‖p - s‖ ≤ 2 * Metric.infDist s (⋂ j, K j)) :
    max (objective law loss p - objective law loss xs) 0 ≤
      2 * max (objective law loss s - objective law loss xs) 0 +
        3 * σ * Metric.infDist s (⋂ j, K j) + 4 * L * Metric.infDist s (⋂ j, K j) ^ 2 := by
  have := h.prob
  set C := ⋂ j, K j
  set d := Metric.infDist s C
  set G := ‖meanGrad law grad xs‖
  have hd0 : 0 ≤ d := Metric.infDist_nonneg
  have hG : G ≤ σ := meanGrad_norm_le h hσ
  have hG0 : 0 ≤ G := norm_nonneg _
  have hC : Convex ℝ C := convex_iInter hK
  have hinner : -(G * d) ≤ ⟪meanGrad law grad xs, s - xs⟫ := by
    apply le_of_forall_pos_le_add
    intro η hη
    obtain ⟨w, hw, hlt⟩ := (Metric.infDist_lt_iff ⟨xs, hxs⟩).mp
      (lt_add_of_pos_right d (show 0 < η / (G + 1) by positivity))
    rw [dist_eq_norm] at hlt
    have h1 := first_order h hL hC hxs hmin hw
    have h2 : ⟪meanGrad law grad xs, s - xs⟫ = ⟪meanGrad law grad xs, s - w⟫ +
        ⟪meanGrad law grad xs, w - xs⟫ := by rw [← inner_add_right]; congr 1; abel
    have h3 : -(G * ‖s - w‖) ≤ ⟪meanGrad law grad xs, s - w⟫ := by
      have := abs_real_inner_le_norm (meanGrad law grad xs) (s - w)
      linarith [neg_abs_le ⟪meanGrad law grad xs, s - w⟫]
    have h4 : G * ‖s - w‖ ≤ G * d + G * (η / (G + 1)) := by nlinarith
    have h5 : G * (η / (G + 1)) ≤ η := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  set D := objective law loss s - objective law loss xs - ⟪meanGrad law grad xs, s - xs⟫
  have hsupp := h.support hL xs s
  have hI : Integrable (fun ξ => ‖grad ξ s - grad ξ xs‖ ^ 2) law := by
    refine Integrable.mono' (integrable_const ((L * ‖s - xs‖) ^ 2))
      (((h.gradMeas s).sub (h.gradMeas xs)).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (h.lip ξ s xs) 2
  have hnorm : ‖meanGrad law grad s - meanGrad law grad xs‖ ^ 2 ≤
      ∫ ξ, ‖grad ξ s - grad ξ xs‖ ^ 2 ∂law := by
    have he : meanGrad law grad s - meanGrad law grad xs = ∫ ξ, (grad ξ s - grad ξ xs) ∂law := by
      unfold meanGrad; rw [integral_sub (h.gradInt s) (h.gradInt xs)]
    rw [he]
    have h1 : ‖∫ ξ, (grad ξ s - grad ξ xs) ∂law‖ ≤ ∫ ξ, ‖grad ξ s - grad ξ xs‖ ∂law :=
      norm_integral_le_integral_norm _
    have hn : Integrable (fun ξ => ‖grad ξ s - grad ξ xs‖) law :=
      ((h.gradInt s).sub (h.gradInt xs)).norm
    have h2 := sq_integral_le hn (by simpa using hI)
    have h0 : 0 ≤ ‖∫ ξ, (grad ξ s - grad ξ xs) ∂law‖ := norm_nonneg _
    nlinarith
  have hcoco : ‖meanGrad law grad s - meanGrad law grad xs‖ ^ 2 ≤ 2 * L * D := by
    have : (1 / (2 * L)) * ∫ ξ, ‖grad ξ s - grad ξ xs‖ ^ 2 ∂law ≤ D := by simp only [D]; linarith
    have hL2 : 0 < 2 * L := by positivity
    rw [one_div, inv_mul_le_iff₀ hL2] at this
    linarith
  have hD0 : 0 ≤ D := by
    have : 0 ≤ (1 / (2 * L)) * ∫ ξ, ‖grad ξ s - grad ξ xs‖ ^ 2 ∂law := by
      have : 0 ≤ ∫ ξ, ‖grad ξ s - grad ξ xs‖ ^ 2 ∂law := integral_nonneg fun _ => sq_nonneg _
      positivity
    simp only [D]; linarith
  have hdam := cleanup_damage (f := objective law loss) (y := s) (p := p)
    (gy := meanGrad law grad s) (gs := meanGrad law grad xs) hL.le (h.model s p) le_rfl hcoco hmove
  have hamgm : 2 * d * Real.sqrt (2 * L * D) ≤ 2 * L * d ^ 2 + D := by
    have hs := Real.sq_sqrt (show 0 ≤ 2 * L * D by positivity)
    have hs0 := Real.sqrt_nonneg (2 * L * D)
    nlinarith [sq_nonneg (Real.sqrt (2 * L * D) - 2 * L * d), sq_nonneg (Real.sqrt (2 * L * D)),
      sq_nonneg d, sq_nonneg (2 * L * d - Real.sqrt (2 * L * D)),
      sq_nonneg (Real.sqrt (2 * L * D) - d * Real.sqrt (2 * L))]
  have hfin : objective law loss p - objective law loss xs ≤
      2 * (objective law loss s - objective law loss xs) + 3 * G * d + 4 * L * d ^ 2 := by
    simp only [D] at hamgm hdam; nlinarith
  have hσd : 3 * G * d ≤ 3 * σ * d := by nlinarith
  rcases le_total (objective law loss s - objective law loss xs) 0 with hneg | hpos
  · rw [max_eq_right hneg]
    apply max_le
    · nlinarith
    · positivity
  · rw [max_eq_left hpos]
    apply max_le
    · linarith
    · positivity

end Damage

end LongTails.Proofs.ManyConstraintCleanup
