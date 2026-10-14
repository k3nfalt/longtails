import LongTails.Proofs.ArrowHurwiczBand
import LongTails.Proofs.ArrowHurwiczGap

open Real Finset
open scoped RealInnerProductSpace

namespace OracleTemplate.ArrowHurwicz

variable {E : Type*} {F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma dsum_inner_K (K : E →L[ℝ] F) (S : Finset ℤ) (f g : ℤ → ℝ) (u : ℤ → F) (v : ℤ → E) :
    ∑ t ∈ S, ∑ s ∈ S, f t * g s * ⟪u t, K (v s)⟫ = ⟪∑ t ∈ S, f t • u t, K (∑ s ∈ S, g s • v s)⟫ := by
  simp only [sum_inner, map_sum, map_smul, inner_sum, inner_smul_left, inner_smul_right, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro t _; apply sum_congr rfl; intro s _
  simp only [RCLike.conj_to_real]; ring

lemma dsum_inner_E (S : Finset ℤ) (f g : ℤ → ℝ) (v : ℤ → E) :
    ∑ t ∈ S, ∑ s ∈ S, f t * g s * ⟪v t, v s⟫ = ⟪∑ t ∈ S, f t • v t, ∑ s ∈ S, g s • v s⟫ := by
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro t _; apply sum_congr rfl; intro s _
  simp only [RCLike.conj_to_real]; ring

lemma quad_bound (K : E →L[ℝ] F) {L η : ℝ} (hK : ‖K‖ ≤ L) (hη : 0 ≤ η) (Cx Sx : E) (Cy Sy : F)
    (s c : ℝ) (hsc : s ^ 2 + c ^ 2 = 1) :
    (s - η * L / 2) * (‖Cx‖ ^ 2 + ‖Sx‖ ^ 2 + ‖Cy‖ ^ 2 + ‖Sy‖ ^ 2) ≤
      s * (‖Cx‖ ^ 2 + ‖Sx‖ ^ 2 + ‖Cy‖ ^ 2 + ‖Sy‖ ^ 2) -
        η * (s * (⟪Cy, K Cx⟫ + ⟪Sy, K Sx⟫) + c * (⟪Sy, K Cx⟫ - ⟪Cy, K Sx⟫)) := by
  set u := s • Cx - c • Sx
  set v := c • Cx + s • Sx
  have e1 : s * (⟪Cy, K Cx⟫ + ⟪Sy, K Sx⟫) + c * (⟪Sy, K Cx⟫ - ⟪Cy, K Sx⟫) = ⟪Cy, K u⟫ + ⟪Sy, K v⟫ := by
    simp only [u, v, map_sub, map_add, map_smul, inner_sub_right, inner_add_right, inner_smul_right]; ring
  have e2 : ‖u‖ ^ 2 + ‖v‖ ^ 2 = ‖Cx‖ ^ 2 + ‖Sx‖ ^ 2 := by
    simp only [u, v]
    rw [@norm_sub_sq_real, @norm_add_sq_real, norm_smul, norm_smul, norm_smul, norm_smul,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs, RCLike.conj_to_real]
    linear_combination (‖Cx‖ ^ 2 + ‖Sx‖ ^ 2) * hsc
  have hL : 0 ≤ L := le_trans (norm_nonneg _) hK
  have b : ∀ (a : F) (w : E), |⟪a, K w⟫| ≤ L / 2 * (‖a‖ ^ 2 + ‖w‖ ^ 2) := by
    intro a w
    have h1 := abs_real_inner_le_norm a (K w)
    have h2 : ‖K w‖ ≤ L * ‖w‖ := le_trans (K.le_opNorm w) (by gcongr)
    have h3 : ‖a‖ * ‖K w‖ ≤ ‖a‖ * (L * ‖w‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    nlinarith [sq_nonneg (‖a‖ - ‖w‖), mul_nonneg hL (sq_nonneg (‖a‖ - ‖w‖))]
  have b1 := b Cy u
  have b2 := b Sy v
  rw [e1]
  have : ⟪Cy, K u⟫ + ⟪Sy, K v⟫ ≤ L / 2 * (‖Cx‖ ^ 2 + ‖Sx‖ ^ 2 + ‖Cy‖ ^ 2 + ‖Sy‖ ^ 2) := by
    have := le_abs_self ⟪Cy, K u⟫
    have := le_abs_self ⟪Sy, K v⟫
    nlinarith
  nlinarith

lemma trig_form_nonneg (K : E →L[ℝ] F) {L η : ℝ} (hK : ‖K‖ ≤ L) (hη : 0 ≤ η) (S : Finset ℤ)
    (xp : ℤ → E) (yp : ℤ → F) (ω : ℝ) (hω : η * L / 2 ≤ sin (ω / 2)) :
    0 ≤ ∑ t ∈ S, ∑ s ∈ S, (sin (ω / 2) * cos (((t - s : ℤ) : ℝ) * ω) * (⟪xp t, xp s⟫ + ⟪yp t, yp s⟫) -
      η * sin ((((t - s : ℤ) : ℝ) + 1 / 2) * ω) * ⟪yp t, K (xp s)⟫) := by
  set Cx := ∑ t ∈ S, cos ((t : ℝ) * ω) • xp t
  set Sx := ∑ t ∈ S, sin ((t : ℝ) * ω) • xp t
  set Cy := ∑ t ∈ S, cos ((t : ℝ) * ω) • yp t
  set Sy := ∑ t ∈ S, sin ((t : ℝ) * ω) • yp t
  have key : ∑ t ∈ S, ∑ s ∈ S, (sin (ω / 2) * cos (((t - s : ℤ) : ℝ) * ω) * (⟪xp t, xp s⟫ + ⟪yp t, yp s⟫) -
      η * sin ((((t - s : ℤ) : ℝ) + 1 / 2) * ω) * ⟪yp t, K (xp s)⟫) =
      sin (ω / 2) * (‖Cx‖ ^ 2 + ‖Sx‖ ^ 2 + ‖Cy‖ ^ 2 + ‖Sy‖ ^ 2) -
        η * (sin (ω / 2) * (⟪Cy, K Cx⟫ + ⟪Sy, K Sx⟫) + cos (ω / 2) * (⟪Sy, K Cx⟫ - ⟪Cy, K Sx⟫)) := by
    simp only [Cx, Sx, Cy, Sy, ← real_inner_self_eq_norm_sq, ← dsum_inner_K, ← dsum_inner_E]
    simp only [mul_add, mul_sub, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl; intro t _; apply sum_congr rfl; intro s _
    push_cast
    rw [show ((t : ℝ) - s + 1 / 2) * ω = ((t : ℝ) * ω - s * ω) + ω / 2 by ring,
      show ((t : ℝ) - s) * ω = (t : ℝ) * ω - s * ω by ring, sin_add, sin_sub, cos_sub]
    ring
  rw [key]
  have := quad_bound K hK hη Cx Sx Cy Sy (sin (ω / 2)) (cos (ω / 2)) (sin_sq_add_cos_sq _)
  have h0 : 0 ≤ (sin (ω / 2) - η * L / 2) * (‖Cx‖ ^ 2 + ‖Sx‖ ^ 2 + ‖Cy‖ ^ 2 + ‖Sy‖ ^ 2) :=
    mul_nonneg (by linarith) (by positivity)
  linarith

noncomputable def bandKer (d : ℤ) : ℝ :=
  2 / π * ∫ ω in (π / 6)..π, bandWeight ω * sin (((d : ℝ) + 1 / 2) * ω)

lemma bandKer_nat (j : ℕ) : bandKer j = bandCoef j := by
  simp [bandKer, bandCoef]

lemma bandKer_neg (d : ℤ) : bandKer (-d - 1) = -bandKer d := by
  unfold bandKer
  rw [← mul_neg, ← intervalIntegral.integral_neg]
  congr 1; apply intervalIntegral.integral_congr; intro ω _
  simp only
  push_cast
  rw [show (-(d : ℝ) - 1 + 1 / 2) * ω = -(((d : ℝ) + 1 / 2) * ω) by ring, sin_neg]; ring

lemma continuous_bandWeight : Continuous bandWeight := by
  unfold bandWeight; fun_prop

lemma bandKer_integral_form (S : Finset ℤ) (P Kg : ℤ → ℤ → ℝ) (η : ℝ) :
    ∑ t ∈ S, ∑ s ∈ S, ((bandKer (t - s) - bandKer (t - s - 1)) / 2 * P t s - η * bandKer (t - s) * Kg t s) =
      2 / π * ∫ ω in (π / 6)..π, bandWeight ω * ∑ t ∈ S, ∑ s ∈ S,
        (sin (ω / 2) * cos (((t - s : ℤ) : ℝ) * ω) * P t s -
          η * sin ((((t - s : ℤ) : ℝ) + 1 / 2) * ω) * Kg t s) := by
  have cw := continuous_bandWeight
  have term : ∀ t s : ℤ, (bandKer (t - s) - bandKer (t - s - 1)) / 2 * P t s - η * bandKer (t - s) * Kg t s =
      2 / π * ∫ ω in (π / 6)..π, bandWeight ω *
        (sin (ω / 2) * cos (((t - s : ℤ) : ℝ) * ω) * P t s -
          η * sin ((((t - s : ℤ) : ℝ) + 1 / 2) * ω) * Kg t s) := by
    intro t s
    have hi : ∀ c : ℝ, IntervalIntegrable (fun ω => bandWeight ω * sin (c * ω)) MeasureTheory.volume (π / 6) π :=
      fun c => (cw.mul (by fun_prop)).intervalIntegrable _ _
    have ident : ∀ ω, bandWeight ω *
        (sin (ω / 2) * cos (((t - s : ℤ) : ℝ) * ω) * P t s -
          η * sin ((((t - s : ℤ) : ℝ) + 1 / 2) * ω) * Kg t s) =
        (P t s / 2 - η * Kg t s) * (bandWeight ω * sin ((((t - s : ℤ) : ℝ) + 1 / 2) * ω)) -
          P t s / 2 * (bandWeight ω * sin ((((t - s - 1 : ℤ) : ℝ) + 1 / 2) * ω)) := by
      intro ω
      have hss := Real.sin_sub_sin ((((t - s : ℤ) : ℝ) + 1 / 2) * ω) ((((t - s - 1 : ℤ) : ℝ) + 1 / 2) * ω)
      push_cast at hss ⊢
      rw [show (((t : ℝ) - s + 1 / 2) * ω - ((t : ℝ) - s - 1 + 1 / 2) * ω) / 2 = ω / 2 by ring,
        show (((t : ℝ) - s + 1 / 2) * ω + ((t : ℝ) - s - 1 + 1 / 2) * ω) / 2 = ((t : ℝ) - s) * ω by ring] at hss
      linear_combination (-(bandWeight ω) * P t s / 2) * hss
    simp_rw [ident]
    rw [intervalIntegral.integral_sub ((hi _).const_mul _) ((hi _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    unfold bandKer
    ring
  simp_rw [term]
  simp_rw [← mul_sum]
  congr 1
  have hc : ∀ t s : ℤ, Continuous (fun ω => bandWeight ω *
      (sin (ω / 2) * cos (((t - s : ℤ) : ℝ) * ω) * P t s -
        η * sin ((((t - s : ℤ) : ℝ) + 1 / 2) * ω) * Kg t s)) := by
    intro t s; exact cw.mul (by fun_prop)
  simp_rw [mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl; intro t _
    rw [intervalIntegral.integral_finsetSum]
    intro s _; exact (hc t s).intervalIntegrable _ _
  · intro t _
    exact (continuous_finsetSum _ fun s _ => hc t s).intervalIntegrable _ _

lemma band_sin_ge {ω : ℝ} (hω : ω ∈ Set.Icc (π / 6) π) : bandEdge ≤ sin (ω / 2) := by
  unfold bandEdge
  apply Real.sin_le_sin_of_le_of_le_pi_div_two
  · linarith [pi_pos]
  · linarith [hω.2]
  · linarith [hω.1]

lemma band_form_nonneg (K : E →L[ℝ] F) {L η : ℝ} (hK : ‖K‖ ≤ L) (hη : 0 ≤ η) (hηL : η * L ≤ 1 / 2)
    (S : Finset ℤ) (xp : ℤ → E) (yp : ℤ → F) :
    0 ≤ ∑ t ∈ S, ∑ s ∈ S, ((bandKer (t - s) - bandKer (t - s - 1)) / 2 * (⟪xp t, xp s⟫ + ⟪yp t, yp s⟫) -
      η * bandKer (t - s) * ⟪yp t, K (xp s)⟫) := by
  rw [bandKer_integral_form]
  apply mul_nonneg (by positivity)
  apply intervalIntegral.integral_nonneg (by linarith [pi_pos])
  intro ω hω
  apply mul_nonneg (by unfold bandWeight; positivity)
  apply trig_form_nonneg K hK hη S xp yp ω
  have := band_sin_ge hω
  have := bandEdge_gt_quarter
  linarith

end OracleTemplate.ArrowHurwicz
