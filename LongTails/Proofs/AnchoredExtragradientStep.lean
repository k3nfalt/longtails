import LongTails.Algorithms.AnchoredExtragradient
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace OracleTemplate.GeneralizedMonotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma local_bound {F : E → E} {L0 L1 : ℝ} (hL0 : 0 ≤ L0) (hL1 : 0 ≤ L1) (hc : Continuous F)
    (hgl : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
      ‖F x - F y‖ ≤ (L0 + L1 * M) * ‖x - y‖)
    (x y : E) (hd : L1 * ‖x - y‖ ≤ 1) :
    ‖F x - F y‖ * (1 - L1 * ‖x - y‖) ≤ (L0 + L1 * ‖F x‖) * ‖x - y‖ := by
  have hcont : ContinuousOn (fun θ : ℝ => ‖F (x + θ • (y - x))‖) (Set.Icc 0 1) :=
    (hc.comp (by fun_prop)).norm.continuousOn
  obtain ⟨θs, hθs, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr zero_le_one) hcont
  have hle : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
      ‖F (x + θ • (y - x))‖ ≤ ‖F (x + θs • (y - x))‖ := fun θ hθ => hmax hθ
  have h1 := hgl x (x + θs • (y - x)) ‖F (x + θs • (y - x))‖ (by
    intro θ hθ
    have he : x + θ • (x + θs • (y - x) - x) = x + (θ * θs) • (y - x) := by
      rw [add_sub_cancel_left, smul_smul]
    rw [he]
    exact hle _ ⟨mul_nonneg hθ.1 hθs.1, by nlinarith [hθ.1, hθ.2, hθs.1, hθs.2]⟩)
  have h2 := hgl x y ‖F (x + θs • (y - x))‖ hle
  have hxz : ‖x - (x + θs • (y - x))‖ ≤ ‖x - y‖ := by
    rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθs.1,
      norm_sub_rev y x]
    exact mul_le_of_le_one_left (norm_nonneg _) hθs.2
  have hins := norm_le_insert (F x) (F (x + θs • (y - x)))
  have hM : 0 ≤ ‖F (x + θs • (y - x))‖ := norm_nonneg _
  generalize ‖F (x + θs • (y - x))‖ = M at h1 h2 hins hM
  have hd0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hc0 : 0 ≤ L0 + L1 * M := by positivity
  have h3 : M ≤ ‖F x‖ + (L0 + L1 * M) * ‖x - y‖ := by
    have := h1.trans (mul_le_mul_of_nonneg_left hxz hc0)
    linarith
  have h4 := mul_le_mul_of_nonneg_left h3 hL1
  have h5 : (L0 + L1 * M) * (1 - L1 * ‖x - y‖) ≤ L0 + L1 * ‖F x‖ := by nlinarith
  have h6 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hd)
  have h7 := mul_le_mul_of_nonneg_right h5 hd0
  nlinarith


lemma anchored_identity (u p q r : E) (S γ : ℝ) (hΓ : S + γ ≠ 0) (hγ : γ ≠ 0) :
    S ^ 2 / 2 * ‖p‖ ^ 2 + S * ⟪p, u⟫ -
        ((S + γ) ^ 2 / 2 * ‖r‖ ^ 2 + (S + γ) * ⟪r, (S / (S + γ)) • u - γ • q⟫) =
      S * (S + γ) / γ * ⟪r - p, -((γ / (S + γ)) • u) - γ • q⟫ +
        (S + γ) ^ 2 / 2 * (‖q - (S / (S + γ)) • p‖ ^ 2 - ‖r - q‖ ^ 2) := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm q p, real_inner_comm q r]
  field_simp
  ring

lemma distance_identity (A B p q : E) (t γ : ℝ) :
    ‖(1 - t) • A + t • B - γ • q‖ ^ 2 =
      (1 - t) * ‖A‖ ^ 2 + t * ‖B‖ ^ 2 - (1 - t) * t * ‖A - B‖ ^ 2 +
        γ ^ 2 * ‖q - t • p‖ ^ 2 - γ ^ 2 * t ^ 2 * ‖p‖ ^ 2 -
        2 * γ * ⟪q, (1 - t) • A + t • B - (t * γ) • p⟫ := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left,
    inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm B A,
    real_inner_comm q A, real_inner_comm q B, real_inner_comm q p]
  ring

structure Hyp (F : E → E) (L0 L1 : ℝ) : Prop where
  L0_pos : 0 < L0
  L1_nonneg : 0 ≤ L1
  cont : Continuous F
  mono : ∀ x y, 0 ≤ ⟪F x - F y, x - y⟫
  lip : ∀ x y M, (∀ θ ∈ Set.Icc (0 : ℝ) 1, ‖F (x + θ • (y - x))‖ ≤ M) →
    ‖F x - F y‖ ≤ (L0 + L1 * M) * ‖x - y‖

lemma Hyp.local {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) (x y : E)
    (hd : L1 * ‖x - y‖ ≤ 1) :
    ‖F x - F y‖ * (1 - L1 * ‖x - y‖) ≤ (L0 + L1 * ‖F x‖) * ‖x - y‖ :=
  local_bound h.L0_pos.le h.L1_nonneg h.cont h.lip x y hd

noncomputable def half (F : E → E) (a x : E) (S γ : ℝ) : E :=
  x + (γ / (S + γ)) • (a - x) - (S / (S + γ) * γ) • F x

noncomputable def full (F : E → E) (a x : E) (S γ : ℝ) : E :=
  x + (γ / (S + γ)) • (a - x) - γ • F (half F a x S γ)

lemma half_bounds {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) {a x : E} {S γ m : ℝ}
    (hS : 0 ≤ S) (hγ : 0 < γ) (hD : ‖x - a‖ ≤ (S + γ) * (m - ‖F x‖))
    (hstep : γ * (L0 + L1 * m) ≤ 1 / 4) :
    ‖F x‖ ≤ m ∧
    ‖half F a x S γ - x‖ ≤ γ / (S + γ) * ‖x - a‖ + S / (S + γ) * (γ * ‖F x‖) ∧
    ‖half F a x S γ - x‖ ≤ γ * m ∧
    γ * ‖F (half F a x S γ) - F x‖ ≤ ‖half F a x S γ - x‖ / 3 ∧
    ‖F (half F a x S γ) - F x‖ ≤ m / 3 := by
  have hΓ : 0 < S + γ := by linarith
  have hb0 : 0 ≤ γ / (S + γ) := by positivity
  have ht0 : 0 ≤ S / (S + γ) := by positivity
  have ht1 : S / (S + γ) ≤ 1 := (div_le_one hΓ).mpr (by linarith)
  have hD0 := norm_nonneg (x - a)
  have hp0 := norm_nonneg (F x)
  have hpm : ‖F x‖ ≤ m := by
    by_contra hlt
    push Not at hlt
    nlinarith [mul_pos hΓ (sub_pos.mpr hlt)]
  have hm0 : 0 ≤ m := hp0.trans hpm
  have hL0 := h.L0_pos
  have hL1 := h.L1_nonneg
  have h1 : ‖half F a x S γ - x‖ ≤ γ / (S + γ) * ‖x - a‖ + S / (S + γ) * (γ * ‖F x‖) := by
    have he : half F a x S γ - x = (γ / (S + γ)) • (a - x) - (S / (S + γ) * γ) • F x := by
      unfold half
      abel
    rw [he]
    calc ‖(γ / (S + γ)) • (a - x) - (S / (S + γ) * γ) • F x‖
        ≤ ‖(γ / (S + γ)) • (a - x)‖ + ‖(S / (S + γ) * γ) • F x‖ := norm_sub_le _ _
      _ = γ / (S + γ) * ‖x - a‖ + S / (S + γ) * (γ * ‖F x‖) := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hb0,
          abs_of_nonneg (mul_nonneg ht0 hγ.le), norm_sub_rev a x, mul_assoc]
  have e1 : γ / (S + γ) * ‖x - a‖ ≤ γ * (m - ‖F x‖) := by
    calc γ / (S + γ) * ‖x - a‖ ≤ γ / (S + γ) * ((S + γ) * (m - ‖F x‖)) :=
          mul_le_mul_of_nonneg_left hD hb0
      _ = γ * (m - ‖F x‖) := by field_simp
  have e2 : S / (S + γ) * (γ * ‖F x‖) ≤ γ * ‖F x‖ :=
    mul_le_of_le_one_left (mul_nonneg hγ.le hp0) ht1
  have h2 : ‖half F a x S γ - x‖ ≤ γ * m := by linarith
  have hd0 := norm_nonneg (half F a x S γ - x)
  have hLm : 0 ≤ L1 * m := mul_nonneg hL1 hm0
  have hLd : L1 * ‖x - half F a x S γ‖ ≤ 1 / 4 := by
    rw [norm_sub_rev]
    have := mul_le_mul_of_nonneg_left h2 hL1
    nlinarith [mul_pos hγ hL0]
  have hloc := h.local x (half F a x S γ) (by linarith)
  rw [norm_sub_rev x (half F a x S γ), norm_sub_rev (F x)] at hloc
  rw [norm_sub_rev x (half F a x S γ)] at hLd
  have hN0 := norm_nonneg (F (half F a x S γ) - F x)
  have a1 : 3 / 4 * ‖F (half F a x S γ) - F x‖ ≤ (L0 + L1 * m) * ‖half F a x S γ - x‖ := by
    have := mul_le_mul_of_nonneg_right
      (add_le_add_left (mul_le_mul_of_nonneg_left hpm hL1) L0) hd0
    nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hLd)]
  have a2 := mul_le_mul_of_nonneg_left a1 hγ.le
  have a3 := mul_le_mul_of_nonneg_right hstep hd0
  have a4 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ L0 + L1 * m)
  have a5 := mul_le_mul_of_nonneg_right hstep hm0
  refine ⟨hpm, h1, h2, by nlinarith, by nlinarith⟩

lemma full_bounds {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) {a x : E} {S γ m : ℝ}
    (hS : 0 ≤ S) (hγ : 0 < γ) (hD : ‖x - a‖ ≤ (S + γ) * (m - ‖F x‖))
    (hstep : γ * (L0 + L1 * m) ≤ 1 / 4) :
    ‖F (full F a x S γ) - F (half F a x S γ)‖ ≤
      ‖F (half F a x S γ) - (S / (S + γ)) • F x‖ := by
  obtain ⟨hpm, -, -, -, hqp⟩ := half_bounds h hS hγ hD hstep
  have hΓ : 0 < S + γ := by linarith
  have ht0 : 0 ≤ S / (S + γ) := by positivity
  have ht1 : S / (S + γ) ≤ 1 := (div_le_one hΓ).mpr (by linarith)
  have hp0 := norm_nonneg (F x)
  have hm0 : 0 ≤ m := hp0.trans hpm
  have hL0 := h.L0_pos
  have hL1 := h.L1_nonneg
  set q := F (half F a x S γ) with hq
  set W := ‖q - (S / (S + γ)) • F x‖ with hW
  have hW0 : 0 ≤ W := norm_nonneg _
  have hWm : W ≤ 4 / 3 * m := by
    have he : q - (S / (S + γ)) • F x = (q - F x) + (1 - S / (S + γ)) • F x := by module
    rw [hW, he]
    calc ‖(q - F x) + (1 - S / (S + γ)) • F x‖
        ≤ ‖q - F x‖ + ‖(1 - S / (S + γ)) • F x‖ := norm_add_le _ _
      _ = ‖q - F x‖ + (1 - S / (S + γ)) * ‖F x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ m / 3 + 1 * m := by
        have := mul_le_mul (by linarith : 1 - S / (S + γ) ≤ 1) hpm hp0 zero_le_one
        linarith
      _ = 4 / 3 * m := by ring
  have hqm : ‖q‖ ≤ 4 / 3 * m := by
    have := norm_le_insert' q (F x)
    linarith
  have hdist : ‖half F a x S γ - full F a x S γ‖ = γ * W := by
    have he : half F a x S γ - full F a x S γ = γ • (q - (S / (S + γ)) • F x) := by
      unfold full
      rw [← hq]
      unfold half
      module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
  have hγm : L1 * (γ * m) ≤ 1 / 4 := by nlinarith [mul_pos hγ hL0]
  have hLd : L1 * ‖half F a x S γ - full F a x S γ‖ ≤ 1 / 3 := by
    rw [hdist]
    have := mul_le_mul_of_nonneg_left hWm (mul_nonneg hL1 hγ.le)
    nlinarith
  have hloc := h.local (half F a x S γ) (full F a x S γ) (by linarith)
  rw [hdist, ← hq, norm_sub_rev q] at hloc
  rw [hdist] at hLd
  have hN0 := norm_nonneg (F (full F a x S γ) - q)
  have b1 : (L0 + L1 * ‖q‖) * (γ * W) ≤ 1 / 3 * W := by
    have c1 : γ * (L0 + L1 * ‖q‖) ≤ 1 / 3 := by
      have := mul_le_mul_of_nonneg_left hqm (mul_nonneg hγ.le hL1)
      nlinarith [mul_pos hγ hL0]
    have := mul_le_mul_of_nonneg_right c1 hW0
    nlinarith
  nlinarith [mul_nonneg hN0 (sub_nonneg.mpr (by linarith : L1 * (γ * W) ≤ 1))]

noncomputable def potential (F : E → E) (a x : E) (S : ℝ) : ℝ :=
  S ^ 2 / 2 * ‖F x‖ ^ 2 + S * ⟪F x, x - a⟫

lemma potential_step {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) {a x : E} {S γ m : ℝ}
    (hS : 0 ≤ S) (hγ : 0 < γ) (hD : ‖x - a‖ ≤ (S + γ) * (m - ‖F x‖))
    (hstep : γ * (L0 + L1 * m) ≤ 1 / 4) :
    potential F a (full F a x S γ) (S + γ) ≤ potential F a x S := by
  have hfull := full_bounds h hS hγ hD hstep
  have hΓ : 0 < S + γ := by linarith
  have hid := anchored_identity (x - a) (F x) (F (half F a x S γ)) (F (full F a x S γ)) S γ
    hΓ.ne' hγ.ne'
  have e1 : full F a x S γ - a = (S / (S + γ)) • (x - a) - γ • F (half F a x S γ) := by
    unfold full
    match_scalars <;> field_simp <;> ring
  have e2 : full F a x S γ - x = -((γ / (S + γ)) • (x - a)) - γ • F (half F a x S γ) := by
    unfold full
    module
  have hmono := h.mono (full F a x S γ) x
  rw [e2] at hmono
  have hsq : ‖F (full F a x S γ) - F (half F a x S γ)‖ ^ 2 ≤
      ‖F (half F a x S γ) - (S / (S + γ)) • F x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hfull 2
  have hc1 : 0 ≤ S * (S + γ) / γ := by positivity
  have := mul_nonneg hc1 hmono
  have hc2 : 0 ≤ (S + γ) ^ 2 / 2 := by positivity
  have := mul_nonneg hc2 (sub_nonneg.mpr hsq)
  unfold potential
  rw [e1]
  linarith

lemma distance_step {F : E → E} {L0 L1 : ℝ} (h : Hyp F L0 L1) {a x xs : E} {S γ : ℝ}
    (hS : 0 ≤ S) (hγ : 0 < γ) (hroot : F xs = 0) :
    ‖full F a x S γ - xs‖ ^ 2 ≤
      γ / (S + γ) * ‖a - xs‖ ^ 2 + S / (S + γ) * ‖x - xs‖ ^ 2 -
        γ / (S + γ) * (S / (S + γ)) * ‖x - a‖ ^ 2 +
        γ ^ 2 * ‖F (half F a x S γ) - (S / (S + γ)) • F x‖ ^ 2 -
        γ ^ 2 * (S / (S + γ)) ^ 2 * ‖F x‖ ^ 2 := by
  have hΓ : 0 < S + γ := by linarith
  have hb : γ / (S + γ) = 1 - S / (S + γ) := by field_simp; ring
  have hid := distance_identity (a - xs) (x - xs) (F x) (F (half F a x S γ)) (S / (S + γ)) γ
  have e1 : full F a x S γ - xs =
      (1 - S / (S + γ)) • (a - xs) + (S / (S + γ)) • (x - xs) - γ • F (half F a x S γ) := by
    unfold full
    rw [hb]
    module
  have e2 : half F a x S γ - xs =
      (1 - S / (S + γ)) • (a - xs) + (S / (S + γ)) • (x - xs) - (S / (S + γ) * γ) • F x := by
    unfold half
    rw [hb]
    module
  have hmono := h.mono (half F a x S γ) xs
  rw [hroot, sub_zero, e2] at hmono
  have e3 : a - xs - (x - xs) = a - x := by abel
  rw [e1, hid, e3, norm_sub_rev a x, hb]
  nlinarith [mul_nonneg hγ.le hmono]

end OracleTemplate.GeneralizedMonotone
