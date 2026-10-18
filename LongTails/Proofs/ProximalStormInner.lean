import LongTails.Proofs.ProximalStormProx

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace OracleTemplate.ProximalStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] {Ω : Type} [MeasurableSpace Ω]

noncomputable def innerStep (g : E → Ω → E) (lam eta a : ℝ) (xt : E) (s : E × E) (ω : Ω) :
    E × E :=
  (s.1 - eta • s.2,
    g (s.1 - eta • s.2) ω + (1 / lam) • (s.1 - eta • s.2 - xt) +
      (1 - a) • (s.2 - (g s.1 ω + (1 / lam) • (s.1 - xt))))

noncomputable def innerErr (f : E → ℝ) (lam : ℝ) (xt : E) (s : E × E) : E :=
  s.2 - phiGrad f lam xt s.1

noncomputable def innerGap (f : E → ℝ) (lam : ℝ) (xt x : E) : ℝ :=
  phi f lam xt x - phi f lam xt (prox f lam xt)

noncomputable def innerPot (f : E → ℝ) (lam eta a Γh : ℝ) (xt : E) (s : E × E) : ℝ :=
  innerGap f lam xt s.1 + eta / a * ‖innerErr f lam xt s‖ ^ 2 -
    4 * eta * a * Γh ^ 2 * ‖phiGrad f lam xt s.1‖ ^ 2

omit [MeasurableSpace E] [MeasurableSpace Ω] in
lemma innerErr_step (f : E → ℝ) (g : E → Ω → E) (lam eta a : ℝ) (xt : E) (s : E × E) (ω : Ω) :
    innerErr f lam xt (innerStep g lam eta a xt s ω) =
      (1 - a) • innerErr f lam xt s +
        (a • (g (s.1 - eta • s.2) ω - gradient f (s.1 - eta • s.2)) +
          (1 - a) • ((g (s.1 - eta • s.2) ω - gradient f (s.1 - eta • s.2)) -
            (g s.1 ω - gradient f s.1))) := by
  simp only [innerErr, innerStep, phiGrad]
  module

omit [MeasurableSpace E] in
lemma sq_norm_add_mean_zero {p : Measure Ω} [IsProbabilityMeasure p] (u : E) {W : Ω → E}
    (hW : Integrable W p) (hW2 : Integrable (fun ω => ‖W ω‖ ^ 2) p) (h0 : ∫ ω, W ω ∂p = 0) :
    Integrable (fun ω => ‖u + W ω‖ ^ 2) p ∧
      ∫ ω, ‖u + W ω‖ ^ 2 ∂p = ‖u‖ ^ 2 + ∫ ω, ‖W ω‖ ^ 2 ∂p := by
  have he : (fun ω => ‖u + W ω‖ ^ 2) = fun ω => (‖u‖ ^ 2 + 2 * ⟪u, W ω⟫) + ‖W ω‖ ^ 2 := by
    funext ω; rw [norm_add_sq_real]
  have hi : Integrable (fun ω => ⟪u, W ω⟫) p := hW.const_inner u
  have h1 : Integrable (fun ω => ‖u‖ ^ 2 + 2 * ⟪u, W ω⟫) p :=
    (integrable_const _).add (hi.const_mul 2)
  rw [he]
  refine ⟨h1.add hW2, ?_⟩
  rw [integral_add h1 hW2, integral_add (integrable_const _) (hi.const_mul 2), integral_const_mul,
    integral_inner hW u, h0, inner_zero_right]
  simp

section Step

variable {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
  {Lbar Γ : ℝ} {xstar : E}

lemma Hyp.zeta_int (H : Hyp p f g Lbar Γ xstar) (x : E) :
    Integrable (fun ω => g x ω - gradient f x) p := (H.int x).sub (integrable_const _)

lemma Hyp.zeta_mean (H : Hyp p f g Lbar Γ xstar) (x : E) :
    ∫ ω, (g x ω - gradient f x) ∂p = 0 := by
  rw [integral_sub (H.int x) (integrable_const _), H.mean, integral_const]
  simp

lemma Hyp.innerErr_moment (H : Hyp p f g Lbar Γ xstar) {lam eta a : ℝ} (hlam : 0 < lam)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (xt : E) (s : E × E) :
    Integrable (fun ω => ‖innerErr f lam xt (innerStep g lam eta a xt s ω)‖ ^ 2) p ∧
      ∫ ω, ‖innerErr f lam xt (innerStep g lam eta a xt s ω)‖ ^ 2 ∂p ≤
        (1 - a) ^ 2 * ‖innerErr f lam xt s‖ ^ 2 +
          2 * a ^ 2 * (2 * Γ ^ 2 * ‖xt - prox f lam xt‖ ^ 2 / lam ^ 2 +
            2 * Lbar ^ 2 * lam ^ 2 * ‖phiGrad f lam xt (s.1 - eta • s.2)‖ ^ 2) +
          2 * (Lbar ^ 2 * (eta ^ 2 * ‖s.2‖ ^ 2)) := by
  set x' := s.1 - eta • s.2
  set Z : Ω → E := fun ω => g x' ω - gradient f x'
  set C : Ω → E := fun ω => (g x' ω - gradient f x') - (g s.1 ω - gradient f s.1)
  set W : Ω → E := fun ω => a • Z ω + (1 - a) • C ω
  have hZ : Integrable Z p := H.zeta_int x'
  have hC : Integrable C p := (H.zeta_int x').sub (H.zeta_int s.1)
  have hZ2 : Integrable (fun ω => ‖Z ω‖ ^ 2) p := H.var_int x'
  obtain ⟨hC2, hCb⟩ := H.centered_diff x' s.1
  have hZa : Integrable (fun ω => a • Z ω) p := hZ.smul a
  have hCa : Integrable (fun ω => (1 - a) • C ω) p := hC.smul (1 - a)
  have hWi : Integrable W p := hZa.add hCa
  have hW0 : ∫ ω, W ω ∂p = 0 := by
    simp only [W]
    rw [integral_add hZa hCa, integral_smul, integral_smul]
    have hz : ∫ ω, Z ω ∂p = 0 := H.zeta_mean x'
    have hc : ∫ ω, C ω ∂p = 0 := by
      simp only [C]
      rw [integral_sub (H.zeta_int x') (H.zeta_int s.1), H.zeta_mean, H.zeta_mean, sub_zero]
    rw [hz, hc, smul_zero, smul_zero, add_zero]
  have hWpt : ∀ ω, ‖W ω‖ ^ 2 ≤ 2 * a ^ 2 * ‖Z ω‖ ^ 2 + 2 * ‖C ω‖ ^ 2 := by
    intro ω
    have h := NormalizedStorm.sq_norm_add_le (a • Z ω) ((1 - a) • C ω)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0,
      abs_of_nonneg (by linarith)] at h
    have h1 : (1 - a) ^ 2 ≤ 1 := by nlinarith
    have h2 : ((1 - a) * ‖C ω‖) ^ 2 ≤ ‖C ω‖ ^ 2 := by
      rw [mul_pow]; nlinarith [sq_nonneg ‖C ω‖]
    nlinarith [sq_nonneg (a * ‖Z ω‖)]
  have hdom : Integrable (fun ω => 2 * a ^ 2 * ‖Z ω‖ ^ 2 + 2 * ‖C ω‖ ^ 2) p :=
    (hZ2.const_mul _).add (hC2.const_mul _)
  have hW2 : Integrable (fun ω => ‖W ω‖ ^ 2) p :=
    hdom.mono' ((hWi.aestronglyMeasurable.norm.pow 2))
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hWpt ω)
  have hrw : ∀ ω, innerErr f lam xt (innerStep g lam eta a xt s ω) =
      (1 - a) • innerErr f lam xt s + W ω := fun ω => innerErr_step f g lam eta a xt s ω
  simp_rw [hrw]
  obtain ⟨hi, he⟩ := sq_norm_add_mean_zero ((1 - a) • innerErr f lam xt s) hWi hW2 hW0
  refine ⟨hi, ?_⟩
  rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hWb := integral_mono hW2 hdom hWpt
  rw [integral_add (hZ2.const_mul _) (hC2.const_mul _), integral_const_mul,
    integral_const_mul] at hWb
  have hZb := H.noise_bound hlam xt x'
  have hd : ‖x' - s.1‖ = eta * ‖s.2‖ ∨ True := Or.inr trivial
  clear hd
  have hx : ‖x' - s.1‖ ^ 2 = eta ^ 2 * ‖s.2‖ ^ 2 := by
    simp only [x']
    rw [show s.1 - eta • s.2 - s.1 = -(eta • s.2) by abel, norm_neg, norm_smul, Real.norm_eq_abs,
      mul_pow, sq_abs]
  rw [hx] at hCb
  have : 2 * a ^ 2 * ∫ ω, ‖Z ω‖ ^ 2 ∂p ≤
      2 * a ^ 2 * (2 * Γ ^ 2 * ‖xt - prox f lam xt‖ ^ 2 / lam ^ 2 +
        2 * Lbar ^ 2 * lam ^ 2 * ‖phiGrad f lam xt x'‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hZb (by positivity)
  linarith


structure InnerTune (Lbar lam eta a Γh : ℝ) : Prop where
  lam_pos : 0 < lam
  eta_nn : 0 ≤ eta
  a_pos : 0 < a
  a_le : a ≤ 1
  smooth : eta * (Lbar + 1 / lam) ≤ 1 / 2
  diff : 8 * Lbar ^ 2 * eta ^ 2 ≤ a
  scale : Lbar * lam ≤ Γh
  growth : 16 * a * Γh ^ 2 ≤ 1

lemma Hyp.gap_descent (H : Hyp p f g Lbar Γ xstar) {lam eta : ℝ} (hlam : 0 < lam)
    (heta : 0 ≤ eta) (hs : eta * (Lbar + 1 / lam) ≤ 1 / 2) (xt : E) (s : E × E) :
    innerGap f lam xt (s.1 - eta • s.2) ≤ innerGap f lam xt s.1 -
      eta / 2 * ‖phiGrad f lam xt s.1‖ ^ 2 - eta / 4 * ‖s.2‖ ^ 2 +
        eta / 2 * ‖innerErr f lam xt s‖ ^ 2 := by
  have h := H.phi_smooth hlam xt s.1 (s.1 - eta • s.2)
  have hx : s.1 - eta • s.2 - s.1 = -(eta • s.2) := by abel
  rw [hx, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg heta] at h
  have hpol : ‖innerErr f lam xt s‖ ^ 2 =
      ‖s.2‖ ^ 2 - 2 * ⟪phiGrad f lam xt s.1, s.2⟫ + ‖phiGrad f lam xt s.1‖ ^ 2 := by
    simp only [innerErr]; rw [norm_sub_sq_real, real_inner_comm]
  have hq : (Lbar + 1 / lam) / 2 * (eta * ‖s.2‖) ^ 2 ≤ eta / 4 * ‖s.2‖ ^ 2 := by
    have h0 : 0 ≤ eta * ‖s.2‖ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hs h0
    nlinarith
  simp only [innerGap]
  nlinarith

lemma Hyp.pot_bounds (H : Hyp p f g Lbar Γ xstar) {lam eta a Γh : ℝ}
    (T : InnerTune Lbar lam eta a Γh) (xt : E) (s : E × E) :
    3 / 4 * innerGap f lam xt s.1 + eta / a * ‖innerErr f lam xt s‖ ^ 2 ≤
        innerPot f lam eta a Γh xt s ∧
      innerPot f lam eta a Γh xt s ≤
        innerGap f lam xt s.1 + eta / a * ‖innerErr f lam xt s‖ ^ 2 := by
  have hg := H.phiGrad_sq_le T.lam_pos xt s.1
  have hgap0 : 0 ≤ innerGap f lam xt s.1 := by
    simp only [innerGap]; linarith [H.phi_prox_le T.lam_pos xt s.1]
  have hM : 0 ≤ Lbar + 1 / lam := by have := H.Lbar_pos; have := T.lam_pos; positivity
  have hc : 0 ≤ 4 * eta * a * Γh ^ 2 := by have := T.eta_nn; have := T.a_pos; positivity
  have hprod : 8 * (eta * (Lbar + 1 / lam)) * (a * Γh ^ 2) ≤ 1 / 4 := by
    have h1 := T.smooth
    have h2 : a * Γh ^ 2 ≤ 1 / 16 := by linarith [T.growth]
    have h3 : 0 ≤ eta * (Lbar + 1 / lam) := mul_nonneg T.eta_nn hM
    have h4 : 0 ≤ a * Γh ^ 2 := by have := T.a_pos; positivity
    nlinarith
  have hb : 4 * eta * a * Γh ^ 2 * ‖phiGrad f lam xt s.1‖ ^ 2 ≤
      1 / 4 * innerGap f lam xt s.1 := by
    have := mul_le_mul_of_nonneg_left hg hc
    simp only [innerGap] at hgap0 ⊢
    nlinarith
  have hn : 0 ≤ 4 * eta * a * Γh ^ 2 * ‖phiGrad f lam xt s.1‖ ^ 2 := by positivity
  constructor <;> simp only [innerPot] <;> linarith

lemma Hyp.pot_step (H : Hyp p f g Lbar Γ xstar) {lam eta a Γh : ℝ}
    (T : InnerTune Lbar lam eta a Γh) (xt : E) (s : E × E) :
    Integrable (fun ω => innerPot f lam eta a Γh xt (innerStep g lam eta a xt s ω)) p ∧
      ∫ ω, innerPot f lam eta a Γh xt (innerStep g lam eta a xt s ω) ∂p ≤
        innerPot f lam eta a Γh xt s - eta / 4 * ‖phiGrad f lam xt s.1‖ ^ 2 -
          eta / 2 * ‖innerErr f lam xt s‖ ^ 2 +
            4 * eta * a * Γ ^ 2 * ‖xt - prox f lam xt‖ ^ 2 / lam ^ 2 := by
  have hlam := T.lam_pos
  have ha := T.a_pos
  obtain ⟨hi, hb⟩ := H.innerErr_moment hlam ha.le T.a_le (eta := eta) xt s
  set x' := s.1 - eta • s.2
  have hfst : ∀ ω, (innerStep g lam eta a xt s ω).1 = x' := fun _ => rfl
  have hpot : ∀ ω, innerPot f lam eta a Γh xt (innerStep g lam eta a xt s ω) =
      (innerGap f lam xt x' - 4 * eta * a * Γh ^ 2 * ‖phiGrad f lam xt x'‖ ^ 2) +
        eta / a * ‖innerErr f lam xt (innerStep g lam eta a xt s ω)‖ ^ 2 := by
    intro ω; simp only [innerPot, hfst]; ring
  simp_rw [hpot]
  refine ⟨(integrable_const _).add (hi.const_mul _), ?_⟩
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const, integral_const_mul]
  simp only [probReal_univ, one_smul]
  have hd := H.gap_descent hlam T.eta_nn T.smooth xt s
  set G2 := ‖phiGrad f lam xt s.1‖ ^ 2
  set E2 := ‖innerErr f lam xt s‖ ^ 2
  set D2 := ‖s.2‖ ^ 2
  set G2' := ‖phiGrad f lam xt x'‖ ^ 2
  set Dd := ‖xt - prox f lam xt‖ ^ 2
  set I := ∫ ω, ‖innerErr f lam xt (innerStep g lam eta a xt s ω)‖ ^ 2 ∂p
  have hE2 : 0 ≤ E2 := sq_nonneg _
  have hD2 : 0 ≤ D2 := sq_nonneg _
  have hG2' : 0 ≤ G2' := sq_nonneg _
  have heta := T.eta_nn
  have hscale : Lbar ^ 2 * lam ^ 2 ≤ Γh ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by have := H.Lbar_pos; positivity) T.scale 2
  have hea : 0 ≤ eta / a := div_nonneg heta ha.le
  have h1 : eta / a * I ≤ eta / a * ((1 - a) ^ 2 * E2 +
      2 * a ^ 2 * (2 * Γ ^ 2 * Dd / lam ^ 2 + 2 * Lbar ^ 2 * lam ^ 2 * G2') +
        2 * (Lbar ^ 2 * (eta ^ 2 * D2))) := mul_le_mul_of_nonneg_left hb hea
  have h2 : eta / a * ((1 - a) ^ 2 * E2) ≤ (eta / a - eta) * E2 := by
    have : (1 - a) ^ 2 ≤ 1 - a := by nlinarith [T.a_le]
    have h3 : eta / a * (1 - a) = eta / a - eta := by field_simp
    calc eta / a * ((1 - a) ^ 2 * E2) = (eta / a * (1 - a) ^ 2) * E2 := by ring
      _ ≤ (eta / a * (1 - a)) * E2 := by
          gcongr
      _ = (eta / a - eta) * E2 := by rw [h3]
  have h4 : eta / a * (2 * a ^ 2 * (2 * Lbar ^ 2 * lam ^ 2 * G2')) ≤
      4 * eta * a * Γh ^ 2 * G2' := by
    have : eta / a * (2 * a ^ 2 * (2 * Lbar ^ 2 * lam ^ 2 * G2')) =
        4 * eta * a * (Lbar ^ 2 * lam ^ 2) * G2' := by field_simp; ring
    rw [this]
    gcongr
  have h5 : eta / a * (2 * (Lbar ^ 2 * (eta ^ 2 * D2))) ≤ eta / 4 * D2 := by
    have : eta / a * (2 * (Lbar ^ 2 * (eta ^ 2 * D2))) =
        eta * D2 * (2 * Lbar ^ 2 * eta ^ 2) / a := by field_simp
    rw [this, div_le_iff₀ ha]
    have hdiff := T.diff
    have : 0 ≤ eta * D2 := mul_nonneg heta hD2
    nlinarith
  have h6 : eta / a * (2 * a ^ 2 * (2 * Γ ^ 2 * Dd / lam ^ 2)) =
      4 * eta * a * Γ ^ 2 * Dd / lam ^ 2 := by field_simp; ring
  have h7 : 4 * eta * a * Γh ^ 2 * G2 ≤ eta / 4 * G2 := by
    have := T.growth
    have : 0 ≤ eta * G2 := mul_nonneg heta (sq_nonneg _)
    nlinarith
  have hexp : eta / a * ((1 - a) ^ 2 * E2 +
      2 * a ^ 2 * (2 * Γ ^ 2 * Dd / lam ^ 2 + 2 * Lbar ^ 2 * lam ^ 2 * G2') +
        2 * (Lbar ^ 2 * (eta ^ 2 * D2))) =
      eta / a * ((1 - a) ^ 2 * E2) + eta / a * (2 * a ^ 2 * (2 * Γ ^ 2 * Dd / lam ^ 2)) +
        eta / a * (2 * a ^ 2 * (2 * Lbar ^ 2 * lam ^ 2 * G2')) +
          eta / a * (2 * (Lbar ^ 2 * (eta ^ 2 * D2))) := by ring
  simp only [innerPot]
  linarith

end Step

end OracleTemplate.ProximalStorm
