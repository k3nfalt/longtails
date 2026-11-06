import LongTails.Proofs.CappedCubicModel
import LongTails.Proofs.CubicRegularization

open scoped RealInnerProductSpace

noncomputable section

namespace LongTails.Proofs.QuasarCubicStep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def stepModel (g : E) (B : E →L[ℝ] E) (M : ℝ) (h : E) : ℝ :=
  ⟪g, h⟫ + ⟪h, B h⟫ / 2 + M / 6 * ‖h‖ ^ 3

lemma stepModel_eq (g : E) (B : E →L[ℝ] E) (M : ℝ) (h : E) :
    stepModel g B M h = CappedCubicModel.model B g 0 (M / 2) h := by
  simp only [stepModel, CappedCubicModel.model]
  ring

lemma stepModel_zero (g : E) (B : E →L[ℝ] E) (M : ℝ) : stepModel g B M 0 = 0 := by
  simp [stepModel]

lemma stepModel_lower (g : E) (B : E →L[ℝ] E) (M : ℝ) (h : E) :
    -‖g‖ * ‖h‖ - ‖B‖ * ‖h‖ ^ 2 / 2 + M / 6 * ‖h‖ ^ 3 ≤ stepModel g B M h := by
  have h₁ : -(‖g‖ * ‖h‖) ≤ ⟪g, h⟫ := by
    have := abs_real_inner_le_norm g h
    linarith [(abs_le.mp this).1]
  have h₂ : -(‖B‖ * ‖h‖ ^ 2) ≤ ⟪h, B h⟫ := by
    have hi := abs_real_inner_le_norm h (B h)
    have hb := B.le_opNorm h
    have : |⟪h, B h⟫| ≤ ‖B‖ * ‖h‖ ^ 2 := by
      calc |⟪h, B h⟫| ≤ ‖h‖ * ‖B h‖ := hi
        _ ≤ ‖h‖ * (‖B‖ * ‖h‖) := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
        _ = ‖B‖ * ‖h‖ ^ 2 := by ring
    linarith [(abs_le.mp this).1]
  simp only [stepModel]
  linarith

lemma stepModel_pos_far (g : E) (B : E →L[ℝ] E) {M : ℝ} (hM : 0 < M) (h : E)
    (hh : 6 * (‖g‖ + ‖B‖ + 1) / M + 1 ≤ ‖h‖) : 0 < stepModel g B M h := by
  have hlow := stepModel_lower g B M h
  set t := ‖h‖
  have hg := norm_nonneg g
  have hB := norm_nonneg B
  have hq : 0 ≤ 6 * (‖g‖ + ‖B‖ + 1) / M := by positivity
  have ht1 : 1 ≤ t := by linarith
  have hMt : 6 * (‖g‖ + ‖B‖ + 1) ≤ M * t := by
    have := (div_le_iff₀ hM).mp (show 6 * (‖g‖ + ‖B‖ + 1) / M ≤ t by linarith)
    linarith
  have key : (‖g‖ + ‖B‖ + 1) * t ^ 2 ≤ M / 6 * t ^ 3 := by
    have : (‖g‖ + ‖B‖ + 1) * t ^ 2 * 6 ≤ M * t * t ^ 2 := by
      have ht2 : 0 ≤ t ^ 2 := by positivity
      nlinarith
    nlinarith
  have hgt : ‖g‖ * t ≤ ‖g‖ * t ^ 2 := by
    have : t ≤ t ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left this hg
  have hBt : ‖B‖ * t ^ 2 / 2 ≤ ‖B‖ * t ^ 2 := by
    have : 0 ≤ ‖B‖ * t ^ 2 := by positivity
    linarith
  have hpos : 0 < t ^ 2 := by positivity
  nlinarith

lemma exists_global_step [FiniteDimensional ℝ E] (g : E) (B : E →L[ℝ] E) {M : ℝ}
    (hM : 0 < M) (hB : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    ∃ h : E, (∀ u, stepModel g B M h ≤ stepModel g B M u) ∧
      g + B h + (M / 2 * ‖h‖) • h = 0 := by
  set ρ : ℝ := 6 * (‖g‖ + ‖B‖ + 1) / M + 1
  have hρ : 0 < ρ := by positivity
  obtain ⟨s, hs, hmin⟩ := CappedCubicModel.model_exists_min B g 0 (M / 2) hρ
  have hsρ : ‖s‖ ≤ ρ := by simpa using hs
  have hmin' : ∀ u ∈ Metric.closedBall (0 : E) ρ, stepModel g B M s ≤ stepModel g B M u := by
    intro u hu
    rw [stepModel_eq, stepModel_eq]
    exact hmin hu
  have hs0 : stepModel g B M s ≤ 0 := by
    have := hmin' 0 (by simp [hρ.le])
    simpa [stepModel_zero] using this
  have hslt : ‖s‖ < ρ := by
    by_contra hc
    have := stepModel_pos_far g B hM s (by push Not at hc; linarith)
    linarith
  refine ⟨s, ?_, ?_⟩
  · intro u
    by_cases hu : ‖u‖ ≤ ρ
    · exact hmin' u (by simpa using hu)
    · have := stepModel_pos_far g B hM u (by push Not at hu; linarith)
      linarith
  · obtain ⟨μ, _, heq, hcap⟩ := CappedCubicModel.multiplier_of_min_ball hρ hsρ
      (CappedCubicModel.model_hasFDerivAt B g 0 (M / 2) s hB) hmin
    have hμ : μ = 0 := by
      rcases mul_eq_zero.mp hcap with h | h
      · exact h
      · exact absurd (by linarith : ‖s‖ = ρ) (ne_of_lt hslt)
    rw [hμ, zero_smul, add_zero] at heq
    convert heq using 2
    ring_nf


open Classical in
def cubicStep (g : E) (B : E →L[ℝ] E) (M : ℝ) : E :=
  if h : ∃ h : E, (∀ u, stepModel g B M h ≤ stepModel g B M u) ∧
      g + B h + (M / 2 * ‖h‖) • h = 0 then h.choose else 0

lemma cubicStep_spec [FiniteDimensional ℝ E] (g : E) (B : E →L[ℝ] E) {M : ℝ}
    (hM : 0 < M) (hB : ∀ x y : E, ⟪x, B y⟫ = ⟪B x, y⟫) :
    (∀ u, stepModel g B M (cubicStep g B M) ≤ stepModel g B M u) ∧
      g + B (cubicStep g B M) + (M / 2 * ‖cubicStep g B M‖) • cubicStep g B M = 0 := by
  have hex := exists_global_step g B hM hB
  simp only [cubicStep, hex, ↓reduceDIte]
  exact hex.choose_spec

def envelope (M : ℝ) (r : ℝ × E × (E →L[ℝ] E)) : ℝ :=
  r.1 + stepModel r.2.1 r.2.2 M (cubicStep r.2.1 r.2.2 M)

section Analysis

variable [FiniteDimensional ℝ E] {f : E → ℝ} {g : E → E} {A : E → E →L[ℝ] E} {H M : ℝ}

lemma envelope_le (hM : 0 < M) (y0 : E) (hB : ∀ x y : E, ⟪x, A y0 y⟫ = ⟪A y0 x, y⟫) :
    envelope M (f y0, g y0, A y0) ≤ f y0 := by
  have := (cubicStep_spec (g y0) (A y0) hM hB).1 0
  simp only [envelope, stepModel_zero] at this ⊢
  linarith

lemma envelope_le_model (hM : 0 < M) (y0 : E) (hB : ∀ x y : E, ⟪x, A y0 y⟫ = ⟪A y0 x, y⟫)
    (h : E) : envelope M (f y0, g y0, A y0) ≤ f y0 + stepModel (g y0) (A y0) M h := by
  have := (cubicStep_spec (g y0) (A y0) hM hB).1 h
  simp only [envelope]
  linarith

omit [FiniteDimensional ℝ E] in
lemma step_descent
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x) (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) (y0 : E) :
    f (y0 + cubicStep (g y0) (A y0) M) ≤
      envelope M (f y0, g y0, A y0) - (M - H) / 6 * ‖cubicStep (g y0) (A y0) M‖ ^ 3 := by
  set h := cubicStep (g y0) (A y0) M
  have ht := CubicRegularization.objective_taylor hf hg hLip y0 h
  have hup := (abs_le.mp ht).2
  simp only [envelope, stepModel]
  linarith

lemma step_gradient
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) (hM : 0 < M) (y0 : E)
    (hB : ∀ x y : E, ⟪x, A y0 y⟫ = ⟪A y0 x, y⟫) :
    ‖g (y0 + cubicStep (g y0) (A y0) M) +
        (M / 2 * ‖cubicStep (g y0) (A y0) M‖) • cubicStep (g y0) (A y0) M‖ ≤
      H * ‖cubicStep (g y0) (A y0) M‖ ^ 2 / 2 := by
  set h := cubicStep (g y0) (A y0) M
  have hs := (cubicStep_spec (g y0) (A y0) hM hB).2
  have ht := CubicRegularization.gradient_taylor hg hLip y0 h
  have he : g (y0 + h) + (M / 2 * ‖h‖) • h = g (y0 + h) - g y0 - A y0 h := by
    have : (M / 2 * ‖h‖) • h = -(g y0 + A y0 h) := by
      rw [eq_neg_iff_add_eq_zero]
      rw [← hs]
      abel
    rw [this]
    abel
  rw [he]
  exact ht

lemma step_inner
    (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) (hM : 0 < M) (y0 : E)
    (hB : ∀ x y : E, ⟪x, A y0 y⟫ = ⟪A y0 x, y⟫) :
    (M - H) / 2 * ‖cubicStep (g y0) (A y0) M‖ ^ 3 ≤
        ⟪g (y0 + cubicStep (g y0) (A y0) M), -cubicStep (g y0) (A y0) M⟫ ∧
      ‖g (y0 + cubicStep (g y0) (A y0) M)‖ ≤
        (M + H) / 2 * ‖cubicStep (g y0) (A y0) M‖ ^ 2 := by
  set h := cubicStep (g y0) (A y0) M
  set e := g (y0 + h) + (M / 2 * ‖h‖) • h
  have he := step_gradient hg hLip hM y0 hB
  change ‖e‖ ≤ H * ‖h‖ ^ 2 / 2 at he
  have hgz : g (y0 + h) = e - (M / 2 * ‖h‖) • h := by simp [e]
  constructor
  · rw [hgz, inner_sub_left, inner_neg_right, inner_neg_right, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    have hc := abs_real_inner_le_norm e h
    have := (abs_le.mp hc).2
    have hn := norm_nonneg h
    nlinarith
  · rw [hgz]
    calc ‖e - (M / 2 * ‖h‖) • h‖ ≤ ‖e‖ + ‖(M / 2 * ‖h‖) • h‖ := norm_sub_le _ _
      _ ≤ H * ‖h‖ ^ 2 / 2 + M / 2 * ‖h‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith [norm_nonneg h]
      _ = (M + H) / 2 * ‖h‖ ^ 2 := by ring

lemma envelope_increment
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x) (hg : ∀ x, HasFDerivAt g (A x) x)
    (hLip : ∀ x y, ‖A x - A y‖ ≤ H * ‖x - y‖) (hM : 0 < M)
    (hsym : ∀ z, ∀ x y : E, ⟪x, A z y⟫ = ⟪A z x, y⟫) (y0 w : E) :
    envelope M (f (y0 + w), g (y0 + w), A (y0 + w)) - envelope M (f y0, g y0, A y0) ≤
      ⟪g (y0 + cubicStep (g y0) (A y0) M), w⟫ +
        H * ‖cubicStep (g y0) (A y0) M‖ ^ 2 * ‖w‖ +
        (‖A y0‖ / 2 + H / 2 * ‖cubicStep (g y0) (A y0) M‖ + H / 6 * ‖w‖) * ‖w‖ ^ 2 := by
  set h := cubicStep (g y0) (A y0) M
  have hplug := envelope_le_model (f := f) (g := g) (A := A) hM (y0 + w) (hsym _) h
  have hs := (cubicStep_spec (g y0) (A y0) hM (hsym y0)).2
  have hge := step_gradient hg hLip hM y0 (hsym y0)
  have ha := (abs_le.mp (CubicRegularization.objective_taylor hf hg hLip y0 w)).2
  have hb := CubicRegularization.gradient_taylor hg hLip y0 w
  have hbi : ⟪g (y0 + w) - g y0 - A y0 w, h⟫ ≤ H * ‖w‖ ^ 2 / 2 * ‖h‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  have hc : ⟪h, (A (y0 + w) - A y0) h⟫ ≤ H * ‖w‖ * ‖h‖ ^ 2 := by
    have h1 := real_inner_le_norm h ((A (y0 + w) - A y0) h)
    have h2 := (A (y0 + w) - A y0).le_opNorm h
    have h3 := hLip (y0 + w) y0
    rw [add_sub_cancel_left] at h3
    have h4 : ‖(A (y0 + w) - A y0) h‖ ≤ H * ‖w‖ * ‖h‖ :=
      h2.trans (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
    calc _ ≤ ‖h‖ * ‖(A (y0 + w) - A y0) h‖ := h1
      _ ≤ ‖h‖ * (H * ‖w‖ * ‖h‖) := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
      _ = H * ‖w‖ * ‖h‖ ^ 2 := by ring
  have hd : ⟪g y0, w⟫ + ⟪A y0 w, h⟫ ≤ ⟪g (y0 + h), w⟫ + H * ‖h‖ ^ 2 / 2 * ‖w‖ := by
    have hsw : ⟪A y0 w, h⟫ = ⟪A y0 h, w⟫ := by
      rw [← hsym y0 w h, real_inner_comm]
    have hlin : g y0 + A y0 h = -((M / 2 * ‖h‖) • h) := by
      rw [eq_neg_iff_add_eq_zero, ← hs]
    have hgw : ⟪g y0, w⟫ + ⟪A y0 h, w⟫ =
        ⟪g (y0 + h), w⟫ - ⟪g (y0 + h) + (M / 2 * ‖h‖) • h, w⟫ := by
      rw [← inner_add_left, hlin, inner_add_left, inner_neg_left]
      ring
    have hi := real_inner_le_norm (g (y0 + h) + (M / 2 * ‖h‖) • h) w
    have hi' := neg_le_of_abs_le (abs_real_inner_le_norm (g (y0 + h) + (M / 2 * ‖h‖) • h) w)
    have hm := mul_le_mul_of_nonneg_right hge (norm_nonneg w)
    rw [hsw, hgw]
    linarith
  have he : ⟪w, A y0 w⟫ ≤ ‖A y0‖ * ‖w‖ ^ 2 := by
    have h1 := real_inner_le_norm w (A y0 w)
    have h2 := (A y0).le_opNorm w
    calc _ ≤ ‖w‖ * ‖A y0 w‖ := h1
      _ ≤ ‖w‖ * (‖A y0‖ * ‖w‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ‖A y0‖ * ‖w‖ ^ 2 := by ring
  have hsplit : ⟪g (y0 + w), h⟫ = ⟪g y0, h⟫ + ⟪A y0 w, h⟫ + ⟪g (y0 + w) - g y0 - A y0 w, h⟫ := by
    simp only [inner_sub_left]
    ring
  have hAsplit : ⟪h, A (y0 + w) h⟫ = ⟪h, A y0 h⟫ + ⟪h, (A (y0 + w) - A y0) h⟫ := by
    simp only [sub_apply, inner_sub_right]
    ring
  simp only [envelope, stepModel] at hplug ⊢
  rw [hsplit, hAsplit] at hplug
  have hn := norm_nonneg h
  have hw := norm_nonneg w
  nlinarith

end Analysis

end LongTails.Proofs.QuasarCubicStep
