import LongTails.Proofs.TwoSidedPerceptronDynamics

open scoped RealInnerProductSpace

namespace LongTails.Proofs.TwoSidedPerceptronPotential

open TwoSidedPerceptronDynamics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Step

variable {c δ C : ℝ} {p r : E} {x : State E}

lemma mistake_inner_le (hm : margin c δ p r x ≤ 0) :
    δ * ⟪feature p r x, x.z⟫ ≤ -(c * x.a * x.q) := by
  unfold margin at hm; linarith

lemma inner_feature_le (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1) :
    |⟪feature p r x, x.z⟫| ≤ (|x.a| + |x.t|) * ‖x.z‖ := by
  have h := abs_real_inner_le_norm (feature p r x) x.z
  have hf := feature_norm_le hp hr x
  calc
    _ ≤ ‖feature p r x‖ * ‖x.z‖ := h
    _ ≤ _ := mul_le_mul_of_nonneg_right hf (norm_nonneg _)

lemma forcing_le (hδ : 0 ≤ δ) (hp : ‖p‖ ≤ 1) : |δ * ⟪p, x.z⟫| ≤ δ * ‖x.z‖ := by
  rw [abs_mul, abs_of_nonneg hδ]
  have h := abs_real_inner_le_norm p x.z
  calc
    δ * |⟪p, x.z⟫| ≤ δ * (‖p‖ * ‖x.z‖) := by gcongr
    _ ≤ δ * (1 * ‖x.z‖) := by gcongr
    _ = _ := by ring

lemma expanding_gate (hδ : 0 ≤ δ) (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1)
    (hm : margin c δ p r x ≤ 0) (_hpos : 0 < c * x.a * x.q) :
    c * x.a * x.q ≤ δ * ((|x.a| + |x.t|) * ‖x.z‖) := by
  have h1 : c * x.a * x.q ≤ -(δ * ⟪feature p r x, x.z⟫) := by
    have := mistake_inner_le hm; linarith
  have h2 : -(δ * ⟪feature p r x, x.z⟫) ≤ δ * |⟪feature p r x, x.z⟫| := by
    have := neg_abs_le (δ * ⟪feature p r x, x.z⟫)
    rw [abs_mul, abs_of_nonneg hδ] at this
    linarith
  have h3 : δ * |⟪feature p r x, x.z⟫| ≤ δ * ((|x.a| + |x.t|) * ‖x.z‖) :=
    mul_le_mul_of_nonneg_left (inner_feature_le hp hr) hδ
  linarith

set_option maxHeartbeats 1000000 in
lemma potential_step_le (hδ : 0 ≤ δ) (hcC : |c| ≤ C) (hC : C ≤ 1 / 8)
    (hp : ‖p‖ ≤ 1) (hr : ‖r‖ ≤ 1) (hm : margin c δ p r x ≤ 0) :
    potential C (step c δ p r x) ≤
      potential C x + 4 * C * δ * ((|x.a| + |x.t|) * ‖x.z‖) +
        δ ^ 2 * (|x.a| + |x.t|) ^ 2 + 3 * mass x * (δ * ‖x.z‖) + 2 * (δ * ‖x.z‖) ^ 2 := by
  have hC0 : 0 ≤ C := (abs_nonneg c).trans hcC
  have h4 : 2 ≤ 4 - 4 * C := by linarith
  have h4' : 0 < 4 - 4 * C := by linarith
  set caq := c * x.a * x.q with hcaq
  set φ := |δ * ⟪p, x.z⟫| with hφ
  have hφ0 : 0 ≤ φ := abs_nonneg _
  have hφz : φ ≤ δ * ‖x.z‖ := forcing_le hδ hp
  have hM := mass_nonneg x
  have hF : ‖feature p r x‖ ≤ |x.a| + |x.t| := feature_norm_le hp hr x
  have hF0 : 0 ≤ |x.a| + |x.t| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hFsq : ‖feature p r x‖ ^ 2 ≤ (|x.a| + |x.t|) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hF 2
  have hzsq := step_z_norm_sq (c := c) (δ := δ) (p := p) (r := r) (x := x)
  have hmsq := mass_sq_step_le (c := c) (δ := δ) (p := p) (r := r) (x := x) hcC (by linarith)
  have hin : δ * ⟪feature p r x, x.z⟫ ≤ -caq := mistake_inner_le hm
  have hfz := inner_feature_le (x := x) hp hr
  have hδsq : δ ^ 2 * ‖feature p r x‖ ^ 2 ≤ δ ^ 2 * (|x.a| + |x.t|) ^ 2 :=
    mul_le_mul_of_nonneg_left hFsq (sq_nonneg δ)
  have hmassφ : 4 * (1 + C) * mass x * φ ≤ 6 * mass x * φ := by
    have h := mul_nonneg (by linarith : (0:ℝ) ≤ 2 - 4 * C) (mul_nonneg hM hφ0)
    linarith [h]
  have hφsq : 4 * φ ^ 2 ≤ 4 * (δ * ‖x.z‖) ^ 2 := by nlinarith
  unfold potential
  rw [hzsq]
  have h1C : (1 : ℝ) - C ≠ 0 := by linarith
  have hdiv : (mass (step c δ p r x)) ^ 2 / (4 - 4 * C) ≤
      ((mass x) ^ 2 + 8 * caq + 4 * C * |caq| + 4 * (1 + C) * mass x * φ + 4 * φ ^ 2) /
        (4 - 4 * C) := div_le_div_of_nonneg_right hmsq h4'.le
  set Rst := 6 * mass x * φ + 4 * (δ * ‖x.z‖) ^ 2 with hRst
  have hrest : Rst / (4 - 4 * C) ≤ 3 * mass x * (δ * ‖x.z‖) + 2 * (δ * ‖x.z‖) ^ 2 := by
    rw [div_le_iff₀ h4']
    have h1 : 6 * mass x * φ ≤ 6 * mass x * (δ * ‖x.z‖) := by
      apply mul_le_mul_of_nonneg_left hφz; positivity
    have hR0 : 0 ≤ 3 * mass x * (δ * ‖x.z‖) + 2 * (δ * ‖x.z‖) ^ 2 := by positivity
    have h2 : (3 * mass x * (δ * ‖x.z‖) + 2 * (δ * ‖x.z‖) ^ 2) * 2 ≤
        (3 * mass x * (δ * ‖x.z‖) + 2 * (δ * ‖x.z‖) ^ 2) * (4 - 4 * C) :=
      mul_le_mul_of_nonneg_left h4 hR0
    rw [hRst]
    linarith only [h1, h2]
  have hFz0 : 0 ≤ 4 * C * δ * ((|x.a| + |x.t|) * ‖x.z‖) := by positivity
  rcases le_or_gt caq 0 with hle | hlt
  · -- contracting: pollution ≤ 2|caq|, mass² decreases by ≥ (8 - 4C)|caq|
    have habs : |caq| = -caq := abs_of_nonpos hle
    have hpoll : 2 * δ * ⟪feature p r x, x.z⟫ ≤ 2 * |caq| := by
      rw [habs]; linarith only [hin]
    have hkey : ((mass x) ^ 2 + 8 * caq + 4 * C * |caq| + 4 * (1 + C) * mass x * φ + 4 * φ ^ 2) /
        (4 - 4 * C) ≤ (mass x) ^ 2 / (4 - 4 * C) - 2 * |caq| + Rst / (4 - 4 * C) := by
      rw [div_le_iff₀ h4']
      have e : ((mass x) ^ 2 / (4 - 4 * C) - 2 * |caq| + Rst / (4 - 4 * C)) * (4 - 4 * C) =
          (mass x) ^ 2 - 2 * |caq| * (4 - 4 * C) + Rst := by
        field_simp
        try ring
      rw [e, hRst]
      have hC' := mul_nonneg hC0 (abs_nonneg caq)
      rw [habs] at hC' ⊢
      linarith only [hmassφ, hφsq, hC', hC]
    linarith only [hdiv, hkey, hrest, hpoll, hδsq, hFz0]
  · -- expanding: payment of 2 caq, mass² increases by ≤ (8 + 4C) caq, gate caq ≤ δ F ‖z‖
    have habs : |caq| = caq := abs_of_pos hlt
    have hpay : 2 * δ * ⟪feature p r x, x.z⟫ ≤ -(2 * caq) := by linarith only [hin]
    have hgate : caq ≤ δ * ((|x.a| + |x.t|) * ‖x.z‖) := by
      have h1 : caq ≤ -(δ * ⟪feature p r x, x.z⟫) := by linarith only [hin]
      have h2 : -(δ * ⟪feature p r x, x.z⟫) ≤ δ * |⟪feature p r x, x.z⟫| := by
        have := neg_abs_le (δ * ⟪feature p r x, x.z⟫)
        rw [abs_mul, abs_of_nonneg hδ] at this
        linarith only [this]
      have h3 : δ * |⟪feature p r x, x.z⟫| ≤ δ * ((|x.a| + |x.t|) * ‖x.z‖) :=
        mul_le_mul_of_nonneg_left hfz hδ
      linarith only [h1, h2, h3]
    have hkey : ((mass x) ^ 2 + 8 * caq + 4 * C * |caq| + 4 * (1 + C) * mass x * φ + 4 * φ ^ 2) /
        (4 - 4 * C) ≤ (mass x) ^ 2 / (4 - 4 * C) + 2 * caq + 4 * C * caq + Rst / (4 - 4 * C) := by
      rw [div_le_iff₀ h4']
      have e : ((mass x) ^ 2 / (4 - 4 * C) + 2 * caq + 4 * C * caq + Rst / (4 - 4 * C)) *
          (4 - 4 * C) = (mass x) ^ 2 + (2 * caq + 4 * C * caq) * (4 - 4 * C) + Rst := by
        field_simp
        try ring
      rw [e, habs, hRst]
      have h1 := mul_nonneg hC0 hlt.le
      have h2 := mul_nonneg (mul_nonneg hC0 hC0) hlt.le
      have h3 : 4 * C * caq ≤ 8 * C * caq - 16 * C ^ 2 * caq := by
        have h := mul_nonneg (mul_nonneg hC0 (by linarith : (0:ℝ) ≤ 1 / 4 - C)) hlt.le
        have e2 : C * (1 / 4 - C) * caq = C * caq / 4 - C ^ 2 * caq := by ring
        linarith only [h, e2]
      linarith only [hmassφ, hφsq, h1, h2, h3]
    have hexc : 4 * C * caq ≤ 4 * C * δ * ((|x.a| + |x.t|) * ‖x.z‖) := by
      have := mul_le_mul_of_nonneg_left hgate (by positivity : (0:ℝ) ≤ 4 * C)
      linarith only [this]
    linarith only [hdiv, hkey, hrest, hpay, hδsq, hexc]

end Step

end LongTails.Proofs.TwoSidedPerceptronPotential
