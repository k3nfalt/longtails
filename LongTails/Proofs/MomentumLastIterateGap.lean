import LongTails.Proofs.MomentumLastIterateExpectation

open MeasureTheory Set InnerProductSpace ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.MomentumConvex

open LongTails.Setups.MomentumLipschitzConvex

open OracleTemplate.SampledConvex (integral_prefix extend measurable_extend extend_agree)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]
  {p : Measure Ξ} [IsProbabilityMeasure p] {f : E → ℝ} {Gr : Ξ → E → E} {G : ℝ} {xstar : E}

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ξ] in
lemma tau_ge_one {N k : ℕ} (hk : k ≤ N) : 1 ≤ tau N k := by
  unfold tau
  have : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
  linarith

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace Ξ] in
lemma cw_props {γ κ : ℝ} (hγ : 0 < γ) (hκ : 0 ≤ κ) {N k : ℕ} (hk : k ≤ N) :
    0 ≤ cw γ κ N k ∧ cw γ κ N k ≤ 1 ∧
      wt γ κ (tau N k) * cw γ κ N k = wt γ κ (tau N k + 1) ∧
      wt γ κ (tau N k) * (1 - cw γ κ N k) = wt γ κ (tau N k) - wt γ κ (tau N k + 1) := by
  have hτ : 0 < tau N k := by linarith [tau_ge_one hk]
  have hw := wt_pos hγ hκ hτ
  have hw' := wt_pos hγ hκ (by linarith : 0 < tau N k + 1)
  have ha := wt_anti hγ hκ hτ
  have h3 : wt γ κ (tau N k) * cw γ κ N k = wt γ κ (tau N k + 1) := by
    unfold cw; field_simp
  refine ⟨?_, ?_, h3, ?_⟩
  · unfold cw; positivity
  · unfold cw; rw [div_le_one hw]; exact ha
  · rw [mul_sub, mul_one, h3]

omit [CompleteSpace E] in
lemma Hyp.ref_gap_step (h : Hyp p f Gr G xstar) {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : 0 < γ) (N : ℕ) (x0 : E) {k : ℕ} (hk : k ≤ N) :
    wt γ (β / (1 - β)) (tau N k) *
        ∫ ξ, (f (refp Gr β γ N x0 xstar ξ (k + 1)) - f xstar) ∂(prodLaw p) ≤
      wt γ (β / (1 - β)) (tau N k + 1) *
        ∫ ξ, (f (refp Gr β γ N x0 xstar ξ k) - f xstar) ∂(prodLaw p) +
      (wt γ (β / (1 - β)) (tau N k) - wt γ (β / (1 - β)) (tau N k + 1)) *
        ∫ ξ, (f (traj Gr β γ N x0 ξ k).1 - f xstar) ∂(prodLaw p) := by
  have hκ : 0 ≤ β / (1 - β) := div_nonneg hβ0 (by linarith)
  obtain ⟨hc0, hc1, hc2, hc3⟩ := cw_props hγ hκ hk
  set c := cw γ (β / (1 - β)) N k
  have hτ : 0 < tau N k := by linarith [tau_ge_one hk]
  have hw := wt_pos hγ hκ hτ
  have hi1 := h.integrable_gap (h.memLp_refp β γ N x0 (xstar := xstar) (k + 1))
  have hi2 := h.integrable_gap (h.memLp_refp β γ N x0 (xstar := xstar) k)
  have hi3 := h.integrable_gap (h.memLp_traj β γ N x0 k).1
  have hpt : ∀ ξ : ℕ → Ξ, f (refp Gr β γ N x0 xstar ξ (k + 1)) - f xstar ≤
      c * (f (refp Gr β γ N x0 xstar ξ k) - f xstar) +
        (1 - c) * (f (traj Gr β γ N x0 ξ k).1 - f xstar) := by
    intro ξ
    have := h.conv.2 (mem_univ (refp Gr β γ N x0 xstar ξ k)) (mem_univ (traj Gr β γ N x0 ξ k).1)
      hc0 (by linarith : (0 : ℝ) ≤ 1 - c) (by ring)
    simp only [smul_eq_mul] at this
    simp only [refp]
    linarith
  have hi4 : Integrable (fun ξ : ℕ → Ξ => c * (f (refp Gr β γ N x0 xstar ξ k) - f xstar) +
      (1 - c) * (f (traj Gr β γ N x0 ξ k).1 - f xstar)) (prodLaw p) :=
    (hi2.const_mul c).add (hi3.const_mul (1 - c))
  have he4 : ∫ ξ : ℕ → Ξ, (c * (f (refp Gr β γ N x0 xstar ξ k) - f xstar) +
      (1 - c) * (f (traj Gr β γ N x0 ξ k).1 - f xstar)) ∂(prodLaw p) =
      c * ∫ ξ, (f (refp Gr β γ N x0 xstar ξ k) - f xstar) ∂(prodLaw p) +
        (1 - c) * ∫ ξ, (f (traj Gr β γ N x0 ξ k).1 - f xstar) ∂(prodLaw p) := by
    rw [integral_add (hi2.const_mul c) (hi3.const_mul (1 - c)), integral_const_mul,
      integral_const_mul]
  have hint := integral_mono hi1 hi4 hpt
  rw [he4] at hint
  have := mul_le_mul_of_nonneg_left hint hw.le
  rw [mul_add, ← mul_assoc, ← mul_assoc, hc2, hc3] at this
  exact this

omit [CompleteSpace E] in
lemma Hyp.jensen_step (h : Hyp p f Gr G xstar) {β γ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : 0 < γ) (N : ℕ) (x0 : E) {k : ℕ} (hk : k ≤ N) :
    wt γ (β / (1 - β)) (tau N k) *
        ∫ ξ, ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ (k + 1)‖ ^ 2 ∂(prodLaw p) ≤
      wt γ (β / (1 - β)) (tau N k + 1) *
        ∫ ξ, ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ k‖ ^ 2 ∂(prodLaw p) +
      (wt γ (β / (1 - β)) (tau N k) - wt γ (β / (1 - β)) (tau N k + 1)) *
        ((β / (1 - β) * γ * tau N k) ^ 2 * G ^ 2) := by
  have hκ : 0 ≤ β / (1 - β) := div_nonneg hβ0 (by linarith)
  obtain ⟨hc0, hc1, hc2, hc3⟩ := cw_props hγ hκ hk
  set c := cw γ (β / (1 - β)) N k
  set d := β / (1 - β) * γ * tau N k
  have hτ : 0 < tau N k := by linarith [tau_ge_one hk]
  have hw := wt_pos hγ hκ hτ
  have hi1 := integrable_sq_sub (h.memLp_zed β γ N x0 k) (h.memLp_refp β γ N x0 (xstar := xstar) (k + 1))
  have hi2 := integrable_sq_sub (h.memLp_zed β γ N x0 k) (h.memLp_refp β γ N x0 (xstar := xstar) k)
  have hi3 := integrable_sq_norm (h.memLp_traj β γ N x0 k).2
  have hpt : ∀ ξ : ℕ → Ξ, ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ (k + 1)‖ ^ 2 ≤
      c * ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ k‖ ^ 2 +
        (1 - c) * d ^ 2 * ‖(traj Gr β γ N x0 ξ k).2‖ ^ 2 := by
    intro ξ
    have e1 : zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ (k + 1) =
        c • (zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ k) +
          (1 - c) • (zed Gr β γ N x0 ξ k - (traj Gr β γ N x0 ξ k).1) := by
      simp only [refp]; module
    have e2 : ‖zed Gr β γ N x0 ξ k - (traj Gr β γ N x0 ξ k).1‖ ^ 2 =
        d ^ 2 * ‖(traj Gr β γ N x0 ξ k).2‖ ^ 2 := by
      have : zed Gr β γ N x0 ξ k - (traj Gr β γ N x0 ξ k).1 = -(d • (traj Gr β γ N x0 ξ k).2) := by
        unfold zed; abel
      rw [this, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have h3 := norm_sq_combo_le (zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ k)
      (zed Gr β γ N x0 ξ k - (traj Gr β γ N x0 ξ k).1) hc0 hc1
    rw [e1]
    rw [e2] at h3
    linarith
  have hi4 : Integrable (fun ξ : ℕ → Ξ =>
      c * ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ k‖ ^ 2 +
        (1 - c) * d ^ 2 * ‖(traj Gr β γ N x0 ξ k).2‖ ^ 2) (prodLaw p) :=
    (hi2.const_mul c).add (hi3.const_mul ((1 - c) * d ^ 2))
  have he4 : ∫ ξ : ℕ → Ξ, (c * ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ k‖ ^ 2 +
        (1 - c) * d ^ 2 * ‖(traj Gr β γ N x0 ξ k).2‖ ^ 2) ∂(prodLaw p) =
      c * ∫ ξ, ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ k‖ ^ 2 ∂(prodLaw p) +
        (1 - c) * d ^ 2 * ∫ ξ, ‖(traj Gr β γ N x0 ξ k).2‖ ^ 2 ∂(prodLaw p) := by
    rw [integral_add (hi2.const_mul c) (hi3.const_mul ((1 - c) * d ^ 2)), integral_const_mul,
      integral_const_mul]
  have hint := integral_mono hi1 hi4 hpt
  rw [he4] at hint
  have hmom := h.moment hβ0 hβ1.le γ N x0 k
  have h1c : 0 ≤ (1 - c) * d ^ 2 := mul_nonneg (by linarith) (sq_nonneg d)
  have h4 := mul_le_mul_of_nonneg_left hmom h1c
  have h5' : ∫ ξ, ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ (k + 1)‖ ^ 2 ∂(prodLaw p) ≤
      c * ∫ ξ, ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ k‖ ^ 2 ∂(prodLaw p) +
        (1 - c) * d ^ 2 * G ^ 2 := by linarith
  have h5 := mul_le_mul_of_nonneg_left h5' hw.le
  set I := ∫ ξ, ‖zed Gr β γ N x0 ξ k - refp Gr β γ N x0 xstar ξ k‖ ^ 2 ∂(prodLaw p)
  have e3 : wt γ (β / (1 - β)) (tau N k) * (c * I + (1 - c) * d ^ 2 * G ^ 2) =
      wt γ (β / (1 - β)) (tau N k + 1) * I +
      (wt γ (β / (1 - β)) (tau N k) - wt γ (β / (1 - β)) (tau N k + 1)) * (d ^ 2 * G ^ 2) := by
    linear_combination I * hc2 + (d ^ 2 * G ^ 2) * hc3
  rw [e3] at h5
  exact h5

end OracleTemplate.MomentumConvex
