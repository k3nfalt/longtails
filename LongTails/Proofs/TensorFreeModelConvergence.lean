import LongTails.Proofs.TensorFreeModel

namespace LongTails.Proofs.TensorFreeModelConvergence

open LongTails.Algorithms.TensorFreeModel
open LongTails.Proofs.TensorFreeModel
open LongTails.Algorithms.TaylorCorrectedNewton
open OracleTemplate OracleTemplate.QueryPlan
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma error_absorption (H : E →L[ℝ] E)
    (hH : ∀ a b, ⟪a, H b⟫ = ⟪H a, b⟫) (hpos : ∀ v, 0 ≤ ⟪v, H v⟫)
    {L t : ℝ} (hL : 0 ≤ L) (ht : 0 ≤ t) (x y u : E) :
    L * t ^ 3 * ‖u - y‖ ≤ ((1 - 1 / Real.sqrt 2) / 2) * kernelBregman H L x u +
      (1 + 1 / Real.sqrt 2) * kernelBregman H L x y + 6 * L * t ^ 4 := by
  have hu := kernel_bregman_lower H hH hpos hL x u
  have hy := kernel_bregman_lower H hH hpos hL x y
  have hAu : 0 ≤ kernelBregman H L x u := le_trans (by positivity) hu
  have hAy : 0 ≤ kernelBregman H L x y := le_trans (by positivity) hy
  have hcu := mul_le_mul_of_nonneg_right kernel_constants.1 hAu
  have hcy := mul_le_mul_of_nonneg_right kernel_constants.2.1 hAy
  have h₁ := mul_le_mul_of_nonneg_left (quartic_young (norm_nonneg (u - x)) ht) hL
  have h₂ := mul_le_mul_of_nonneg_left (quartic_young (norm_nonneg (y - x)) ht) hL
  have hn : ‖u - y‖ ≤ ‖u - x‖ + ‖y - x‖ := by
    simpa only [norm_sub_rev y x] using norm_sub_le_norm_sub_add_norm_sub u x y
  have he := mul_le_mul_of_nonneg_left hn (show 0 ≤ L * t ^ 3 by positivity)
  nlinarith

lemma inexact_step (H : E →L[ℝ] E)
    (hH : ∀ a b, ⟪a, H b⟫ = ⟪H a, b⟫) (hpos : ∀ v, 0 ≤ ⟪v, H v⟫)
    {L ρ t : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (F : E → ℝ) (x e g u : E) (hu : u ∈ Metric.closedBall (0 : E) ρ)
    (herr : ‖e - g‖ ≤ L * t ^ 3)
    (hlo : (1 - 1 / Real.sqrt 2) * kernelBregman H L x u ≤ F u - F x - ⟪g, u - x⟫)
    (hhi : F (stepPoint H L ρ x e) - F x - ⟪g, stepPoint H L ρ x e - x⟫ ≤
      (1 + 1 / Real.sqrt 2) * kernelBregman H L x (stepPoint H L ρ x e)) :
    let y := stepPoint H L ρ x e
    kernelBregman H L y u ≤ (23 / 24 : ℝ) * kernelBregman H L x u +
      (F u - F y) / (2 * (1 + 1 / Real.sqrt 2)) + 3 * L * t ^ 4 := by
  let y := stepPoint H L ρ x e
  let b := 2 * (1 + 1 / Real.sqrt 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hstep := stepPoint_energy H hH L hρ x e u hu
  have he : ⟪e, u - y⟫ = ⟪g, u - x⟫ - ⟪g, y - x⟫ + ⟪e - g, u - y⟫ := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  have herr' : ⟪e - g, u - y⟫ ≤ L * t ^ 3 * ‖u - y‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right herr (norm_nonneg _))
  have habs := error_absorption H hH hpos hL ht x y u
  have hraw : b * kernelBregman H L y u ≤
      (b - (1 - 1 / Real.sqrt 2) / 2) * kernelBregman H L x u +
        F u - F y + 6 * L * t ^ 4 := by
    change b * kernelBregman H L y u ≤ b * kernelBregman H L x u -
      b * kernelBregman H L x y + ⟪e, u - y⟫ at hstep
    rw [he] at hstep
    dsimp [b] at *
    nlinarith
  have hA : 0 ≤ kernelBregman H L x u :=
    le_trans (by positivity) (kernel_bregman_lower H hH hpos hL x u)
  have hcoef : b - (1 - 1 / Real.sqrt 2) / 2 ≤ (23 / 24 : ℝ) * b := by
    dsimp [b]
    linarith [kernel_constants.2.2]
  have hcoef' := mul_le_mul_of_nonneg_right hcoef hA
  have hb2 : 2 ≤ b := by dsimp [b]; linarith [kernel_constants.2.1]
  have herr2 := mul_le_mul_of_nonneg_right hb2 (show 0 ≤ 3 * L * t ^ 4 by positivity)
  dsimp only
  apply (mul_le_mul_iff_right₀ hb).mp
  have heq : b * ((F u - F y) / b) = F u - F y := by field_simp
  change b * kernelBregman H L y u ≤
    b * ((23 / 24 : ℝ) * kernelBregman H L x u + (F u - F y) / b + 3 * L * t ^ 4)
  rw [mul_add, mul_add, heq]
  nlinarith

lemma actual_model_step {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L ρ t : ℝ} (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (w x e u : E)
    (hu : u ∈ Metric.closedBall (0 : E) ρ)
    (herr : ‖e - exactGradient (gradient f w) (fderiv ℝ (gradient f) w)
      (fderiv ℝ (fderiv ℝ (gradient f)) w) L x‖ ≤ L * t ^ 3) :
    let H := fderiv ℝ (gradient f) w
    let T := fderiv ℝ (fderiv ℝ (gradient f)) w
    let M := modelValue (gradient f w) H T L
    let y := stepPoint H L ρ x e
    kernelBregman H L y u ≤ (23 / 24 : ℝ) * kernelBregman H L x u +
      (M u - M y) / (2 * (1 + 1 / Real.sqrt 2)) + 3 * L * t ^ 4 := by
  let H := fderiv ℝ (gradient f) w
  have hH : ∀ a b, ⟪a, H b⟫ = ⟪H a, b⟫ := by
    intro a b
    exact (OracleTemplate.NonlinearTemporalDiscrepancy.hessian_symmetric
      (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) w a b).symm
  have hsupp (a b : E) : f a + ⟪gradient f a, b - a⟫ + (0 : ℝ) / 2 * ‖b - a‖ ^ 2 ≤ f b := by
    have hh := OracleTemplate.Gradient.convex_support hc
      (fun z => (hf.differentiable (by norm_num) z).hasGradientAt) a b
    linarith
  have hpos (v : E) : 0 ≤ ⟪v, H v⟫ := by
    have hh := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_lower_bound
      ((GradientDependentLocal.gradient_contDiff_two hf).differentiable (by norm_num)) hsupp w v
    simpa [H, real_inner_comm] using hh
  exact inexact_step H hH hpos hL hρ ht _ x e _ u hu herr
    (model_relative_support hf hc hL hT w x u).1
    (model_relative_support hf hc hL hT w x (stepPoint H L ρ x e)).2

lemma modelRound_mem {n : ℕ} (oracle : Fin n × E → Reply E)
    (g : E) (H : E →L[ℝ] E) (L τ δ tol : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (z : E) (st : ModelState E) (hst : st.displacement ∈ Metric.closedBall (0 : E) ρ) :
    (eval oracle (modelRound g H L τ ρ δ tol z st)).displacement ∈ Metric.closedBall (0 : E) ρ := by
  classical
  simp only [modelRound, eval_bind, eval_map]
  split_ifs
  · exact hst
  · exact hst
  · exact (stepPoint_optimal H L hρ _ _).1

lemma modelRounds_mem {n : ℕ} (oracle : Fin n × E → Reply E)
    (g : E) (H : E →L[ℝ] E) (L τ δ tol : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (z : E) (k : ℕ) (st : ModelState E) (hst : st.displacement ∈ Metric.closedBall (0 : E) ρ) :
    (eval oracle (modelRounds g H L τ ρ δ tol z k st)).displacement ∈ Metric.closedBall (0 : E) ρ := by
  induction k generalizing st with
  | zero => exact hst
  | succ k ih =>
    rw [modelRounds, eval_bind]
    exact ih _ (modelRound_mem oracle g H L τ δ tol hρ z st hst)

omit [FiniteDimensional ℝ E] in
lemma modelRound_preserves {n : ℕ} (oracle : Fin n × E → Reply E)
    (g : E) (H : E →L[ℝ] E) (L τ ρ δ tol : ℝ) (z : E)
    (st : ModelState E) (hst : st.accepted = true) :
    eval oracle (modelRound g H L τ ρ δ tol z st) = st := by
  simp only [modelRound, eval_bind, eval_map, hst, ↓reduceIte]

omit [FiniteDimensional ℝ E] in
lemma modelRounds_preserves {n : ℕ} (oracle : Fin n × E → Reply E)
    (g : E) (H : E →L[ℝ] E) (L τ ρ δ tol : ℝ) (z : E)
    (k : ℕ) (st : ModelState E) (hst : st.accepted = true) :
    eval oracle (modelRounds g H L τ ρ δ tol z k st) = st := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [modelRounds, eval_bind, modelRound_preserves oracle g H L τ ρ δ tol z st hst]
    exact ih

lemma exists_quartic_model_min {M : E → ℝ} (hM : Continuous M) (hzero : M 0 = 0)
    {a G : ℝ} (ha : 0 < a) (hG : 0 ≤ G)
    (hlower : ∀ s, -G * ‖s‖ + a * ‖s‖ ^ 4 ≤ M s) :
    ∃ u, ∀ s, M u ≤ M s := by
  let r := 1 + G / a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  obtain ⟨u, _, hu⟩ := (isCompact_closedBall (0 : E) r).exists_isMinOn
    (show (Metric.closedBall (0 : E) r).Nonempty from ⟨0, by simpa using hr⟩) hM.continuousOn
  have hu0 : M u ≤ 0 := by
    have hh : M u ≤ M 0 := hu (show (0 : E) ∈ Metric.closedBall 0 r by simpa using hr)
    simpa only [hzero] using hh
  refine ⟨u, fun s => ?_⟩
  by_cases hs : s ∈ Metric.closedBall (0 : E) r
  · exact hu hs
  · have hn : r < ‖s‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hs
    have hn1 : 1 ≤ ‖s‖ := by
      have hg : 0 ≤ G / a := div_nonneg hG ha.le
      dsimp [r] at hn
      linarith
    have hp := le_self_pow₀ hn1 (by decide : (3 : ℕ) ≠ 0)
    have hGa : G < a * ‖s‖ := by
      have hh := mul_lt_mul_of_pos_left hn ha
      have ha0 := ne_of_gt ha
      dsimp [r] at hh
      field_simp at hh
      nlinarith
    have hq := mul_le_mul_of_nonneg_left hp ha.le
    have ht := mul_le_mul_of_nonneg_right (hGa.le.trans hq) (norm_nonneg s)
    have hl := hlower s
    nlinarith

lemma model_growth {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L : ℝ} (hL : 0 ≤ L)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (w s : E) :
    -‖gradient f w‖ * ‖s‖ + L / 16 * ‖s‖ ^ 4 ≤
      modelValue (gradient f w) (fderiv ℝ (gradient f) w)
        (fderiv ℝ (fderiv ℝ (gradient f)) w) L s := by
  have hh := (model_relative_support hf hc hL hT w 0 s).1
  simp only [kernelBregman, kernelValue, kernelGradient, modelValue, exactGradient,
    map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 4 ≠ 0),
    mul_zero, add_zero, inner_zero_left, inner_zero_right,
    sub_zero, zero_div, smul_zero] at hh
  have hsupp (a b : E) : f a + ⟪gradient f a, b - a⟫ + (0 : ℝ) / 2 * ‖b - a‖ ^ 2 ≤ f b := by
    have hh := OracleTemplate.Gradient.convex_support hc
      (fun z => (hf.differentiable (by norm_num) z).hasGradientAt) a b
    linarith
  have hp := OracleTemplate.NonlinearTemporalDiscrepancy.hessian_lower_bound
    ((GradientDependentLocal.gradient_contDiff_two hf).differentiable (by norm_num)) hsupp w s
  have hpos : 0 ≤ ⟪s, fderiv ℝ (gradient f) w s⟫ := by simpa [real_inner_comm] using hp
  have hcoef := mul_le_mul_of_nonneg_right kernel_constants.1
    (show 0 ≤ ⟪s, fderiv ℝ (gradient f) w s⟫ / 2 + L * ‖s‖ ^ 4 / 4 by positivity)
  have hi := (abs_le.mp (abs_real_inner_le_norm (gradient f w) s)).1
  dsimp [modelValue, kernelValue]
  nlinarith

lemma global_model_min {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (hc : ConvexOn ℝ Set.univ f) {L ρ : ℝ} (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hT : ∀ x y, ‖fderiv ℝ (fderiv ℝ (gradient f)) x -
      fderiv ℝ (fderiv ℝ (gradient f)) y‖ ≤ L * ‖x - y‖) (w : E)
    (hR : 16 * ‖gradient f w‖ ≤ L * ρ ^ 3) :
    ∃ u ∈ Metric.closedBall (0 : E) ρ, ∀ s,
      modelValue (gradient f w) (fderiv ℝ (gradient f) w)
        (fderiv ℝ (fderiv ℝ (gradient f)) w) L u ≤
      modelValue (gradient f w) (fderiv ℝ (gradient f) w)
        (fderiv ℝ (fderiv ℝ (gradient f)) w) L s := by
  let M := modelValue (gradient f w) (fderiv ℝ (gradient f) w)
    (fderiv ℝ (fderiv ℝ (gradient f)) w) L
  have hM := (model_contDiff (gradient f w) (fderiv ℝ (gradient f) w)
    (fderiv ℝ (fderiv ℝ (gradient f)) w) L).continuous
  have hzero : M 0 = 0 := by simp [M, modelValue, kernelValue]
  have hlower := model_growth hf hc hL.le hT w
  obtain ⟨u, hu⟩ := exists_quartic_model_min hM hzero
    (by positivity : 0 < L / 16) (norm_nonneg (gradient f w)) hlower
  refine ⟨u, ?_, hu⟩
  have hu0 : M u ≤ 0 := (hu 0).trans_eq hzero
  have hl := hlower u
  by_contra hn
  have hr : ρ < ‖u‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hn
  have hru : 0 < ‖u‖ := hρ.trans_lt hr
  have hp := pow_lt_pow_left₀ hr hρ (by decide : (3 : ℕ) ≠ 0)
  have hpL := mul_lt_mul_of_pos_left hp hL
  have hpLu := mul_lt_mul_of_pos_right hpL hru
  have hRu := mul_le_mul_of_nonneg_right hR (norm_nonneg u)
  nlinarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma contraction_energy (A : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hstep : ∀ k, A (k + 1) ≤ (23 / 24 : ℝ) * A k + C) (k : ℕ) :
    A k ≤ (23 / 24 : ℝ) ^ k * A 0 + 24 * C := by
  induction k with
  | zero => simp only [pow_zero, one_mul]; linarith
  | succ k ih =>
    have hh := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℝ) ≤ 23 / 24)
    have hs := hstep k
    rw [pow_succ]
    nlinarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma last_gap_bound (A gap : ℕ → ℝ) {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hA : ∀ k, 0 ≤ A k) (hgap : ∀ k, 0 ≤ gap (k + 1))
    (hstep : ∀ k, A (k + 1) ≤ (23 / 24 : ℝ) * A k - gap (k + 1) / b + C) (k : ℕ) :
    gap (k + 1) ≤ b * (23 / 24 : ℝ) ^ (k + 1) * A 0 + 24 * b * C := by
  have hrec (j : ℕ) : A (j + 1) ≤ (23 / 24 : ℝ) * A j + C :=
    (hstep j).trans (by linarith [div_nonneg (hgap j) hb.le])
  have hAk := contraction_energy A hC hrec k
  have hpre : gap (k + 1) / b ≤ (23 / 24 : ℝ) * A k + C := by
    linarith [hstep k, hA (k + 1)]
  have hgb := (div_le_iff₀ hb).mp hpre
  have he := mul_le_mul_of_nonneg_left hAk (show 0 ≤ b * (23 / 24 : ℝ) by positivity)
  rw [pow_succ]
  nlinarith

end LongTails.Proofs.TensorFreeModelConvergence
