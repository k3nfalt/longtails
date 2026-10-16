import LongTails.Proofs.ProximalLinearDecayStep
import LongTails.Proofs.ProximalLinearDecayWeights
import LongTails.Proofs.LinearDecaySgdExpectation

open MeasureTheory Set InnerProductSpace ProbabilityTheory
open scoped RealInnerProductSpace
open OracleTemplate.SampledConvex (step tail step_pos step_le tail_pos tail_nonneg tail_succ tail_last
  tail_zero prefix_indep map_prefix_pair integral_prefix extend measurable_extend extend_agree)

namespace OracleTemplate.SampledComposite

section Trajectory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]

noncomputable def anchor (G : Ξ → E → E) (prox : ℝ → E → E → E) (L η : ℝ) (T : ℕ) (x0 xstar : E)
    (ξ : ℕ → Ξ) : ℕ → E
  | 0 => xstar
  | k + 1 => (pweight L η T k / pweight L η T (k + 1)) • anchor G prox L η T x0 xstar ξ k +
      (1 - pweight L η T k / pweight L η T (k + 1)) • path G prox η T x0 ξ (k + 1)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ] in
lemma path_succ (G : Ξ → E → E) (prox : ℝ → E → E → E) (η : ℝ) (T : ℕ) (x0 : E) (ξ : ℕ → Ξ) (k : ℕ) :
    path G prox η T x0 ξ (k + 1) =
      prox (step η T k) (path G prox η T x0 ξ k) (G (ξ (2 * k)) (path G prox η T x0 ξ k)) := rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ] in
lemma path_congr (G : Ξ → E → E) (prox : ℝ → E → E → E) (η : ℝ) (T : ℕ) (x0 : E) {ξ ξ' : ℕ → Ξ} :
    ∀ k, (∀ i, i < 2 * k → ξ i = ξ' i) → path G prox η T x0 ξ k = path G prox η T x0 ξ' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hξ
    rw [path_succ, path_succ, ih (fun i hi => hξ i (by omega)), hξ (2 * k) (by omega)]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ] in
lemma anchor_congr (G : Ξ → E → E) (prox : ℝ → E → E → E) (L η : ℝ) (T : ℕ) (x0 xstar : E)
    {ξ ξ' : ℕ → Ξ} :
    ∀ k, (∀ i, i < 2 * k → ξ i = ξ' i) →
      anchor G prox L η T x0 xstar ξ k = anchor G prox L η T x0 xstar ξ' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hξ
    simp only [anchor]
    rw [ih (fun i hi => hξ i (by omega)), path_congr G prox η T x0 (k + 1) hξ]

end Trajectory

section Moments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]
  {p : Measure Ξ} [IsProbabilityMeasure p] {F : Ξ → E → ℝ} {G : Ξ → E → E} {ψ : E → ℝ}
  {Q : Set E} {prox : ℝ → E → E → E} {L σ : ℝ} {xstar : E}

lemma Hyp.obj_convex (h : Hyp p F G ψ Q prox L σ xstar) : ConvexOn ℝ univ (obj p F) := by
  refine ⟨convex_univ, fun a _ b _ θ φ hθ hφ hs => ?_⟩
  set w := θ • a + φ • b
  have ha := h.obj_lower w a
  have hb := h.obj_lower w b
  have hz : θ • (a - w) + φ • (b - w) = 0 := by
    simp only [w, smul_sub]
    rw [show θ • a - θ • (θ • a + φ • b) + (φ • b - φ • (θ • a + φ • b)) =
      (1 - (θ + φ)) • (θ • a + φ • b) by module, hs, sub_self, zero_smul]
  have hi : θ * ⟪mean p G w, a - w⟫ + φ * ⟪mean p G w, b - w⟫ = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hz, inner_zero_right]
  simp only [smul_eq_mul]
  have e1 := mul_le_mul_of_nonneg_left ha hθ
  have e2 := mul_le_mul_of_nonneg_left hb hφ
  linear_combination e1 + e2 - hi - obj p F w * hs

lemma Hyp.total_convex (h : Hyp p F G ψ Q prox L σ xstar) : ConvexOn ℝ Q (total p F ψ) := by
  have h1 : ConvexOn ℝ Q (obj p F) := h.obj_convex.subset (subset_univ Q) h.convQ
  exact h1.add h.convψ

lemma Hyp.mean_lip (h : Hyp p F G ψ Q prox L σ xstar) (x y : E) :
    ‖mean p G x - mean p G y‖ ≤ L * ‖x - y‖ := by
  have hx := h.int_grad x
  have hy := h.int_grad y
  have hsub : mean p G x - mean p G y = ∫ ξ, (G ξ x - G ξ y) ∂p := by
    simp only [mean]; rw [integral_sub hx hy]
  rw [hsub]
  calc ‖∫ ξ, (G ξ x - G ξ y) ∂p‖ ≤ ∫ ξ, ‖G ξ x - G ξ y‖ ∂p := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ, L * ‖x - y‖ ∂p := by
        apply integral_mono (hx.sub hy).norm (integrable_const _)
        intro ξ; exact h.lip ξ x y
    _ = L * ‖x - y‖ := by simp

lemma Hyp.mean_continuous (h : Hyp p F G ψ Q prox L σ xstar) : Continuous (mean p G) := by
  have hlip : LipschitzWith (⟨L, h.pos.le⟩ : NNReal) (mean p G) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    exact h.mean_lip x y
  exact hlip.continuous

omit [SecondCountableTopology E] in
lemma integrable_eval_sq (h : Hyp p F G ψ Q prox L σ xstar) (k : ℕ) :
    Integrable (fun ξ : ℕ → Ξ => ‖G (ξ k) xstar‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p) := by
  have hm : Measurable (fun ξ : ℕ → Ξ => ξ k) := measurable_pi_apply k
  have hf : Measurable (fun ω : Ξ => ‖G ω xstar‖ ^ 2) := (h.grad_meas xstar).norm.pow_const 2
  have hmap : (Measure.infinitePi fun _ : ℕ => p).map (fun ξ : ℕ → Ξ => ξ k) = p :=
    Measure.infinitePi_map_eval (μ := fun _ : ℕ => p) k
  have hi : Integrable (fun ω : Ξ => ‖G ω xstar‖ ^ 2)
      ((Measure.infinitePi fun _ : ℕ => p).map (fun ξ : ℕ → Ξ => ξ k)) := by
    rw [hmap]; exact h.sq_int_star
  exact (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp hi

lemma integrable_eval_var (h : Hyp p F G ψ Q prox L σ xstar) (k : ℕ) :
    Integrable (fun ξ : ℕ → Ξ => ‖G (ξ k) xstar - mean p G xstar‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) := by
  have hm : Measurable (fun ξ : ℕ → Ξ => ξ k) := measurable_pi_apply k
  have hf : Measurable (fun ω : Ξ => ‖G ω xstar - mean p G xstar‖ ^ 2) :=
    ((h.grad_meas xstar).sub measurable_const).norm.pow_const 2
  have hmap : (Measure.infinitePi fun _ : ℕ => p).map (fun ξ : ℕ → Ξ => ξ k) = p :=
    Measure.infinitePi_map_eval (μ := fun _ : ℕ => p) k
  have hi : Integrable (fun ω : Ξ => ‖G ω xstar - mean p G xstar‖ ^ 2)
      ((Measure.infinitePi fun _ : ℕ => p).map (fun ξ : ℕ → Ξ => ξ k)) := by
    rw [hmap]; exact h.var_int
  exact (integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mp hi

omit [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure p] in
lemma integrable_dist (X Y : (ℕ → Ξ) → E) (hX : Measurable X) (hY : Measurable Y)
    (hXs : Integrable (fun ξ => ‖X ξ - xstar‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p))
    (hYs : Integrable (fun ξ => ‖Y ξ - xstar‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p)) :
    Integrable (fun ξ => ‖X ξ - Y ξ‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p) := by
  have hb : Integrable (fun ξ => 2 * ‖X ξ - xstar‖ ^ 2 + 2 * ‖Y ξ - xstar‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) := (hXs.const_mul 2).add (hYs.const_mul 2)
  refine Integrable.mono' hb
    ((hX.sub hY).norm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 := norm_sub_le (X ξ - xstar) (Y ξ - xstar)
  rw [show X ξ - xstar - (Y ξ - xstar) = X ξ - Y ξ by abel] at h1
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖X ξ - xstar‖ - ‖Y ξ - xstar‖)]

variable (h : Hyp p F G ψ Q prox L σ xstar) {η : ℝ} (hη : 0 < η) {T : ℕ} {x0 : E} (hx0 : x0 ∈ Q)
include h hη hx0

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma path_mem (ξ : ℕ → Ξ) : ∀ k, k ≤ T → path G prox η T x0 ξ k ∈ Q := by
  intro k
  induction k with
  | zero => intro _; exact hx0
  | succ k ih =>
    intro hk
    rw [path_succ]
    exact h.prox_mem (step_pos hη (by omega)) _ _

omit [IsProbabilityMeasure p] hx0 in
lemma measurable_path : ∀ k, k ≤ T → Measurable (fun ξ : ℕ → Ξ => path G prox η T x0 ξ k) := by
  intro k
  induction k with
  | zero => intro _; exact measurable_const
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    simp only [path_succ]
    have hs : 0 < step η T k := step_pos hη (by omega)
    have hg : Measurable (fun ξ : ℕ → Ξ => G (ξ (2 * k)) (path G prox η T x0 ξ k)) :=
      h.meas.comp ((measurable_pi_apply (2 * k)).prodMk ih')
    exact (h.prox_measurable hs).comp (ih'.prodMk hg)

omit [IsProbabilityMeasure p] hx0 in
lemma measurable_anchor :
    ∀ k, k ≤ T → Measurable (fun ξ : ℕ → Ξ => anchor G prox L η T x0 xstar ξ k) := by
  intro k
  induction k with
  | zero => intro _; exact measurable_const
  | succ k ih =>
    intro hk
    simp only [anchor]
    exact ((ih (by omega)).const_smul _).add ((measurable_path h hη (x0 := x0) (k + 1) hk).const_smul _)

omit hx0 in
lemma integrable_path_sq :
    ∀ k, k ≤ T → Integrable (fun ξ : ℕ → Ξ => ‖path G prox η T x0 ξ k - xstar‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) := by
  intro k
  induction k with
  | zero =>
    intro _
    show Integrable (fun _ : ℕ → Ξ => ‖x0 - xstar‖ ^ 2) _
    exact integrable_const _
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    set s := step η T k
    have hs : 0 < s := step_pos hη (by omega)
    set C := ‖prox s xstar (mean p G xstar) - xstar‖
    have hb : Integrable (fun ξ : ℕ → Ξ => 3 * (1 + s * L) ^ 2 * ‖path G prox η T x0 ξ k - xstar‖ ^ 2 +
        3 * s ^ 2 * ‖G (ξ (2 * k)) xstar - mean p G xstar‖ ^ 2 + 3 * C ^ 2)
        (Measure.infinitePi fun _ : ℕ => p) :=
      ((ih'.const_mul _).add ((integrable_eval_var h (2 * k)).const_mul _)).add (integrable_const _)
    refine Integrable.mono' hb
      (((measurable_path h hη (x0 := x0) (k + 1) hk).sub_const xstar).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), path_succ]
    set x := path G prox η T x0 ξ k
    set g := G (ξ (2 * k)) x
    set m := mean p G xstar
    have h1 : ‖g - m‖ ≤ L * ‖x - xstar‖ + ‖G (ξ (2 * k)) xstar - m‖ := by
      calc ‖g - m‖ = ‖(G (ξ (2 * k)) x - G (ξ (2 * k)) xstar) + (G (ξ (2 * k)) xstar - m)‖ := by
            congr 1; abel
        _ ≤ ‖G (ξ (2 * k)) x - G (ξ (2 * k)) xstar‖ + ‖G (ξ (2 * k)) xstar - m‖ := norm_add_le _ _
        _ ≤ _ := by linarith [h.lip (ξ (2 * k)) x xstar]
    have h2 : ‖prox s x g - xstar‖ ≤ (1 + s * L) * ‖x - xstar‖ + s * ‖G (ξ (2 * k)) xstar - m‖ + C := by
      have hl := h.prox_lipschitz hs x g xstar m
      calc ‖prox s x g - xstar‖ = ‖(prox s x g - prox s xstar m) + (prox s xstar m - xstar)‖ := by
            congr 1; abel
        _ ≤ ‖prox s x g - prox s xstar m‖ + C := norm_add_le _ _
        _ ≤ ‖(x - s • g) - (xstar - s • m)‖ + C := by linarith
        _ = ‖(x - xstar) - s • (g - m)‖ + C := by congr 2; module
        _ ≤ ‖x - xstar‖ + s * ‖g - m‖ + C := by
            have := norm_sub_le (x - xstar) (s • (g - m))
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs] at this
            linarith
        _ ≤ _ := by nlinarith [h1, hs]
    have h3 : 0 ≤ (1 + s * L) * ‖x - xstar‖ := mul_nonneg (by have := h.pos; positivity) (norm_nonneg _)
    have h4 : 0 ≤ s * ‖G (ξ (2 * k)) xstar - m‖ := mul_nonneg hs.le (norm_nonneg _)
    have h5 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have hC : 0 ≤ C := norm_nonneg _
    have h6 : ((1 + s * L) * ‖x - xstar‖ + s * ‖G (ξ (2 * k)) xstar - m‖ + C) ^ 2 ≤
        3 * (1 + s * L) ^ 2 * ‖x - xstar‖ ^ 2 + 3 * s ^ 2 * ‖G (ξ (2 * k)) xstar - m‖ ^ 2 +
          3 * C ^ 2 := by
      nlinarith [sq_nonneg ((1 + s * L) * ‖x - xstar‖ - s * ‖G (ξ (2 * k)) xstar - m‖),
        sq_nonneg ((1 + s * L) * ‖x - xstar‖ - C), sq_nonneg (s * ‖G (ξ (2 * k)) xstar - m‖ - C)]
    linarith

omit hx0 in
lemma integrable_anchor_sq :
    ∀ k, k ≤ T → Integrable (fun ξ : ℕ → Ξ => ‖anchor G prox L η T x0 xstar ξ k - xstar‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) := by
  intro k
  induction k with
  | zero => intro _; simp [anchor]
  | succ k ih =>
    intro hk
    set θ := pweight L η T k / pweight L η T (k + 1)
    have hb : Integrable (fun ξ : ℕ → Ξ => 2 * θ ^ 2 * ‖anchor G prox L η T x0 xstar ξ k - xstar‖ ^ 2 +
        2 * (1 - θ) ^ 2 * ‖path G prox η T x0 ξ (k + 1) - xstar‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => p) :=
      ((ih (by omega)).const_mul _).add ((integrable_path_sq h hη (x0 := x0) (k + 1) hk).const_mul _)
    refine Integrable.mono' hb
      (((measurable_anchor h hη (x0 := x0) (k + 1) hk).sub_const xstar).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [anchor]
    set a := anchor G prox L η T x0 xstar ξ k
    set b := path G prox η T x0 ξ (k + 1)
    have he : θ • a + (1 - θ) • b - xstar = θ • (a - xstar) + (1 - θ) • (b - xstar) := by module
    rw [he]
    have h1 := norm_add_le (θ • (a - xstar)) ((1 - θ) • (b - xstar))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h1
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (|θ| * ‖a - xstar‖ + |1 - θ| * ‖b - xstar‖) ^ 2 ≤
        2 * θ ^ 2 * ‖a - xstar‖ ^ 2 + 2 * (1 - θ) ^ 2 * ‖b - xstar‖ ^ 2 := by
      have := sq_abs θ
      have := sq_abs (1 - θ)
      nlinarith [sq_nonneg (|θ| * ‖a - xstar‖ - |1 - θ| * ‖b - xstar‖)]
    linarith

omit hx0 in
lemma integrable_grad_path_sq :
    ∀ k, k ≤ T → Integrable (fun ξ : ℕ → Ξ => ‖G (ξ (2 * k)) (path G prox η T x0 ξ k)‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) := by
  intro k hk
  have hb : Integrable (fun ξ : ℕ → Ξ => 2 * ‖G (ξ (2 * k)) xstar‖ ^ 2 +
      2 * L ^ 2 * ‖path G prox η T x0 ξ k - xstar‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p) :=
    ((integrable_eval_sq h (2 * k)).const_mul _).add ((integrable_path_sq h hη (x0 := x0) k hk).const_mul _)
  have hm : Measurable (fun ξ : ℕ → Ξ => G (ξ (2 * k)) (path G prox η T x0 ξ k)) :=
    h.meas.comp ((measurable_pi_apply (2 * k)).prodMk (measurable_path h hη (x0 := x0) k hk))
  refine Integrable.mono' hb (hm.norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact h.grad_sq_le (ξ (2 * k)) _

omit hx0 in
lemma integrable_dev_path_sq :
    ∀ k, k ≤ T → Integrable (fun ξ : ℕ → Ξ =>
      ‖mean p G (path G prox η T x0 ξ k) - G (ξ (2 * k)) (path G prox η T x0 ξ k)‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) := by
  intro k hk
  have hmm : Measurable (fun ξ : ℕ → Ξ => mean p G (path G prox η T x0 ξ k)) :=
    h.mean_continuous.measurable.comp (measurable_path h hη (x0 := x0) k hk)
  have hgm : Measurable (fun ξ : ℕ → Ξ => G (ξ (2 * k)) (path G prox η T x0 ξ k)) :=
    h.meas.comp ((measurable_pi_apply (2 * k)).prodMk (measurable_path h hη (x0 := x0) k hk))
  have hb : Integrable (fun ξ : ℕ → Ξ =>
      2 * (2 * ‖mean p G xstar‖ ^ 2 + 2 * L ^ 2 * ‖path G prox η T x0 ξ k - xstar‖ ^ 2) +
        2 * ‖G (ξ (2 * k)) (path G prox η T x0 ξ k)‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p) :=
    (((integrable_const _).add ((integrable_path_sq h hη (x0 := x0) k hk).const_mul _)).const_mul _).add
      ((integrable_grad_path_sq h hη (x0 := x0) k hk).const_mul _)
  refine Integrable.mono' hb ((hmm.sub hgm).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ξ => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  set x := path G prox η T x0 ξ k
  set g := G (ξ (2 * k)) x
  have hm1 : ‖mean p G x‖ ≤ ‖mean p G xstar‖ + L * ‖x - xstar‖ := by
    have := h.mean_lip x xstar
    calc ‖mean p G x‖ = ‖mean p G xstar + (mean p G x - mean p G xstar)‖ := by congr 1; abel
      _ ≤ ‖mean p G xstar‖ + ‖mean p G x - mean p G xstar‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hm2 : ‖mean p G x‖ ^ 2 ≤ 2 * ‖mean p G xstar‖ ^ 2 + 2 * L ^ 2 * ‖x - xstar‖ ^ 2 := by
    have h0 : 0 ≤ L * ‖x - xstar‖ := mul_nonneg h.pos.le (norm_nonneg _)
    nlinarith [sq_nonneg (‖mean p G xstar‖ - L * ‖x - xstar‖), norm_nonneg (mean p G x)]
  have hsub := norm_sub_le (mean p G x) g
  nlinarith [sq_nonneg (‖mean p G x‖ - ‖g‖), norm_nonneg (mean p G x), norm_nonneg g,
    norm_nonneg (mean p G x - g)]

lemma integrable_total_path (hLη : L * η ≤ 1 / 8) :
    ∀ k, k ≤ T → Integrable (fun ξ : ℕ → Ξ => total p F ψ (path G prox η T x0 ξ k) - total p F ψ xstar)
      (Measure.infinitePi fun _ : ℕ => p) := by
  intro k
  induction k with
  | zero =>
    intro _
    show Integrable (fun _ : ℕ → Ξ => total p F ψ x0 - total p F ψ xstar) _
    exact integrable_const _
  | succ k ih =>
    intro hk
    have hk' : k ≤ T := by omega
    set s := step η T k
    have hs : 0 < s := step_pos hη (by omega)
    have hLs : L * s ≤ 1 / 2 := by
      have := step_le hη.le (show k < T by omega)
      have := mul_le_mul_of_nonneg_left this h.pos.le
      linarith
    have hθ : 0 < 1 - L * s := by linarith
    set c := s / (2 * (1 - L * s))
    have hb : Integrable (fun ξ : ℕ → Ξ =>
        ‖path G prox η T x0 ξ k - xstar‖ ^ 2 / (2 * s) +
          (‖mean p G (path G prox η T x0 ξ k) - G (ξ (2 * k)) (path G prox η T x0 ξ k)‖ ^ 2 +
            ‖path G prox η T x0 ξ k - xstar‖ ^ 2) / 2 +
          c * ‖mean p G (path G prox η T x0 ξ k) - G (ξ (2 * k)) (path G prox η T x0 ξ k)‖ ^ 2)
        (Measure.infinitePi fun _ : ℕ => p) :=
      (((integrable_path_sq h hη (x0 := x0) k hk').div_const _).add
        (((integrable_dev_path_sq h hη (x0 := x0) k hk').add (integrable_path_sq h hη (x0 := x0) k hk')).div_const _)).add
        ((integrable_dev_path_sq h hη (x0 := x0) k hk').const_mul _)
    have hmeas : Measurable (fun ξ : ℕ → Ξ => total p F ψ (path G prox η T x0 ξ (k + 1)) - total p F ψ xstar) :=
      (h.total_measurable.comp (measurable_path h hη (x0 := x0) (k + 1) hk)).sub_const _
    refine Integrable.mono' hb hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => ?_))
    have hx'Q := path_mem h hη hx0 ξ (k + 1) hk
    have hlow : 0 ≤ total p F ψ (path G prox η T x0 ξ (k + 1)) - total p F ψ xstar :=
      sub_nonneg.mpr (h.total_ge hx'Q)
    rw [Real.norm_eq_abs, abs_of_nonneg hlow]
    have hos : total p F ψ (path G prox η T x0 ξ (k + 1)) ≤ total p F ψ xstar +
        (‖path G prox η T x0 ξ k - xstar‖ ^ 2 - ‖path G prox η T x0 ξ (k + 1) - xstar‖ ^ 2) / (2 * s) +
          ⟪mean p G (path G prox η T x0 ξ k) - G (ξ (2 * k)) (path G prox η T x0 ξ k),
            path G prox η T x0 ξ k - xstar⟫ +
          c * ‖mean p G (path G prox η T x0 ξ k) - G (ξ (2 * k)) (path G prox η T x0 ξ k)‖ ^ 2 :=
      h.one_step_pointwise h.starQ hs hLs (ξ (2 * k))
    set x := path G prox η T x0 ξ k
    set g := G (ξ (2 * k)) x
    have hd : 0 ≤ ‖path G prox η T x0 ξ (k + 1) - xstar‖ ^ 2 / (2 * s) := by positivity
    have hcs : ⟪mean p G x - g, x - xstar⟫ ≤ (‖mean p G x - g‖ ^ 2 + ‖x - xstar‖ ^ 2) / 2 := by
      have := real_inner_le_norm (mean p G x - g) (x - xstar)
      nlinarith [sq_nonneg (‖mean p G x - g‖ - ‖x - xstar‖)]
    have e : (‖x - xstar‖ ^ 2 - ‖path G prox η T x0 ξ (k + 1) - xstar‖ ^ 2) / (2 * s) =
        ‖x - xstar‖ ^ 2 / (2 * s) - ‖path G prox η T x0 ξ (k + 1) - xstar‖ ^ 2 / (2 * s) := by ring
    rw [e] at hos
    linarith

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma anchor_mem (hLη : L * η ≤ 1 / 8) (ξ : ℕ → Ξ) :
    ∀ k, k < T → anchor G prox L η T x0 xstar ξ k ∈ Q := by
  intro k
  induction k with
  | zero => intro _; exact h.starQ
  | succ k ih =>
    intro hk
    simp only [anchor]
    have hw := (pweight_bounds h.pos.le hη hLη k (show k < T by omega)).1
    have hw' := (pweight_bounds h.pos.le hη hLη (k + 1) hk).1
    have hmono := pweight_mono h.pos.le hη hLη hk
    have hθ0 : 0 ≤ pweight L η T k / pweight L η T (k + 1) := div_nonneg hw.le hw'.le
    have hθ1 : pweight L η T k / pweight L η T (k + 1) ≤ 1 := (div_le_one hw').mpr hmono
    exact h.convQ (ih (by omega)) (path_mem h hη hx0 ξ (k + 1) hk.le) hθ0 (by linarith) (by ring)

lemma integrable_total_anchor (hLη : L * η ≤ 1 / 8) :
    ∀ k, k < T → Integrable (fun ξ : ℕ → Ξ =>
      total p F ψ (anchor G prox L η T x0 xstar ξ k) - total p F ψ xstar)
      (Measure.infinitePi fun _ : ℕ => p) := by
  intro k
  induction k with
  | zero =>
    intro _
    show Integrable (fun _ : ℕ → Ξ => total p F ψ xstar - total p F ψ xstar) _
    exact integrable_const _
  | succ k ih =>
    intro hk
    have hw := (pweight_bounds h.pos.le hη hLη k (show k < T by omega)).1
    have hw' := (pweight_bounds h.pos.le hη hLη (k + 1) hk).1
    have hmono := pweight_mono h.pos.le hη hLη hk
    set θ := pweight L η T k / pweight L η T (k + 1)
    have hθ0 : 0 ≤ θ := div_nonneg hw.le hw'.le
    have hθ1 : θ ≤ 1 := (div_le_one hw').mpr hmono
    have hb : Integrable (fun ξ : ℕ → Ξ =>
        θ * (total p F ψ (anchor G prox L η T x0 xstar ξ k) - total p F ψ xstar) +
          (1 - θ) * (total p F ψ (path G prox η T x0 ξ (k + 1)) - total p F ψ xstar))
        (Measure.infinitePi fun _ : ℕ => p) :=
      ((ih (by omega)).const_mul _).add ((integrable_total_path h hη hx0 hLη (k + 1) hk.le).const_mul _)
    have hmeas : Measurable (fun ξ : ℕ → Ξ =>
        total p F ψ (anchor G prox L η T x0 xstar ξ (k + 1)) - total p F ψ xstar) :=
      (h.total_measurable.comp (measurable_anchor h hη (x0 := x0) (k + 1) hk.le)).sub_const _
    refine Integrable.mono' hb hmeas.aestronglyMeasurable (Filter.Eventually.of_forall (fun ξ => ?_))
    have haQ : anchor G prox L η T x0 xstar ξ k ∈ Q := anchor_mem h hη hx0 hLη ξ k (by omega)
    have hbQ : path G prox η T x0 ξ (k + 1) ∈ Q := path_mem h hη hx0 ξ (k + 1) hk.le
    have ha'Q : anchor G prox L η T x0 xstar ξ (k + 1) ∈ Q := by
      simp only [anchor]
      exact h.convQ haQ hbQ hθ0 (by linarith) (by ring)
    have hlow : 0 ≤ total p F ψ (anchor G prox L η T x0 xstar ξ (k + 1)) - total p F ψ xstar :=
      sub_nonneg.mpr (h.total_ge ha'Q)
    rw [Real.norm_eq_abs, abs_of_nonneg hlow]
    have hc := h.total_convex.2 haQ hbQ hθ0 (sub_nonneg.mpr hθ1) (add_sub_cancel θ 1)
    simp only [smul_eq_mul] at hc
    have ha' : anchor G prox L η T x0 xstar ξ (k + 1) =
        θ • anchor G prox L η T x0 xstar ξ k + (1 - θ) • path G prox η T x0 ξ (k + 1) := rfl
    rw [← ha'] at hc
    linarith

end Moments

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ξ : Type*} [MeasurableSpace Ξ]
  {p : Measure Ξ} [IsProbabilityMeasure p] {F : Ξ → E → ℝ} {G : Ξ → E → E} {ψ : E → ℝ}
  {Q : Set E} {prox : ℝ → E → E → E} {L σ : ℝ} {xstar : E}

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ξ] in
lemma prefix_eq (G : Ξ → E → E) (prox : ℝ → E → E → E) (L η : ℝ) (T : ℕ) (x0 xstar : E) (ω0 : Ξ)
    (k : ℕ) (ξ : ℕ → Ξ) :
    (path G prox η T x0 (extend ω0 (fun i : Fin (2 * k) => ξ i)) k,
      anchor G prox L η T x0 xstar (extend ω0 (fun i : Fin (2 * k) => ξ i)) k) =
    (path G prox η T x0 ξ k, anchor G prox L η T x0 xstar ξ k) := by
  rw [path_congr G prox η T x0 k (extend_agree ω0 ξ),
    anchor_congr G prox L η T x0 xstar k (extend_agree ω0 ξ)]

variable (h : Hyp p F G ψ Q prox L σ xstar) {η : ℝ} (hη : 0 < η) (hLη : L * η ≤ 1 / 8) {T : ℕ}
  {x0 : E} (hx0 : x0 ∈ Q)
include h hη hLη hx0

lemma step_bound {k : ℕ} (hk : k < T) :
    step η T k * pweight L η T k *
      ((∫ ξ, total p F ψ (path G prox η T x0 ξ (k + 1)) - total p F ψ xstar
          ∂(Measure.infinitePi fun _ : ℕ => p)) -
        ∫ ξ, total p F ψ (anchor G prox L η T x0 xstar ξ k) - total p F ψ xstar
          ∂(Measure.infinitePi fun _ : ℕ => p)) ≤
    pweight L η T k / 2 *
      ((∫ ξ, ‖path G prox η T x0 ξ k - anchor G prox L η T x0 xstar ξ k‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => p)) -
        ∫ ξ, ‖path G prox η T x0 ξ (k + 1) - anchor G prox L η T x0 xstar ξ k‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => p)) +
    pweight L η T k * pcharge L η T k *
      (∫ ξ, total p F ψ (path G prox η T x0 ξ k) - total p F ψ xstar
        ∂(Measure.infinitePi fun _ : ℕ => p)) +
    step η T k ^ 2 * pweight L η T k * (1 + 2 * L * step η T k) * σ ^ 2 := by
  set P := Measure.infinitePi fun _ : ℕ => p
  have hL := h.pos
  obtain ⟨ω0⟩ := nonempty_of_isProbabilityMeasure p
  set s := step η T k
  have hs : 0 < s := step_pos hη hk
  have hLs : L * s ≤ 1 / 2 := by
    have := step_le hη.le hk
    have := mul_le_mul_of_nonneg_left this h.pos.le
    linarith
  have hw : 0 < pweight L η T k := (pweight_bounds h.pos.le hη hLη k hk).1
  set x := fun ξ : ℕ → Ξ => path G prox η T x0 ξ k
  set y := fun ξ : ℕ → Ξ => anchor G prox L η T x0 xstar ξ k
  set x' := fun ξ : ℕ → Ξ => path G prox η T x0 ξ (k + 1)
  have hxm : Measurable x := measurable_path h hη (x0 := x0) k hk.le
  have hym : Measurable y := measurable_anchor h hη (x0 := x0) k hk.le
  have hx'm : Measurable x' := measurable_path h hη (x0 := x0) (k + 1) hk
  have hxs := integrable_path_sq h hη (x0 := x0) k hk.le
  have hys := integrable_anchor_sq h hη (x0 := x0) k hk.le
  have hx's := integrable_path_sq h hη (x0 := x0) (k + 1) hk
  have hgx := integrable_total_path h hη hx0 hLη k hk.le
  have hgy := integrable_total_anchor h hη hx0 hLη k hk
  have hgx' := integrable_total_path h hη hx0 hLη (k + 1) hk
  have hd := integrable_dist x y hxm hym hxs hys
  have he := integrable_dist x' y hx'm hym hx's hys
  let X : (Fin (2 * k) → Ξ) → E × E := fun u =>
    (path G prox η T x0 (extend ω0 u) k, anchor G prox L η T x0 xstar (extend ω0 u) k)
  have hX : Measurable X :=
    ((measurable_path h hη (x0 := x0) k hk.le).comp (measurable_extend ω0)).prodMk
      ((measurable_anchor h hη (x0 := x0) k hk.le).comp (measurable_extend ω0))
  have hXeq : ∀ ξ : ℕ → Ξ, X (fun i : Fin (2 * k) => ξ i) = (x ξ, y ξ) :=
    fun ξ => prefix_eq G prox L η T x0 xstar ω0 k ξ
  have hpm := h.prox_measurable hs
  let Φ1 : E × E → Ξ → ℝ := fun q ω => total p F ψ (prox s q.1 (G ω q.1))
  have hΦ1 : Measurable (Function.uncurry Φ1) := by
    have hg : Measurable (fun r : (E × E) × Ξ => G r.2 r.1.1) :=
      h.meas.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    exact h.total_measurable.comp (hpm.comp ((measurable_fst.comp measurable_fst).prodMk hg))
  let Φ2 : E × E → Ξ → ℝ := fun q ω => ‖prox s q.1 (G ω q.1) - q.2‖ ^ 2
  have hΦ2 : Measurable (Function.uncurry Φ2) := by
    have hg : Measurable (fun r : (E × E) × Ξ => G r.2 r.1.1) :=
      h.meas.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
    exact ((hpm.comp ((measurable_fst.comp measurable_fst).prodMk hg)).sub
      (measurable_snd.comp measurable_fst)).norm.pow_const 2
  have hc1 : ∀ ξ : ℕ → Ξ, Φ1 (X (fun i : Fin (2 * k) => ξ i)) (ξ (2 * k)) = total p F ψ (x' ξ) := by
    intro ξ; rw [hXeq]; rfl
  have hc2 : ∀ ξ : ℕ → Ξ, Φ2 (X (fun i : Fin (2 * k) => ξ i)) (ξ (2 * k)) = ‖x' ξ - y ξ‖ ^ 2 := by
    intro ξ; rw [hXeq]; rfl
  have hobj' : Integrable (fun ξ => total p F ψ (x' ξ)) P :=
    (hgx'.add (integrable_const (total p F ψ xstar))).congr
      (Filter.Eventually.of_forall (fun ξ => by simp [x']))
  obtain ⟨hI1, hE1⟩ := integral_prefix p (2 * k) X hX Φ1 hΦ1 (by simp_rw [hc1]; exact hobj')
  obtain ⟨hI2, hE2⟩ := integral_prefix p (2 * k) X hX Φ2 hΦ2 (by simp_rw [hc2]; exact he)
  simp_rw [hc1] at hE1
  simp_rw [hc2] at hE2
  simp_rw [hXeq] at hI1 hI2 hE1 hE2
  set inner1 := fun ξ => ∫ ω, total p F ψ (prox s (x ξ) (G ω (x ξ))) ∂p
  set inner2 := fun ξ => ∫ ω, ‖prox s (x ξ) (G ω (x ξ)) - y ξ‖ ^ 2 ∂p
  have hxQ : ∀ ξ, x ξ ∈ Q := fun ξ => path_mem h hη hx0 ξ k hk.le
  have hyQ : ∀ ξ, y ξ ∈ Q := fun ξ => anchor_mem h hη hx0 hLη ξ k hk
  have hpt : ∀ ξ, inner1 ξ - total p F ψ (y ξ) ≤
      (‖x ξ - y ξ‖ ^ 2 - inner2 ξ) / (2 * s) +
        2 * L * s * (1 + 2 * L * s) * (total p F ψ (x ξ) - total p F ψ xstar) +
          s * (1 + 2 * L * s) * σ ^ 2 :=
    fun ξ => (h.one_sample (hxQ ξ) (hyQ ξ) hs hLs).2.2
  have hli : Integrable (fun ξ => inner1 ξ - total p F ψ (y ξ)) P := by
    have := hI1.sub (hgy.add (integrable_const (total p F ψ xstar)))
    refine this.congr (Filter.Eventually.of_forall (fun ξ => ?_))
    simp [inner1, y]
  have hri : Integrable (fun ξ => (‖x ξ - y ξ‖ ^ 2 - inner2 ξ) / (2 * s) +
      2 * L * s * (1 + 2 * L * s) * (total p F ψ (x ξ) - total p F ψ xstar) +
        s * (1 + 2 * L * s) * σ ^ 2) P :=
    (((hd.sub hI2).div_const _).add (hgx.const_mul _)).add (integrable_const _)
  have hmono := integral_mono hli hri hpt
  have hl : ∫ ξ, inner1 ξ - total p F ψ (y ξ) ∂P =
      (∫ ξ, total p F ψ (x' ξ) - total p F ψ xstar ∂P) -
        ∫ ξ, total p F ψ (y ξ) - total p F ψ xstar ∂P := by
    have hy' : Integrable (fun ξ => total p F ψ (y ξ)) P :=
      (hgy.add (integrable_const (total p F ψ xstar))).congr
        (Filter.Eventually.of_forall (fun ξ => by simp [y]))
    rw [integral_sub hI1 hy', ← hE1, integral_sub hobj' (integrable_const _),
      integral_sub hy' (integrable_const _)]
    ring
  have hr : ∫ ξ, ((‖x ξ - y ξ‖ ^ 2 - inner2 ξ) / (2 * s) +
      2 * L * s * (1 + 2 * L * s) * (total p F ψ (x ξ) - total p F ψ xstar) +
        s * (1 + 2 * L * s) * σ ^ 2) ∂P =
      ((∫ ξ, ‖x ξ - y ξ‖ ^ 2 ∂P) - ∫ ξ, ‖x' ξ - y ξ‖ ^ 2 ∂P) / (2 * s) +
        2 * L * s * (1 + 2 * L * s) * (∫ ξ, total p F ψ (x ξ) - total p F ψ xstar ∂P) +
        s * (1 + 2 * L * s) * σ ^ 2 := by
    have j3 : Integrable (fun ξ => ‖x ξ - y ξ‖ ^ 2 - inner2 ξ) P := hd.sub hI2
    have j1 : Integrable (fun ξ => (‖x ξ - y ξ‖ ^ 2 - inner2 ξ) / (2 * s)) P := j3.div_const _
    have j2 : Integrable (fun ξ => 2 * L * s * (1 + 2 * L * s) *
        (total p F ψ (x ξ) - total p F ψ xstar)) P := hgx.const_mul _
    have j12 : Integrable (fun ξ => (‖x ξ - y ξ‖ ^ 2 - inner2 ξ) / (2 * s) +
        2 * L * s * (1 + 2 * L * s) * (total p F ψ (x ξ) - total p F ψ xstar)) P := j1.add j2
    rw [integral_add j12 (integrable_const _), integral_add j1 j2, integral_div,
      integral_sub hd hI2, ← hE2, integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [hl, hr] at hmono
  have hsw : 0 ≤ s * pweight L η T k := (mul_pos hs hw).le
  have := mul_le_mul_of_nonneg_left hmono hsw
  have hch : pcharge L η T k = 2 * L * s ^ 2 * (1 + 2 * L * s) := rfl
  rw [hch]
  have hs0 : s ≠ 0 := hs.ne'
  calc _ = s * pweight L η T k * ((∫ ξ, total p F ψ (x' ξ) - total p F ψ xstar ∂P) -
        ∫ ξ, total p F ψ (y ξ) - total p F ψ xstar ∂P) := rfl
    _ ≤ _ := this
    _ = _ := by field_simp; ring

lemma jensen_bound {k : ℕ} (hk : k + 1 < T) :
    pweight L η T (k + 1) *
        ∫ ξ, total p F ψ (anchor G prox L η T x0 xstar ξ (k + 1)) - total p F ψ xstar
          ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      pweight L η T k * ∫ ξ, total p F ψ (anchor G prox L η T x0 xstar ξ k) - total p F ψ xstar
          ∂(Measure.infinitePi fun _ : ℕ => p) +
      (pweight L η T (k + 1) - pweight L η T k) *
        ∫ ξ, total p F ψ (path G prox η T x0 ξ (k + 1)) - total p F ψ xstar
          ∂(Measure.infinitePi fun _ : ℕ => p) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  have hw := (pweight_bounds h.pos.le hη hLη k (Nat.lt_of_succ_lt hk)).1
  have hw' := (pweight_bounds h.pos.le hη hLη (k + 1) hk).1
  have hmono := pweight_mono h.pos.le hη hLη hk
  set a := fun ξ => anchor G prox L η T x0 xstar ξ k
  set a' := fun ξ => anchor G prox L η T x0 xstar ξ (k + 1)
  set b := fun ξ => path G prox η T x0 ξ (k + 1)
  have hga := integrable_total_anchor h hη hx0 hLη k (Nat.lt_of_succ_lt hk)
  have hga' := integrable_total_anchor h hη hx0 hLη (k + 1) hk
  have hgb := integrable_total_path h hη hx0 hLη (k + 1) hk.le
  set θ := pweight L η T k / pweight L η T (k + 1)
  have hθ0 : 0 ≤ θ := div_nonneg hw.le hw'.le
  have hθ1 : θ ≤ 1 := (div_le_one hw').mpr hmono
  have hpt : ∀ ξ, pweight L η T (k + 1) * (total p F ψ (a' ξ) - total p F ψ xstar) ≤
      pweight L η T k * (total p F ψ (a ξ) - total p F ψ xstar) +
        (pweight L η T (k + 1) - pweight L η T k) * (total p F ψ (b ξ) - total p F ψ xstar) := by
    intro ξ
    have haQ : a ξ ∈ Q := anchor_mem h hη hx0 hLη ξ k (Nat.lt_of_succ_lt hk)
    have hbQ : b ξ ∈ Q := path_mem h hη hx0 ξ (k + 1) hk.le
    have hc := h.total_convex.2 haQ hbQ hθ0 (sub_nonneg.mpr hθ1) (add_sub_cancel θ 1)
    simp only [smul_eq_mul] at hc
    have ha' : a' ξ = θ • a ξ + (1 - θ) • b ξ := rfl
    rw [← ha'] at hc
    have hm := mul_le_mul_of_nonneg_left hc hw'.le
    have e1 : pweight L η T (k + 1) * θ = pweight L η T k := by
      rw [mul_comm]; exact div_mul_cancel₀ _ hw'.ne'
    have e2 : pweight L η T (k + 1) * (1 - θ) = pweight L η T (k + 1) - pweight L η T k := by
      rw [mul_sub, mul_one, e1]
    linear_combination hm + total p F ψ (a ξ) * e1 + total p F ψ (b ξ) * e2
  have hl : Integrable (fun ξ => pweight L η T (k + 1) * (total p F ψ (a' ξ) - total p F ψ xstar)) P :=
    hga'.const_mul _
  have hr1 : Integrable (fun ξ => pweight L η T k * (total p F ψ (a ξ) - total p F ψ xstar)) P :=
    hga.const_mul _
  have hr2 : Integrable (fun ξ => (pweight L η T (k + 1) - pweight L η T k) *
      (total p F ψ (b ξ) - total p F ψ xstar)) P := hgb.const_mul _
  have hr12 : Integrable (fun ξ => pweight L η T k * (total p F ψ (a ξ) - total p F ψ xstar) +
      (pweight L η T (k + 1) - pweight L η T k) * (total p F ψ (b ξ) - total p F ψ xstar)) P :=
    hr1.add hr2
  have hm := integral_mono hl hr12 hpt
  rw [integral_add hr1 hr2, integral_const_mul, integral_const_mul, integral_const_mul] at hm
  exact hm

omit hx0 in
lemma anchor_dist {k : ℕ} (hk : k + 1 < T) :
    pweight L η T (k + 1) *
        ∫ ξ, ‖path G prox η T x0 ξ (k + 1) - anchor G prox L η T x0 xstar ξ (k + 1)‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      pweight L η T k * ∫ ξ, ‖path G prox η T x0 ξ (k + 1) - anchor G prox L η T x0 xstar ξ k‖ ^ 2
          ∂(Measure.infinitePi fun _ : ℕ => p) := by
  set P := Measure.infinitePi fun _ : ℕ => p
  have hw := (pweight_bounds h.pos.le hη hLη k (Nat.lt_of_succ_lt hk)).1
  have hw' := (pweight_bounds h.pos.le hη hLη (k + 1) hk).1
  have hmono := pweight_mono h.pos.le hη hLη hk
  set θ := pweight L η T k / pweight L η T (k + 1)
  have hθ0 : 0 ≤ θ := div_nonneg hw.le hw'.le
  have hθ1 : θ ≤ 1 := (div_le_one hw').mpr hmono
  have hd1 := integrable_dist (fun ξ => path G prox η T x0 ξ (k + 1))
    (fun ξ => anchor G prox L η T x0 xstar ξ (k + 1)) (measurable_path h hη (x0 := x0) (k + 1) hk.le)
    (measurable_anchor h hη (x0 := x0) (k + 1) hk.le) (integrable_path_sq h hη (x0 := x0) (k + 1) hk.le)
    (integrable_anchor_sq h hη (x0 := x0) (k + 1) hk.le)
  have hd2 := integrable_dist (fun ξ => path G prox η T x0 ξ (k + 1))
    (fun ξ => anchor G prox L η T x0 xstar ξ k) (measurable_path h hη (x0 := x0) (k + 1) hk.le)
    (measurable_anchor h hη (x0 := x0) k (Nat.lt_of_succ_lt hk).le)
    (integrable_path_sq h hη (x0 := x0) (k + 1) hk.le)
    (integrable_anchor_sq h hη (x0 := x0) k (Nat.lt_of_succ_lt hk).le)
  have hpt : ∀ ξ, pweight L η T (k + 1) *
      ‖path G prox η T x0 ξ (k + 1) - anchor G prox L η T x0 xstar ξ (k + 1)‖ ^ 2 ≤
      pweight L η T k * ‖path G prox η T x0 ξ (k + 1) - anchor G prox L η T x0 xstar ξ k‖ ^ 2 := by
    intro ξ
    set b := path G prox η T x0 ξ (k + 1)
    set a := anchor G prox L η T x0 xstar ξ k
    have he : b - anchor G prox L η T x0 xstar ξ (k + 1) = θ • (b - a) := by
      simp only [anchor]
      module
    rw [he, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have e1 : pweight L η T (k + 1) * θ = pweight L η T k := by
      rw [mul_comm]; exact div_mul_cancel₀ _ hw'.ne'
    have hsq : 0 ≤ ‖b - a‖ ^ 2 := sq_nonneg _
    have : pweight L η T (k + 1) * (θ ^ 2 * ‖b - a‖ ^ 2) = pweight L η T k * θ * ‖b - a‖ ^ 2 := by
      rw [← e1]; ring
    rw [this]
    have := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hw.le hθ1) hsq
    linarith
  have hm := integral_mono (hd1.const_mul _) (hd2.const_mul _) hpt
  rwa [integral_const_mul, integral_const_mul] at hm

theorem expected_gap (hT : 0 < T) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (hA0 : total p F ψ x0 - total p F ψ xstar ≤ Δ) :
    Integrable (fun ξ => total p F ψ (path G prox η T x0 ξ T) - total p F ψ xstar)
      (Measure.infinitePi fun _ : ℕ => p) ∧
    ∫ ξ, total p F ψ (path G prox η T x0 ξ T) - total p F ψ xstar
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      3 * ‖x0 - xstar‖ ^ 2 / (η * T) + 7 * η * σ ^ 2 + 2 * Δ / T := by
  set P := Measure.infinitePi fun _ : ℕ => p
  refine ⟨integrable_total_path h hη hx0 hLη T le_rfl, ?_⟩
  let A : ℕ → ℝ := fun k => ∫ ξ, total p F ψ (path G prox η T x0 ξ k) - total p F ψ xstar ∂P
  let Φ : ℕ → ℝ := fun k => ∫ ξ, total p F ψ (anchor G prox L η T x0 xstar ξ k) - total p F ψ xstar ∂P
  let d : ℕ → ℝ := fun k => ∫ ξ, ‖path G prox η T x0 ξ k - anchor G prox L η T x0 xstar ξ k‖ ^ 2 ∂P
  let e : ℕ → ℝ := fun k => ∫ ξ, ‖path G prox η T x0 ξ (k + 1) - anchor G prox L η T x0 xstar ξ k‖ ^ 2 ∂P
  have hH : ∀ k, k < T → step η T k * pweight L η T k * (A (k + 1) - Φ k) ≤
      pweight L η T k / 2 * (d k - e k) + pweight L η T k * pcharge L η T k * A k +
        step η T k ^ 2 * pweight L η T k * (1 + 2 * L * step η T k) * σ ^ 2 :=
    fun k hk => step_bound h hη hLη hx0 hk
  have hJ : ∀ k, k + 1 < T → pweight L η T (k + 1) * Φ (k + 1) ≤
      pweight L η T k * Φ k + (pweight L η T (k + 1) - pweight L η T k) * A (k + 1) :=
    fun k hk => jensen_bound h hη hLη hx0 hk
  have hD : ∀ k, k + 1 < T → pweight L η T (k + 1) * d (k + 1) ≤ pweight L η T k * e k :=
    fun k hk => anchor_dist h hη hLη (x0 := x0) hk
  have he : ∀ k, k < T → 0 ≤ e k := fun k _ => integral_nonneg (fun ξ => sq_nonneg _)
  have hΦ0 : Φ 0 = 0 := by simp [Φ, anchor]
  have hd0 : d 0 ≤ ‖x0 - xstar‖ ^ 2 := by simp [d, anchor, path]
  have hA0' : A 0 ≤ Δ := by
    simp only [A, path, integral_const, probReal_univ, one_smul]
    exact hA0
  exact ppotential_bound h.pos.le hη hLη hT A Φ d e hH hJ hD he hΦ0 hd0 hΔ hA0'

end Assembly

end OracleTemplate.SampledComposite
