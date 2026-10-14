import LongTails.Proofs.TwoSidedPLPath
import LongTails.Proofs.TwoSidedPLSampling

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped RealInnerProductSpace
open LongTails.Setups.StochasticTwoSidedPL

namespace OracleTemplate.TwoSidedPL

section Path

variable {E F Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

noncomputable def path (Gx : E × F → Ω → E) (Gy : E × F → Ω → F) (L μy τ : ℝ) (x0 : E) (y0 : F)
    (ξ : ℕ → Ω) : ℕ → E × F × E
  | 0 => (x0, y0, x0)
  | t + 1 =>
    ((path Gx Gy L μy τ x0 y0 ξ t).1 - τ • (Gx ((path Gx Gy L μy τ x0 y0 ξ t).1,
        (path Gx Gy L μy τ x0 y0 ξ t).2.1) (ξ (2 * t)) +
        (2 * L) • ((path Gx Gy L μy τ x0 y0 ξ t).1 - (path Gx Gy L μy τ x0 y0 ξ t).2.2)),
      (path Gx Gy L μy τ x0 y0 ξ t).2.1 + (τ / 32) • Gy ((path Gx Gy L μy τ x0 y0 ξ t).1 -
        τ • (Gx ((path Gx Gy L μy τ x0 y0 ξ t).1, (path Gx Gy L μy τ x0 y0 ξ t).2.1) (ξ (2 * t)) +
        (2 * L) • ((path Gx Gy L μy τ x0 y0 ξ t).1 - (path Gx Gy L μy τ x0 y0 ξ t).2.2)),
        (path Gx Gy L μy τ x0 y0 ξ t).2.1) (ξ (2 * t + 1)),
      (path Gx Gy L μy τ x0 y0 ξ t).2.2 + (τ * μy / 6144) • ((path Gx Gy L μy τ x0 y0 ξ t).1 -
        τ • (Gx ((path Gx Gy L μy τ x0 y0 ξ t).1, (path Gx Gy L μy τ x0 y0 ξ t).2.1) (ξ (2 * t)) +
        (2 * L) • ((path Gx Gy L μy τ x0 y0 ξ t).1 - (path Gx Gy L μy τ x0 y0 ξ t).2.2)) -
        (path Gx Gy L μy τ x0 y0 ξ t).2.2))

noncomputable def noise1 (gx : E → F → E) (Gx : E × F → Ω → E) (Gy : E × F → Ω → F)
    (L μy τ : ℝ) (x0 : E) (y0 : F) (ξ : ℕ → Ω) (t : ℕ) : E :=
  Gx ((path Gx Gy L μy τ x0 y0 ξ t).1, (path Gx Gy L μy τ x0 y0 ξ t).2.1) (ξ (2 * t)) -
    gx (path Gx Gy L μy τ x0 y0 ξ t).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1

noncomputable def noise2 (gy : E → F → F) (Gx : E × F → Ω → E) (Gy : E × F → Ω → F)
    (L μy τ : ℝ) (x0 : E) (y0 : F) (ξ : ℕ → Ω) (t : ℕ) : F :=
  Gy ((path Gx Gy L μy τ x0 y0 ξ (t + 1)).1, (path Gx Gy L μy τ x0 y0 ξ t).2.1) (ξ (2 * t + 1)) -
    gy (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1

variable (gx : E → F → E) (gy : E → F → F) (Gx : E × F → Ω → E) (Gy : E × F → Ω → F)
  (L μy τ : ℝ) (x0 : E) (y0 : F)

lemma path_succ_fst (ξ : ℕ → Ω) (t : ℕ) :
    (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 = (path Gx Gy L μy τ x0 y0 ξ t).1 -
      τ • (Gx ((path Gx Gy L μy τ x0 y0 ξ t).1, (path Gx Gy L μy τ x0 y0 ξ t).2.1) (ξ (2 * t)) +
        (2 * L) • ((path Gx Gy L μy τ x0 y0 ξ t).1 - (path Gx Gy L μy τ x0 y0 ξ t).2.2)) := rfl

lemma path_succ_snd (ξ : ℕ → Ω) (t : ℕ) :
    (path Gx Gy L μy τ x0 y0 ξ (t + 1)).2.1 = (path Gx Gy L μy τ x0 y0 ξ t).2.1 +
      (τ / 32) • Gy ((path Gx Gy L μy τ x0 y0 ξ (t + 1)).1, (path Gx Gy L μy τ x0 y0 ξ t).2.1)
        (ξ (2 * t + 1)) := rfl

lemma path_succ_thd (ξ : ℕ → Ω) (t : ℕ) :
    (path Gx Gy L μy τ x0 y0 ξ (t + 1)).2.2 = (path Gx Gy L μy τ x0 y0 ξ t).2.2 +
      (τ * μy / 6144) • ((path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 -
        (path Gx Gy L μy τ x0 y0 ξ t).2.2) := rfl

lemma path_rec (ξ : ℕ → Ω) (t : ℕ) :
    path Gx Gy L μy τ x0 y0 ξ (t + 1) = nextState gx gy L μy τ (path Gx Gy L μy τ x0 y0 ξ t)
      (noise1 gx Gx Gy L μy τ x0 y0 ξ t) (noise2 gy Gx Gy L μy τ x0 y0 ξ t) := by
  have hx : (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 = (path Gx Gy L μy τ x0 y0 ξ t).1 -
      τ • (xgrad gx L (path Gx Gy L μy τ x0 y0 ξ t).2.2 (path Gx Gy L μy τ x0 y0 ξ t).1
        (path Gx Gy L μy τ x0 y0 ξ t).2.1 + noise1 gx Gx Gy L μy τ x0 y0 ξ t) := by
    rw [path_succ_fst]
    congr 2
    simp only [xgrad, noise1]
    abel
  ext
  · exact hx
  · simp only [nextState]
    rw [path_succ_snd, ← hx]
    simp only [noise2]
    congr 2
    abel
  · simp only [nextState]
    rw [path_succ_thd, ← hx]

lemma path_congr : ∀ (t : ℕ) (ξ ξ' : ℕ → Ω), (∀ i, i < 2 * t → ξ i = ξ' i) →
    path Gx Gy L μy τ x0 y0 ξ t = path Gx Gy L μy τ x0 y0 ξ' t := by
  intro t
  induction t with
  | zero => intro _ _ _; rfl
  | succ t ih =>
    intro ξ ξ' h
    have h0 := ih ξ ξ' (fun i hi => h i (by omega))
    have h1 := h (2 * t) (by omega)
    have h2 := h (2 * t + 1) (by omega)
    simp only [path]
    rw [h0, h1, h2]

lemma path_fst_congr (t : ℕ) (ξ ξ' : ℕ → Ω) (h : ∀ i, i < 2 * t + 1 → ξ i = ξ' i) :
    (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 = (path Gx Gy L μy τ x0 y0 ξ' (t + 1)).1 := by
  rw [path_succ_fst, path_succ_fst,
    path_congr Gx Gy L μy τ x0 y0 t ξ ξ' (fun i hi => h i (by omega)), h (2 * t) (by omega)]

end Path

section Measurable

variable {E F Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]

variable {Gx : E × F → Ω → E} {Gy : E × F → Ω → F}

omit [CompleteSpace E] [CompleteSpace F] in
lemma measurable_path (hGx : Measurable (Function.uncurry Gx)) (hGy : Measurable (Function.uncurry Gy))
    (L μy τ : ℝ) (x0 : E) (y0 : F) :
    ∀ t, Measurable fun ξ : ℕ → Ω => path Gx Gy L μy τ x0 y0 ξ t := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have h1 : Measurable fun ξ : ℕ → Ω => (path Gx Gy L μy τ x0 y0 ξ t).1 := ih.fst
    have h2 : Measurable fun ξ : ℕ → Ω => (path Gx Gy L μy τ x0 y0 ξ t).2.1 := ih.snd.fst
    have h3 : Measurable fun ξ : ℕ → Ω => (path Gx Gy L μy τ x0 y0 ξ t).2.2 := ih.snd.snd
    have hg : Measurable fun ξ : ℕ → Ω =>
        Gx ((path Gx Gy L μy τ x0 y0 ξ t).1, (path Gx Gy L μy τ x0 y0 ξ t).2.1) (ξ (2 * t)) :=
      hGx.comp ((h1.prodMk h2).prodMk (measurable_pi_apply _))
    have hx : Measurable fun ξ : ℕ → Ω => (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 := by
      simp only [path_succ_fst]
      exact h1.sub ((hg.add ((h1.sub h3).const_smul _)).const_smul _)
    have hy : Measurable fun ξ : ℕ → Ω => (path Gx Gy L μy τ x0 y0 ξ (t + 1)).2.1 := by
      simp only [path_succ_snd]
      exact h2.add ((hGy.comp ((hx.prodMk h2).prodMk (measurable_pi_apply _))).const_smul _)
    have hz : Measurable fun ξ : ℕ → Ω => (path Gx Gy L μy τ x0 y0 ξ (t + 1)).2.2 := by
      simp only [path_succ_thd]
      exact h3.add ((hx.sub h3).const_smul _)
    exact hx.prodMk (hy.prodMk hz)

end Measurable

section Continuity

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μx μy : ℝ}

lemma Hyp.continuous_gx (H : Hyp f gx gy L μx μy) : Continuous fun w : E × F => gx w.1 w.2 := by
  have hL := H.hL
  have : LipschitzWith (Real.toNNReal (2 * L)) (fun w : E × F => gx w.1 w.2) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith)]
      have h := H.lipx a.1 b.1 a.2 b.2
      have h1 : ‖a.1 - b.1‖ ≤ ‖a - b‖ := norm_fst_le (a - b)
      have h2 : ‖a.2 - b.2‖ ≤ ‖a - b‖ := norm_snd_le (a - b)
      linarith [mul_le_mul_of_nonneg_left h1 hL.le, mul_le_mul_of_nonneg_left h2 hL.le]
  exact this.continuous

lemma Hyp.continuous_gy (H : Hyp f gx gy L μx μy) : Continuous fun w : E × F => gy w.1 w.2 := by
  have hL := H.hL
  have : LipschitzWith (Real.toNNReal (2 * L)) (fun w : E × F => gy w.1 w.2) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith)]
      have h := H.lipy a.1 b.1 a.2 b.2
      have h1 : ‖a.1 - b.1‖ ≤ ‖a - b‖ := norm_fst_le (a - b)
      have h2 : ‖a.2 - b.2‖ ≤ ‖a - b‖ := norm_snd_le (a - b)
      linarith [mul_le_mul_of_nonneg_left h1 hL.le, mul_le_mul_of_nonneg_left h2 hL.le]
  exact this.continuous

lemma Hyp.continuous_xhat [ProperSpace E] (H : Hyp f gx gy L μx μy) :
    Continuous fun w : F × E => xhat f L w.1 w.2 := by
  have : LipschitzWith (Real.toNNReal 3) (fun w : F × E => xhat f L w.1 w.2) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by norm_num)]
      have h := H.xhat_lip a.1 b.1 a.2 b.2
      have h1 : ‖a.1 - b.1‖ ≤ ‖a - b‖ := norm_fst_le (a - b)
      have h2 : ‖a.2 - b.2‖ ≤ ‖a - b‖ := norm_snd_le (a - b)
      linarith
  exact this.continuous

lemma Hyp.continuous_f (H : Hyp f gx gy L μx μy) : Continuous fun w : E × F => f w.1 w.2 := by
  have hL := H.hL
  rw [continuous_iff_continuousAt]
  intro w
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  let φ := fun v : E × F => (‖gy w.1 w.2‖ + L * ‖v.1 - w.1‖) * ‖v.2 - w.2‖ +
    L / 2 * ‖v.2 - w.2‖ ^ 2 + ‖gx w.1 w.2‖ * ‖v.1 - w.1‖ + L / 2 * ‖v.1 - w.1‖ ^ 2
  have hφc : Continuous φ := by fun_prop
  have hφ0 : φ w = 0 := by simp [φ]
  have hlim : Tendsto φ (𝓝 w) (𝓝 0) := by rw [← hφ0]; exact hφc.tendsto w
  refine squeeze_zero (fun v => norm_nonneg _) (fun v => ?_) hlim
  have a1 := H.upper_y v.1 w.2 v.2
  have a2 := H.lower_y v.1 w.2 v.2
  have a3 := H.upper_x w.1 v.1 w.2
  have a4 := H.lower_x w.1 v.1 w.2
  have i1 := abs_le.1 (abs_real_inner_le_norm (gy v.1 w.2) (v.2 - w.2))
  have i2 := abs_le.1 (abs_real_inner_le_norm (gx w.1 w.2) (v.1 - w.1))
  have g1 : ‖gy v.1 w.2‖ ≤ ‖gy w.1 w.2‖ + L * ‖v.1 - w.1‖ := by
    have := H.lipy v.1 w.1 w.2 w.2
    simp only [sub_self, norm_zero, add_zero] at this
    have := norm_le_insert' (gy v.1 w.2) (gy w.1 w.2)
    linarith
  have g2 : ‖gy v.1 w.2‖ * ‖v.2 - w.2‖ ≤ (‖gy w.1 w.2‖ + L * ‖v.1 - w.1‖) * ‖v.2 - w.2‖ :=
    mul_le_mul_of_nonneg_right g1 (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_le]
  simp only [φ]
  constructor <;> linarith

lemma Hyp.norm_gx_le (H : Hyp f gx gy L μx μy) (x : E) (y : F) :
    ‖gx x y‖ ≤ ‖gx 0 0‖ + L * (‖x‖ + ‖y‖) := by
  have h := H.lipx x 0 y 0
  simp only [sub_zero] at h
  have := norm_le_insert' (gx x y) (gx 0 0)
  linarith

lemma Hyp.norm_gy_le (H : Hyp f gx gy L μx μy) (x : E) (y : F) :
    ‖gy x y‖ ≤ ‖gy 0 0‖ + L * (‖x‖ + ‖y‖) := by
  have h := H.lipy x 0 y 0
  simp only [sub_zero] at h
  have := norm_le_insert' (gy x y) (gy 0 0)
  linarith

lemma Hyp.norm_xhat_le [ProperSpace E] (H : Hyp f gx gy L μx μy) (y : F) (z : E) :
    ‖xhat f L y z‖ ≤ ‖xhat f L 0 0‖ + ‖y‖ + 2 * ‖z‖ := by
  have h := H.xhat_lip y 0 z 0
  simp only [sub_zero] at h
  have := norm_le_insert' (xhat f L y z) (xhat f L 0 0)
  linarith

end Continuity

section Moments

variable {E F Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μx μy σ : ℝ}
  {Gx : E × F → Ω → E} {Gy : E × F → Ω → F} {p : Measure Ω} [IsProbabilityMeasure p]

lemma noise1_sq (H : Hyp f gx gy L μx μy)
    (ox : IsUnbiasedOracle p (fun w : E × F => gx w.1 w.2) Gx σ)
    (oy : IsUnbiasedOracle p (fun w : E × F => gy w.1 w.2) Gy σ) (μy' τ : ℝ) (x0 : E) (y0 : F)
    (t : ℕ) :
    Integrable (fun ξ => ‖noise1 gx Gx Gy L μy' τ x0 y0 ξ t‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p) ∧
      ∫ ξ, ‖noise1 gx Gx Gy L μy' τ x0 y0 ξ t‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p) ≤ σ ^ 2 := by
  have hp := measurable_path ox.measurable oy.measurable L μy' τ x0 y0 t
  have hX : Measurable fun ξ : ℕ → Ω => ((path Gx Gy L μy' τ x0 y0 ξ t).1,
      (path Gx Gy L μy' τ x0 y0 ξ t).2.1) := hp.fst.prodMk hp.snd.fst
  have hΦ : Measurable (Function.uncurry fun (w : E × F) (ω : Ω) => ‖Gx w ω - gx w.1 w.2‖ ^ 2) :=
    (ox.measurable.sub (H.continuous_gx.measurable.comp measurable_fst)).norm.pow_const 2
  exact integrable_prefix_dep p (2 * t) _ hX
    (fun ξ ξ' h => by rw [path_congr Gx Gy L μy' τ x0 y0 t ξ ξ' h]) _ hΦ
    (fun _ _ => sq_nonneg _) ox.variance_integrable ox.variance

lemma noise2_sq (H : Hyp f gx gy L μx μy)
    (ox : IsUnbiasedOracle p (fun w : E × F => gx w.1 w.2) Gx σ)
    (oy : IsUnbiasedOracle p (fun w : E × F => gy w.1 w.2) Gy σ) (μy' τ : ℝ) (x0 : E) (y0 : F)
    (t : ℕ) :
    Integrable (fun ξ => ‖noise2 gy Gx Gy L μy' τ x0 y0 ξ t‖ ^ 2) (Measure.infinitePi fun _ : ℕ => p) ∧
      ∫ ξ, ‖noise2 gy Gx Gy L μy' τ x0 y0 ξ t‖ ^ 2 ∂(Measure.infinitePi fun _ : ℕ => p) ≤ σ ^ 2 := by
  have hp := measurable_path ox.measurable oy.measurable L μy' τ x0 y0
  have hX : Measurable fun ξ : ℕ → Ω => ((path Gx Gy L μy' τ x0 y0 ξ (t + 1)).1,
      (path Gx Gy L μy' τ x0 y0 ξ t).2.1) := (hp (t + 1)).fst.prodMk (hp t).snd.fst
  have hΦ : Measurable (Function.uncurry fun (w : E × F) (ω : Ω) => ‖Gy w ω - gy w.1 w.2‖ ^ 2) :=
    (oy.measurable.sub (H.continuous_gy.measurable.comp measurable_fst)).norm.pow_const 2
  exact integrable_prefix_dep p (2 * t + 1) _ hX
    (fun ξ ξ' h => by
      rw [path_fst_congr Gx Gy L μy' τ x0 y0 t ξ ξ' h,
        path_congr Gx Gy L μy' τ x0 y0 t ξ ξ' (fun i hi => h i (by omega))]) _ hΦ
    (fun _ _ => sq_nonneg _) oy.variance_integrable oy.variance

end Moments

section Expectation

variable {E F Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [ProperSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μx μy σ : ℝ}
  {Gx : E × F → Ω → E} {Gy : E × F → Ω → F} {p : Measure Ω} [IsProbabilityMeasure p]

omit [ProperSpace E] in
lemma memLp_noise1 (H : Hyp f gx gy L μx μy)
    (ox : IsUnbiasedOracle p (fun w : E × F => gx w.1 w.2) Gx σ)
    (oy : IsUnbiasedOracle p (fun w : E × F => gy w.1 w.2) Gy σ) (τ : ℝ) (x0 : E) (y0 : F)
    (t : ℕ) :
    MemLp (fun ξ => noise1 gx Gx Gy L μy τ x0 y0 ξ t) 2 (Measure.infinitePi fun _ : ℕ => p) := by
  have hp := measurable_path ox.measurable oy.measurable L μy τ x0 y0 t
  have hm : Measurable fun ξ : ℕ → Ω => noise1 gx Gx Gy L μy τ x0 y0 ξ t :=
    (ox.measurable.comp ((hp.fst.prodMk hp.snd.fst).prodMk (measurable_pi_apply _))).sub
      (H.continuous_gx.measurable.comp (hp.fst.prodMk hp.snd.fst))
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
    (noise1_sq H ox oy μy τ x0 y0 t).1

omit [ProperSpace E] in
lemma memLp_noise2 (H : Hyp f gx gy L μx μy)
    (ox : IsUnbiasedOracle p (fun w : E × F => gx w.1 w.2) Gx σ)
    (oy : IsUnbiasedOracle p (fun w : E × F => gy w.1 w.2) Gy σ) (τ : ℝ) (x0 : E) (y0 : F)
    (t : ℕ) :
    MemLp (fun ξ => noise2 gy Gx Gy L μy τ x0 y0 ξ t) 2 (Measure.infinitePi fun _ : ℕ => p) := by
  have hp := measurable_path ox.measurable oy.measurable L μy τ x0 y0
  have hX : Measurable fun ξ : ℕ → Ω => ((path Gx Gy L μy τ x0 y0 ξ (t + 1)).1,
      (path Gx Gy L μy τ x0 y0 ξ t).2.1) := (hp (t + 1)).fst.prodMk (hp t).snd.fst
  have hm : Measurable fun ξ : ℕ → Ω => noise2 gy Gx Gy L μy τ x0 y0 ξ t :=
    (oy.measurable.comp (hX.prodMk (measurable_pi_apply _))).sub (H.continuous_gy.measurable.comp hX)
  exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
    (noise2_sq H ox oy μy τ x0 y0 t).1

lemma memLp_list_sum {X : Type*} [MeasurableSpace X] {P : Measure X}
    (vs : List (X → ℝ)) (hvs : ∀ v ∈ vs, MemLp v 2 P) :
    MemLp (fun x => (vs.map fun v => v x).sum) 2 P := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hvs v (by simp)).add (ih fun w hw => hvs w (by simp [hw]))

lemma memLp_of_bound {X G : Type*} [MeasurableSpace X] {P : Measure X} [IsFiniteMeasure P]
    [NormedAddCommGroup G] {u : X → G} (hu : AEStronglyMeasurable u P) {c0 : ℝ}
    (vs : List (X → ℝ)) (hvs : ∀ v ∈ vs, MemLp v 2 P)
    (h : ∀ x, ‖u x‖ ≤ c0 + (vs.map fun v => v x).sum) : MemLp u 2 P :=
  memLp_two_of_norm_le ((memLp_const c0).add (memLp_list_sum vs hvs)) hu h

omit [ProperSpace E] in
lemma memLp_path (H : Hyp f gx gy L μx μy)
    (ox : IsUnbiasedOracle p (fun w : E × F => gx w.1 w.2) Gx σ)
    (oy : IsUnbiasedOracle p (fun w : E × F => gy w.1 w.2) Gy σ) (τ : ℝ) (x0 : E) (y0 : F) :
    ∀ t, MemLp (fun ξ => (path Gx Gy L μy τ x0 y0 ξ t).1) 2 (Measure.infinitePi fun _ : ℕ => p) ∧
      MemLp (fun ξ => (path Gx Gy L μy τ x0 y0 ξ t).2.1) 2 (Measure.infinitePi fun _ : ℕ => p) ∧
      MemLp (fun ξ => (path Gx Gy L μy τ x0 y0 ξ t).2.2) 2 (Measure.infinitePi fun _ : ℕ => p) := by
  have hL := H.hL
  have hp := measurable_path ox.measurable oy.measurable L μy τ x0 y0
  intro t
  induction t with
  | zero => exact ⟨memLp_const _, memLp_const _, memLp_const _⟩
  | succ t ih =>
    obtain ⟨hx, hy, hz⟩ := ih
    have he1 := memLp_noise1 H ox oy τ x0 y0 t
    have he2 := memLp_noise2 H ox oy τ x0 y0 t
    have hrec := fun ξ => path_rec gx gy Gx Gy L μy τ x0 y0 ξ t
    have hx' : MemLp (fun ξ => (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1) 2
        (Measure.infinitePi fun _ : ℕ => p) := by
      refine memLp_of_bound (hp (t + 1)).fst.aestronglyMeasurable (c0 := |τ| * ‖gx 0 0‖)
        [fun ξ => (1 + 3 * |τ| * L) * ‖(path Gx Gy L μy τ x0 y0 ξ t).1‖,
          fun ξ => |τ| * L * ‖(path Gx Gy L μy τ x0 y0 ξ t).2.1‖,
          fun ξ => 2 * |τ| * L * ‖(path Gx Gy L μy τ x0 y0 ξ t).2.2‖,
          fun ξ => |τ| * ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖] ?_ ?_
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl | rfl
        · exact hx.norm.const_mul _
        · exact hy.norm.const_mul _
        · exact hz.norm.const_mul _
        · exact he1.norm.const_mul _
      · intro ξ
        rw [hrec ξ]
        simp only [nextState, xgrad, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        set x := (path Gx Gy L μy τ x0 y0 ξ t).1
        set y := (path Gx Gy L μy τ x0 y0 ξ t).2.1
        set z := (path Gx Gy L μy τ x0 y0 ξ t).2.2
        set e := noise1 gx Gx Gy L μy τ x0 y0 ξ t
        have h1 := H.norm_gx_le x y
        have h2 : ‖x - τ • (gx x y + (2 * L) • (x - z) + e)‖ ≤
            ‖x‖ + |τ| * (‖gx x y‖ + 2 * L * (‖x‖ + ‖z‖) + ‖e‖) := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          refine norm_add₃_le.trans ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 2 * L)]
          gcongr
          exact norm_sub_le _ _
        have hτ0 := abs_nonneg τ
        linarith [mul_le_mul_of_nonneg_left h1 hτ0]
    have hy' : MemLp (fun ξ => (path Gx Gy L μy τ x0 y0 ξ (t + 1)).2.1) 2
        (Measure.infinitePi fun _ : ℕ => p) := by
      refine memLp_of_bound (hp (t + 1)).snd.fst.aestronglyMeasurable (c0 := |τ / 32| * ‖gy 0 0‖)
        [fun ξ => (1 + |τ / 32| * L) * ‖(path Gx Gy L μy τ x0 y0 ξ t).2.1‖,
          fun ξ => |τ / 32| * L * ‖(path Gx Gy L μy τ x0 y0 ξ (t + 1)).1‖,
          fun ξ => |τ / 32| * ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖] ?_ ?_
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl | rfl
        · exact hy.norm.const_mul _
        · exact hx'.norm.const_mul _
        · exact he2.norm.const_mul _
      · intro ξ
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [path_succ_snd]
        set x' := (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1
        set y := (path Gx Gy L μy τ x0 y0 ξ t).2.1
        have hG : Gy (x', y) (ξ (2 * t + 1)) = gy x' y + noise2 gy Gx Gy L μy τ x0 y0 ξ t := by
          simp only [noise2, x', y]; abel
        rw [hG]
        have h1 := H.norm_gy_le x' y
        have h2 : ‖y + (τ / 32) • (gy x' y + noise2 gy Gx Gy L μy τ x0 y0 ξ t)‖ ≤
            ‖y‖ + |τ / 32| * (‖gy x' y‖ + ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          exact norm_add_le _ _
        have hτ0 := abs_nonneg (τ / 32)
        linarith [mul_le_mul_of_nonneg_left h1 hτ0]
    have hz' : MemLp (fun ξ => (path Gx Gy L μy τ x0 y0 ξ (t + 1)).2.2) 2
        (Measure.infinitePi fun _ : ℕ => p) := by
      refine memLp_of_bound (hp (t + 1)).snd.snd.aestronglyMeasurable (c0 := 0)
        [fun ξ => (1 + |τ * μy / 6144|) * ‖(path Gx Gy L μy τ x0 y0 ξ t).2.2‖,
          fun ξ => |τ * μy / 6144| * ‖(path Gx Gy L μy τ x0 y0 ξ (t + 1)).1‖] ?_ ?_
      · intro v hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact hz.norm.const_mul _
        · exact hx'.norm.const_mul _
      · intro ξ
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        rw [path_succ_thd]
        set x' := (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1
        set z := (path Gx Gy L μy τ x0 y0 ξ t).2.2
        have h2 : ‖z + (τ * μy / 6144) • (x' - z)‖ ≤ ‖z‖ + |τ * μy / 6144| * (‖x'‖ + ‖z‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          exact norm_sub_le _ _
        linarith [abs_nonneg (τ * μy / 6144)]
    exact ⟨hx', hy', hz'⟩

end Expectation

section Window

variable {E F Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [ProperSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]
variable {f : E → F → ℝ} {gx : E → F → E} {gy : E → F → F} {L μx μy σ : ℝ}
  {Gx : E × F → Ω → E} {Gy : E × F → Ω → F} {p : Measure Ω} [IsProbabilityMeasure p]

lemma martingale_props (H : Hyp f gx gy L μx μy)
    (ox : IsUnbiasedOracle p (fun w : E × F => gx w.1 w.2) Gx σ)
    (oy : IsUnbiasedOracle p (fun w : E × F => gy w.1 w.2) Gy σ) (τ : ℝ) (x0 : E) (y0 : F)
    (t : ℕ) :
    Integrable (fun ξ => martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t)
      (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (noise1 gx Gx Gy L μy τ x0 y0 ξ t)
      (noise2 gy Gx Gy L μy τ x0 y0 ξ t)) (Measure.infinitePi fun _ : ℕ => p) ∧
    ∫ ξ, martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t)
      (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (noise1 gx Gx Gy L μy τ x0 y0 ξ t)
      (noise2 gy Gx Gy L μy τ x0 y0 ξ t) ∂(Measure.infinitePi fun _ : ℕ => p) = 0 := by
  have hL := H.hL
  have hp := measurable_path ox.measurable oy.measurable L μy τ x0 y0
  obtain ⟨hx, hy, hz⟩ := memLp_path H ox oy τ x0 y0 t
  have hx' := (memLp_path H ox oy τ x0 y0 (t + 1)).1
  have he1 := memLp_noise1 H ox oy τ x0 y0 t
  have he2 := memLp_noise2 H ox oy τ x0 y0 t
  have hgxc := H.continuous_gx
  have hgyc := H.continuous_gy
  have hxhc := H.continuous_xhat
  have hU1m : Measurable fun s : E × F × E => xgrad gx L s.2.2 s.1 s.2.1 :=
    (hgxc.measurable.comp (measurable_fst.prodMk measurable_snd.fst)).add
      ((measurable_fst.sub measurable_snd.snd).const_smul _)
  have hU1 : MemLp (fun ξ => xgrad gx L (path Gx Gy L μy τ x0 y0 ξ t).2.2
      (path Gx Gy L μy τ x0 y0 ξ t).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1) 2
      (Measure.infinitePi fun _ : ℕ => p) := by
    refine memLp_of_bound (hU1m.comp (hp t)).aestronglyMeasurable (c0 := ‖gx 0 0‖)
      [fun ξ => 3 * L * ‖(path Gx Gy L μy τ x0 y0 ξ t).1‖,
        fun ξ => L * ‖(path Gx Gy L μy τ x0 y0 ξ t).2.1‖,
        fun ξ => 2 * L * ‖(path Gx Gy L μy τ x0 y0 ξ t).2.2‖] ?_ ?_
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact hx.norm.const_mul _
      · exact hy.norm.const_mul _
      · exact hz.norm.const_mul _
    · intro ξ
      simp only [xgrad, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      set x := (path Gx Gy L μy τ x0 y0 ξ t).1
      set y := (path Gx Gy L μy τ x0 y0 ξ t).2.1
      set z := (path Gx Gy L μy τ x0 y0 ξ t).2.2
      have h1 := H.norm_gx_le x y
      have h2 : ‖gx x y + (2 * L) • (x - z)‖ ≤ ‖gx x y‖ + 2 * L * (‖x‖ + ‖z‖) := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 2 * L)]
        gcongr
        exact norm_sub_le _ _
      linarith
  set c := τ / 32 + 5 * L * τ ^ 2 / 1024
  have hU2m : Measurable fun w : (E × F × E) × E =>
      (τ / 16) • gy (xhat f L w.1.2.1 w.1.2.2) w.1.2.1 - c • gy w.2 w.1.2.1 :=
    ((hgyc.measurable.comp ((hxhc.measurable.comp
      (measurable_fst.snd.fst.prodMk measurable_fst.snd.snd)).prodMk measurable_fst.snd.fst)).const_smul _).sub
      ((hgyc.measurable.comp (measurable_snd.prodMk measurable_fst.snd.fst)).const_smul _)
  have hXm : Measurable fun ξ : ℕ → Ω => (path Gx Gy L μy τ x0 y0 ξ t,
      (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1) := (hp t).prodMk (hp (t + 1)).fst
  have hU2 : MemLp (fun ξ => (τ / 16) • gy (xhat f L (path Gx Gy L μy τ x0 y0 ξ t).2.1
      (path Gx Gy L μy τ x0 y0 ξ t).2.2) (path Gx Gy L μy τ x0 y0 ξ t).2.1 -
      c • gy (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1) 2
      (Measure.infinitePi fun _ : ℕ => p) := by
    refine memLp_of_bound (hU2m.comp hXm).aestronglyMeasurable
      (c0 := |τ / 16| * (‖gy 0 0‖ + L * ‖xhat f L 0 0‖) + |c| * ‖gy 0 0‖)
      [fun ξ => (2 * |τ / 16| * L + |c| * L) * ‖(path Gx Gy L μy τ x0 y0 ξ t).2.1‖,
        fun ξ => 2 * |τ / 16| * L * ‖(path Gx Gy L μy τ x0 y0 ξ t).2.2‖,
        fun ξ => |c| * L * ‖(path Gx Gy L μy τ x0 y0 ξ (t + 1)).1‖] ?_ ?_
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact hy.norm.const_mul _
      · exact hz.norm.const_mul _
      · exact hx'.norm.const_mul _
    · intro ξ
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      set x' := (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1
      set y := (path Gx Gy L μy τ x0 y0 ξ t).2.1
      set z := (path Gx Gy L μy τ x0 y0 ξ t).2.2
      have h1 := H.norm_gy_le (xhat f L y z) y
      have h2 := H.norm_xhat_le y z
      have h3 := H.norm_gy_le x' y
      have h4 : ‖(τ / 16) • gy (xhat f L y z) y - c • gy x' y‖ ≤
          |τ / 16| * ‖gy (xhat f L y z) y‖ + |c| * ‖gy x' y‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have a1 := abs_nonneg (τ / 16)
      have a2 := abs_nonneg c
      linarith [mul_le_mul_of_nonneg_left h1 a1, mul_le_mul_of_nonneg_left h2 (mul_nonneg a1 hL.le),
        mul_le_mul_of_nonneg_left h3 a2]
  have hi1 := integrable_inner_of_memLp hU1 he1
  have hi2 := integrable_inner_of_memLp hU2 he2
  have hdep0 : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < 2 * t → ξ i = ξ' i) →
      path Gx Gy L μy τ x0 y0 ξ t = path Gx Gy L μy τ x0 y0 ξ' t :=
    fun ξ ξ' h => path_congr Gx Gy L μy τ x0 y0 t ξ ξ' h
  have hdep1 : ∀ ξ ξ' : ℕ → Ω, (∀ i, i < 2 * t + 1 → ξ i = ξ' i) →
      (path Gx Gy L μy τ x0 y0 ξ t, (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1) =
        (path Gx Gy L μy τ x0 y0 ξ' t, (path Gx Gy L μy τ x0 y0 ξ' (t + 1)).1) := by
    intro ξ ξ' h
    rw [path_congr Gx Gy L μy τ x0 y0 t ξ ξ' (fun i hi => h i (by omega)),
      path_fst_congr Gx Gy L μy τ x0 y0 t ξ ξ' h]
  have z1 := integral_inner_prefix p (2 * t) (fun ξ => path Gx Gy L μy τ x0 y0 ξ t) (hp t) hdep0
    (fun s => xgrad gx L s.2.2 s.1 s.2.1) hU1m (fun s ω => Gx (s.1, s.2.1) ω)
    (ox.measurable.comp ((measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd))
    (fun s => gx s.1 s.2.1) (hgxc.measurable.comp (measurable_fst.prodMk measurable_snd.fst))
    (fun s => ox.integrable _) (fun s => ox.unbiased _) hi1
  have z2 := integral_inner_prefix p (2 * t + 1) _ hXm hdep1
    (fun w => (τ / 16) • gy (xhat f L w.1.2.1 w.1.2.2) w.1.2.1 - c • gy w.2 w.1.2.1) hU2m
    (fun w ω => Gy (w.2, w.1.2.1) ω)
    (oy.measurable.comp ((measurable_fst.snd.prodMk measurable_fst.fst.snd.fst).prodMk measurable_snd))
    (fun w => gy w.2 w.1.2.1) (hgyc.measurable.comp (measurable_snd.prodMk measurable_fst.snd.fst))
    (fun w => oy.integrable _) (fun w => oy.unbiased _) hi2
  have hfun : (fun ξ => martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t)
      (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (noise1 gx Gx Gy L μy τ x0 y0 ξ t)
      (noise2 gy Gx Gy L μy τ x0 y0 ξ t)) = fun ξ =>
      (τ - 3 * L * τ ^ 2) * ⟪xgrad gx L (path Gx Gy L μy τ x0 y0 ξ t).2.2
        (path Gx Gy L μy τ x0 y0 ξ t).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1,
        noise1 gx Gx Gy L μy τ x0 y0 ξ t⟫ +
      ⟪(τ / 16) • gy (xhat f L (path Gx Gy L μy τ x0 y0 ξ t).2.1
        (path Gx Gy L μy τ x0 y0 ξ t).2.2) (path Gx Gy L μy τ x0 y0 ξ t).2.1 -
        c • gy (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1,
        noise2 gy Gx Gy L μy τ x0 y0 ξ t⟫ := rfl
  rw [hfun]
  refine ⟨(hi1.const_mul _).add hi2, ?_⟩
  rw [integral_add (hi1.const_mul _) hi2, integral_const_mul]
  have z1' : ∫ ξ, ⟪xgrad gx L (path Gx Gy L μy τ x0 y0 ξ t).2.2 (path Gx Gy L μy τ x0 y0 ξ t).1
      (path Gx Gy L μy τ x0 y0 ξ t).2.1, noise1 gx Gx Gy L μy τ x0 y0 ξ t⟫
      ∂(Measure.infinitePi fun _ : ℕ => p) = 0 := z1
  have z2' : ∫ ξ, ⟪(τ / 16) • gy (xhat f L (path Gx Gy L μy τ x0 y0 ξ t).2.1
      (path Gx Gy L μy τ x0 y0 ξ t).2.2) (path Gx Gy L μy τ x0 y0 ξ t).2.1 -
      c • gy (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1,
      noise2 gy Gx Gy L μy τ x0 y0 ξ t⟫ ∂(Measure.infinitePi fun _ : ℕ => p) = 0 := z2
  rw [z1', z2']
  ring

omit [ProperSpace E] [IsProbabilityMeasure p] in
lemma measurable_gap (H : Hyp f gx gy L μx μy)
    (ox : IsUnbiasedOracle p (fun w : E × F => gx w.1 w.2) Gx σ)
    (oy : IsUnbiasedOracle p (fun w : E × F => gy w.1 w.2) Gy σ) (τ : ℝ) (x0 : E) (y0 : F)
    (t : ℕ) : Measurable fun ξ : ℕ → Ω => gapValue f (path Gx Gy L μy τ x0 y0 ξ t) := by
  have hp := measurable_path ox.measurable oy.measurable L μy τ x0 y0 t
  have h1 : Measurable fun ξ : ℕ → Ω => maxValue f (path Gx Gy L μy τ x0 y0 ξ t).1 :=
    H.lsc_maxValue.measurable.comp hp.fst
  have h2 : Measurable fun ξ : ℕ → Ω => f (path Gx Gy L μy τ x0 y0 ξ t).1
      (path Gx Gy L μy τ x0 y0 ξ t).2.1 := H.continuous_f.measurable.comp (hp.fst.prodMk hp.snd.fst)
  exact (h1.sub measurable_const).add (h1.sub h2)

omit [ProperSpace E] in
lemma gap_integrable (H : Hyp f gx gy L μx μy)
    (ox : IsUnbiasedOracle p (fun w : E × F => gx w.1 w.2) Gx σ)
    (oy : IsUnbiasedOracle p (fun w : E × F => gy w.1 w.2) Gy σ) (τ : ℝ) (x0 : E) (y0 : F)
    (t : ℕ) :
    Integrable (fun ξ => gapValue f (path Gx Gy L μy τ x0 y0 ξ t))
      (Measure.infinitePi fun _ : ℕ => p) := by
  have hL := H.hL
  have hp := measurable_path ox.measurable oy.measurable L μy τ x0 y0 t
  obtain ⟨hx, hy, _⟩ := memLp_path H ox oy τ x0 y0 t
  have hxy : Measurable fun ξ : ℕ → Ω => ((path Gx Gy L μy τ x0 y0 ξ t).1,
      (path Gx Gy L μy τ x0 y0 ξ t).2.1) := hp.fst.prodMk hp.snd.fst
  have hgx : MemLp (fun ξ => gx (path Gx Gy L μy τ x0 y0 ξ t).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1) 2
      (Measure.infinitePi fun _ : ℕ => p) := by
    refine memLp_of_bound (H.continuous_gx.measurable.comp hxy).aestronglyMeasurable
      (c0 := ‖gx 0 0‖) [fun ξ => L * ‖(path Gx Gy L μy τ x0 y0 ξ t).1‖,
        fun ξ => L * ‖(path Gx Gy L μy τ x0 y0 ξ t).2.1‖] ?_ ?_
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hx.norm.const_mul _
      · exact hy.norm.const_mul _
    · intro ξ
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have := H.norm_gx_le (path Gx Gy L μy τ x0 y0 ξ t).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1
      linarith
  have hgy : MemLp (fun ξ => gy (path Gx Gy L μy τ x0 y0 ξ t).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1) 2
      (Measure.infinitePi fun _ : ℕ => p) := by
    refine memLp_of_bound (H.continuous_gy.measurable.comp hxy).aestronglyMeasurable
      (c0 := ‖gy 0 0‖) [fun ξ => L * ‖(path Gx Gy L μy τ x0 y0 ξ t).1‖,
        fun ξ => L * ‖(path Gx Gy L μy τ x0 y0 ξ t).2.1‖] ?_ ?_
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hx.norm.const_mul _
      · exact hy.norm.const_mul _
    · intro ξ
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have := H.norm_gy_le (path Gx Gy L μy τ x0 y0 ξ t).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1
      linarith
  have i1 := (memLp_two_iff_integrable_sq_norm hgx.aestronglyMeasurable).1 hgx
  have i2 := (memLp_two_iff_integrable_sq_norm hgy.aestronglyMeasurable).1 hgy
  have hm := measurable_gap H ox oy τ x0 y0 t
  have hb : Integrable (fun ξ =>
      1 / μy * ‖gy (path Gx Gy L μy τ x0 y0 ξ t).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1‖ ^ 2 +
      1 / (2 * μx) * ‖gx (path Gx Gy L μy τ x0 y0 ξ t).1 (path Gx Gy L μy τ x0 y0 ξ t).2.1‖ ^ 2)
      (Measure.infinitePi fun _ : ℕ => p) := (i2.const_mul (1 / μy)).add (i1.const_mul (1 / (2 * μx)))
  refine hb.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  set x := (path Gx Gy L μy τ x0 y0 ξ t).1
  set y := (path Gx Gy L μy τ x0 y0 ξ t).2.1
  have a1 := H.maxValue_sub_le x y
  have a2 := H.sub_minimax_le x y
  have a3 := H.le_maxValue x y
  have a4 := H.minimax_le x
  have e1 : ‖gy x y‖ ^ 2 / (2 * μy) = 1 / 2 * (1 / μy * ‖gy x y‖ ^ 2) := by
    field_simp
  have e2 : ‖gx x y‖ ^ 2 / (2 * μx) = 1 / (2 * μx) * ‖gx x y‖ ^ 2 := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (by simp only [gapValue]; linarith)]
  simp only [gapValue]
  have : 0 ≤ 1 / μy * ‖gy x y‖ ^ 2 := by have := H.hμy; positivity
  linarith

lemma expected_window (H : Hyp f gx gy L μx μy)
    (ox : IsUnbiasedOracle p (fun w : E × F => gx w.1 w.2) Gx σ)
    (oy : IsUnbiasedOracle p (fun w : E × F => gy w.1 w.2) Gy σ) {τ : ℝ} (hτ : 0 < τ)
    (hs : 3 * L * τ ≤ 1) (x0 : E) (y0 : F) (n : ℕ) :
    Integrable (fun ξ => ∑ t ∈ Ico n (n + (n + 1)), gapValue f (path Gx Gy L μy τ x0 y0 ξ t))
      (Measure.infinitePi fun _ : ℕ => p) ∧
    ∫ ξ, ∑ t ∈ Ico n (n + (n + 1)), gapValue f (path Gx Gy L μy τ x0 y0 ξ t)
        ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      2 * (2 ^ 18 * L / (μx * μy * τ)) *
        ((1 - 1 / (2 ^ 18 * L / (μx * μy * τ))) ^ n * (statePotential f L (x0, y0, x0) - minimaxValue f) +
          ∑ t ∈ range n, (1 - 1 / (2 ^ 18 * L / (μx * μy * τ))) ^ (n - 1 - t) *
            (9 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx / (2 ^ 18 * L / (μx * μy * τ)) +
              2 * L * τ ^ 2 * (σ ^ 2 + σ ^ 2)) +
          (n + 1) * (2 * L * τ ^ 2 * (σ ^ 2 + σ ^ 2))) +
      (n + 1) * (12 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx) := by
  have hL := H.hL
  have hμx := H.hμx
  have hμy := H.hμy
  set C := 2 ^ 18 * L / (μx * μy * τ) with hCdef
  have hm : 0 < μx * μy * τ := by positivity
  have hC0 : 0 < C := by positivity
  have hC1 : 1 ≤ C := by
    rw [hCdef, le_div_iff₀ hm]
    have h1 : μx * μy * τ ≤ L * L * τ :=
      mul_le_mul_of_nonneg_right (mul_le_mul H.hμxL H.hμyL hμy.le hL.le) hτ.le
    have h2 := mul_le_mul_of_nonneg_left hs hL.le
    linarith
  have hρ0 : 0 ≤ 1 - 1 / C := by rw [sub_nonneg, div_le_one hC0]; exact hC1
  have hgap : Integrable (fun ξ => ∑ t ∈ Ico n (n + (n + 1)), gapValue f (path Gx Gy L μy τ x0 y0 ξ t))
      (Measure.infinitePi fun _ : ℕ => p) :=
    integrable_finsetSum _ fun t _ => gap_integrable H ox oy τ x0 y0 t
  refine ⟨hgap, ?_⟩
  have hN : ∀ t, Integrable (fun ξ => 9 * L ^ 2 * τ ^ 2 * ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 / μx)
      (Measure.infinitePi fun _ : ℕ => p) := fun t =>
    ((noise1_sq H ox oy μy τ x0 y0 t).1.const_mul _).div_const _
  have hns : ∀ t, Integrable (fun ξ => 2 * L * τ ^ 2 * (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
      ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2)) (Measure.infinitePi fun _ : ℕ => p) := fun t =>
    ((noise1_sq H ox oy μy τ x0 y0 t).1.add (noise2_sq H ox oy μy τ x0 y0 t).1).const_mul _
  have hNab : ∀ t, Integrable (fun ξ => 12 * L ^ 2 * τ ^ 2 * ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 / μx)
      (Measure.infinitePi fun _ : ℕ => p) := fun t =>
    ((noise1_sq H ox oy μy τ x0 y0 t).1.const_mul _).div_const _
  have hM := fun t => (martingale_props H ox oy τ x0 y0 t).1
  have hRi : Integrable (fun ξ => 2 * C * ((1 - 1 / C) ^ n * (statePotential f L (x0, y0, x0) - minimaxValue f) +
      ∑ t ∈ range n, (1 - 1 / C) ^ (n - 1 - t) *
        (9 * L ^ 2 * τ ^ 2 * ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 / μx / C +
          2 * L * τ ^ 2 * (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 + ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) -
          martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t) (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1
            (noise1 gx Gx Gy L μy τ x0 y0 ξ t) (noise2 gy Gx Gy L μy τ x0 y0 ξ t)) +
      ∑ t ∈ Ico n (n + (n + 1)), (2 * L * τ ^ 2 * (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
          ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2) -
        martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t) (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1
          (noise1 gx Gx Gy L μy τ x0 y0 ξ t) (noise2 gy Gx Gy L μy τ x0 y0 ξ t))) +
      ∑ t ∈ Ico n (n + (n + 1)), 12 * L ^ 2 * τ ^ 2 * ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 / μx)
      (Measure.infinitePi fun _ : ℕ => p) := by
    refine (((integrable_const _).add (integrable_finsetSum _ fun t _ => ?_)).add
      (integrable_finsetSum _ fun t _ => ?_)).const_mul _ |>.add
      (integrable_finsetSum _ fun t _ => hNab t)
    · exact ((((hN t).div_const C).add (hns t)).sub (hM t)).const_mul _
    · exact (hns t).sub (hM t)
  have hpath := fun ξ => H.window hτ hs (path Gx Gy L μy τ x0 y0 ξ)
    (noise1 gx Gx Gy L μy τ x0 y0 ξ) (noise2 gy Gx Gy L μy τ x0 y0 ξ)
    (path_rec gx gy Gx Gy L μy τ x0 y0 ξ) n
  have hmono := integral_mono hgap hRi hpath
  refine hmono.trans ?_
  have hrhs := integral_window_rhs (P := Measure.infinitePi fun _ : ℕ => p)
    (a := 2 * C) (b := statePotential f L (x0, y0, x0) - minimaxValue f) (ρ := 1 - 1 / C) (C := C)
    (bN := 9 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx) (bns := 2 * L * τ ^ 2 * (σ ^ 2 + σ ^ 2))
    (bNab := 12 * L ^ 2 * τ ^ 2 * σ ^ 2 / μx) n
    (fun t ξ => 9 * L ^ 2 * τ ^ 2 * ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 / μx)
    (fun t ξ => 2 * L * τ ^ 2 * (‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 +
      ‖noise2 gy Gx Gy L μy τ x0 y0 ξ t‖ ^ 2))
    (fun t ξ => martingale f gx gy L τ (path Gx Gy L μy τ x0 y0 ξ t) (path Gx Gy L μy τ x0 y0 ξ (t + 1)).1
      (noise1 gx Gx Gy L μy τ x0 y0 ξ t) (noise2 gy Gx Gy L μy τ x0 y0 ξ t))
    (fun t ξ => 12 * L ^ 2 * τ ^ 2 * ‖noise1 gx Gx Gy L μy τ x0 y0 ξ t‖ ^ 2 / μx)
    hN hns hM hNab ?_ ?_ (fun t => (martingale_props H ox oy τ x0 y0 t).2) ?_ (by linarith) hρ0 hC0
  · exact hrhs
  · intro t
    rw [integral_div, integral_const_mul]
    have := (noise1_sq H ox oy μy τ x0 y0 t).2
    have h9 : 0 ≤ 9 * L ^ 2 * τ ^ 2 := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this h9) hμx.le
  · intro t
    rw [integral_const_mul, integral_add (noise1_sq H ox oy μy τ x0 y0 t).1
      (noise2_sq H ox oy μy τ x0 y0 t).1]
    have h1 := (noise1_sq H ox oy μy τ x0 y0 t).2
    have h2 := (noise2_sq H ox oy μy τ x0 y0 t).2
    have h0 : 0 ≤ 2 * L * τ ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) h0
  · intro t
    rw [integral_div, integral_const_mul]
    have := (noise1_sq H ox oy μy τ x0 y0 t).2
    have h12 : 0 ≤ 12 * L ^ 2 * τ ^ 2 := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this h12) hμx.le

end Window

end OracleTemplate.TwoSidedPL
