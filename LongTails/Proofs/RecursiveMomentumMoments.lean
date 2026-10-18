import LongTails.Proofs.RecursiveMomentumTrajectory
import LongTails.Proofs.NormalizedStormMoments

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.RecursiveMomentum

open OracleTemplate.NormalizedStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]

structure AffineHyp (p : Measure Ω) (F : E → ℝ) (g : E → Ω → E) (L Lbar Γ Λ lower : ℝ) :
    Prop where
  grad : ∀ x, HasGradientAt F (gradient F x) x
  lip : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖
  low : ∀ x, lower ≤ F x
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = gradient F x
  var_int : ∀ x, Integrable (fun ω => ‖g x ω - gradient F x‖ ^ 2) p
  var : ∀ x, ∫ ω, ‖g x ω - gradient F x‖ ^ 2 ∂p ≤ Γ ^ 2 * ‖gradient F x‖ ^ 2 + Λ ^ 2
  diff_int : ∀ x y, Integrable (fun ω => ‖g x ω - g y ω‖ ^ 2) p
  mss : ∀ x y, ∫ ω, ‖g x ω - g y ω‖ ^ 2 ∂p ≤ Lbar ^ 2 * ‖x - y‖ ^ 2
  L_pos : 0 < L

section Basic

variable {p : Measure Ω} {F : E → ℝ} {g : E → Ω → E} {L Lbar Γ Λ lower : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
lemma AffineHyp.grad_continuous (H : AffineHyp p F g L Lbar Γ Λ lower) :
    Continuous (gradient F) := by
  have hl : LipschitzWith ⟨L, H.L_pos.le⟩ (gradient F) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [dist_eq_norm]
      exact H.lip x y
  exact hl.continuous

omit [BorelSpace E] [SecondCountableTopology E] in
lemma AffineHyp.continuous (H : AffineHyp p F g L Lbar Γ Λ lower) : Continuous F :=
  continuous_iff_continuousAt.mpr fun x => (H.grad x).differentiableAt.continuousAt

omit [BorelSpace E] [SecondCountableTopology E] in
lemma AffineHyp.grad_sq_le (H : AffineHyp p F g L Lbar Γ Λ lower) (x : E) :
    ‖gradient F x‖ ^ 2 ≤ 2 * L * (F x - lower) := by
  have h := Gradient.descent H.L_pos H.grad H.lip x
  have hl := H.low (x - (1 / L) • gradient F x)
  have h1 : ‖gradient F x‖ ^ 2 / (2 * L) ≤ F x - lower := by linarith
  have hL : (0 : ℝ) < 2 * L := by linarith [H.L_pos]
  rw [div_le_iff₀ hL] at h1
  linarith

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma momentumStep_norm {γ : ℝ} (hγ : 0 ≤ γ) (x d : E) :
    ‖momentumStep γ x d - x‖ = γ * ‖d‖ := by
  unfold momentumStep
  rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ]

omit [BorelSpace E] [SecondCountableTopology E] in
lemma AffineHyp.step_descent (H : AffineHyp p F g L Lbar Γ Λ lower) {γ : ℝ} (hγ : 0 ≤ γ)
    (hγL : γ * L ≤ 1 / 2) (x d : E) :
    F (momentumStep γ x d) ≤ F x - γ / 2 * ‖gradient F x‖ ^ 2 - γ / 4 * ‖d‖ ^ 2 +
      γ / 2 * ‖d - gradient F x‖ ^ 2 := by
  have h := Gradient.smooth_upper_bound (oracle := gradient F) H.grad H.lip x (momentumStep γ x d)
  have hs : momentumStep γ x d - x = -(γ • d) := by
    simp [momentumStep]
  rw [hs, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hγ] at h
  have hpol : ‖d - gradient F x‖ ^ 2 =
      ‖d‖ ^ 2 - 2 * ⟪gradient F x, d⟫ + ‖gradient F x‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  have hq : L / 2 * (γ * ‖d‖) ^ 2 ≤ γ / 4 * ‖d‖ ^ 2 := by
    have h0 : 0 ≤ γ * ‖d‖ ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hγL h0
    nlinarith
  nlinarith

end Basic

section Moments

variable {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E}
  {L Lbar Γ Λ lower : ℝ}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

lemma AffineHyp.batch_moment (H : AffineHyp p F g L Lbar Γ Λ lower) (x0 : E) :
    ∀ j : ℕ, Integrable (fun ξ : ℕ → Ω => ‖batchMean g x0 ξ j - gradient F x0‖ ^ 2) P ∧
      (j : ℝ) * ∫ ξ, ‖batchMean g x0 ξ j - gradient F x0‖ ^ 2 ∂P ≤
        Γ ^ 2 * ‖gradient F x0‖ ^ 2 + Λ ^ 2
  | 0 => by
      refine ⟨by simp only [batchMean]; exact integrable_const _, ?_⟩
      simp only [Nat.cast_zero, zero_mul]
      positivity
  | j + 1 => by
      obtain ⟨ih1, ih2⟩ := H.batch_moment x0 j
      set s0 := Γ ^ 2 * ‖gradient F x0‖ ^ 2 + Λ ^ 2
      set G := gradient F x0
      set c : ℝ := 1 - 1 / ((j : ℝ) + 1)
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hS : Measurable (fun ξ : ℕ → Ω => batchMean g x0 ξ j) :=
        measurable_batchMean H.meas x0 j
      have hW : Measurable (Function.uncurry fun (_ : E) (ω : Ω) =>
          (1 / ((j : ℝ) + 1)) • (g x0 ω - G)) :=
        ((H.meas.comp (measurable_const.prodMk measurable_snd)).sub measurable_const).const_smul _
      have hWi : ∀ _y : E, Integrable (fun ω => (1 / ((j : ℝ) + 1)) • (g x0 ω - G)) p :=
        fun _ => ((H.int x0).sub (integrable_const _)).smul _
      have hW0 : ∀ _y : E, ∫ ω, (1 / ((j : ℝ) + 1)) • (g x0 ω - G) ∂p = 0 := by
        intro _
        rw [integral_smul, integral_sub (H.int x0) (integrable_const _), H.mean, integral_const]
        simp [G]
      have hW2 : ∀ _y : E,
          Integrable (fun ω => ‖(1 / ((j : ℝ) + 1)) • (g x0 ω - G)‖ ^ 2) p := by
        intro _
        simp_rw [norm_smul, mul_pow]
        exact (H.var_int x0).const_mul _
      have hw : ∀ _y : E, ∫ ω, ‖(1 / ((j : ℝ) + 1)) • (g x0 ω - G)‖ ^ 2 ∂p ≤
          (1 / ((j : ℝ) + 1)) ^ 2 * s0 := by
        intro _
        simp_rw [norm_smul, mul_pow]
        rw [integral_const_mul, Real.norm_eq_abs, sq_abs]
        exact mul_le_mul_of_nonneg_left (H.var x0) (by positivity)
      have hstep := fresh_step_sq p j (fun ξ : ℕ → Ω => batchMean g x0 ξ j) hS
        (fun ξ ξ' h => batchMean_congr g x0 j h) (fun m => m - G)
        (measurable_id.sub measurable_const)
        (fun _ ω => (1 / ((j : ℝ) + 1)) • (g x0 ω - G)) hW hWi hW0 hW2
        (fun _ => (1 / ((j : ℝ) + 1)) ^ 2 * s0) hw (integrable_const _) ih1 c
      have hid : ∀ ξ : ℕ → Ω, batchMean g x0 ξ (j + 1) - G =
          c • (batchMean g x0 ξ j - G) + (1 / ((j : ℝ) + 1)) • (g x0 (ξ j) - G) := by
        intro ξ
        simp only [batchMean, c]
        module
      simp_rw [hid]
      refine ⟨hstep.1, ?_⟩
      have hb := hstep.2
      rw [integral_const] at hb
      simp only [probReal_univ, one_smul] at hb
      have hc : c = (j : ℝ) / ((j : ℝ) + 1) := by
        simp only [c]; field_simp; ring
      push_cast
      have hs0 : 0 ≤ s0 := by positivity
      have hI : 0 ≤ ∫ ξ, ‖batchMean g x0 ξ j - G‖ ^ 2 ∂P :=
        integral_nonneg fun _ => by positivity
      calc ((j : ℝ) + 1) * ∫ ξ, ‖c • (batchMean g x0 ξ j - G) +
            (1 / ((j : ℝ) + 1)) • (g x0 (ξ j) - G)‖ ^ 2 ∂P
          ≤ ((j : ℝ) + 1) * (c ^ 2 * ∫ ξ, ‖batchMean g x0 ξ j - G‖ ^ 2 ∂P +
            (1 / ((j : ℝ) + 1)) ^ 2 * s0) := mul_le_mul_of_nonneg_left hb hj.le
        _ = ((j : ℝ) / ((j : ℝ) + 1)) * ((j : ℝ) * ∫ ξ, ‖batchMean g x0 ξ j - G‖ ^ 2 ∂P) +
            s0 / ((j : ℝ) + 1) := by rw [hc]; field_simp
        _ ≤ ((j : ℝ) / ((j : ℝ) + 1)) * s0 + s0 / ((j : ℝ) + 1) := by
            gcongr
        _ = s0 := by field_simp

noncomputable def momentumErr (g : E → Ω → E) (F : E → ℝ) (γ a : ℝ) (b0 : ℕ) (x0 : E)
    (ξ : ℕ → Ω) (j : ℕ) : E :=
  (momentumPair g γ a b0 x0 ξ j).2 - gradient F (momentumPair g γ a b0 x0 ξ j).1

lemma AffineHyp.momentum_moment (H : AffineHyp p F g L Lbar Γ Λ lower) {γ a : ℝ} (hγ : 0 ≤ γ)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (b0 : ℕ) (x0 : E) (j : ℕ)
    (hU2 : Integrable (fun ξ => ‖momentumErr g F γ a b0 x0 ξ j‖ ^ 2) P)
    (hG : Integrable (fun ξ => ‖gradient F (momentumPair g γ a b0 x0 ξ (j + 1)).1‖ ^ 2) P)
    (hD : Integrable (fun ξ => ‖(momentumPair g γ a b0 x0 ξ j).2‖ ^ 2) P) :
    Integrable (fun ξ => ‖momentumErr g F γ a b0 x0 ξ (j + 1)‖ ^ 2) P ∧
      ∫ ξ, ‖momentumErr g F γ a b0 x0 ξ (j + 1)‖ ^ 2 ∂P ≤
        (1 - a) ^ 2 * ∫ ξ, ‖momentumErr g F γ a b0 x0 ξ j‖ ^ 2 ∂P +
          (2 * a ^ 2 * (Γ ^ 2 * ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ (j + 1)).1‖ ^ 2 ∂P +
            Λ ^ 2) + 4 * (Lbar ^ 2 + L ^ 2) * γ ^ 2 *
              ∫ ξ, ‖(momentumPair g γ a b0 x0 ξ j).2‖ ^ 2 ∂P) := by
  set S := fun ξ : ℕ → Ω => momentumPair g γ a b0 x0 ξ j
  have hS : Measurable S := measurable_momentumPair H.meas γ a b0 x0 j
  have hGc := H.grad_continuous
  let x' : E × E → E := fun z => momentumStep γ z.1 z.2
  have hx' : Measurable x' := measurable_momentumStep γ
  let W : E × E → Ω → E := fun z ω =>
    (g (x' z) ω - gradient F (x' z)) - (1 - a) • (g z.1 ω - gradient F z.1)
  have hW : Measurable (Function.uncurry W) := by
    have h1 : Measurable fun w : (E × E) × Ω => g (x' w.1) w.2 :=
      H.meas.comp ((hx'.comp measurable_fst).prodMk measurable_snd)
    have h2 : Measurable fun w : (E × E) × Ω => g w.1.1 w.2 :=
      H.meas.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h3 : Measurable fun w : (E × E) × Ω => gradient F (x' w.1) :=
      hGc.measurable.comp (hx'.comp measurable_fst)
    have h4 : Measurable fun w : (E × E) × Ω => gradient F w.1.1 :=
      hGc.measurable.comp (measurable_fst.comp measurable_fst)
    exact (h1.sub h3).sub ((h2.sub h4).const_smul _)
  have hWi : ∀ z, Integrable (W z) p := fun z =>
    ((H.int (x' z)).sub (integrable_const _)).sub (((H.int z.1).sub (integrable_const _)).smul _)
  have hW0 : ∀ z, ∫ ω, W z ω ∂p = 0 := by
    intro z
    have i1 : Integrable (fun ω => g (x' z) ω - gradient F (x' z)) p :=
      (H.int _).sub (integrable_const _)
    have i2 : Integrable (fun ω => g z.1 ω - gradient F z.1) p :=
      (H.int _).sub (integrable_const _)
    have e1 : ∫ ω, (g (x' z) ω - gradient F (x' z)) ∂p = 0 := by
      rw [integral_sub (H.int _) (integrable_const _), H.mean, integral_const]; simp
    have e2 : ∫ ω, (g z.1 ω - gradient F z.1) ∂p = 0 := by
      rw [integral_sub (H.int _) (integrable_const _), H.mean, integral_const]; simp
    have i3 : Integrable (fun ω => (1 - a) • (g z.1 ω - gradient F z.1)) p := i2.smul _
    simp only [W]
    rw [integral_sub i1 i3, integral_smul, e1, e2]
    simp
  have hpt : ∀ z ω, ‖W z ω‖ ^ 2 ≤ 2 * a ^ 2 * ‖g (x' z) ω - gradient F (x' z)‖ ^ 2 +
      4 * ‖g (x' z) ω - g z.1 ω‖ ^ 2 + 4 * L ^ 2 * γ ^ 2 * ‖z.2‖ ^ 2 := by
    intro z ω
    have hd := momentumStep_norm hγ z.1 z.2
    have hlip : ‖gradient F (x' z) - gradient F z.1‖ ≤ L * (γ * ‖z.2‖) := by
      have := H.lip (x' z) z.1
      rw [hd] at this
      exact this
    have hsplit : W z ω = a • (g (x' z) ω - gradient F (x' z)) +
        (1 - a) • ((g (x' z) ω - g z.1 ω) - (gradient F (x' z) - gradient F z.1)) := by
      simp only [W]; module
    have h1 := sq_norm_add_le (a • (g (x' z) ω - gradient F (x' z)))
      ((1 - a) • ((g (x' z) ω - g z.1 ω) - (gradient F (x' z) - gradient F z.1)))
    have h2 := sq_norm_add_le (g (x' z) ω - g z.1 ω) (-(gradient F (x' z) - gradient F z.1))
    rw [← sub_eq_add_neg, norm_neg] at h2
    rw [hsplit]
    rw [norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
      sq_abs] at h1
    have h3 : (1 - a) ^ 2 ≤ 1 := by nlinarith
    have h4 : ‖gradient F (x' z) - gradient F z.1‖ ^ 2 ≤ L ^ 2 * γ ^ 2 * ‖z.2‖ ^ 2 := by
      have := norm_nonneg (gradient F (x' z) - gradient F z.1)
      have : 0 ≤ L * (γ * ‖z.2‖) := mul_nonneg H.L_pos.le (by positivity)
      nlinarith
    have h5 : 0 ≤ ‖(g (x' z) ω - g z.1 ω) - (gradient F (x' z) - gradient F z.1)‖ ^ 2 := by
      positivity
    nlinarith
  have hB : ∀ z, Integrable (fun ω => 2 * a ^ 2 * ‖g (x' z) ω - gradient F (x' z)‖ ^ 2 +
      4 * ‖g (x' z) ω - g z.1 ω‖ ^ 2 + 4 * L ^ 2 * γ ^ 2 * ‖z.2‖ ^ 2) p := fun z =>
    (((H.var_int _).const_mul _).add ((H.diff_int _ _).const_mul _)).add (integrable_const _)
  have hW2 : ∀ z, Integrable (fun ω => ‖W z ω‖ ^ 2) p := by
    intro z
    refine Integrable.mono' (hB z) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((hW.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpt z ω
  let w : E × E → ℝ := fun z => 2 * a ^ 2 * (Γ ^ 2 * ‖gradient F (x' z)‖ ^ 2 + Λ ^ 2) +
    4 * (Lbar ^ 2 + L ^ 2) * γ ^ 2 * ‖z.2‖ ^ 2
  have hw : ∀ z, ∫ ω, ‖W z ω‖ ^ 2 ∂p ≤ w z := by
    intro z
    have hd := momentumStep_norm hγ z.1 z.2
    calc ∫ ω, ‖W z ω‖ ^ 2 ∂p ≤ ∫ ω, (2 * a ^ 2 * ‖g (x' z) ω - gradient F (x' z)‖ ^ 2 +
          4 * ‖g (x' z) ω - g z.1 ω‖ ^ 2 + 4 * L ^ 2 * γ ^ 2 * ‖z.2‖ ^ 2) ∂p :=
          integral_mono (hW2 z) (hB z) (hpt z)
      _ = 2 * a ^ 2 * ∫ ω, ‖g (x' z) ω - gradient F (x' z)‖ ^ 2 ∂p +
          4 * ∫ ω, ‖g (x' z) ω - g z.1 ω‖ ^ 2 ∂p + 4 * L ^ 2 * γ ^ 2 * ‖z.2‖ ^ 2 := by
          have i1 : Integrable (fun ω => 2 * a ^ 2 * ‖g (x' z) ω - gradient F (x' z)‖ ^ 2) p :=
            (H.var_int (x' z)).const_mul _
          have i2 : Integrable (fun ω => 4 * ‖g (x' z) ω - g z.1 ω‖ ^ 2) p :=
            (H.diff_int (x' z) z.1).const_mul _
          have i12 : Integrable (fun ω => 2 * a ^ 2 * ‖g (x' z) ω - gradient F (x' z)‖ ^ 2 +
              4 * ‖g (x' z) ω - g z.1 ω‖ ^ 2) p := i1.add i2
          rw [integral_add i12 (integrable_const _), integral_add i1 i2, integral_const_mul,
            integral_const_mul, integral_const]
          simp
      _ ≤ 2 * a ^ 2 * (Γ ^ 2 * ‖gradient F (x' z)‖ ^ 2 + Λ ^ 2) +
          4 * (Lbar ^ 2 * (γ * ‖z.2‖) ^ 2) + 4 * L ^ 2 * γ ^ 2 * ‖z.2‖ ^ 2 := by
          have hm := H.mss (x' z) z.1
          rw [hd] at hm
          gcongr
          exact H.var _
      _ = w z := by simp only [w]; ring
  have hwi : Integrable (fun ξ => w (S ξ)) P := by
    simp only [w, S, x']
    exact ((((hG.const_mul (Γ ^ 2)).add (integrable_const _)).const_mul _).add
      (hD.const_mul _))
  have hstep := fresh_step_sq p (b0 + j) S hS
    (fun ξ ξ' h => momentumPair_congr g γ a b0 x0 j h) (fun z => z.2 - gradient F z.1)
    (measurable_snd.sub (hGc.measurable.comp measurable_fst)) W hW hWi hW0 hW2 w hw hwi hU2
    (1 - a)
  have hid : ∀ ξ : ℕ → Ω, momentumErr g F γ a b0 x0 ξ (j + 1) =
      (1 - a) • ((S ξ).2 - gradient F (S ξ).1) + W (S ξ) (ξ (b0 + j)) := by
    intro ξ
    simp only [momentumErr, momentumPair_succ, W, x', S]
    module
  simp_rw [hid]
  refine ⟨hstep.1, hstep.2.trans_eq ?_⟩
  congr 1
  have i1 : Integrable (fun ξ => Γ ^ 2 * ‖gradient F (x' (S ξ))‖ ^ 2 + Λ ^ 2) P :=
    (hG.const_mul _).add (integrable_const _)
  have i2 : Integrable (fun ξ => 2 * a ^ 2 * (Γ ^ 2 * ‖gradient F (x' (S ξ))‖ ^ 2 + Λ ^ 2)) P :=
    i1.const_mul _
  have i3 : Integrable (fun ξ => 4 * (Lbar ^ 2 + L ^ 2) * γ ^ 2 * ‖(S ξ).2‖ ^ 2) P :=
    hD.const_mul _
  change ∫ ξ, (2 * a ^ 2 * (Γ ^ 2 * ‖gradient F (x' (S ξ))‖ ^ 2 + Λ ^ 2) +
      4 * (Lbar ^ 2 + L ^ 2) * γ ^ 2 * ‖(S ξ).2‖ ^ 2) ∂P = _
  have hG' : Integrable (fun ξ => Γ ^ 2 * ‖gradient F (x' (S ξ))‖ ^ 2) P := hG.const_mul _
  rw [integral_add i2 i3, integral_const_mul, integral_const_mul,
    integral_add hG' (integrable_const _), integral_const_mul, integral_const]
  simp [momentumPair_succ, S, x']

end Moments

end OracleTemplate.RecursiveMomentum
