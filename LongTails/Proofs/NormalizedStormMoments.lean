import LongTails.Proofs.NormalizedStormTrajectory
import LongTails.Proofs.NormalizedStormOrthogonality
import LongTails.Proofs.GdConvex
import Mathlib.Probability.Moments.Variance

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.NormalizedStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]

structure Hyp (p : Measure Ω) (F : E → ℝ) (g : E → Ω → E) (L A C lower : ℝ) : Prop where
  grad : ∀ x, HasGradientAt F (gradient F x) x
  lip : ∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖
  meas : Measurable (Function.uncurry g)
  int : ∀ x, Integrable (g x) p
  mean : ∀ x, ∫ ω, g x ω ∂p = gradient F x
  var_int : ∀ x, Integrable (fun ω => ‖g x ω - gradient F x‖ ^ 2) p
  diff_int : ∀ x y, Integrable (fun ω => ‖g x ω - g y ω‖ ^ 2) p
  mss : ∀ x y, ∫ ω, ‖g x ω - g y ω‖ ^ 2 ∂p ≤ L ^ 2 * ‖x - y‖ ^ 2
  low : ∀ x, lower ≤ F x
  abc : ∀ x, ∫ ω, ‖g x ω - gradient F x‖ ^ 2 ∂p ≤ 2 * A * (F x - lower) + C
  L_pos : 0 < L
  A_nn : 0 ≤ A
  C_nn : 0 ≤ C

section Basic

variable {p : Measure Ω} {F : E → ℝ} {g : E → Ω → E} {L A C lower : ℝ}

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.grad_continuous (H : Hyp p F g L A C lower) : Continuous (gradient F) := by
  have hl : LipschitzWith ⟨L, H.L_pos.le⟩ (gradient F) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [dist_eq_norm]
      exact H.lip x y
  exact hl.continuous

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.continuous (H : Hyp p F g L A C lower) : Continuous F :=
  continuous_iff_continuousAt.mpr fun x => (H.grad x).differentiableAt.continuousAt

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma stormStep_dist {η : ℝ} (hη : 0 ≤ η) (x d : E) : ‖stormStep η x d - x‖ ≤ η := by
  unfold stormStep
  rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_div, abs_norm,
    abs_of_nonneg hη]
  by_cases hd : d = 0
  · simp [hd, hη]
  · have hn : 0 < ‖d‖ := norm_pos_iff.mpr hd
    rw [div_mul_cancel₀ _ hn.ne']

omit [BorelSpace E] [SecondCountableTopology E] in
lemma Hyp.descent (H : Hyp p F g L A C lower) {η : ℝ} (hη : 0 ≤ η) (x d : E) :
    F (stormStep η x d) ≤ F x - η * ‖gradient F x‖ + 2 * η * ‖d - gradient F x‖ +
      L / 2 * η ^ 2 := by
  have h := Gradient.smooth_upper_bound (oracle := gradient F) H.grad H.lip x (stormStep η x d)
  have hdist := stormStep_dist hη x d
  have hsq : L / 2 * ‖stormStep η x d - x‖ ^ 2 ≤ L / 2 * η ^ 2 := by
    have := H.L_pos
    gcongr
  set G := gradient F x
  by_cases hd : d = 0
  · have hx : stormStep η x d = x := by simp [stormStep, hd]
    rw [hx]
    simp only [hd, zero_sub, norm_neg]
    have := H.L_pos
    nlinarith [norm_nonneg G]
  · have hn : 0 < ‖d‖ := norm_pos_iff.mpr hd
    have hstep : stormStep η x d - x = -((η / ‖d‖) • d) := by
      simp [stormStep]
    have hin : ⟪G, stormStep η x d - x⟫ = -((η / ‖d‖) * ⟪G, d⟫) := by
      rw [hstep, inner_neg_right, inner_smul_right]
    have hGd : ⟪G, d⟫ = ‖d‖ ^ 2 - ⟪d - G, d⟫ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm]
      ring
    have hcs : ⟪d - G, d⟫ ≤ ‖d - G‖ * ‖d‖ := real_inner_le_norm _ _
    have htri : ‖G‖ ≤ ‖d‖ + ‖d - G‖ := by
      calc ‖G‖ = ‖d - (d - G)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖d‖ + ‖d - G‖ := norm_sub_le _ _
    have hkey : η * ‖G‖ - 2 * η * ‖d - G‖ ≤ (η / ‖d‖) * ⟪G, d⟫ := by
      rw [hGd]
      have h1 : (η / ‖d‖) * (‖d‖ ^ 2 - ⟪d - G, d⟫) ≥ (η / ‖d‖) * (‖d‖ ^ 2 - ‖d - G‖ * ‖d‖) := by
        apply mul_le_mul_of_nonneg_left _ (div_nonneg hη hn.le)
        linarith
      have h2 : (η / ‖d‖) * (‖d‖ ^ 2 - ‖d - G‖ * ‖d‖) = η * ‖d‖ - η * ‖d - G‖ := by
        field_simp
      nlinarith [norm_nonneg (d - G)]
    linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma sq_norm_add_le (u v : E) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := norm_add_le u v
  nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg (u + v), sq_nonneg (‖u‖ - ‖v‖)]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma integral_norm_le_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {f : α → E} (hf : AEStronglyMeasurable f μ) (h2 : Integrable (fun a => ‖f a‖ ^ 2) μ) :
    ∫ a, ‖f a‖ ∂μ ≤ Real.sqrt (∫ a, ‖f a‖ ^ 2 ∂μ) := by
  have hL : MemLp (fun a => ‖f a‖) 2 μ := by
    have := (TwoSidedPL.memLp_two_iff_sq hf).mpr h2
    exact this.norm
  have hv := variance_nonneg (fun a => ‖f a‖) μ
  rw [variance_eq_sub hL] at hv
  have hm : 0 ≤ ∫ a, ‖f a‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
  apply Real.le_sqrt_of_sq_le
  have e1 : μ[(fun a => ‖f a‖) ^ 2] = ∫ a, ‖f a‖ ^ 2 ∂μ := by
    congr 1
  have e2 : μ[fun a => ‖f a‖] = ∫ a, ‖f a‖ ∂μ := rfl
  rw [e1, e2] at hv
  linarith

end Basic

section Moments

variable {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E} {L A C lower : ℝ}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

lemma Hyp.batch_moment (H : Hyp p F g L A C lower) (x0 : E) :
    ∀ j : ℕ, Integrable (fun ξ : ℕ → Ω => ‖batchMean g x0 ξ j - gradient F x0‖ ^ 2) P ∧
      (j : ℝ) * ∫ ξ, ‖batchMean g x0 ξ j - gradient F x0‖ ^ 2 ∂P ≤ 2 * A * (F x0 - lower) + C
  | 0 => by
      refine ⟨by simp only [batchMean]; exact integrable_const _, ?_⟩
      have := H.A_nn; have := H.C_nn; have := H.low x0
      simp only [Nat.cast_zero, zero_mul]
      nlinarith
  | j + 1 => by
      obtain ⟨ih1, ih2⟩ := H.batch_moment x0 j
      set s0 := 2 * A * (F x0 - lower) + C
      set G := gradient F x0
      set c : ℝ := 1 - 1 / ((j : ℝ) + 1)
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hS : Measurable (fun ξ : ℕ → Ω => batchMean g x0 ξ j) := measurable_batchMean H.meas x0 j
      have hW : Measurable (Function.uncurry fun (_ : E) (ω : Ω) => (1 / ((j : ℝ) + 1)) • (g x0 ω - G)) :=
        ((H.meas.comp (measurable_const.prodMk measurable_snd)).sub measurable_const).const_smul _
      have hWi : ∀ _y : E, Integrable (fun ω => (1 / ((j : ℝ) + 1)) • (g x0 ω - G)) p :=
        fun _ => ((H.int x0).sub (integrable_const _)).smul _
      have hW0 : ∀ _y : E, ∫ ω, (1 / ((j : ℝ) + 1)) • (g x0 ω - G) ∂p = 0 := by
        intro _
        rw [integral_smul, integral_sub (H.int x0) (integrable_const _), H.mean, integral_const]
        simp [G]
      have hW2 : ∀ _y : E, Integrable (fun ω => ‖(1 / ((j : ℝ) + 1)) • (g x0 ω - G)‖ ^ 2) p := by
        intro _
        simp_rw [norm_smul, mul_pow]
        exact (H.var_int x0).const_mul _
      have hw : ∀ _y : E, ∫ ω, ‖(1 / ((j : ℝ) + 1)) • (g x0 ω - G)‖ ^ 2 ∂p ≤
          (1 / ((j : ℝ) + 1)) ^ 2 * s0 := by
        intro _
        simp_rw [norm_smul, mul_pow]
        rw [integral_const_mul, Real.norm_eq_abs, sq_abs]
        exact mul_le_mul_of_nonneg_left (H.abc x0) (by positivity)
      have hstep := fresh_step_sq p j (fun ξ : ℕ → Ω => batchMean g x0 ξ j) hS
        (fun ξ ξ' h => batchMean_congr g x0 j h) (fun m => m - G) (measurable_id.sub measurable_const)
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
      have hs0 : 0 ≤ s0 := by
        have := H.A_nn; have := H.C_nn; have := H.low x0
        simp only [s0]; nlinarith
      have hI : 0 ≤ ∫ ξ, ‖batchMean g x0 ξ j - G‖ ^ 2 ∂P := integral_nonneg fun _ => by positivity
      calc ((j : ℝ) + 1) * ∫ ξ, ‖c • (batchMean g x0 ξ j - G) + (1 / ((j : ℝ) + 1)) • (g x0 (ξ j) - G)‖ ^ 2 ∂P
          ≤ ((j : ℝ) + 1) * (c ^ 2 * ∫ ξ, ‖batchMean g x0 ξ j - G‖ ^ 2 ∂P +
            (1 / ((j : ℝ) + 1)) ^ 2 * s0) := mul_le_mul_of_nonneg_left hb hj.le
        _ = ((j : ℝ) / ((j : ℝ) + 1)) * ((j : ℝ) * ∫ ξ, ‖batchMean g x0 ξ j - G‖ ^ 2 ∂P) +
            s0 / ((j : ℝ) + 1) := by rw [hc]; field_simp
        _ ≤ ((j : ℝ) / ((j : ℝ) + 1)) * s0 + s0 / ((j : ℝ) + 1) := by
            gcongr
        _ = s0 := by field_simp

noncomputable def stormErr (g : E → Ω → E) (F : E → ℝ) (η a : ℝ) (b0 : ℕ) (x0 : E) (ξ : ℕ → Ω)
    (j : ℕ) : E :=
  (stormPair g η a b0 x0 ξ j).2 - gradient F (stormPair g η a b0 x0 ξ j).1

lemma Hyp.storm_moment (H : Hyp p F g L A C lower) {η a : ℝ} (hη : 0 ≤ η) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (b0 : ℕ) (x0 : E) (j : ℕ)
    (hU2 : Integrable (fun ξ => ‖stormErr g F η a b0 x0 ξ j‖ ^ 2) P)
    (hF : Integrable (fun ξ => F (stormPair g η a b0 x0 ξ (j + 1)).1 - lower) P) :
    Integrable (fun ξ => ‖stormErr g F η a b0 x0 ξ (j + 1)‖ ^ 2) P ∧
      ∫ ξ, ‖stormErr g F η a b0 x0 ξ (j + 1)‖ ^ 2 ∂P ≤
        (1 - a) ^ 2 * ∫ ξ, ‖stormErr g F η a b0 x0 ξ j‖ ^ 2 ∂P +
          (2 * a ^ 2 * (2 * A * ∫ ξ, (F (stormPair g η a b0 x0 ξ (j + 1)).1 - lower) ∂P + C) +
            8 * L ^ 2 * η ^ 2) := by
  set S := fun ξ : ℕ → Ω => stormPair g η a b0 x0 ξ j
  have hS : Measurable S := measurable_stormPair H.meas η a b0 x0 j
  have hGc := H.grad_continuous
  let x' : E × E → E := fun z => stormStep η z.1 z.2
  have hx' : Measurable x' := measurable_stormStep η
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
    have i2 : Integrable (fun ω => g z.1 ω - gradient F z.1) p := (H.int _).sub (integrable_const _)
    have e1 : ∫ ω, (g (x' z) ω - gradient F (x' z)) ∂p = 0 := by
      rw [integral_sub (H.int _) (integrable_const _), H.mean, integral_const]; simp
    have e2 : ∫ ω, (g z.1 ω - gradient F z.1) ∂p = 0 := by
      rw [integral_sub (H.int _) (integrable_const _), H.mean, integral_const]; simp
    have i3 : Integrable (fun ω => (1 - a) • (g z.1 ω - gradient F z.1)) p := i2.smul _
    simp only [W]
    rw [integral_sub i1 i3, integral_smul, e1, e2]
    simp
  have hpt : ∀ z ω, ‖W z ω‖ ^ 2 ≤ 2 * a ^ 2 * ‖g (x' z) ω - gradient F (x' z)‖ ^ 2 +
      4 * ‖g (x' z) ω - g z.1 ω‖ ^ 2 + 4 * L ^ 2 * η ^ 2 := by
    intro z ω
    have hd := stormStep_dist hη z.1 z.2
    have hlip : ‖gradient F (x' z) - gradient F z.1‖ ≤ L * η :=
      (H.lip _ _).trans (mul_le_mul_of_nonneg_left hd H.L_pos.le)
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
    have h4 : ‖gradient F (x' z) - gradient F z.1‖ ^ 2 ≤ L ^ 2 * η ^ 2 := by
      have := norm_nonneg (gradient F (x' z) - gradient F z.1)
      have : 0 ≤ L * η := mul_nonneg H.L_pos.le hη
      nlinarith
    have h5 : 0 ≤ ‖(g (x' z) ω - g z.1 ω) - (gradient F (x' z) - gradient F z.1)‖ ^ 2 := by positivity
    nlinarith
  have hB : ∀ z, Integrable (fun ω => 2 * a ^ 2 * ‖g (x' z) ω - gradient F (x' z)‖ ^ 2 +
      4 * ‖g (x' z) ω - g z.1 ω‖ ^ 2 + 4 * L ^ 2 * η ^ 2) p := fun z =>
    (((H.var_int _).const_mul _).add ((H.diff_int _ _).const_mul _)).add (integrable_const _)
  have hW2 : ∀ z, Integrable (fun ω => ‖W z ω‖ ^ 2) p := by
    intro z
    refine Integrable.mono' (hB z) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact ((hW.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hpt z ω
  let w : E × E → ℝ := fun z => 2 * a ^ 2 * (2 * A * (F (x' z) - lower) + C) + 8 * L ^ 2 * η ^ 2
  have hw : ∀ z, ∫ ω, ‖W z ω‖ ^ 2 ∂p ≤ w z := by
    intro z
    have hd := stormStep_dist hη z.1 z.2
    calc ∫ ω, ‖W z ω‖ ^ 2 ∂p ≤ ∫ ω, (2 * a ^ 2 * ‖g (x' z) ω - gradient F (x' z)‖ ^ 2 +
          4 * ‖g (x' z) ω - g z.1 ω‖ ^ 2 + 4 * L ^ 2 * η ^ 2) ∂p :=
          integral_mono (hW2 z) (hB z) (hpt z)
      _ = 2 * a ^ 2 * ∫ ω, ‖g (x' z) ω - gradient F (x' z)‖ ^ 2 ∂p +
          4 * ∫ ω, ‖g (x' z) ω - g z.1 ω‖ ^ 2 ∂p + 4 * L ^ 2 * η ^ 2 := by
          have i1 : Integrable (fun ω => 2 * a ^ 2 * ‖g (x' z) ω - gradient F (x' z)‖ ^ 2) p :=
            (H.var_int (x' z)).const_mul _
          have i2 : Integrable (fun ω => 4 * ‖g (x' z) ω - g z.1 ω‖ ^ 2) p :=
            (H.diff_int (x' z) z.1).const_mul _
          have i12 : Integrable (fun ω => 2 * a ^ 2 * ‖g (x' z) ω - gradient F (x' z)‖ ^ 2 +
              4 * ‖g (x' z) ω - g z.1 ω‖ ^ 2) p := i1.add i2
          rw [integral_add i12 (integrable_const _), integral_add i1 i2, integral_const_mul,
            integral_const_mul, integral_const]
          simp
      _ ≤ 2 * a ^ 2 * (2 * A * (F (x' z) - lower) + C) + 4 * (L ^ 2 * η ^ 2) + 4 * L ^ 2 * η ^ 2 := by
          have hm := H.mss (x' z) z.1
          have hdd : L ^ 2 * ‖x' z - z.1‖ ^ 2 ≤ L ^ 2 * η ^ 2 := by
            have := norm_nonneg (x' z - z.1)
            gcongr
          gcongr
          · exact H.abc _
          · exact hm.trans hdd
      _ = w z := by simp only [w]; ring
  have hwi : Integrable (fun ξ => w (S ξ)) P := by
    simp only [w, S, x']
    exact ((((hF.const_mul (2 * A)).add (integrable_const C)).const_mul (2 * a ^ 2)).add
      (integrable_const _))
  have hstep := fresh_step_sq p (b0 + j) S hS
    (fun ξ ξ' h => stormPair_congr g η a b0 x0 j h) (fun z => z.2 - gradient F z.1)
    (measurable_snd.sub (hGc.measurable.comp measurable_fst)) W hW hWi hW0 hW2 w hw hwi hU2 (1 - a)
  have hid : ∀ ξ : ℕ → Ω, stormErr g F η a b0 x0 ξ (j + 1) =
      (1 - a) • ((S ξ).2 - gradient F (S ξ).1) + W (S ξ) (ξ (b0 + j)) := by
    intro ξ
    simp only [stormErr, stormPair_succ, W, x', S]
    module
  simp_rw [hid]
  refine ⟨hstep.1, hstep.2.trans_eq ?_⟩
  congr 1
  have hF' : Integrable (fun ξ => F (stormStep η (S ξ).1 (S ξ).2) - lower) P := hF
  have i2 : Integrable (fun ξ => 2 * A * (F (stormStep η (S ξ).1 (S ξ).2) - lower)) P :=
    hF'.const_mul _
  have i2' : Integrable (fun ξ => 2 * A * (F (stormStep η (S ξ).1 (S ξ).2) - lower) + C) P :=
    i2.add (integrable_const C)
  have i1 : Integrable (fun ξ => 2 * a ^ 2 * (2 * A * (F (stormStep η (S ξ).1 (S ξ).2) - lower) + C)) P :=
    i2'.const_mul _
  change ∫ ξ, (2 * a ^ 2 * (2 * A * (F (stormStep η (S ξ).1 (S ξ).2) - lower) + C) +
      8 * L ^ 2 * η ^ 2) ∂P = _
  rw [integral_add i1 (integrable_const _), integral_const_mul, integral_add i2 (integrable_const C),
    integral_const_mul, integral_const, integral_const]
  simp [stormPair_succ, S]

end Moments

end OracleTemplate.NormalizedStorm
