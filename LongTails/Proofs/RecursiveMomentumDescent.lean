import LongTails.Proofs.RecursiveMomentumMoments

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.RecursiveMomentum

open OracleTemplate.NormalizedStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E} {L Lbar Γ Λ lower : ℝ}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

omit [IsProbabilityMeasure p] in
lemma AffineHyp.measurable_err (H : AffineHyp p F g L Lbar Γ Λ lower) (γ a : ℝ) (b0 : ℕ)
    (x0 : E) (j : ℕ) : Measurable (fun ξ : ℕ → Ω => momentumErr g F γ a b0 x0 ξ j) :=
  (measurable_momentumPair H.meas γ a b0 x0 j).snd.sub
    (H.grad_continuous.measurable.comp (measurable_momentumPair H.meas γ a b0 x0 j).fst)

omit [IsProbabilityMeasure p] in
lemma AffineHyp.measurable_gap (H : AffineHyp p F g L Lbar Γ Λ lower) (γ a : ℝ) (b0 : ℕ)
    (x0 : E) (j : ℕ) :
    Measurable (fun ξ : ℕ → Ω => F (momentumPair g γ a b0 x0 ξ j).1 - lower) :=
  (H.continuous.measurable.comp (measurable_momentumPair H.meas γ a b0 x0 j).fst).sub_const _

omit [IsProbabilityMeasure p] in
lemma AffineHyp.measurable_gradNorm (H : AffineHyp p F g L Lbar Γ Λ lower) (γ a : ℝ) (b0 : ℕ)
    (x0 : E) (j : ℕ) :
    Measurable (fun ξ : ℕ → Ω => ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖) :=
  (H.grad_continuous.measurable.comp (measurable_momentumPair H.meas γ a b0 x0 j).fst).norm

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma dir_sq_le (F : E → ℝ) (x d : E) :
    ‖d‖ ^ 2 ≤ 2 * ‖d - gradient F x‖ ^ 2 + 2 * ‖gradient F x‖ ^ 2 := by
  have h := sq_norm_add_le (d - gradient F x) (gradient F x)
  rwa [sub_add_cancel] at h

omit [IsProbabilityMeasure p] [BorelSpace E] [SecondCountableTopology E] in
lemma AffineHyp.path_descent (H : AffineHyp p F g L Lbar Γ Λ lower) {γ : ℝ} (hγ : 0 ≤ γ)
    (hγL : γ * L ≤ 1 / 2) (a : ℝ) (b0 : ℕ) (x0 : E) (j : ℕ) (ξ : ℕ → Ω) :
    F (momentumPair g γ a b0 x0 ξ (j + 1)).1 - lower ≤
      (F (momentumPair g γ a b0 x0 ξ j).1 - lower) -
        γ / 2 * ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ^ 2 -
        γ / 4 * ‖(momentumPair g γ a b0 x0 ξ j).2‖ ^ 2 +
        γ / 2 * ‖momentumErr g F γ a b0 x0 ξ j‖ ^ 2 := by
  have h := H.step_descent hγ hγL (momentumPair g γ a b0 x0 ξ j).1 (momentumPair g γ a b0 x0 ξ j).2
  rw [momentumPair_succ]
  simp only [momentumErr]
  linarith

theorem AffineHyp.integrable_all (H : AffineHyp p F g L Lbar Γ Λ lower) {γ a : ℝ} (hγ : 0 ≤ γ)
    (hγL : γ * L ≤ 1 / 2) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (b0 : ℕ) (x0 : E) :
    ∀ j, Integrable (fun ξ => ‖momentumErr g F γ a b0 x0 ξ j‖ ^ 2) P ∧
      Integrable (fun ξ => F (momentumPair g γ a b0 x0 ξ j).1 - lower) P ∧
      Integrable (fun ξ => ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ^ 2) P ∧
      Integrable (fun ξ => ‖(momentumPair g γ a b0 x0 ξ j).2‖ ^ 2) P
  | 0 => by
      obtain ⟨hb1, -⟩ := H.batch_moment (p := p) x0 b0
      have e0 : ∀ ξ : ℕ → Ω, momentumErr g F γ a b0 x0 ξ 0 = batchMean g x0 ξ b0 - gradient F x0 :=
        fun ξ => rfl
      have f0 : ∀ ξ : ℕ → Ω, F (momentumPair g γ a b0 x0 ξ 0).1 - lower = F x0 - lower :=
        fun _ => rfl
      have g0 : ∀ ξ : ℕ → Ω, ‖gradient F (momentumPair g γ a b0 x0 ξ 0).1‖ ^ 2 =
          ‖gradient F x0‖ ^ 2 := fun _ => rfl
      have d0 : ∀ ξ : ℕ → Ω, (momentumPair g γ a b0 x0 ξ 0).2 = batchMean g x0 ξ b0 :=
        fun _ => rfl
      simp_rw [e0, f0, g0, d0]
      refine ⟨hb1, integrable_const _, integrable_const _, ?_⟩
      refine Integrable.mono' ((hb1.const_mul 2).add (integrable_const (2 * ‖gradient F x0‖ ^ 2)))
        ((measurable_batchMean H.meas x0 b0).norm.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact dir_sq_le F x0 (batchMean g x0 ξ b0)
  | j + 1 => by
      obtain ⟨i1, i2, i3, i4⟩ := H.integrable_all hγ hγL ha0 ha1 b0 x0 j
      have hF1 : Integrable (fun ξ => F (momentumPair g γ a b0 x0 ξ (j + 1)).1 - lower) P := by
        refine Integrable.mono' (i2.add (i1.const_mul (γ / 2)))
          (H.measurable_gap γ a b0 x0 (j + 1)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ξ => ?_)
        have h := H.path_descent hγ hγL a b0 x0 j ξ
        have hl := H.low (momentumPair g γ a b0 x0 ξ (j + 1)).1
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        have : 0 ≤ γ / 2 * ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ^ 2 := by positivity
        have : 0 ≤ γ / 4 * ‖(momentumPair g γ a b0 x0 ξ j).2‖ ^ 2 := by positivity
        simp only [Pi.add_apply]
        linarith
      have hG1 : Integrable (fun ξ => ‖gradient F (momentumPair g γ a b0 x0 ξ (j + 1)).1‖ ^ 2) P := by
        refine Integrable.mono' (hF1.const_mul (2 * L))
          ((H.measurable_gradNorm γ a b0 x0 (j + 1)).pow_const 2).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ξ => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact H.grad_sq_le _
      obtain ⟨he1, -⟩ := H.momentum_moment hγ ha0 ha1 b0 x0 j i1 hG1 i4
      refine ⟨he1, hF1, hG1, ?_⟩
      refine Integrable.mono' ((he1.const_mul 2).add (hG1.const_mul 2))
        ((measurable_momentumPair H.meas γ a b0 x0 (j + 1)).snd.norm.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ξ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact dir_sq_le F _ _

lemma AffineHyp.mean_descent (H : AffineHyp p F g L Lbar Γ Λ lower) {γ a : ℝ} (hγ : 0 ≤ γ)
    (hγL : γ * L ≤ 1 / 2) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (b0 : ℕ) (x0 : E) (j : ℕ) :
    ∫ ξ, (F (momentumPair g γ a b0 x0 ξ (j + 1)).1 - lower) ∂P ≤
      ∫ ξ, (F (momentumPair g γ a b0 x0 ξ j).1 - lower) ∂P -
        γ / 2 * ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ^ 2 ∂P -
        γ / 4 * ∫ ξ, ‖(momentumPair g γ a b0 x0 ξ j).2‖ ^ 2 ∂P +
        γ / 2 * ∫ ξ, ‖momentumErr g F γ a b0 x0 ξ j‖ ^ 2 ∂P := by
  obtain ⟨i1, i2, i3, i4⟩ := H.integrable_all hγ hγL ha0 ha1 b0 x0 j
  obtain ⟨-, i2', -, -⟩ := H.integrable_all hγ hγL ha0 ha1 b0 x0 (j + 1)
  have hA : Integrable (fun ξ => (F (momentumPair g γ a b0 x0 ξ j).1 - lower) -
      γ / 2 * ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ^ 2) P := i2.sub (i3.const_mul (γ / 2))
  have hB : Integrable (fun ξ => (F (momentumPair g γ a b0 x0 ξ j).1 - lower) -
      γ / 2 * ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ^ 2 -
      γ / 4 * ‖(momentumPair g γ a b0 x0 ξ j).2‖ ^ 2) P := hA.sub (i4.const_mul (γ / 4))
  have hC : Integrable (fun ξ => (F (momentumPair g γ a b0 x0 ξ j).1 - lower) -
      γ / 2 * ‖gradient F (momentumPair g γ a b0 x0 ξ j).1‖ ^ 2 -
      γ / 4 * ‖(momentumPair g γ a b0 x0 ξ j).2‖ ^ 2 +
      γ / 2 * ‖momentumErr g F γ a b0 x0 ξ j‖ ^ 2) P := hB.add (i1.const_mul (γ / 2))
  have hm := integral_mono i2' hC (H.path_descent hγ hγL a b0 x0 j)
  rw [integral_add hB (i1.const_mul _), integral_sub hA (i4.const_mul _),
    integral_sub i2 (i3.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul] at hm
  exact hm

theorem AffineHyp.lyapunov (H : AffineHyp p F g L Lbar Γ Λ lower) {γ a : ℝ} (hγ : 0 ≤ γ)
    (hγL : γ * L ≤ 1 / 2) (ha0 : 0 < a) (ha1 : a ≤ 1) (haΓ : a * Γ ^ 2 ≤ 1 / 8)
    (hc : 4 * (Lbar ^ 2 + L ^ 2) * γ ^ 2 ≤ a / 4) (b0 : ℕ) (x0 : E) :
    ∀ n : ℕ, γ / 4 * ∑ s ∈ Finset.range n,
        ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ s).1‖ ^ 2 ∂P +
      ∫ ξ, (F (momentumPair g γ a b0 x0 ξ n).1 - lower) ∂P +
      γ / a * ∫ ξ, ‖momentumErr g F γ a b0 x0 ξ n‖ ^ 2 ∂P -
      2 * a * γ * Γ ^ 2 * ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ n).1‖ ^ 2 ∂P ≤
    ∫ ξ, (F (momentumPair g γ a b0 x0 ξ 0).1 - lower) ∂P +
      γ / a * ∫ ξ, ‖momentumErr g F γ a b0 x0 ξ 0‖ ^ 2 ∂P -
      2 * a * γ * Γ ^ 2 * ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ 0).1‖ ^ 2 ∂P +
      2 * a * γ * Λ ^ 2 * n
  | 0 => by simp
  | n + 1 => by
      have ih := H.lyapunov hγ hγL ha0 ha1 haΓ hc b0 x0 n
      obtain ⟨i1, i2, i3, i4⟩ := H.integrable_all hγ hγL ha0.le ha1 b0 x0 n
      obtain ⟨-, -, i3', -⟩ := H.integrable_all hγ hγL ha0.le ha1 b0 x0 (n + 1)
      have hd := H.mean_descent hγ hγL ha0.le ha1 b0 x0 n
      obtain ⟨-, hr⟩ := H.momentum_moment hγ ha0.le ha1 b0 x0 n i1 i3' i4
      set un := ∫ ξ, ‖momentumErr g F γ a b0 x0 ξ n‖ ^ 2 ∂P
      set un1 := ∫ ξ, ‖momentumErr g F γ a b0 x0 ξ (n + 1)‖ ^ 2 ∂P
      set Gn := ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ n).1‖ ^ 2 ∂P
      set Gn1 := ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ (n + 1)).1‖ ^ 2 ∂P
      set Dn := ∫ ξ, ‖(momentumPair g γ a b0 x0 ξ n).2‖ ^ 2 ∂P
      have hun : 0 ≤ un := integral_nonneg fun _ => by positivity
      have hGn : 0 ≤ Gn := integral_nonneg fun _ => by positivity
      have hDn : 0 ≤ Dn := integral_nonneg fun _ => by positivity
      have hq : 0 ≤ γ / a := div_nonneg hγ ha0.le
      have h1 := mul_le_mul_of_nonneg_left hr hq
      have e1 : γ / a * ((1 - a) ^ 2 * un + (2 * a ^ 2 * (Γ ^ 2 * Gn1 + Λ ^ 2) +
          4 * (Lbar ^ 2 + L ^ 2) * γ ^ 2 * Dn)) =
          γ / a * (1 - a) ^ 2 * un + 2 * a * γ * Γ ^ 2 * Gn1 + 2 * a * γ * Λ ^ 2 +
            γ / a * (4 * (Lbar ^ 2 + L ^ 2) * γ ^ 2) * Dn := by
        field_simp
        ring
      rw [e1] at h1
      have e2 : γ / a * (1 - a) ^ 2 ≤ γ / a - γ := by
        have : (1 - a) ^ 2 ≤ 1 - a := by nlinarith
        have h := mul_le_mul_of_nonneg_left this hq
        have : γ / a * (1 - a) = γ / a - γ := by field_simp
        linarith
      have e3 : γ / a * (4 * (Lbar ^ 2 + L ^ 2) * γ ^ 2) ≤ γ / 4 := by
        have h := mul_le_mul_of_nonneg_left hc hq
        have : γ / a * (a / 4) = γ / 4 := by field_simp
        linarith
      have e4 : 2 * a * γ * Γ ^ 2 ≤ γ / 4 := by nlinarith
      have h5 := mul_le_mul_of_nonneg_right e2 hun
      have h6 := mul_le_mul_of_nonneg_right e3 hDn
      have h7 := mul_le_mul_of_nonneg_right e4 hGn
      rw [Finset.sum_range_succ]
      push_cast
      nlinarith

theorem AffineHyp.grad_sq_sum (H : AffineHyp p F g L Lbar Γ Λ lower) {γ a : ℝ} (hγ : 0 < γ)
    (hγL : γ * L ≤ 1 / 2) (ha0 : 0 < a) (ha1 : a ≤ 1) (haΓ : a * Γ ^ 2 ≤ 1 / 8)
    (hc : 4 * (Lbar ^ 2 + L ^ 2) * γ ^ 2 ≤ a / 4) (b0 : ℕ) (x0 : E) (N : ℕ) :
    ∑ s ∈ Finset.range N, ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ s).1‖ ^ 2 ∂P ≤
      4 / γ * (F x0 - lower) + 4 / a * ∫ ξ, ‖batchMean g x0 ξ b0 - gradient F x0‖ ^ 2 ∂P +
        8 * a * Λ ^ 2 * N := by
  have h := H.lyapunov hγ.le hγL ha0 ha1 haΓ hc b0 x0 N
  obtain ⟨i1, i2, i3, -⟩ := H.integrable_all hγ.le hγL ha0.le ha1 b0 x0 N
  have hGN : ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ N).1‖ ^ 2 ∂P ≤
      2 * L * ∫ ξ, (F (momentumPair g γ a b0 x0 ξ N).1 - lower) ∂P := by
    rw [← integral_const_mul]
    exact integral_mono i3 (i2.const_mul _) fun ξ => H.grad_sq_le _
  have huN : 0 ≤ ∫ ξ, ‖momentumErr g F γ a b0 x0 ξ N‖ ^ 2 ∂P :=
    integral_nonneg fun _ => by positivity
  have hφN : 0 ≤ ∫ ξ, (F (momentumPair g γ a b0 x0 ξ N).1 - lower) ∂P :=
    integral_nonneg fun ξ => sub_nonneg.mpr (H.low _)
  have f0 : ∫ ξ, (F (momentumPair g γ a b0 x0 ξ 0).1 - lower) ∂P = F x0 - lower := by
    have : ∀ ξ : ℕ → Ω, F (momentumPair g γ a b0 x0 ξ 0).1 - lower = F x0 - lower :=
      fun _ => rfl
    simp [this]
  have g0 : 0 ≤ ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ 0).1‖ ^ 2 ∂P :=
    integral_nonneg fun _ => by positivity
  have e0 : ∫ ξ, ‖momentumErr g F γ a b0 x0 ξ 0‖ ^ 2 ∂P =
      ∫ ξ, ‖batchMean g x0 ξ b0 - gradient F x0‖ ^ 2 ∂P := rfl
  rw [f0, e0] at h
  have hκ : 2 * a * γ * Γ ^ 2 * (2 * L) ≤ 1 := by
    have := mul_le_mul haΓ hγL (mul_nonneg hγ.le H.L_pos.le) (by norm_num)
    nlinarith
  have hκ0 : 0 ≤ 2 * a * γ * Γ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha0.le) hγ.le) (sq_nonneg Γ)
  have hk := mul_le_mul_of_nonneg_left hGN hκ0
  have hk2 : 2 * a * γ * Γ ^ 2 * (2 * L * ∫ ξ, (F (momentumPair g γ a b0 x0 ξ N).1 - lower) ∂P) ≤
      ∫ ξ, (F (momentumPair g γ a b0 x0 ξ N).1 - lower) ∂P := by
    rw [← mul_assoc]
    nlinarith
  have hq : 0 ≤ γ / a := div_nonneg hγ.le ha0.le
  have hsum : γ / 4 * ∑ s ∈ Finset.range N,
      ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ s).1‖ ^ 2 ∂P ≤
      (F x0 - lower) + γ / a * ∫ ξ, ‖batchMean g x0 ξ b0 - gradient F x0‖ ^ 2 ∂P +
        2 * a * γ * Λ ^ 2 * N := by
    nlinarith [mul_nonneg hq huN, mul_nonneg hκ0 g0]
  have e : 4 / γ * (γ / 4 * ∑ s ∈ Finset.range N,
      ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ s).1‖ ^ 2 ∂P) =
      ∑ s ∈ Finset.range N, ∫ ξ, ‖gradient F (momentumPair g γ a b0 x0 ξ s).1‖ ^ 2 ∂P := by
    field_simp
  have e' : 4 / γ * ((F x0 - lower) + γ / a * ∫ ξ, ‖batchMean g x0 ξ b0 - gradient F x0‖ ^ 2 ∂P +
      2 * a * γ * Λ ^ 2 * N) = 4 / γ * (F x0 - lower) +
        4 / a * ∫ ξ, ‖batchMean g x0 ξ b0 - gradient F x0‖ ^ 2 ∂P + 8 * a * Λ ^ 2 * N := by
    field_simp
    ring
  have h4 := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ 4 / γ)
  rw [e, e'] at h4
  exact h4

end OracleTemplate.RecursiveMomentum
