import LongTails.Proofs.NormalizedStormMoments

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.NormalizedStorm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {F : E → ℝ} {g : E → Ω → E} {L A C lower : ℝ}

local notation "P" => Measure.infinitePi fun _ : ℕ => p

omit [IsProbabilityMeasure p] in
lemma Hyp.measurable_err (H : Hyp p F g L A C lower) (η a : ℝ) (b0 : ℕ) (x0 : E) (j : ℕ) :
    Measurable (fun ξ : ℕ → Ω => stormErr g F η a b0 x0 ξ j) :=
  (measurable_stormPair H.meas η a b0 x0 j).snd.sub
    (H.grad_continuous.measurable.comp (measurable_stormPair H.meas η a b0 x0 j).fst)

omit [IsProbabilityMeasure p] in
lemma Hyp.measurable_value (H : Hyp p F g L A C lower) (η a : ℝ) (b0 : ℕ) (x0 : E) (j : ℕ) :
    Measurable (fun ξ : ℕ → Ω => F (stormPair g η a b0 x0 ξ j).1 - lower) :=
  (H.continuous.measurable.comp (measurable_stormPair H.meas η a b0 x0 j).fst).sub_const _

lemma Hyp.integrable_err_norm (H : Hyp p F g L A C lower) (η a : ℝ) (b0 : ℕ) (x0 : E) (j : ℕ)
    (h2 : Integrable (fun ξ => ‖stormErr g F η a b0 x0 ξ j‖ ^ 2) P) :
    Integrable (fun ξ => ‖stormErr g F η a b0 x0 ξ j‖) P :=
  (((TwoSidedPL.memLp_two_iff_sq (H.measurable_err η a b0 x0 j).aestronglyMeasurable).mpr h2).integrable
    one_le_two).norm

omit [BorelSpace E] [SecondCountableTopology E] [IsProbabilityMeasure p] in
lemma Hyp.path_descent (H : Hyp p F g L A C lower) {η : ℝ} (hη : 0 ≤ η) (a : ℝ) (b0 : ℕ) (x0 : E)
    (j : ℕ) (ξ : ℕ → Ω) :
    η * ‖gradient F (stormPair g η a b0 x0 ξ j).1‖ + (F (stormPair g η a b0 x0 ξ (j + 1)).1 - lower) ≤
      (F (stormPair g η a b0 x0 ξ j).1 - lower) + 2 * η * ‖stormErr g F η a b0 x0 ξ j‖ +
        L / 2 * η ^ 2 := by
  have h := H.descent hη (stormPair g η a b0 x0 ξ j).1 (stormPair g η a b0 x0 ξ j).2
  rw [stormPair_succ]
  simp only [stormErr]
  linarith

theorem Hyp.moments_all (H : Hyp p F g L A C lower) {η a : ℝ} (hη : 0 ≤ η) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) {b0 : ℕ} (hb0 : 1 ≤ b0) (x0 : E) {V Dmax : ℝ} {T : ℕ}
    (h0 : (2 * A * (F x0 - lower) + C) / b0 ≤ V)
    (hV : (1 - a) ^ 2 * V + (2 * a ^ 2 * (2 * A * Dmax + C) + 8 * L ^ 2 * η ^ 2) ≤ V)
    (hD : (F x0 - lower) + ((T : ℝ) + 1) * (2 * η * Real.sqrt V + L / 2 * η ^ 2) ≤ Dmax) :
    ∀ j, j ≤ T + 1 →
      Integrable (fun ξ => ‖stormErr g F η a b0 x0 ξ j‖ ^ 2) P ∧
      ∫ ξ, ‖stormErr g F η a b0 x0 ξ j‖ ^ 2 ∂P ≤ V ∧
      Integrable (fun ξ => F (stormPair g η a b0 x0 ξ j).1 - lower) P ∧
      ∫ ξ, (F (stormPair g η a b0 x0 ξ j).1 - lower) ∂P ≤
        (F x0 - lower) + (j : ℝ) * (2 * η * Real.sqrt V + L / 2 * η ^ 2)
  | 0, _ => by
      obtain ⟨hb1, hb2⟩ := H.batch_moment (p := p) x0 b0
      have hb : (0 : ℝ) < b0 := by exact_mod_cast hb0
      have e0 : ∀ ξ : ℕ → Ω, stormErr g F η a b0 x0 ξ 0 = batchMean g x0 ξ b0 - gradient F x0 :=
        fun ξ => rfl
      have f0 : ∀ ξ : ℕ → Ω, F (stormPair g η a b0 x0 ξ 0).1 - lower = F x0 - lower := fun ξ => rfl
      simp_rw [e0, f0]
      refine ⟨hb1, ?_, integrable_const _, ?_⟩
      · rw [div_le_iff₀ hb] at h0
        have : (∫ ξ, ‖batchMean g x0 ξ b0 - gradient F x0‖ ^ 2 ∂P) * b0 ≤ V * b0 := by
          nlinarith [hb2]
        exact le_of_mul_le_mul_right this hb
      · simp
  | j + 1, hj => by
      obtain ⟨i1, i2, i3, i4⟩ := H.moments_all hη ha0 ha1 hb0 x0 h0 hV hD j (by omega)
      have hen := H.integrable_err_norm η a b0 x0 j i1
      have hc : 0 ≤ 2 * η * Real.sqrt V + L / 2 * η ^ 2 := by
        have := H.L_pos; positivity
      have hdom : Integrable (fun ξ => (F (stormPair g η a b0 x0 ξ j).1 - lower) +
          2 * η * ‖stormErr g F η a b0 x0 ξ j‖ + L / 2 * η ^ 2) P :=
        (i3.add (hen.const_mul _)).add (integrable_const _)
      have hFi : Integrable (fun ξ => F (stormPair g η a b0 x0 ξ (j + 1)).1 - lower) P := by
        refine Integrable.mono' hdom (H.measurable_value η a b0 x0 (j + 1)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ξ => ?_)
        have h := H.path_descent hη a b0 x0 j ξ
        have := H.low (stormPair g η a b0 x0 ξ (j + 1)).1
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        nlinarith [norm_nonneg (gradient F (stormPair g η a b0 x0 ξ j).1)]
      have hjen : ∫ ξ, ‖stormErr g F η a b0 x0 ξ j‖ ∂P ≤ Real.sqrt V :=
        (integral_norm_le_sqrt (H.measurable_err η a b0 x0 j).aestronglyMeasurable i1).trans
          (Real.sqrt_le_sqrt i2)
      have hDj : ∫ ξ, (F (stormPair g η a b0 x0 ξ (j + 1)).1 - lower) ∂P ≤
          (F x0 - lower) + ((j + 1 : ℕ) : ℝ) * (2 * η * Real.sqrt V + L / 2 * η ^ 2) := by
        have hm : ∫ ξ, (F (stormPair g η a b0 x0 ξ (j + 1)).1 - lower) ∂P ≤
            ∫ ξ, ((F (stormPair g η a b0 x0 ξ j).1 - lower) +
              2 * η * ‖stormErr g F η a b0 x0 ξ j‖ + L / 2 * η ^ 2) ∂P := by
          refine integral_mono hFi hdom fun ξ => ?_
          have h := H.path_descent hη a b0 x0 j ξ
          nlinarith [norm_nonneg (gradient F (stormPair g η a b0 x0 ξ j).1)]
        have hl : ∫ ξ, ((F (stormPair g η a b0 x0 ξ j).1 - lower) +
              2 * η * ‖stormErr g F η a b0 x0 ξ j‖ + L / 2 * η ^ 2) ∂P =
            ∫ ξ, (F (stormPair g η a b0 x0 ξ j).1 - lower) ∂P +
              2 * η * ∫ ξ, ‖stormErr g F η a b0 x0 ξ j‖ ∂P + L / 2 * η ^ 2 := by
          have hx : Integrable (fun ξ => 2 * η * ‖stormErr g F η a b0 x0 ξ j‖) P := hen.const_mul _
          have hy : Integrable (fun ξ => (F (stormPair g η a b0 x0 ξ j).1 - lower) +
              2 * η * ‖stormErr g F η a b0 x0 ξ j‖) P := i3.add hx
          rw [integral_add hy (integrable_const _), integral_add i3 hx, integral_const_mul,
            integral_const]
          simp
        rw [hl] at hm
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hjen (by positivity : (0 : ℝ) ≤ 2 * η)]
      have hDmax : ∫ ξ, (F (stormPair g η a b0 x0 ξ (j + 1)).1 - lower) ∂P ≤ Dmax := by
        refine hDj.trans (le_trans ?_ hD)
        have hjT : ((j + 1 : ℕ) : ℝ) ≤ (T : ℝ) + 1 := by exact_mod_cast hj
        nlinarith
      obtain ⟨s1, s2⟩ := H.storm_moment hη ha0 ha1 b0 x0 j i1 hFi
      refine ⟨s1, ?_, hFi, hDj⟩
      refine s2.trans (le_trans ?_ hV)
      have hA := H.A_nn
      have h1a : 0 ≤ (1 - a) ^ 2 := sq_nonneg _
      have : 2 * a ^ 2 * (2 * A * ∫ ξ, (F (stormPair g η a b0 x0 ξ (j + 1)).1 - lower) ∂P + C) ≤
          2 * a ^ 2 * (2 * A * Dmax + C) := by
        gcongr
      nlinarith [mul_le_mul_of_nonneg_left i2 h1a]

theorem Hyp.grad_sum (H : Hyp p F g L A C lower) {η a : ℝ} (hη : 0 < η) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) {b0 : ℕ} (hb0 : 1 ≤ b0) (x0 : E) {V Dmax : ℝ} {T : ℕ}
    (h0 : (2 * A * (F x0 - lower) + C) / b0 ≤ V)
    (hV : (1 - a) ^ 2 * V + (2 * a ^ 2 * (2 * A * Dmax + C) + 8 * L ^ 2 * η ^ 2) ≤ V)
    (hD : (F x0 - lower) + ((T : ℝ) + 1) * (2 * η * Real.sqrt V + L / 2 * η ^ 2) ≤ Dmax) :
    (∀ j, j ≤ T → Integrable (fun ξ => ‖gradient F (stormPair g η a b0 x0 ξ j).1‖) P) ∧
    η * ∑ j ∈ Finset.range (T + 1), ∫ ξ, ‖gradient F (stormPair g η a b0 x0 ξ j).1‖ ∂P ≤
      (F x0 - lower) + ((T : ℝ) + 1) * (2 * η * Real.sqrt V + L / 2 * η ^ 2) := by
  have hm := H.moments_all hη.le ha0 ha1 hb0 x0 h0 hV hD
  have hgi : ∀ j, j ≤ T → Integrable (fun ξ => ‖gradient F (stormPair g η a b0 x0 ξ j).1‖) P := by
    intro j hj
    obtain ⟨i1, -, i3, -⟩ := hm j (by omega)
    have hen := H.integrable_err_norm η a b0 x0 j i1
    have hdom : Integrable (fun ξ => ((F (stormPair g η a b0 x0 ξ j).1 - lower) +
        2 * η * ‖stormErr g F η a b0 x0 ξ j‖ + L / 2 * η ^ 2) / η) P :=
      ((i3.add (hen.const_mul _)).add (integrable_const _)).div_const _
    refine Integrable.mono' hdom
      ((H.grad_continuous.measurable.comp (measurable_stormPair H.meas η a b0 x0 j).fst).norm.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ξ => ?_)
    have h := H.path_descent hη.le a b0 x0 j ξ
    have := H.low (stormPair g η a b0 x0 ξ (j + 1)).1
    rw [norm_norm, le_div_iff₀ hη, mul_comm]
    linarith
  refine ⟨hgi, ?_⟩
  have key : ∀ n, n ≤ T + 1 →
      η * ∑ j ∈ Finset.range n, ∫ ξ, ‖gradient F (stormPair g η a b0 x0 ξ j).1‖ ∂P +
        ∫ ξ, (F (stormPair g η a b0 x0 ξ n).1 - lower) ∂P ≤
      (F x0 - lower) + (n : ℝ) * (2 * η * Real.sqrt V + L / 2 * η ^ 2) := by
    intro n
    induction n with
    | zero =>
        intro _
        have : ∀ ξ : ℕ → Ω, F (stormPair g η a b0 x0 ξ 0).1 - lower = F x0 - lower := fun _ => rfl
        simp [this]
    | succ n ih =>
        intro hn
        have ih' := ih (by omega)
        obtain ⟨i1, i2, i3, -⟩ := hm n (by omega)
        obtain ⟨-, -, i3', -⟩ := hm (n + 1) hn
        have hen := H.integrable_err_norm η a b0 x0 n i1
        have hgn := hgi n (by omega)
        have hjen : ∫ ξ, ‖stormErr g F η a b0 x0 ξ n‖ ∂P ≤ Real.sqrt V :=
          (integral_norm_le_sqrt (H.measurable_err η a b0 x0 n).aestronglyMeasurable i1).trans
            (Real.sqrt_le_sqrt i2)
        have hl : Integrable (fun ξ => η * ‖gradient F (stormPair g η a b0 x0 ξ n).1‖ +
            (F (stormPair g η a b0 x0 ξ (n + 1)).1 - lower)) P := (hgn.const_mul _).add i3'
        have hr : Integrable (fun ξ => (F (stormPair g η a b0 x0 ξ n).1 - lower) +
            2 * η * ‖stormErr g F η a b0 x0 ξ n‖ + L / 2 * η ^ 2) P :=
          (i3.add (hen.const_mul _)).add (integrable_const _)
        have hmono := integral_mono hl hr (H.path_descent hη.le a b0 x0 n)
        have hx : Integrable (fun ξ => 2 * η * ‖stormErr g F η a b0 x0 ξ n‖) P := hen.const_mul _
        have hy : Integrable (fun ξ => (F (stormPair g η a b0 x0 ξ n).1 - lower) +
            2 * η * ‖stormErr g F η a b0 x0 ξ n‖) P := i3.add hx
        have hgn' : Integrable (fun ξ => η * ‖gradient F (stormPair g η a b0 x0 ξ n).1‖) P :=
          hgn.const_mul _
        rw [integral_add hgn' i3', integral_add hy (integrable_const _), integral_add i3 hx,
          integral_const_mul, integral_const_mul, integral_const] at hmono
        simp only [probReal_univ, one_smul] at hmono
        rw [Finset.sum_range_succ, mul_add]
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hjen (by positivity : (0 : ℝ) ≤ 2 * η)]
  have h := key (T + 1) le_rfl
  obtain ⟨-, -, -, -⟩ := hm (T + 1) le_rfl
  have hnn : 0 ≤ ∫ ξ, (F (stormPair g η a b0 x0 ξ (T + 1)).1 - lower) ∂P :=
    integral_nonneg fun ξ => sub_nonneg.mpr (H.low _)
  push_cast at h
  linarith

end OracleTemplate.NormalizedStorm
