import LongTails.Proofs.HighProbabilityPilot
import LongTails.Proofs.IidVectorConcentration
import LongTails.Proofs.RobustEnergyConcentration
import LongTails.Proofs.AdaptiveIID

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HighProbabilityEstimator

open LongTails.Algorithms.HighProbabilityStationarity OracleTemplate RobustGradient
open LongTails.Proofs.IidVectorConcentration

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def clipMean (B : ℝ) (c : E) (mc : ℕ) (w : Fin mc → E) : E :=
  c + (1 / (mc : ℝ)) • ∑ i : Fin mc, clip B (w i - c)

lemma clipEstimate_eq (B : ℝ) (K mp mc : ℕ) (v : Fin (mp + mc) → E) :
    clipEstimate B K mp mc v =
      clipMean B (gradedPilot B K (fun i : Fin mp => v (Fin.castAdd mc i)) 0) mc
        (fun i => v (Fin.natAdd mp i)) := rfl

lemma clipMean_sub_center {B : ℝ} (hB : 0 ≤ B) (c : E) {mc : ℕ} (hmc : 0 < mc)
    (w : Fin mc → E) : ‖clipMean B c mc w - c‖ ≤ B := by
  have he : clipMean B c mc w - c = (1 / (mc : ℝ)) • ∑ i : Fin mc, clip B (w i - c) := by
    simp only [clipMean, add_sub_cancel_left]
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hs := norm_sum_le (Finset.univ : Finset (Fin mc)) (fun i => clip B (w i - c))
  have hb : ∑ i : Fin mc, ‖clip B (w i - c)‖ ≤ ∑ _i : Fin mc, B :=
    Finset.sum_le_sum fun i _ => norm_clip_le hB _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hmcpos : (0 : ℝ) < mc := by exact_mod_cast hmc
  calc 1 / (mc : ℝ) * ‖∑ i : Fin mc, clip B (w i - c)‖ ≤ 1 / (mc : ℝ) * (mc * B) :=
        mul_le_mul_of_nonneg_left (hs.trans hb) (by positivity)
    _ = B := by field_simp

lemma clipMean_sub (B : ℝ) (c u : E) {mc : ℕ} (hmc : 0 < mc) (w : Fin mc → E) :
    clipMean B c mc w - u = (1 / (mc : ℝ)) • ∑ i : Fin mc, (centeredClip B c (w i) - u) := by
  have hmcne : (mc : ℝ) ≠ 0 := by exact_mod_cast hmc.ne'
  simp only [clipMean, centeredClip, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub, smul_add]
  rw [← Nat.cast_smul_eq_nsmul ℝ mc c, ← Nat.cast_smul_eq_nsmul ℝ mc u, smul_smul, smul_smul]
  simp only [one_div, inv_mul_cancel₀ hmcne, one_smul]

variable [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

noncomputable def clipRadius (σ B : ℝ) (mc : ℕ) (ell : ℝ) : ℝ :=
  3 * Real.sqrt mc * σ + 12 * B * (1 + ell) + 22 * mc * σ ^ 2 / B

lemma clip_tail {V : Ω → E} (hV : Measurable V) (hVi : Integrable V p) {u c : E}
    (hmean : ∫ ω, V ω ∂p = u) (hvi : Integrable (fun ω => ‖V ω - u‖ ^ 2) p)
    {σ B : ℝ} (hσ : 0 ≤ σ) (hvar : (∫ ω, ‖V ω - u‖ ^ 2 ∂p) ≤ σ ^ 2) (hB : 0 < B)
    (hc : ‖u - c‖ ≤ B / 2) {mc : ℕ} (hmc : 0 < mc) {ell : ℝ} (hell : 0 ≤ ell) :
    (Measure.infinitePi fun _ : ℕ => p).real
      {ξ | clipRadius σ B mc ell / mc < ‖clipMean B c mc (fun i => V (ξ i)) - u‖} ≤
        2 * Real.exp (-ell) := by
  set R := clipRadius σ B mc ell with hRdef
  have hmcpos : (0 : ℝ) < mc := by exact_mod_cast hmc
  have hR0 : 0 < R := by
    simp only [hRdef, clipRadius]
    have : 0 < 12 * B * (1 + ell) := by positivity
    have : 0 ≤ 3 * Real.sqrt mc * σ := by positivity
    have : 0 ≤ 22 * (mc : ℝ) * σ ^ 2 / B := by positivity
    linarith
  have hiid := OracleTemplate.StochasticGeneralized.infinitePi_iid p
  let Y : (n : ℕ) → (Fin n → Ω) × Ω → E := fun n az =>
    if n < mc then centeredClip B c (V az.2) - u else 0
  have hY : ∀ n, Measurable (Y n) := by
    intro n
    by_cases hn : n < mc
    · simp only [Y, hn, ↓reduceIte]
      exact ((measurable_centeredClip B c).comp (hV.comp measurable_snd)).sub_const u
    · simp only [Y, hn, ↓reduceIte]
      exact measurable_const
  have hmom := centeredClip_moments hV hVi hmean hB hc hvi hvar
  have hbound (z : Ω) : ‖centeredClip B c (V z) - u‖ ≤ 3 * B / 2 :=
    centeredClip_error_bounded hB.le hc (V z)
  let θe : ℝ := 4 / (9 * B ^ 2)
  let θc : ℝ := 2 / (3 * B * R)
  have hθe : 0 ≤ θe := by positivity
  have hθc : 0 ≤ θc := by positivity
  let variance : ℕ → ℝ := fun i => if i < mc then σ ^ 2 else 0
  let cost : ℕ → ℝ := fun i => if i < mc then θc * R * (2 * σ ^ 2 / B) + θc ^ 2 * R ^ 2 * σ ^ 2
    else 0
  let energy : ℝ := 2 * mc * σ ^ 2 + 9 * B ^ 2 * ell / 4
  let cross : ℝ := 8 / 3 * mc * R * σ ^ 2 / B + 3 / 2 * B * R * ell
  have hcap : ∀ i a z, ‖Y i (a, z)‖ ^ 2 ≤ 9 * B ^ 2 / 4 := by
    intro i a z
    by_cases hi : i < mc
    · simp only [Y, hi, ↓reduceIte]
      have h := hbound z
      have h0 := norm_nonneg (centeredClip B c (V z) - u)
      nlinarith
    · simp only [Y, hi, ↓reduceIte, norm_zero]
      nlinarith [sq_nonneg B]
  have hvariance : ∀ i a, (∫ z, ‖Y i (a, z)‖ ^ 2 ∂p) ≤ variance i := by
    intro i a
    by_cases hi : i < mc
    · simp only [Y, hi, ↓reduceIte, variance]
      exact hmom.2.2.1
    · simp [Y, hi, variance]
  have hdirection : ∀ i a v, ‖v‖ ≤ R →
      Integrable (fun z => Real.exp (θc * ⟪v, Y i (a, z)⟫)) p ∧
        (∫ z, Real.exp (θc * ⟪v, Y i (a, z)⟫) ∂p) ≤ Real.exp (cost i) := by
    intro i a v hv
    by_cases hi : i < mc
    · simp only [Y, hi, ↓reduceIte, cost]
      have hZ : Measurable (fun z => θc * ⟪v, centeredClip B c (V z) - u⟫) :=
        (measurable_const.inner (((measurable_centeredClip B c).comp hV).sub_const u)).const_mul θc
      have hZb : ∀ z, |θc * ⟪v, centeredClip B c (V z) - u⟫| ≤ 1 := by
        intro z
        rw [abs_mul, abs_of_nonneg hθc]
        have h1 := abs_real_inner_le_norm v (centeredClip B c (V z) - u)
        have h2 : ‖v‖ * ‖centeredClip B c (V z) - u‖ ≤ R * (3 * B / 2) :=
          mul_le_mul hv (hbound z) (norm_nonneg _) hR0.le
        have h3 : θc * (R * (3 * B / 2)) = 1 := by
          simp only [θc]; field_simp
        calc θc * |⟪v, centeredClip B c (V z) - u⟫| ≤ θc * (R * (3 * B / 2)) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) hθc
          _ = 1 := h3
      have hYi : Integrable (fun z => centeredClip B c (V z) - u) p :=
        hmom.1.sub (integrable_const u)
      have hmeanZ : (∫ z, θc * ⟪v, centeredClip B c (V z) - u⟫ ∂p) ≤ θc * R * (2 * σ ^ 2 / B) := by
        rw [integral_const_mul, integral_inner hYi v, integral_sub hmom.1 (integrable_const u),
          integral_const, probReal_univ, one_smul]
        have h1 := real_inner_le_norm v ((∫ z, centeredClip B c (V z) ∂p) - u)
        have h2 : ‖v‖ * ‖(∫ z, centeredClip B c (V z) ∂p) - u‖ ≤ R * (2 * σ ^ 2 / B) :=
          mul_le_mul hv hmom.2.2.2 (norm_nonneg _) hR0.le
        calc θc * ⟪v, (∫ z, centeredClip B c (V z) ∂p) - u⟫ ≤ θc * (R * (2 * σ ^ 2 / B)) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) hθc
          _ = θc * R * (2 * σ ^ 2 / B) := by ring
      have hsecondZ : (∫ z, (θc * ⟪v, centeredClip B c (V z) - u⟫) ^ 2 ∂p) ≤
          θc ^ 2 * R ^ 2 * σ ^ 2 := by
        have hpt (z : Ω) : (θc * ⟪v, centeredClip B c (V z) - u⟫) ^ 2 ≤
            θc ^ 2 * R ^ 2 * ‖centeredClip B c (V z) - u‖ ^ 2 := by
          have h1 := abs_real_inner_le_norm v (centeredClip B c (V z) - u)
          have h2 : |⟪v, centeredClip B c (V z) - u⟫| ≤ R * ‖centeredClip B c (V z) - u‖ :=
            h1.trans (mul_le_mul_of_nonneg_right hv (norm_nonneg _))
          have h3 := pow_le_pow_left₀ (abs_nonneg _) h2 2
          rw [sq_abs] at h3
          nlinarith [sq_nonneg θc]
        have hi2 : Integrable (fun z => (θc * ⟪v, centeredClip B c (V z) - u⟫) ^ 2) p := by
          refine Integrable.of_bound (hZ.pow_const 2).aestronglyMeasurable 1 ?_
          refine Filter.Eventually.of_forall fun z => ?_
          rw [Real.norm_eq_abs, abs_pow]
          have := hZb z
          nlinarith [abs_nonneg (θc * ⟪v, centeredClip B c (V z) - u⟫)]
        calc (∫ z, (θc * ⟪v, centeredClip B c (V z) - u⟫) ^ 2 ∂p) ≤
              ∫ z, θc ^ 2 * R ^ 2 * ‖centeredClip B c (V z) - u‖ ^ 2 ∂p :=
            integral_mono hi2 (hmom.2.1.const_mul _) hpt
          _ = θc ^ 2 * R ^ 2 * ∫ z, ‖centeredClip B c (V z) - u‖ ^ 2 ∂p := integral_const_mul _ _
          _ ≤ θc ^ 2 * R ^ 2 * σ ^ 2 :=
            mul_le_mul_of_nonneg_left hmom.2.2.1 (by positivity)
      exact bounded_increment_mgf hZ hZb hmeanZ hsecondZ
    · simp only [Y, hi, ↓reduceIte, inner_zero_right, mul_zero, Real.exp_zero, cost]
      exact ⟨integrable_const 1, by simp⟩
  have hsum_var : (∑ i ∈ Finset.range mc, variance i) = mc * σ ^ 2 := by
    rw [Finset.sum_congr rfl fun i hi => (ite_eq_left (Finset.mem_range.mp hi) : variance i = σ ^ 2)]
    simp
  have hsum_cost : (∑ i ∈ Finset.range mc, cost i) =
      mc * (θc * R * (2 * σ ^ 2 / B) + θc ^ 2 * R ^ 2 * σ ^ 2) := by
    rw [Finset.sum_congr rfl fun i hi => (ite_eq_left (Finset.mem_range.mp hi) :
      cost i = θc * R * (2 * σ ^ 2 / B) + θc ^ 2 * R ^ 2 * σ ^ 2)]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hebudget : 2 * θe * (∑ i ∈ Finset.range mc, variance i) - θe * energy ≤ -ell := by
    rw [hsum_var]
    apply le_of_eq
    simp only [θe, energy]
    field_simp
    ring
  have hcbudget : (∑ i ∈ Finset.range mc, cost i) - θc * cross ≤ -ell := by
    rw [hsum_cost]
    apply le_of_eq
    simp only [θc, cross]
    field_simp
    ring
  have hrbudget : energy + 2 * cross ≤ R ^ 2 := by
    have hR : R = 3 * Real.sqrt mc * σ + 12 * B * (1 + ell) + 22 * mc * σ ^ 2 / B := rfl
    have hsq : Real.sqrt mc ^ 2 = mc := Real.sq_sqrt hmcpos.le
    have hA1 : 0 ≤ 3 * Real.sqrt mc * σ := by positivity
    have hA2 : 0 ≤ 12 * B * (1 + ell) := by positivity
    have hA3 : 0 ≤ 22 * (mc : ℝ) * σ ^ 2 / B := by positivity
    have hR1 : 3 * Real.sqrt mc * σ ≤ R := by rw [hR]; linarith
    have hR2 : 12 * B * (1 + ell) ≤ R := by rw [hR]; linarith
    have hR3 : 22 * (mc : ℝ) * σ ^ 2 / B ≤ R := by rw [hR]; linarith
    have t1 : 2 * (mc : ℝ) * σ ^ 2 ≤ R ^ 2 / 4 := by
      have h1 : (3 * Real.sqrt mc * σ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hA1 hR1 2
      have h9 : (3 * Real.sqrt mc * σ) ^ 2 = 9 * (mc : ℝ) * σ ^ 2 := by
        rw [mul_pow, mul_pow, hsq]; ring
      have : 0 ≤ (mc : ℝ) * σ ^ 2 := by positivity
      linarith
    have t2 : 9 * B ^ 2 * ell / 4 ≤ R ^ 2 / 4 := by
      have h1 : (12 * B * (1 + ell)) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hA2 hR2 2
      have hl : ell ≤ 16 * (1 + ell) ^ 2 := by nlinarith [sq_nonneg ell]
      have h3 : 9 * B ^ 2 * ell ≤ (12 * B * (1 + ell)) ^ 2 := by
        calc 9 * B ^ 2 * ell ≤ 9 * B ^ 2 * (16 * (1 + ell) ^ 2) :=
              mul_le_mul_of_nonneg_left hl (by positivity)
          _ = (12 * B * (1 + ell)) ^ 2 := by ring
      linarith
    have t3 : 2 * (8 / 3 * mc * R * σ ^ 2 / B) ≤ R ^ 2 / 4 := by
      have hx : 0 ≤ (mc : ℝ) * σ ^ 2 / B := by positivity
      have he1 : 2 * (8 / 3 * mc * R * σ ^ 2 / B) = 16 / 3 * R * ((mc : ℝ) * σ ^ 2 / B) := by ring
      have he2 : 22 * (mc : ℝ) * σ ^ 2 / B = 22 * ((mc : ℝ) * σ ^ 2 / B) := by ring
      rw [he2] at hR3
      rw [he1]
      calc 16 / 3 * R * ((mc : ℝ) * σ ^ 2 / B) ≤ 16 / 3 * R * (R / 22) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 8 / 33 * R ^ 2 := by ring
        _ ≤ R ^ 2 / 4 := by nlinarith [sq_nonneg R]
    have t4 : 2 * (3 / 2 * B * R * ell) ≤ R ^ 2 / 4 := by
      have h12 : 12 * B * ell ≤ R := by
        have : 12 * B * (1 + ell) = 12 * B + 12 * B * ell := by ring
        linarith
      calc 2 * (3 / 2 * B * R * ell) = R / 4 * (12 * B * ell) := by ring
        _ ≤ R / 4 * R := mul_le_mul_of_nonneg_left h12 (by positivity)
        _ = R ^ 2 / 4 := by ring
    simp only [energy, cross]
    linarith
  have htail := iid_vector_tail (P := Measure.infinitePi fun _ : ℕ => p) (p := p)
    (ξ := fun k (ξ : ℕ → Ω) => ξ k) hiid.measurable hiid.independent hiid.marginal (Y := Y) hY
    (R := R) (b := 9 * B ^ 2 / 4) (θe := θe) (θc := θc) (energy := energy) (cross := cross)
    (ell := ell) hR0.le hθe hθc (le_of_eq (by simp only [θe]; field_simp)) variance cost hcap
    hvariance hdirection mc hebudget hcbudget hrbudget
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) htail
  intro ξ hξ
  simp only [Set.mem_ofPred_eq] at hξ ⊢
  have hsum : (∑ i ∈ Finset.range mc, Y i ((fun j => ξ j), ξ i)) =
      ∑ i : Fin mc, (centeredClip B c (V (ξ i)) - u) := by
    rw [Finset.sum_range (fun i => Y i ((fun j => ξ j), ξ i))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Y, i.isLt, ↓reduceIte]
  rw [hsum]
  rw [clipMean_sub B c u hmc, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)] at hξ
  rw [div_lt_iff₀ hmcpos] at hξ
  have : R < ‖∑ i : Fin mc, (centeredClip B c (V (ξ i)) - u)‖ := by
    calc R < 1 / (mc : ℝ) * ‖∑ i : Fin mc, (centeredClip B c (V (ξ i)) - u)‖ * mc := hξ
      _ = ‖∑ i : Fin mc, (centeredClip B c (V (ξ i)) - u)‖ := by field_simp
  exact this

end LongTails.Proofs.HighProbabilityEstimator
