import LongTails.Proofs.HighProbabilityStep

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LongTails.Proofs.HeavyTailedHighProbabilityStep

open LongTails.Algorithms.HighProbabilityStationarity OracleTemplate RobustGradient
open LongTails.Proofs.IidVectorConcentration LongTails.Proofs.HighProbabilityPilot
open LongTails.Proofs.HighProbabilityEstimator LongTails.Proofs.HighProbabilityStep

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type} [MeasurableSpace Ω] {p : Measure Ω} [IsProbabilityMeasure p]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
lemma far_prob_heavy {V : Ω → E} {u : E} {α σ s : ℝ} (hα : 0 < α)
    (hpi : Integrable (fun ω => ‖V ω - u‖ ^ α) p) (hs : 0 < s)
    (hpm : (∫ ω, ‖V ω - u‖ ^ α ∂p) ≤ σ ^ α) :
    p.real {ω | s < ‖V ω - u‖} ≤ σ ^ α / s ^ α := by
  have hsα : 0 < s ^ α := Real.rpow_pos_of_pos hs α
  have hsub : {ω | s < ‖V ω - u‖} ⊆ {ω | s ^ α ≤ ‖V ω - u‖ ^ α} := by
    intro ω hω
    exact Real.rpow_le_rpow hs.le (le_of_lt hω) hα.le
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := p)
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg (V ω - u)) α) hpi (s ^ α)
  have h1 : p.real {ω | s < ‖V ω - u‖} ≤ p.real {ω | s ^ α ≤ ‖V ω - u‖ ^ α} :=
    measureReal_mono hsub (measure_ne_top _ _)
  rw [le_div_iff₀ hsα]
  nlinarith

omit [CompleteSpace E] in
lemma centeredClip_moments_heavy {V : Ω → E} (hV : Measurable V) (hVi : Integrable V p)
    {u c : E} (hmean : ∫ ω, V ω ∂p = u) {B : ℝ} (hB : 0 < B) (hc : ‖u - c‖ ≤ B / 2)
    {α s σ : ℝ} (hα1 : 1 ≤ α) (hα2 : α ≤ 2) (hpi : Integrable (fun ω => ‖V ω - u‖ ^ α) p)
    (hpm : (∫ ω, ‖V ω - u‖ ^ α ∂p) ≤ s ^ α) (hs : 0 ≤ s)
    (hlink : 2 * s ^ α * B ^ (2 - α) ≤ σ ^ 2) :
    Integrable (fun ω => centeredClip B c (V ω)) p ∧
    Integrable (fun ω => ‖centeredClip B c (V ω) - u‖ ^ 2) p ∧
    (∫ ω, ‖centeredClip B c (V ω) - u‖ ^ 2 ∂p) ≤ σ ^ 2 ∧
    ‖(∫ ω, centeredClip B c (V ω) ∂p) - u‖ ≤ 2 * σ ^ 2 / B := by
  have hY := (measurable_centeredClip B c).comp hV
  have hYi : Integrable (fun ω => centeredClip B c (V ω)) p :=
    (integrable_const c).add (integrable_clip (hV.sub_const c) hB.le)
  have hb32 : (0 : ℝ) ≤ 3 * B / 2 := by positivity
  have hpoint (ω : Ω) : ‖centeredClip B c (V ω) - u‖ ^ 2 ≤
      (3 * B / 2) ^ (2 - α) * ‖V ω - u‖ ^ α := by
    have h1 := centeredClip_error hB.le (by linarith : ‖u - c‖ ≤ B) (V ω)
    have h2 := centeredClip_error_bounded hB.le hc (V ω)
    refine (sq_le_rpow_mul (norm_nonneg _) h2 hα2).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) h1 (by linarith))
      (Real.rpow_nonneg hb32 _)
  have hYi2 : Integrable (fun ω => ‖centeredClip B c (V ω) - u‖ ^ 2) p := by
    apply (hpi.const_mul ((3 * B / 2) ^ (2 - α))).mono'
      ((hY.sub_const u).norm.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint ω)
  have hfac : (3 * B / 2) ^ (2 - α) ≤ 2 * B ^ (2 - α) := by
    have he : 3 * B / 2 = (3 / 2) * B := by ring
    rw [he, Real.mul_rpow (by norm_num) hB.le]
    have h32 : (3 / 2 : ℝ) ^ (2 - α) ≤ 2 := by
      calc (3 / 2 : ℝ) ^ (2 - α) ≤ (3 / 2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ ≤ 2 := by norm_num
    exact mul_le_mul_of_nonneg_right h32 (Real.rpow_nonneg hB.le _)
  have hsα : 0 ≤ s ^ α := Real.rpow_nonneg hs α
  have hvar : (∫ ω, ‖centeredClip B c (V ω) - u‖ ^ 2 ∂p) ≤ σ ^ 2 := by
    calc (∫ ω, ‖centeredClip B c (V ω) - u‖ ^ 2 ∂p) ≤
          ∫ ω, (3 * B / 2) ^ (2 - α) * ‖V ω - u‖ ^ α ∂p :=
        integral_mono hYi2 (hpi.const_mul _) hpoint
      _ = (3 * B / 2) ^ (2 - α) * ∫ ω, ‖V ω - u‖ ^ α ∂p := integral_const_mul _ _
      _ ≤ (3 * B / 2) ^ (2 - α) * s ^ α :=
        mul_le_mul_of_nonneg_left hpm (Real.rpow_nonneg hb32 _)
      _ ≤ 2 * B ^ (2 - α) * s ^ α := mul_le_mul_of_nonneg_right hfac hsα
      _ ≤ σ ^ 2 := by linarith
  refine ⟨hYi, hYi2, hvar, ?_⟩
  have hres (ω : Ω) : ‖centeredClip B c (V ω) - V ω‖ ≤ ‖V ω - u‖ ^ α / (B / 2) ^ (α - 1) := by
    have h := clip_residual_le_moment hB hα1 (u := u - c) (by simpa using hc) (V ω - c)
    have he : centeredClip B c (V ω) - V ω = -(V ω - c - clip B (V ω - c)) := by
      unfold centeredClip
      abel
    rw [he, norm_neg]
    simpa only [show V ω - c - (u - c) = V ω - u by abel] using h
  have hb := norm_integral_le_of_norm_le (hpi.div_const ((B / 2) ^ (α - 1)))
    (f := fun ω => centeredClip B c (V ω) - V ω) (Filter.Eventually.of_forall hres)
  rw [integral_sub hYi hVi, hmean, integral_div] at hb
  have hb1 : 0 < (B / 2) ^ (α - 1) := Real.rpow_pos_of_pos (by positivity) _
  have h2 : (2 : ℝ) ^ (α - 1) ≤ 2 := by
    calc (2 : ℝ) ^ (α - 1) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have hB2 : B ^ (α - 1) / 2 ≤ (B / 2) ^ (α - 1) := by
    rw [Real.div_rpow hB.le (by norm_num)]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hB.le _) (Real.rpow_pos_of_pos (by norm_num) _) h2
  have hBp : B ^ (α - 1) * B ^ (2 - α) = B := by
    rw [← Real.rpow_add hB, show α - 1 + (2 - α) = 1 by ring, Real.rpow_one]
  have hkey : s ^ α / (B / 2) ^ (α - 1) ≤ 2 * σ ^ 2 / B := by
    rw [div_le_div_iff₀ hb1 hB]
    have hBa : 0 ≤ B ^ (α - 1) := Real.rpow_nonneg hB.le _
    calc s ^ α * B = s ^ α * (B ^ (α - 1) * B ^ (2 - α)) := by rw [hBp]
      _ = (s ^ α * B ^ (2 - α)) * B ^ (α - 1) := by ring
      _ ≤ (σ ^ 2 / 2) * B ^ (α - 1) := mul_le_mul_of_nonneg_right (by linarith) hBa
      _ = σ ^ 2 * (B ^ (α - 1) / 2) := by ring
      _ ≤ σ ^ 2 * (B / 2) ^ (α - 1) := mul_le_mul_of_nonneg_left hB2 (sq_nonneg σ)
      _ ≤ 2 * σ ^ 2 * (B / 2) ^ (α - 1) := by nlinarith [sq_nonneg σ, hb1.le]
  refine hb.trans (le_trans ?_ hkey)
  exact div_le_div_of_nonneg_right hpm hb1.le

set_option maxHeartbeats 1000000 in
lemma clip_tail_heavy {V : Ω → E} (hV : Measurable V) (hVi : Integrable V p) {u c : E}
    (hmean : ∫ ω, V ω ∂p = u) {α s : ℝ} (hα1 : 1 ≤ α) (hα2 : α ≤ 2)
    (hpi : Integrable (fun ω => ‖V ω - u‖ ^ α) p) (hpm : (∫ ω, ‖V ω - u‖ ^ α ∂p) ≤ s ^ α)
    (hs : 0 ≤ s) {σ B : ℝ} (hσ : 0 ≤ σ) (hlink : 2 * s ^ α * B ^ (2 - α) ≤ σ ^ 2) (hB : 0 < B)
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
  have hmom := centeredClip_moments_heavy hV hVi hmean hB hc hα1 hα2 hpi hpm hs hlink
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
      _ = ‖∑ i : Fin mc, (centeredClip B c (V (ξ i)) - u)‖ := by
          rw [one_div_mul_eq_div, div_mul_cancel₀ _ hmcpos.ne']
  exact this

lemma block_ok_mgf_heavy {V : Ω → E} (hV : Measurable V) (hVi : Integrable V p) {u : E}
    (hmean : ∫ ω, V ω ∂p = u) {α s : ℝ} (hα1 : 1 ≤ α) (hα2 : α ≤ 2)
    (hpi : Integrable (fun ω => ‖V ω - u‖ ^ α) p) (hpm : (∫ ω, ‖V ω - u‖ ^ α ∂p) ≤ s ^ α)
    (hs : 0 ≤ s) {σ B : ℝ} (hσ : 0 ≤ σ) (hlink : 2 * s ^ α * B ^ (2 - α) ≤ σ ^ 2) (hB : 0 < B)
    {K mp mc : ℕ} (hmc : 0 < mc) :
    let a0 := clipRadius σ B mc 0 / mc
    let a1 := 12 * B / mc
    Integrable (fun z => Real.exp (okError B K mp mc V u z / (2 * a1)))
        (Measure.pi fun _ : Fin (mp + mc) => p) ∧
      (∫ z, Real.exp (okError B K mp mc V u z / (2 * a1))
        ∂(Measure.pi fun _ : Fin (mp + mc) => p)) ≤ 5 * Real.exp ((a0 + a1) / (2 * a1)) := by
  classical
  intro a0 a1
  have hmcpos : (0 : ℝ) < mc := by exact_mod_cast hmc
  have ha1 : 0 < a1 := by positivity
  have ha0 : 0 ≤ a0 := by
    simp only [a0, clipRadius]
    have : 0 ≤ 3 * Real.sqrt mc * σ + 12 * B * (1 + 0) + 22 * mc * σ ^ 2 / B := by positivity
    positivity
  have hthr (ell : ℝ) : clipRadius σ B mc ell / mc = a0 + a1 * ell := by
    simp only [a0, a1, clipRadius]
    field_simp
    ring
  let H : (Fin mp → Ω) × (ℕ → Ω) → ℝ := fun w =>
    Real.exp (okError B K mp mc V u (fun i => if h : (i : ℕ) < mp then w.1 ⟨i, h⟩
      else w.2 ((i : ℕ) - mp)) / (2 * a1))
  have hjoin : Measurable (fun w : (Fin mp → Ω) × (ℕ → Ω) => fun i : Fin (mp + mc) =>
      if h : (i : ℕ) < mp then w.1 ⟨i, h⟩ else w.2 ((i : ℕ) - mp)) := by
    refine Measurable.of_eval fun i => ?_
    by_cases h : (i : ℕ) < mp
    · simp only [h, ↓reduceDIte]; exact (measurable_pi_apply _).comp measurable_fst
    · simp only [h, ↓reduceDIte]; exact (measurable_pi_apply _).comp measurable_snd
  have hH : Measurable H :=
    (((measurable_okError B K mp mc hV u).comp hjoin).div_const _).exp
  have hsplit := OracleTemplate.StochasticGeneralized.splitStream_preserving
    p mp
  have hcomp : (fun ξ : ℕ → Ω => Real.exp (okError B K mp mc V u (fun i => ξ i) / (2 * a1))) =
      H ∘ (OracleTemplate.StochasticGeneralized.splitStream mp) := by
    funext ξ
    simp only [H, Function.comp_apply]
    congr 3
    funext i
    by_cases h : (i : ℕ) < mp
    · simp only [h, ↓reduceDIte]
      rfl
    · simp only [h, ↓reduceDIte]
      show ξ i = ξ (mp + ((i : ℕ) - mp))
      congr 1
      omega
  have hfiber : ∀ a : Fin mp → Ω, Integrable (fun τ => H (a, τ)) (Measure.infinitePi fun _ : ℕ => p) ∧
      (∫ τ, H (a, τ) ∂(Measure.infinitePi fun _ : ℕ => p)) ≤ 5 * Real.exp ((a0 + a1) / (2 * a1)) := by
    intro a
    set c := gradedPilot B K (fun i => V (a i)) 0 with hc
    have hpilot : ∀ τ : ℕ → Ω, pilotOf B K mp mc V (fun i : Fin (mp + mc) =>
        if h : (i : ℕ) < mp then (a, τ).1 ⟨i, h⟩ else (a, τ).2 ((i : ℕ) - mp)) = c := by
      intro τ
      simp only [pilotOf, hc]
      congr 1
      funext i
      simp [Fin.castAdd, i.isLt]
    have hest : ∀ τ : ℕ → Ω, estimateOf B K mp mc V (fun i : Fin (mp + mc) =>
        if h : (i : ℕ) < mp then (a, τ).1 ⟨i, h⟩ else (a, τ).2 ((i : ℕ) - mp)) =
        clipMean B c mc (fun j => V (τ j)) := by
      intro τ
      rw [estimateOf, clipEstimate_eq]
      have := hpilot τ
      simp only [pilotOf] at this
      rw [this]
      congr 1
      funext j
      simp [Fin.natAdd]
    by_cases hok : ‖c - u‖ ≤ B / 2
    · have hX : Measurable (fun τ : ℕ → Ω => ‖clipMean B c mc (fun j => V (τ j)) - u‖) := by
        have : Measurable (fun τ : ℕ → Ω => clipMean B c mc (fun j => V (τ j))) := by
          unfold clipMean
          refine measurable_const.add (Measurable.const_smul ?_ _)
          exact Finset.measurable_sum _ fun i _ =>
            (measurable_clip B).comp ((hV.comp (measurable_pi_apply _)).sub_const c)
        exact (this.sub_const u).norm
      have hM : ∀ τ : ℕ → Ω, ‖clipMean B c mc (fun j => V (τ j)) - u‖ ≤ 3 * B / 2 := by
        intro τ
        have h1 := clipMean_sub_center hB.le c hmc (fun j => V (τ j))
        have h2 : ‖clipMean B c mc (fun j => V (τ j)) - u‖ ≤
            ‖clipMean B c mc (fun j => V (τ j)) - c‖ + ‖c - u‖ := by
          have := norm_add_le (clipMean B c mc (fun j => V (τ j)) - c) (c - u)
          simpa only [sub_add_sub_cancel] using this
        linarith
      have htail : ∀ k : ℕ, (Measure.infinitePi fun _ : ℕ => p).real
          {τ | a0 + a1 * (k + 1) < ‖clipMean B c mc (fun j => V (τ j)) - u‖} ≤
            2 * Real.exp (-(k + 1)) := by
        intro k
        have h := clip_tail_heavy hV hVi hmean hα1 hα2 hpi hpm hs hσ hlink hB
          (by rw [norm_sub_rev]; exact hok) hmc
          (ell := (k : ℝ) + 1) (by positivity)
        rw [hthr] at h
        exact h
      have hmgf := mgf_of_tail hX hM ha0 ha1 htail
      have hHeq : (fun τ => H (a, τ)) =
          fun τ => Real.exp (‖clipMean B c mc (fun j => V (τ j)) - u‖ / (2 * a1)) := by
        funext τ
        simp only [H, okError, hpilot τ, hok, ↓reduceIte, hest τ]
      rw [hHeq]
      exact hmgf
    · have hHeq : (fun τ => H (a, τ)) = fun _ => 1 := by
        funext τ
        simp only [H, okError, hpilot τ, hok, ↓reduceIte, zero_div, Real.exp_zero]
      rw [hHeq]
      refine ⟨integrable_const 1, ?_⟩
      simp only [integral_const, probReal_univ, one_smul]
      have : 1 ≤ Real.exp ((a0 + a1) / (2 * a1)) := Real.one_le_exp (by positivity)
      linarith
  have hbound := LongTails.Proofs.WeakGradientConvolution.nonnegative_fiber_integral_bound
    (P := Measure.pi fun _ : Fin mp => p) (Q := Measure.infinitePi fun _ : ℕ => p)
    hH.stronglyMeasurable (fun w => (Real.exp_pos _).le)
    (Filter.Eventually.of_forall fun a => (hfiber a).1)
    (integrable_const (5 * Real.exp ((a0 + a1) / (2 * a1))))
    (Filter.Eventually.of_forall fun a => (hfiber a).2)
  have hpre := OracleTemplate.StochasticGeneralized.prefix_preserving p (mp + mc)
  have hFm : Measurable (fun z : Fin (mp + mc) → Ω => Real.exp (okError B K mp mc V u z / (2 * a1))) :=
    ((measurable_okError B K mp mc hV u).div_const _).exp
  have hi : Integrable (fun ξ : ℕ → Ω => Real.exp (okError B K mp mc V u (fun i => ξ i) / (2 * a1)))
      (Measure.infinitePi fun _ : ℕ => p) := by
    rw [hcomp]
    exact hsplit.integrable_comp_of_integrable hbound.1
  refine ⟨?_, ?_⟩
  · rw [← hpre.map_eq]
    exact (integrable_map_measure hFm.aestronglyMeasurable hpre.measurable.aemeasurable).mpr hi
  · rw [block_prefix _ hFm]
    rw [hcomp, Function.comp_def, hsplit.integral_comp' H]
    refine hbound.2.trans ?_
    simp


omit [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E] in
lemma pilot_tail_gen {V : Ω → E} (hV : Measurable V) {u : E} {θ s B : ℝ} {K mp : ℕ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (htail : p.real {ω | s < ‖V ω - u‖} ≤ θ)
    (hs : B ≤ 12 * s) (hK : 6 * s ≤ 2 ^ K * B) :
    (Measure.pi fun _ : Fin mp => p) {a | 5 * s < ‖gradedPilot B K (fun i => V (a i)) 0 - u‖} ≤
      ENNReal.ofReal ((2 * Real.sqrt θ) ^ mp) := by
  classical
  let A : Set Ω := {ω | s < ‖V ω - u‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const ((hV.sub_const u).norm)
  have hmaj := majority_failure_probability_le hA hθ hθ1 htail mp
  refine le_trans (measure_mono ?_) hmaj
  intro a ha
  simp only [Set.mem_ofPred_eq] at ha ⊢
  by_contra hcon
  push Not at hcon
  have hgood : mp < 2 * (Finset.univ.filter (fun i => ‖V (a i) - u‖ ≤ s)).card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin mp))) (fun i => a i ∈ A)
    have hneg : (Finset.univ.filter (fun i => ¬ a i ∈ A)) =
        Finset.univ.filter (fun i => ‖V (a i) - u‖ ≤ s) := by
      ext i
      simp [A, not_lt]
    rw [hneg, Finset.card_univ, Fintype.card_fin] at hpart
    omega
  have hclose := gradedPilot_close (fun i => V (a i)) u 0 hs hK hgood
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma block_scale_gen {V : Ω → E} (hV : Measurable V) {u : E} {θ t B : ℝ} {K mp mc : ℕ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (htail : p.real {ω | t / 5 < ‖V ω - u‖} ≤ θ)
    (ht : 5 * B ≤ 12 * t) (hK : 6 * t ≤ 5 * (2 ^ K * B)) :
    (Measure.pi fun _ : Fin (mp + mc) => p) {z | t < ‖pilotOf B K mp mc V z - u‖} ≤
      ENNReal.ofReal ((2 * Real.sqrt θ) ^ mp) := by
  rw [block_pilot_measure hV u t]
  have h := pilot_tail_gen (mp := mp) hV hθ hθ1 htail (by linarith) (by linarith) (K := K) (B := B)
  have he : 5 * (t / 5) = t := by ring
  rw [he] at h
  exact h


end LongTails.Proofs.HeavyTailedHighProbabilityStep
