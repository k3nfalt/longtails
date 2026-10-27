import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

open scoped RealInnerProductSpace
open MeasureTheory

namespace LongTails.Proofs.HessianAdaptiveCubicNormalization

lemma radius_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ b : ℝ) (hb : 0 ≤ b) (x y : E) :
    |Real.sqrt (κ ^ 2 + b ^ 2 * ‖x‖ ^ 2) - Real.sqrt (κ ^ 2 + b ^ 2 * ‖y‖ ^ 2)| ≤
      b * ‖x - y‖ := by
  have h := abs_norm_sub_norm_le (WithLp.toLp 2 (κ, b • x)) (WithLp.toLp 2 (κ, b • y))
  simpa [WithLp.prod_norm_eq_of_L2, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb,
    mul_pow, ← smul_sub, Real.sqrt_sq hb] using h

lemma inverse_lipschitz {κ x y : ℝ} (hκ : 0 < κ) (hx : κ ≤ x) (hy : κ ≤ y) :
    |x⁻¹ - y⁻¹| ≤ |x - y| / κ ^ 2 := by
  have hxpos : 0 < x := hκ.trans_le hx
  have hypos : 0 < y := hκ.trans_le hy
  have hid : x⁻¹ - y⁻¹ = -(x - y) / (x * y) := by field_simp; ring
  rw [hid, abs_div, abs_neg, abs_of_pos (mul_pos hxpos hypos)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hκ)
    (by nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)])

lemma max_lipschitz (x y z : ℝ) : |max x z - max y z| ≤ |x - y| := by
  rcases le_total x z with hx | hx <;> rcases le_total y z with hy | hy
  · simp [max_eq_right hx, max_eq_right hy]
  · rw [max_eq_right hx, max_eq_left hy, abs_of_nonpos (by linarith),
      abs_of_nonpos (by linarith)]
    linarith
  · rw [max_eq_left hx, max_eq_right hy, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    linarith
  · rw [max_eq_left hx, max_eq_left hy]

lemma reciprocal_radius_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ b floor : ℝ) (hκ : 0 < κ) (hb : 0 ≤ b) (x y : E) :
    |(max (Real.sqrt (κ ^ 2 + b ^ 2 * ‖x‖ ^ 2)) floor)⁻¹ -
      (max (Real.sqrt (κ ^ 2 + b ^ 2 * ‖y‖ ^ 2)) floor)⁻¹| ≤
      b / κ ^ 2 * ‖x - y‖ := by
  have hlo (v : E) : κ ≤ max (Real.sqrt (κ ^ 2 + b ^ 2 * ‖v‖ ^ 2)) floor := by
    apply le_trans _ (le_max_left _ _)
    apply (Real.le_sqrt hκ.le (by positivity)).2
    nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg ‖v‖)]
  calc
    _ ≤ |max (Real.sqrt (κ ^ 2 + b ^ 2 * ‖x‖ ^ 2)) floor -
        max (Real.sqrt (κ ^ 2 + b ^ 2 * ‖y‖ ^ 2)) floor| / κ ^ 2 :=
      inverse_lipschitz hκ (hlo x) (hlo y)
    _ ≤ |Real.sqrt (κ ^ 2 + b ^ 2 * ‖x‖ ^ 2) -
        Real.sqrt (κ ^ 2 + b ^ 2 * ‖y‖ ^ 2)| / κ ^ 2 :=
      div_le_div_of_nonneg_right (max_lipschitz _ _ _) (sq_nonneg κ)
    _ ≤ (b * ‖x - y‖) / κ ^ 2 :=
      div_le_div_of_nonneg_right (radius_lipschitz κ b hb x y) (sq_nonneg κ)
    _ = _ := by ring

lemma centered_normalization_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) (ξ : Ω → E) (v : E) (h : Ω → ℝ) (h0 L : ℝ)
    (hξ : Integrable ξ μ) (hmean : ∫ ω, ξ ω ∂μ = 0)
    (hsq : Integrable (fun ω => ‖ξ ω‖ ^ 2) μ)
    (hprod : Integrable (fun ω => ⟪v, ξ ω⟫ * h ω) μ)
    (hlip : ∀ ω, |h ω - h0| ≤ L * ‖ξ ω‖) :
    |∫ ω, ⟪v, ξ ω⟫ * h ω ∂μ| ≤ L * ‖v‖ * ∫ ω, ‖ξ ω‖ ^ 2 ∂μ := by
  have hconst := (hξ.const_inner v).mul_const h0
  have hdiff : Integrable (fun ω => ⟪v, ξ ω⟫ * (h ω - h0)) μ := by
    convert hprod.sub hconst using 1
    ext ω
    exact mul_sub _ _ _
  have heq : (∫ ω, ⟪v, ξ ω⟫ * (h ω - h0) ∂μ) = ∫ ω, ⟪v, ξ ω⟫ * h ω ∂μ := by
    simp only [mul_sub]
    rw [integral_sub hprod hconst, integral_mul_const, integral_inner hξ, hmean]
    simp
  have hpoint (ω : Ω) : |⟪v, ξ ω⟫ * (h ω - h0)| ≤ L * ‖v‖ * ‖ξ ω‖ ^ 2 := by
    rw [abs_mul]
    calc
      _ ≤ (‖v‖ * ‖ξ ω‖) * (L * ‖ξ ω‖) :=
        mul_le_mul (abs_real_inner_le_norm v (ξ ω)) (hlip ω) (abs_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  rw [← heq]
  calc
    _ ≤ ∫ ω, |⟪v, ξ ω⟫ * (h ω - h0)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, L * ‖v‖ * ‖ξ ω‖ ^ 2 ∂μ :=
      integral_mono hdiff.abs (hsq.const_mul _) hpoint
    _ = _ := integral_const_mul _ _

lemma normalized_energy_step {κ Λ Enew Eprev V D znoise : ℝ}
    (hκ : 0 < κ) (hΛ : κ ≤ Λ) (hE : 0 ≤ Eprev)
    (henergy : Enew + κ / 2 * V ≤ Eprev + (7 / 2) * D ^ 2 * (Λ - κ) + znoise) :
    Enew / Λ + (κ / Λ) / 2 * V ≤
      Eprev / κ + (7 / 2) * D ^ 2 * (1 - κ / Λ) + znoise / Λ := by
  have hΛpos := hκ.trans_le hΛ
  have hdiv := (div_le_div_iff_of_pos_right hΛpos).2 henergy
  have hprev := div_le_div_of_nonneg_left hE hκ hΛ
  have hleft : (Enew + κ / 2 * V) / Λ = Enew / Λ + (κ / Λ) / 2 * V := by ring
  have hright : (Eprev + (7 / 2) * D ^ 2 * (Λ - κ) + znoise) / Λ =
      Eprev / Λ + (7 / 2) * D ^ 2 * (1 - κ / Λ) + znoise / Λ := by
    field_simp
  rw [hleft, hright] at hdiv
  linarith

lemma scale_ratio_log {κ Λ : ℝ} (hκ : 0 < κ) (hΛ : 0 < Λ) :
    1 - κ / Λ ≤ Real.log Λ - Real.log κ := by
  have h := Real.one_sub_inv_le_log_of_pos (div_pos hΛ hκ)
  simpa only [inv_div, Real.log_div (ne_of_gt hΛ) (ne_of_gt hκ)] using h

lemma sum_scale_ratios (κ : ℕ → ℝ) (hκ : ∀ n, 0 < κ n) (N : ℕ) :
    ∑ n ∈ Finset.range N, (1 - κ n / κ (n + 1)) ≤ Real.log (κ N) - Real.log (κ 0) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := scale_ratio_log (hκ n) (hκ (n + 1))
    linarith

lemma normalized_energy_telescope (F V κ noise : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hκ : ∀ n, 0 < κ n)
    (hstep : ∀ n, F (n + 1) + (κ n / κ (n + 1)) / 2 * V n ≤
      F n + C * (1 - κ n / κ (n + 1)) + noise n) (N : ℕ) :
    F N + ∑ n ∈ Finset.range N, (κ n / κ (n + 1)) / 2 * V n ≤
      F 0 + C * (Real.log (κ N) - Real.log (κ 0)) + ∑ n ∈ Finset.range N, noise n := by
  have hsum : F N + ∑ n ∈ Finset.range N, (κ n / κ (n + 1)) / 2 * V n ≤
      F 0 + C * (∑ n ∈ Finset.range N, (1 - κ n / κ (n + 1))) +
        ∑ n ∈ Finset.range N, noise n := by
    induction N with
    | zero => simp
    | succ n ih =>
      simp only [Finset.sum_range_succ]
      have h := hstep n
      linarith
  have hlog := mul_le_mul_of_nonneg_left (sum_scale_ratios κ hκ N) hC
  linarith

lemma gradient_floor_drift {a w σ κ D t : ℝ} (hσ : 0 ≤ σ) (hκ : 0 < κ)
    (hD : 0 < D) (ht : 0 < t) (hcap : a * w ≤ t ^ 5 / D ^ 2)
    (hfloor : σ * t ^ 3 / D ^ 2 ≤ κ) :
    a * w * σ ^ 2 / κ ^ 2 ≤ D ^ 2 / t := by
  have hDsq : 0 < D ^ 2 := sq_pos_of_pos hD
  have hf := (div_le_iff₀ hDsq).mp hfloor
  have hsq := mul_self_le_mul_self (show 0 ≤ σ * t ^ 3 by positivity) hf
  have hm := mul_le_mul_of_nonneg_right hcap (sq_nonneg σ)
  have hmt := mul_le_mul_of_nonneg_right hm (show 0 ≤ D ^ 2 * t by positivity)
  have he : (t ^ 5 / D ^ 2 * σ ^ 2) * (D ^ 2 * t) = σ ^ 2 * t ^ 6 := by field_simp
  rw [he] at hmt
  apply (div_le_div_iff₀ (sq_pos_of_pos hκ) ht).2
  have hresult : D ^ 2 * (a * w * σ ^ 2 * t - D ^ 2 * κ ^ 2) ≤ 0 := by nlinarith
  nlinarith

lemma integral_log_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (hiX : Integrable X μ)
    (hXone : ∀ ω, 1 ≤ X ω) :
    Integrable (fun ω => Real.log (X ω)) μ ∧
      (∫ ω, Real.log (X ω) ∂μ) ≤ Real.log (∫ ω, X ω ∂μ) := by
  have hXpos (ω : Ω) : 0 < X ω := lt_of_lt_of_le zero_lt_one (hXone ω)
  have hilog : Integrable (fun ω => Real.log (X ω)) μ := by
    apply hiX.mono' hX.log.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (hXone ω))]
    linarith [Real.log_le_sub_one_of_pos (hXpos ω)]
  have hS : 1 ≤ ∫ ω, X ω ∂μ := by
    have h := integral_mono (integrable_const (1 : ℝ)) hiX hXone
    simpa using h
  have hSpos : 0 < ∫ ω, X ω ∂μ := lt_of_lt_of_le zero_lt_one hS
  have hpoint (ω : Ω) : Real.log (X ω) ≤
      Real.log (∫ z, X z ∂μ) + X ω / (∫ z, X z ∂μ) - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos (hXpos ω) hSpos)
    rw [Real.log_div (ne_of_gt (hXpos ω)) (ne_of_gt hSpos)] at h
    linarith
  refine ⟨hilog, ?_⟩
  have hright : Integrable (fun ω => Real.log (∫ z, X z ∂μ) + X ω / (∫ z, X z ∂μ) - 1) μ :=
    ((integrable_const _).add (hiX.div_const _)).sub (integrable_const _)
  have hb := integral_mono hilog hright hpoint
  rw [integral_sub (f := fun ω => Real.log (∫ z, X z ∂μ) + X ω / (∫ z, X z ∂μ))
      (g := fun _ => (1 : ℝ)) ((integrable_const _).add (hiX.div_const _)) (integrable_const _),
    integral_add (f := fun _ => Real.log (∫ z, X z ∂μ))
      (g := fun ω => X ω / (∫ z, X z ∂μ)) (integrable_const _) (hiX.div_const _), integral_div] at hb
  simpa [ne_of_gt hSpos] using hb

lemma logarithmic_self_bound {S B H : ℝ} (hS : 0 < S)
    (hbound : S ≤ B + 10 * (1 + H) + 5 * Real.log S) :
    S ≤ 2 * B + 20 * H + 34 := by
  have hten : Real.log (10 : ℝ) ≤ 12 / 5 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 10 / 8 by norm_num)
    rw [Real.log_div (by norm_num : (10 : ℝ) ≠ 0) (by norm_num : (8 : ℝ) ≠ 0)] at h
    have he : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [he] at h
    nlinarith [Real.log_two_lt_d9]
  have h := Real.log_le_sub_one_of_pos (div_pos hS (by norm_num : (0 : ℝ) < 10))
  rw [Real.log_div (ne_of_gt hS) (by norm_num : (10 : ℝ) ≠ 0)] at h
  nlinarith

lemma reciprocal_radius_inner_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) (ξ : Ω → E) (v r0 : E) (κ b floor σ : ℝ)
    (hκ : 0 < κ) (hb : 0 ≤ b) (hξ : Measurable ξ) (hiξ : Integrable ξ μ)
    (hmean : ∫ ω, ξ ω ∂μ = 0) (hisq : Integrable (fun ω => ‖ξ ω‖ ^ 2) μ)
    (hsq : (∫ ω, ‖ξ ω‖ ^ 2 ∂μ) ≤ σ ^ 2) :
    let h := fun ω => (max (Real.sqrt (κ ^ 2 + b ^ 2 * ‖ξ ω + r0‖ ^ 2)) floor)⁻¹
    Integrable (fun ω => ⟪v, ξ ω⟫ * h ω) μ ∧
      |∫ ω, ⟪v, ξ ω⟫ * h ω ∂μ| ≤ (b / κ ^ 2) * ‖v‖ * σ ^ 2 := by
  dsimp only
  let h := fun ω => (max (Real.sqrt (κ ^ 2 + b ^ 2 * ‖ξ ω + r0‖ ^ 2)) floor)⁻¹
  have hm : Measurable h := by dsimp [h]; fun_prop
  have hlow (ω : Ω) : κ ≤ max (Real.sqrt (κ ^ 2 + b ^ 2 * ‖ξ ω + r0‖ ^ 2)) floor := by
    apply le_trans _ (le_max_left _ _)
    apply (Real.le_sqrt hκ.le (by positivity)).2
    nlinarith [mul_nonneg (sq_nonneg b) (sq_nonneg ‖ξ ω + r0‖)]
  have hbound (ω : Ω) : ‖h ω‖ ≤ κ⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hκ.trans_le (hlow ω)))]
    exact inv_anti₀ hκ (hlow ω)
  have hip := (hiξ.const_inner v).mul_bdd hm.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨hip, ?_⟩
  have hlip (ω : Ω) : |h ω - (max (Real.sqrt (κ ^ 2 + b ^ 2 * ‖r0‖ ^ 2)) floor)⁻¹| ≤
      b / κ ^ 2 * ‖ξ ω‖ := by
    simpa only [add_sub_cancel_right] using reciprocal_radius_lipschitz κ b floor hκ hb (ξ ω + r0) r0
  have hcenter := centered_normalization_bound μ ξ v h _ (b / κ ^ 2) hiξ hmean hisq hip hlip
  exact hcenter.trans (mul_le_mul_of_nonneg_left hsq (by positivity))

lemma scale_square_increment {κ r Fprev Fnext : ℝ} (hr : 0 ≤ r)
    (hprev : 0 ≤ Fprev) (hκ : Fprev ≤ κ) (hnext : Fprev ≤ Fnext) :
    (max (Real.sqrt (κ ^ 2 + r)) Fnext) ^ 2 ≤ κ ^ 2 + r + Fnext ^ 2 - Fprev ^ 2 := by
  have hrad : 0 ≤ κ ^ 2 + r := by positivity
  have hsq := Real.sq_sqrt hrad
  rcases le_total (Real.sqrt (κ ^ 2 + r)) Fnext with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h, hsq]
    nlinarith

lemma bounded_movement_recovery {q V B : ℝ} (hq : q ≤ 1) (hV : V ≤ B) :
    V ≤ q * V + B * (1 - q) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hV)]

lemma movement_telescope (F V κ noise : ℕ → ℝ) (D : ℝ)
    (hκ : ∀ n, 0 < κ n) (hmono : ∀ n, κ n ≤ κ (n + 1))
    (hF : ∀ n, 0 ≤ F n) (hV : ∀ n, V n ≤ D ^ 2)
    (hstep : ∀ n, F (n + 1) + (κ n / κ (n + 1)) / 2 * V n ≤
      F n + (7 / 2) * D ^ 2 * (1 - κ n / κ (n + 1)) + noise n) (N : ℕ) :
    ∑ n ∈ Finset.range N, V n ≤
      2 * F 0 + 8 * D ^ 2 * (Real.log (κ N) - Real.log (κ 0)) +
        2 * ∑ n ∈ Finset.range N, noise n := by
  have he := normalized_energy_telescope F V κ noise ((7 / 2) * D ^ 2)
    (by positivity) hκ hstep N
  have hr : (∑ n ∈ Finset.range N, V n) ≤
      2 * (∑ n ∈ Finset.range N, (κ n / κ (n + 1)) / 2 * V n) +
        D ^ 2 * (∑ n ∈ Finset.range N, (1 - κ n / κ (n + 1))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n hn
    have hq : κ n / κ (n + 1) ≤ 1 := (div_le_one (hκ _)).2 (hmono n)
    have h := bounded_movement_recovery hq (hV n)
    nlinarith
  have hl := mul_le_mul_of_nonneg_left (sum_scale_ratios κ hκ N) (sq_nonneg D)
  linarith [hF N]

lemma weighted_movement_sum (V : ℕ → ℝ) (hV : ∀ n, 0 ≤ V n) (N : ℕ) :
    (∑ n ∈ Finset.range N, Real.sqrt (n + 1) * V n) ≤
      Real.sqrt N * (∑ n ∈ Finset.range N, V n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_right _ (hV n)
  apply Real.sqrt_le_sqrt
  exact_mod_cast (show n + 1 ≤ N from Nat.succ_le_of_lt (Finset.mem_range.mp hn))

lemma scale_square_telescope (κ floor cost : ℕ → ℝ)
    (hstep : ∀ n, κ (n + 1) ^ 2 ≤ κ n ^ 2 + cost n + floor (n + 1) ^ 2 - floor n ^ 2)
    (N : ℕ) :
    κ N ^ 2 ≤ κ 0 ^ 2 + (∑ n ∈ Finset.range N, cost n) + floor N ^ 2 - floor 0 ^ 2 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith [hstep n]

lemma integrable_square_of_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X B : Ω → ℝ) (hX : Measurable X) (hB : Integrable B μ)
    (hbound : ∀ ω, X ω ^ 2 ≤ B ω) : Integrable (fun ω => X ω ^ 2) μ := by
  apply hB.mono' (hX.pow_const 2).aestronglyMeasurable
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (X ω))] using hbound ω

lemma normalized_noise_drift {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) (ξ : Ω → E) (v r0 : E) (a w κ floor σ D t : ℝ)
    (ha : 0 ≤ a) (hw : 0 ≤ w) (hκ : 0 < κ) (hD : 0 < D) (ht : 0 < t)
    (hσ : 0 ≤ σ) (hv : ‖v‖ ≤ D) (hcap : a * w ≤ t ^ 5 / D ^ 2)
    (hfloor : σ * t ^ 3 / D ^ 2 ≤ κ)
    (hξ : Measurable ξ) (hiξ : Integrable ξ μ)
    (hmean : ∫ ω, ξ ω ∂μ = 0) (hisq : Integrable (fun ω => ‖ξ ω‖ ^ 2) μ)
    (hsq : (∫ ω, ‖ξ ω‖ ^ 2 ∂μ) ≤ σ ^ 2) :
    let η := fun ω => -a * ⟪v, ξ ω⟫ *
      (max (Real.sqrt (κ ^ 2 + (w / D) ^ 2 * ‖ξ ω + r0‖ ^ 2)) floor)⁻¹
    Integrable η μ ∧ (∫ ω, η ω ∂μ) ≤ D ^ 2 / t := by
  dsimp only
  let h := fun ω => (max (Real.sqrt (κ ^ 2 + (w / D) ^ 2 * ‖ξ ω + r0‖ ^ 2)) floor)⁻¹
  have hb := reciprocal_radius_inner_bound μ ξ v r0 κ (w / D) floor σ hκ
    (div_nonneg hw hD.le) hξ hiξ hmean hisq hsq
  have hi : Integrable (fun ω => -a * (⟪v, ξ ω⟫ * h ω)) μ := hb.1.const_mul (-a)
  refine ⟨by simpa only [mul_assoc] using hi, ?_⟩
  change (∫ ω, -a * ⟪v, ξ ω⟫ * h ω ∂μ) ≤ _
  simp only [mul_assoc, integral_const_mul]
  have hiabs : -a * (∫ ω, ⟪v, ξ ω⟫ * h ω ∂μ) ≤
      a * |∫ ω, ⟪v, ξ ω⟫ * h ω ∂μ| := by
    have hh := neg_le_abs (∫ ω, ⟪v, ξ ω⟫ * h ω ∂μ)
    nlinarith
  have h₁ := mul_le_mul_of_nonneg_left hb.2 ha
  have h₂ := mul_le_mul_of_nonneg_left hv
    (show 0 ≤ a * ((w / D) / κ ^ 2) * σ ^ 2 by positivity)
  have he : a * ((w / D) / κ ^ 2) * σ ^ 2 * D = a * w * σ ^ 2 / κ ^ 2 := by
    field_simp
  have hf := gradient_floor_drift hσ hκ hD ht hcap hfloor
  dsimp only at h₁
  change a * |∫ ω, ⟪v, ξ ω⟫ * h ω ∂μ| ≤ _ at h₁
  nlinarith

end LongTails.Proofs.HessianAdaptiveCubicNormalization
