import LongTails.Proofs.MinimaxLmoNoise
import LongTails.Proofs.NormalizedStormMoments

open MeasureTheory
open scoped RealInnerProductSpace

namespace OracleTemplate.MinimaxLmo

open LongTails.Setups.UscgConstant (Space dualNorm IsBallLMO constantMomentum)
open LongTails.Setups.MinimaxLmo (GeneralizedMinimax clip)

section Clip

variable {d : ℕ}

lemma clip_norm_le {c : ℝ} (hc : 0 ≤ c) (v : Space d) : ‖clip c v‖ ≤ c := by
  unfold clip
  split_ifs with h
  · exact h
  · push Not at h
    have hv : 0 < ‖v‖ := lt_of_le_of_lt hc h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hc hv.le), div_mul_cancel₀ c hv.ne']

lemma clip_norm_le' {c : ℝ} (hc : 0 ≤ c) (v : Space d) : ‖clip c v‖ ≤ ‖v‖ := by
  unfold clip
  split_ifs with h
  · exact le_rfl
  · push Not at h
    have hv : 0 < ‖v‖ := lt_of_le_of_lt hc h
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hc hv.le), div_mul_cancel₀ c hv.ne']
    exact h.le

lemma clip_bias {c : ℝ} (hc : 0 < c) (g m : Space d) (hm : ‖m‖ ≤ c / 2) :
    ‖g - clip c g‖ ≤ 2 * ‖g - m‖ ^ 2 / c := by
  unfold clip
  split_ifs with h
  · rw [sub_self, norm_zero]; positivity
  · push Not at h
    have hg : 0 < ‖g‖ := lt_of_le_of_lt hc.le h
    have e : g - (c / ‖g‖) • g = (1 - c / ‖g‖) • g := by rw [sub_smul, one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by rw [sub_nonneg, div_le_one hg]; exact h.le),
      sub_mul, div_mul_cancel₀ c hg.ne', one_mul]
    have h1 : ‖g‖ ≤ ‖g - m‖ + ‖m‖ := by
      have := norm_add_le (g - m) m; rwa [sub_add_cancel] at this
    have h2 : c / 2 ≤ ‖g - m‖ := by linarith
    rw [le_div_iff₀ hc]
    nlinarith [norm_nonneg (g - m)]

end Clip

section Step

variable {d₁ d₂ : ℕ} {Ω : Type} [MeasurableSpace Ω] {N : Seminorm ℝ (Space d₁)}
  {L₀ L₁ μ σx σy Δ W : ℝ} {x₁ : Space d₁} {y₁ : Space d₂} {f : Space d₁ → Space d₂ → ℝ}
  {gx : Space d₁ → Space d₂ → Space d₁} {gy : Space d₁ → Space d₂ → Space d₂}
  {ox : Space d₁ → Space d₂ → Ω → Space d₁} {oy : Space d₁ → Space d₂ → Ω → Space d₂} {p : Measure Ω}

variable (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p) (hμ : 0 < μ)
include H

theorem track_step_sq [IsProbabilityMeasure p] {β c : ℝ} (hβ : 0 ≤ β) (hβ2 : 2 * β * L₀ ^ 2 ≤ μ)
    (hc : 0 < c) (x : Space d₁) (y : Space d₂) (hgy : ‖gy x y‖ ≤ c / 2)
    (hG : ‖gy x y‖ ≤ L₀ * ‖y - ystar H hμ x‖) :
    Integrable (fun ω => ‖y + β • clip c (oy x y ω) - ystar H hμ x‖ ^ 2) p ∧
      ∫ ω, ‖y + β • clip c (oy x y ω) - ystar H hμ x‖ ^ 2 ∂p ≤
        (1 - β * μ / 2) * ‖y - ystar H hμ x‖ ^ 2 + 8 * β * σy ^ 4 / (μ * c ^ 2) + 2 * β ^ 2 * σy ^ 2 := by
  set ys := ystar H hμ x
  set D := ‖y - ys‖
  have hD : 0 ≤ D := norm_nonneg _
  have hgi := H.integrable_y x y
  have hvi := H.variance_y_integrable x y
  have hmeas : Measurable fun ω => oy x y ω := by
    have h2 : Measurable fun ω : Ω => (((x, y) : Space d₁ × Space d₂), ω) :=
      measurable_const.prodMk measurable_id
    exact H.measurable_y.comp h2
  set U : Ω → ℝ := fun ω => D ^ 2 + 2 * β * ⟪oy x y ω, y - ys⟫ + 4 * β * D * ‖oy x y ω - gy x y‖ ^ 2 / c +
    2 * β ^ 2 * (L₀ ^ 2 * D ^ 2 + ‖oy x y ω - gy x y‖ ^ 2)
  have hpt : ∀ ω, ‖y + β • clip c (oy x y ω) - ys‖ ^ 2 ≤ U ω := by
    intro ω
    set g := oy x y ω
    have e : y + β • clip c g - ys = (y - ys) + β • clip c g := by abel
    rw [e, norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs, abs_of_nonneg hβ]
    have hb := clip_bias hc g (gy x y) hgy
    have hci : ⟪y - ys, clip c g⟫ ≤ ⟪g, y - ys⟫ + ‖g - clip c g‖ * D := by
      have e2 : ⟪y - ys, clip c g⟫ = ⟪g, y - ys⟫ - ⟪g - clip c g, y - ys⟫ := by
        rw [real_inner_comm (clip c g) (y - ys), inner_sub_left (g) (clip c g) (y - ys)]; ring
      rw [e2]
      have := real_inner_le_norm (g - clip c g) (y - ys)
      have h3 := neg_le_abs ⟪g - clip c g, y - ys⟫
      have h4 := abs_real_inner_le_norm (g - clip c g) (y - ys)
      linarith
    have hcn : ‖clip c g‖ ^ 2 ≤ 2 * (L₀ ^ 2 * D ^ 2 + ‖g - gy x y‖ ^ 2) := by
      have h1 := clip_norm_le' hc.le g
      have h2 : ‖g‖ ≤ ‖gy x y‖ + ‖g - gy x y‖ := by
        have := norm_add_le (gy x y) (g - gy x y); rwa [add_sub_cancel] at this
      have h3 : ‖clip c g‖ ≤ L₀ * D + ‖g - gy x y‖ := by linarith
      have h4 := norm_nonneg (clip c g)
      nlinarith [sq_nonneg (L₀ * D - ‖g - gy x y‖)]
    have hbD : ‖g - clip c g‖ * D ≤ 2 * ‖g - gy x y‖ ^ 2 / c * D := mul_le_mul_of_nonneg_right hb hD
    simp only [U]
    have hβ2' : 0 ≤ β ^ 2 := sq_nonneg β
    have hsq : (β * ‖clip c g‖) ^ 2 = β ^ 2 * ‖clip c g‖ ^ 2 := by ring
    have h5 := mul_le_mul_of_nonneg_left hci (by positivity : (0 : ℝ) ≤ 2 * β)
    have h6 := mul_le_mul_of_nonneg_left hcn hβ2'
    have h7 := mul_le_mul_of_nonneg_left hbD (by positivity : (0 : ℝ) ≤ 2 * β)
    have e4 : 2 * β * (2 * ‖g - gy x y‖ ^ 2 / c * D) = 4 * β * D * ‖g - gy x y‖ ^ 2 / c := by ring
    have e5 : 2 * (β * ⟪y - ys, clip c g⟫) = 2 * β * ⟪y - ys, clip c g⟫ := by ring
    rw [hsq, e5]
    linarith
  have hUi : Integrable U p := by
    have h1 : Integrable (fun ω => ⟪oy x y ω, y - ys⟫) p := hgi.inner_const (y - ys)
    simp only [U]
    exact ((((integrable_const _).add (h1.const_mul _)).add ((hvi.const_mul (4 * β * D)).div_const c)).add
      ((((integrable_const (L₀ ^ 2 * D ^ 2)).add hvi)).const_mul _))
  have hQm : Measurable fun ω => ‖y + β • clip c (oy x y ω) - ys‖ ^ 2 :=
    ((measurable_const.add (((clip_measurable c).comp hmeas).const_smul β)).sub measurable_const).norm.pow_const 2
  have hQi : Integrable (fun ω => ‖y + β • clip c (oy x y ω) - ys‖ ^ 2) p :=
    Integrable.mono' hUi hQm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_of_nonneg (by positivity)]; exact hpt ω)
  refine ⟨hQi, (integral_mono hQi hUi hpt).trans ?_⟩
  have hinner : ∫ ω, ⟪oy x y ω, y - ys⟫ ∂p = ⟪gy x y, y - ys⟫ := by
    have e : (fun ω => ⟪oy x y ω, y - ys⟫) = fun ω => ⟪y - ys, oy x y ω⟫ :=
      funext fun ω => real_inner_comm _ _
    rw [e, integral_inner hgi, H.unbiased_y x y, real_inner_comm]
  have hneg := inner_grad_le H hμ x y
  have hvar := H.variance_y x y
  have hint : ∫ ω, U ω ∂p = D ^ 2 + 2 * β * ⟪gy x y, y - ys⟫ +
      4 * β * D * (∫ ω, ‖oy x y ω - gy x y‖ ^ 2 ∂p) / c +
      2 * β ^ 2 * (L₀ ^ 2 * D ^ 2 + ∫ ω, ‖oy x y ω - gy x y‖ ^ 2 ∂p) := by
    have h1 : Integrable (fun ω => ⟪oy x y ω, y - ys⟫) p := hgi.inner_const (y - ys)
    have hU' : U = fun ω => (D ^ 2 + 2 * β ^ 2 * L₀ ^ 2 * D ^ 2) + (2 * β) * ⟪oy x y ω, y - ys⟫ +
        (4 * β * D / c + 2 * β ^ 2) * ‖oy x y ω - gy x y‖ ^ 2 := by
      funext ω; simp only [U]; ring
    have hA : Integrable (fun ω => (D ^ 2 + 2 * β ^ 2 * L₀ ^ 2 * D ^ 2) + (2 * β) * ⟪oy x y ω, y - ys⟫) p :=
      (integrable_const _).add (h1.const_mul _)
    have hB : Integrable (fun ω => (4 * β * D / c + 2 * β ^ 2) * ‖oy x y ω - gy x y‖ ^ 2) p :=
      hvi.const_mul _
    rw [hU', integral_add hA hB, integral_add (integrable_const _) (h1.const_mul _), integral_const_mul,
      integral_const_mul, hinner]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    ring
  rw [hint]
  have hσ0 : 0 ≤ ∫ ω, ‖oy x y ω - gy x y‖ ^ 2 ∂p := integral_nonneg fun _ => by positivity
  have hamgm : 4 * β * D * σy ^ 2 / c ≤ β * μ / 2 * D ^ 2 + 8 * β * σy ^ 4 / (μ * c ^ 2) := by
    have key : β * μ / 2 * D ^ 2 + 8 * β * σy ^ 4 / (μ * c ^ 2) - 4 * β * D * σy ^ 2 / c =
        β * (μ * D * c - 4 * σy ^ 2) ^ 2 / (2 * μ * c ^ 2) := by field_simp; ring
    have : 0 ≤ β * (μ * D * c - 4 * σy ^ 2) ^ 2 / (2 * μ * c ^ 2) := by positivity
    linarith
  have hv1 : 4 * β * D * (∫ ω, ‖oy x y ω - gy x y‖ ^ 2 ∂p) / c ≤ 4 * β * D * σy ^ 2 / c := by
    gcongr
  have hv2 : 2 * β ^ 2 * (L₀ ^ 2 * D ^ 2 + ∫ ω, ‖oy x y ω - gy x y‖ ^ 2 ∂p) ≤
      2 * β ^ 2 * (L₀ ^ 2 * D ^ 2 + σy ^ 2) := by gcongr
  have hβL : 2 * β ^ 2 * L₀ ^ 2 * D ^ 2 ≤ β * μ * D ^ 2 := by
    have := mul_le_mul_of_nonneg_left hβ2 (mul_nonneg hβ (sq_nonneg D))
    nlinarith
  have hneg' : 2 * β * ⟪gy x y, y - ys⟫ ≤ -(2 * β * μ * D ^ 2) := by
    have := mul_le_mul_of_nonneg_left hneg (by positivity : (0 : ℝ) ≤ 2 * β)
    nlinarith
  nlinarith

set_option maxHeartbeats 1000000 in
theorem track_step_exp [IsProbabilityMeasure p] {β c κs a r₀ lam : ℝ} (hβ : 0 ≤ β)
    (hβ2 : 2 * β * L₀ ^ 2 ≤ μ) (hc : 0 < c) (hκs : 0 ≤ κs) (ha : 0 < a) (hlam : 0 ≤ lam)
    (hlamB : lam * (β * c + κs) ≤ 1) (x : Space d₁) (y : Space d₂) (hgy : ‖gy x y‖ ≤ c / 2)
    (hG : ‖gy x y‖ ≤ L₀ * ‖y - ystar H hμ x‖) (hDa : a ≤ ‖y - ystar H hμ x‖)
    (hDr : ‖y - ystar H hμ x‖ ≤ r₀)
    (hcond : (8 * β * σy ^ 4 / (μ * c ^ 2) + 2 * β ^ 2 * σy ^ 2) / (2 * a) + κs +
      lam * (4 * β ^ 2 * (L₀ ^ 2 * r₀ ^ 2 + σy ^ 2) + 2 * κs ^ 2) ≤ β * μ * a / 4) :
    Integrable (fun ω => Real.exp (lam * (‖y + β • clip c (oy x y ω) - ystar H hμ x‖ + κs))) p ∧
      ∫ ω, Real.exp (lam * (‖y + β • clip c (oy x y ω) - ystar H hμ x‖ + κs)) ∂p ≤
        Real.exp (lam * ‖y - ystar H hμ x‖) := by
  set ys := ystar H hμ x
  set D := ‖y - ys‖
  have hD : 0 < D := lt_of_lt_of_le ha hDa
  have hmeas : Measurable fun ω => oy x y ω := by
    have h2 : Measurable fun ω : Ω => (((x, y) : Space d₁ × Space d₂), ω) :=
      measurable_const.prodMk measurable_id
    exact H.measurable_y.comp h2
  have hvi := H.variance_y_integrable x y
  set Z : Ω → ℝ := fun ω => ‖y + β • clip c (oy x y ω) - ys‖
  have hZm : Measurable Z :=
    ((measurable_const.add (((clip_measurable c).comp hmeas).const_smul β)).sub measurable_const).norm
  set Δ' : Ω → ℝ := fun ω => Z ω + κs - D
  have hinc : ∀ ω, |Z ω - D| ≤ β * ‖clip c (oy x y ω)‖ := by
    intro ω
    have e : y + β • clip c (oy x y ω) - ys = (y - ys) + β • clip c (oy x y ω) := by abel
    simp only [Z]
    rw [e]
    have := abs_norm_sub_norm_le ((y - ys) + β • clip c (oy x y ω)) (y - ys)
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hβ] at this
    exact this
  have hcl : ∀ ω, ‖clip c (oy x y ω)‖ ≤ c := fun ω => clip_norm_le hc.le _
  have hΔabs : ∀ ω, |lam * Δ' ω| ≤ 1 := by
    intro ω
    have h1 := hinc ω
    have h2 : β * ‖clip c (oy x y ω)‖ ≤ β * c := mul_le_mul_of_nonneg_left (hcl ω) hβ
    have h3 : |Δ' ω| ≤ β * c + κs := by
      simp only [Δ']
      rw [show Z ω + κs - D = (Z ω - D) + κs by ring]
      exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hκs]; linarith)
    rw [abs_mul, abs_of_nonneg hlam]
    exact (mul_le_mul_of_nonneg_left h3 hlam).trans hlamB
  have hpt : ∀ ω, Real.exp (lam * (Z ω + κs)) ≤
      Real.exp (lam * D) * (1 + lam * Δ' ω + lam ^ 2 * Δ' ω ^ 2) := by
    intro ω
    have h := Real.abs_exp_sub_one_sub_id_le (hΔabs ω)
    have e : lam * (Z ω + κs) = lam * D + lam * Δ' ω := by simp only [Δ']; ring
    rw [e, Real.exp_add]
    have h2 : Real.exp (lam * Δ' ω) ≤ 1 + lam * Δ' ω + lam ^ 2 * Δ' ω ^ 2 := by
      have := (abs_le.mp h).2
      nlinarith
    exact mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  have hsq := track_step_sq H hμ hβ hβ2 hc x y hgy hG
  have hZ2 : Integrable (fun ω => Z ω ^ 2) p := hsq.1
  have hZi : Integrable Z p := by
    refine Integrable.mono' ((hZ2.add (integrable_const 1))) hZm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (Z ω - 1), norm_nonneg (y + β • clip c (oy x y ω) - ys)]
  have hΔi : Integrable Δ' p := (hZi.add (integrable_const _)).sub (integrable_const _)
  have hΔ2b : ∀ ω, Δ' ω ^ 2 ≤ 4 * β ^ 2 * (L₀ ^ 2 * D ^ 2 + ‖oy x y ω - gy x y‖ ^ 2) + 2 * κs ^ 2 := by
    intro ω
    have h1 := hinc ω
    have hcn : ‖clip c (oy x y ω)‖ ^ 2 ≤ 2 * (L₀ ^ 2 * D ^ 2 + ‖oy x y ω - gy x y‖ ^ 2) := by
      have h1 := clip_norm_le' hc.le (oy x y ω)
      have h2 : ‖oy x y ω‖ ≤ ‖gy x y‖ + ‖oy x y ω - gy x y‖ := by
        have := norm_add_le (gy x y) (oy x y ω - gy x y); rwa [add_sub_cancel] at this
      have h3 : ‖clip c (oy x y ω)‖ ≤ L₀ * D + ‖oy x y ω - gy x y‖ := by linarith
      have h4 := norm_nonneg (clip c (oy x y ω))
      nlinarith [sq_nonneg (L₀ * D - ‖oy x y ω - gy x y‖)]
    have h5 : (Z ω - D) ^ 2 ≤ β ^ 2 * ‖clip c (oy x y ω)‖ ^ 2 := by
      have := sq_le_sq' (neg_le_of_abs_le h1) (le_of_abs_le h1)
      nlinarith
    simp only [Δ']
    nlinarith [sq_nonneg (Z ω - D - κs), mul_le_mul_of_nonneg_left hcn (sq_nonneg β)]
  have hΔ2m : Measurable fun ω => Δ' ω ^ 2 := ((hZm.add measurable_const).sub measurable_const).pow_const 2
  have hBi : Integrable (fun ω => 4 * β ^ 2 * (L₀ ^ 2 * D ^ 2 + ‖oy x y ω - gy x y‖ ^ 2) + 2 * κs ^ 2) p :=
    (((integrable_const _).add hvi).const_mul _).add (integrable_const _)
  have hΔ2i : Integrable (fun ω => Δ' ω ^ 2) p :=
    Integrable.mono' hBi hΔ2m.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hΔ2b ω)
  have hEm : Measurable fun ω => Real.exp (lam * (Z ω + κs)) :=
    Real.measurable_exp.comp ((hZm.add measurable_const).const_mul lam)
  have hEi : Integrable (fun ω => Real.exp (lam * (Z ω + κs))) p := by
    refine Integrable.of_bound hEm.aestronglyMeasurable (Real.exp (lam * D + 1))
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
    have := (abs_le.mp (hΔabs ω)).2
    have e : lam * (Z ω + κs) = lam * D + lam * Δ' ω := by simp only [Δ']; ring
    linarith
  refine ⟨hEi, ?_⟩
  have hRi : Integrable (fun ω => Real.exp (lam * D) * (1 + lam * Δ' ω + lam ^ 2 * Δ' ω ^ 2)) p :=
    (((integrable_const 1).add (hΔi.const_mul lam)).add (hΔ2i.const_mul (lam ^ 2))).const_mul _
  have hmono := integral_mono hEi hRi hpt
  have hcalc : ∫ ω, Real.exp (lam * D) * (1 + lam * Δ' ω + lam ^ 2 * Δ' ω ^ 2) ∂p =
      Real.exp (lam * D) * (1 + lam * ∫ ω, Δ' ω ∂p + lam ^ 2 * ∫ ω, Δ' ω ^ 2 ∂p) := by
    have hA : Integrable (fun ω => 1 + lam * Δ' ω) p := (integrable_const 1).add (hΔi.const_mul lam)
    rw [integral_const_mul, integral_add hA (hΔ2i.const_mul (lam ^ 2)), integral_add (integrable_const 1)
      (hΔi.const_mul lam), integral_const_mul, integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [hcalc] at hmono
  set E₁ := 8 * β * σy ^ 4 / (μ * c ^ 2) + 2 * β ^ 2 * σy ^ 2
  have hjen : ∫ ω, Z ω ∂p ≤ Real.sqrt (∫ ω, Z ω ^ 2 ∂p) :=
    OracleTemplate.NormalizedStorm.integral_norm_le_sqrt
      ((measurable_const.add (((clip_measurable c).comp hmeas).const_smul β)).sub
        measurable_const).aestronglyMeasurable hZ2
  have hA0 : 0 ≤ ∫ ω, Z ω ^ 2 ∂p := integral_nonneg fun _ => sq_nonneg _
  have hsqrt : Real.sqrt (∫ ω, Z ω ^ 2 ∂p) ≤ (∫ ω, Z ω ^ 2 ∂p + D ^ 2) / (2 * D) := by
    rw [le_div_iff₀ (by positivity)]
    have := Real.sq_sqrt hA0
    nlinarith [sq_nonneg (Real.sqrt (∫ ω, Z ω ^ 2 ∂p) - D)]
  have hZ2b : ∫ ω, Z ω ^ 2 ∂p ≤ (1 - β * μ / 2) * D ^ 2 + E₁ := by
    have := hsq.2; simp only [E₁, Z, ys, D] at this ⊢; linarith
  have hfirst : ∫ ω, Δ' ω ∂p ≤ -(β * μ * a / 4) + E₁ / (2 * a) + κs := by
    have hint : ∫ ω, Δ' ω ∂p = ∫ ω, Z ω ∂p + κs - D := by
      simp only [Δ']
      have hZκ : Integrable (fun ω => Z ω + κs) p := hZi.add (integrable_const κs)
      rw [integral_sub hZκ (integrable_const D), integral_add hZi (integrable_const κs)]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [hint]
    have h1 : (∫ ω, Z ω ^ 2 ∂p + D ^ 2) / (2 * D) ≤ D - β * μ * D / 4 + E₁ / (2 * D) := by
      rw [div_le_iff₀ (by positivity)]
      have : (D - β * μ * D / 4 + E₁ / (2 * D)) * (2 * D) = 2 * D ^ 2 - β * μ * D ^ 2 / 2 + E₁ := by
        field_simp; ring
      rw [this]; linarith
    have h2 : E₁ / (2 * D) ≤ E₁ / (2 * a) := by
      have hE : 0 ≤ E₁ := by positivity
      exact div_le_div_of_nonneg_left hE (by positivity) (by linarith)
    have h3 : β * μ * a / 4 ≤ β * μ * D / 4 := by
      have : 0 ≤ β * μ := mul_nonneg hβ hμ.le
      nlinarith
    linarith
  have hsecond : ∫ ω, Δ' ω ^ 2 ∂p ≤ 4 * β ^ 2 * (L₀ ^ 2 * r₀ ^ 2 + σy ^ 2) + 2 * κs ^ 2 := by
    have h := integral_mono hΔ2i hBi hΔ2b
    have hcalc2 : ∫ ω, (4 * β ^ 2 * (L₀ ^ 2 * D ^ 2 + ‖oy x y ω - gy x y‖ ^ 2) + 2 * κs ^ 2) ∂p =
        4 * β ^ 2 * (L₀ ^ 2 * D ^ 2 + ∫ ω, ‖oy x y ω - gy x y‖ ^ 2 ∂p) + 2 * κs ^ 2 := by
      have hC : Integrable (fun ω => 4 * β ^ 2 * (L₀ ^ 2 * D ^ 2 + ‖oy x y ω - gy x y‖ ^ 2)) p :=
        ((integrable_const _).add hvi).const_mul _
      have hC2 : Integrable (fun ω => L₀ ^ 2 * D ^ 2 + ‖oy x y ω - gy x y‖ ^ 2) p :=
        (integrable_const _).add hvi
      rw [integral_add hC (integrable_const _), integral_const_mul, integral_add (integrable_const _) hvi]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [hcalc2] at h
    have hv := H.variance_y x y
    have hDr2 : L₀ ^ 2 * D ^ 2 ≤ L₀ ^ 2 * r₀ ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD.le hDr 2) (sq_nonneg _)
    nlinarith [sq_nonneg β]
  have hneg : lam * ∫ ω, Δ' ω ∂p + lam ^ 2 * ∫ ω, Δ' ω ^ 2 ∂p ≤ 0 := by
    have h1 := mul_le_mul_of_nonneg_left hfirst hlam
    have h2 := mul_le_mul_of_nonneg_left hsecond (sq_nonneg lam)
    have h3 := mul_le_mul_of_nonneg_left hcond hlam
    have e : lam ^ 2 * (4 * β ^ 2 * (L₀ ^ 2 * r₀ ^ 2 + σy ^ 2) + 2 * κs ^ 2) =
        lam * (lam * (4 * β ^ 2 * (L₀ ^ 2 * r₀ ^ 2 + σy ^ 2) + 2 * κs ^ 2)) := by ring
    nlinarith
  have hfin : Real.exp (lam * D) * (1 + lam * ∫ ω, Δ' ω ∂p + lam ^ 2 * ∫ ω, Δ' ω ^ 2 ∂p) ≤ Real.exp (lam * D) := by
    have := Real.exp_pos (lam * D)
    nlinarith
  exact hmono.trans hfin

end Step

section Continuity

variable {d₁ d₂ : ℕ} {Ω : Type} [MeasurableSpace Ω] {N : Seminorm ℝ (Space d₁)}
  {L₀ L₁ μ σx σy Δ W : ℝ} {x₁ : Space d₁} {y₁ : Space d₂} {f : Space d₁ → Space d₂ → ℝ}
  {gx : Space d₁ → Space d₂ → Space d₁} {gy : Space d₁ → Space d₂ → Space d₂}
  {ox : Space d₁ → Space d₂ → Ω → Space d₁} {oy : Space d₁ → Space d₂ → Ω → Space d₂} {p : Measure Ω}

variable (H : GeneralizedMinimax N L₀ L₁ μ σx σy Δ W x₁ y₁ f gx gy ox oy p) (hμ : 0 < μ)
include H

lemma ystar_continuous (hL₀ : 0 ≤ L₀) (hL₁ : 0 ≤ L₁) : Continuous (ystar H hμ) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  set S := ∑ i, N (EuclideanSpace.single i (1 : ℝ)) + 1
  have hS : 0 < S := by
    have : 0 ≤ ∑ i, N (EuclideanSpace.single i (1 : ℝ)) := Finset.sum_nonneg fun i _ => apply_nonneg N _
    positivity
  set r := min (1 / ((L₁ + 1) * S)) (ε / ((L₀ / μ + 1) * S))
  have hr : 0 < r := lt_min (by positivity) (by have := div_nonneg hL₀ hμ.le; positivity)
  refine ⟨r, hr, fun x' hx' => ?_⟩
  rw [dist_eq_norm] at hx' ⊢
  have hN : N (x' - x) ≤ S * r := by
    have h1 := OracleTemplate.NormBallLMO.seminorm_le_norm N (x' - x)
    have h2 : (∑ i, N (EuclideanSpace.single i (1 : ℝ))) * ‖x' - x‖ ≤ S * r := by
      have : 0 ≤ ∑ i, N (EuclideanSpace.single i (1 : ℝ)) := Finset.sum_nonneg fun i _ => apply_nonneg N _
      calc (∑ i, N (EuclideanSpace.single i (1 : ℝ))) * ‖x' - x‖ ≤ S * ‖x' - x‖ :=
            mul_le_mul_of_nonneg_right (by simp only [S]; linarith) (norm_nonneg _)
        _ ≤ S * r := mul_le_mul_of_nonneg_left hx'.le hS.le
    linarith
  have hloc : L₁ * N (x' - x) ≤ 1 := by
    have h1 : S * r ≤ 1 / (L₁ + 1) := by
      have := min_le_left (1 / ((L₁ + 1) * S)) (ε / ((L₀ / μ + 1) * S))
      calc S * r ≤ S * (1 / ((L₁ + 1) * S)) := mul_le_mul_of_nonneg_left this hS.le
        _ = 1 / (L₁ + 1) := by field_simp
    have h2 : L₁ * (1 / (L₁ + 1)) ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
    nlinarith [mul_le_mul_of_nonneg_left (hN.trans h1) hL₁]
  have hy := ystar_lip H hμ x' x hloc
  have hκ : 0 ≤ L₀ / μ := div_nonneg hL₀ hμ.le
  have h3 : S * r ≤ ε / (L₀ / μ + 1) := by
    have := min_le_right (1 / ((L₁ + 1) * S)) (ε / ((L₀ / μ + 1) * S))
    calc S * r ≤ S * (ε / ((L₀ / μ + 1) * S)) := mul_le_mul_of_nonneg_left this hS.le
      _ = ε / (L₀ / μ + 1) := by field_simp
  calc ‖ystar H hμ x' - ystar H hμ x‖ ≤ L₀ / μ * N (x' - x) := hy
    _ ≤ L₀ / μ * (ε / (L₀ / μ + 1)) := mul_le_mul_of_nonneg_left (hN.trans h3) hκ
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith

end Continuity

end OracleTemplate.MinimaxLmo
