import LongTails.Proofs.LookaheadMomentumMoments
import LongTails.Proofs.GdConvex

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.LookaheadMomentum

open OracleTemplate.CompositeTransport (OracleHyp)

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {f : E → ℝ} {grad : E → E} {L σ Δ D ε : ℝ} {g : E → Ω → E} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

structure CfgHyp (cfg : Config) (L σ Δ D ε : ℝ) : Prop where
  n0 : 1 ≤ cfg.n0
  γ0 : 0 < cfg.γ
  γ1 : cfg.γ ≤ 1
  η0 : 0 < cfg.η
  ε0 : 0 < ε
  bias : 2 * (D / (1 - keep cfg)) ≤ ε / 4
  smooth : L / 2 * cfg.η ≤ ε / 4
  noise : 10 * (σ ^ 2 / cfg.n0 + 5 * cfg.γ * σ ^ 2) / ε ≤ ε / 5
  horizon : Δ / cfg.η ≤ (cfg.T + 1) * (ε / 5)
  Δ0 : 0 ≤ Δ

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma keep_bounds {cfg : Config} (hγ : 0 < cfg.γ) (hγ1 : cfg.γ ≤ 1) :
    0 ≤ keep cfg ∧ keep cfg < 1 := by
  unfold keep
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hγ1) (by linarith : (0 : ℝ) ≤ 2 - cfg.γ)]
  · nlinarith [mul_pos hγ (by linarith : (0 : ℝ) < 3 - cfg.γ)]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma normalized_descent (hL : 0 ≤ L) (hg : ∀ x, HasGradientAt f (grad x) x)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖) (cfg : Config) (hη : 0 ≤ cfg.η) (x m : E) :
    f (stepTo cfg x m) ≤ f x - cfg.η * ‖grad x‖ + 2 * cfg.η * ‖m - grad x‖ + L / 2 * cfg.η ^ 2 := by
  have hup := OracleTemplate.Gradient.smooth_upper_bound hg hlip x (stepTo cfg x m)
  have hmove := stepTo_move (cfg := cfg) hη x m
  have hsq : L / 2 * ‖stepTo cfg x m - x‖ ^ 2 ≤ L / 2 * cfg.η ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hmove 2) (by positivity)
  have hinner : ⟪grad x, stepTo cfg x m - x⟫ ≤ -(cfg.η * ‖grad x‖) + 2 * cfg.η * ‖m - grad x‖ := by
    by_cases hm : ‖m‖ = 0
    · have hm0 : m = 0 := norm_eq_zero.mp hm
      have hst : stepTo cfg x m - x = 0 := by simp [stepTo, hm0]
      rw [hst, inner_zero_right, hm0, zero_sub, norm_neg]
      nlinarith [norm_nonneg (grad x)]
    · have hmpos : 0 < ‖m‖ := lt_of_le_of_ne (norm_nonneg m) (Ne.symm hm)
      have hst : stepTo cfg x m - x = -((cfg.η / ‖m‖) • m) := by simp [stepTo]
      rw [hst, inner_neg_right, inner_smul_right]
      have h1 : ⟪grad x, m⟫ = ‖m‖ ^ 2 - ⟪m - grad x, m⟫ := by
        rw [inner_sub_left, real_inner_self_eq_norm_sq]; ring
      have h2 : ⟪m - grad x, m⟫ ≤ ‖m - grad x‖ * ‖m‖ := real_inner_le_norm _ _
      have h3 : ‖grad x‖ ≤ ‖m‖ + ‖m - grad x‖ := by
        have := norm_sub_le m (m - grad x)
        rwa [sub_sub_cancel] at this
      have h4 : cfg.η / ‖m‖ * ⟪grad x, m⟫ ≥ cfg.η * ‖m‖ - cfg.η * ‖m - grad x‖ := by
        have e : cfg.η * ‖m‖ - cfg.η * ‖m - grad x‖ =
            cfg.η / ‖m‖ * (‖m‖ ^ 2 - ‖m - grad x‖ * ‖m‖) := by field_simp
        rw [e, ge_iff_le]
        exact mul_le_mul_of_nonneg_left (by rw [h1]; linarith) (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left h3 hη]
  linarith

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma path_sum (hL : 0 ≤ L) (hg : ∀ x, HasGradientAt f (grad x) x)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {cfg : Config} (hc : CfgHyp cfg L σ Δ D ε) {x0 : E}
    (hD : ∀ x x' : E, ‖x' - x‖ ≤ cfg.η → ‖drift cfg grad x x'‖ ≤ D)
    (hΔ : ∀ x, f x0 - f x ≤ Δ) (ξ : ℕ → Ω) :
    ∑ t ∈ Finset.range (cfg.T + 1), ‖grad (traj cfg x0 g ξ t).1‖ ≤
      Δ / cfg.η + ∑ t ∈ Finset.range (cfg.T + 1),
        (10 / ε * ‖noise cfg x0 g grad ξ t‖ ^ 2 + (ε / 10 + ε / 4 + ε / 4)) := by
  obtain ⟨hk0, hk1⟩ := keep_bounds hc.γ0 hc.γ1
  set B := D / (1 - keep cfg)
  set X := fun t => (traj cfg x0 g ξ t).1
  have hε := hc.ε0
  have hη := hc.η0
  have hstep : ∀ t, ‖grad (X t)‖ ≤ (f (X t) - f (X (t + 1))) / cfg.η +
      (10 / ε * ‖noise cfg x0 g grad ξ t‖ ^ 2 + (ε / 10 + ε / 4 + ε / 4)) := by
    intro t
    have hd := normalized_descent hL hg hlip cfg hη.le (X t) (traj cfg x0 g ξ t).2.2
    have hX1 : X (t + 1) = stepTo cfg (X t) (traj cfg x0 g ξ t).2.2 := traj_succ_fst cfg x0 g ξ t
    rw [← hX1] at hd
    have hsplit := error_split cfg x0 g grad ξ hc.n0 t
    have hB := bias_bound (x0 := x0) (g := g) hk0 hk1 hη.le hD ξ t
    have he : ‖(traj cfg x0 g ξ t).2.2 - grad (X t)‖ ≤ ‖noise cfg x0 g grad ξ t‖ + B := by
      change ‖(traj cfg x0 g ξ t).2.2 - grad (traj cfg x0 g ξ t).1‖ ≤ _
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add le_rfl hB)
    have hn : 2 * ‖noise cfg x0 g grad ξ t‖ ≤ 10 / ε * ‖noise cfg x0 g grad ξ t‖ ^ 2 + ε / 10 := by
      have h0 := sq_nonneg (10 * ‖noise cfg x0 g grad ξ t‖ - ε)
      have e : 10 / ε * ‖noise cfg x0 g grad ξ t‖ ^ 2 + ε / 10 - 2 * ‖noise cfg x0 g grad ξ t‖ =
          (10 * ‖noise cfg x0 g grad ξ t‖ - ε) ^ 2 / (10 * ε) := by field_simp; ring
      have : 0 ≤ (10 * ‖noise cfg x0 g grad ξ t‖ - ε) ^ 2 / (10 * ε) := by positivity
      linarith
    have hdiv : ‖grad (X t)‖ ≤ (f (X t) - f (X (t + 1))) / cfg.η +
        2 * ‖(traj cfg x0 g ξ t).2.2 - grad (X t)‖ + L / 2 * cfg.η := by
      rw [div_add' _ _ _ hη.ne', div_add' _ _ _ hη.ne', le_div_iff₀ hη]
      nlinarith
    have hb := hc.bias
    have hs := hc.smooth
    linarith
  calc ∑ t ∈ Finset.range (cfg.T + 1), ‖grad (X t)‖
      ≤ ∑ t ∈ Finset.range (cfg.T + 1), ((f (X t) - f (X (t + 1))) / cfg.η +
          (10 / ε * ‖noise cfg x0 g grad ξ t‖ ^ 2 + (ε / 10 + ε / 4 + ε / 4))) :=
        Finset.sum_le_sum fun t _ => hstep t
    _ = (f (X 0) - f (X (cfg.T + 1))) / cfg.η + ∑ t ∈ Finset.range (cfg.T + 1),
          (10 / ε * ‖noise cfg x0 g grad ξ t‖ ^ 2 + (ε / 10 + ε / 4 + ε / 4)) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_range_sub' (fun t => f (X t))]
    _ ≤ Δ / cfg.η + ∑ t ∈ Finset.range (cfg.T + 1),
          (10 / ε * ‖noise cfg x0 g grad ξ t‖ ^ 2 + (ε / 10 + ε / 4 + ε / 4)) := by
        gcongr
        exact hΔ (X (cfg.T + 1))

lemma expected_bound (hL : 0 ≤ L) (hg : ∀ x, HasGradientAt f (grad x) x)
    (hlip : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖)
    {cfg : Config} (hc : CfgHyp cfg L σ Δ D ε) {x0 : E}
    (hD : ∀ x x' : E, ‖x' - x‖ ≤ cfg.η → ‖drift cfg grad x x'‖ ≤ D)
    (hΔ : ∀ x, f x0 - f x ≤ Δ) (O : OracleHyp g grad μ σ) :
    Measurable (fun ω : Fin (cfg.T + 1) × (ℕ → Ω) => (traj cfg x0 g ω.2 ω.1.val).1) ∧
    ∫⁻ ω, ENNReal.ofReal ‖grad (traj cfg x0 g ω.2 ω.1.val).1‖
      ∂((PMF.uniformOfFintype (Fin (cfg.T + 1))).toMeasure.prod (Measure.infinitePi fun _ : ℕ => μ)) ≤
      ENNReal.ofReal ε := by
  set P := Measure.infinitePi fun _ : ℕ => μ
  set ν := (PMF.uniformOfFintype (Fin (cfg.T + 1))).toMeasure
  have hgrad : Continuous grad := by
    have : LipschitzWith (Real.toNNReal L) grad := LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL]; exact hlip a b
    exact this.continuous
  set Gm : E → ℝ := fun x => ‖grad x‖
  have hGm : Measurable Gm := hgrad.measurable.norm
  have htraj : ∀ t, Measurable (fun ξ : ℕ → Ω => (traj cfg x0 g ξ t).1) :=
    fun t => measurable_fst.comp (measurable_traj cfg x0 g O.meas t)
  have hout : Measurable (fun ω : Fin (cfg.T + 1) × (ℕ → Ω) => (traj cfg x0 g ω.2 ω.1.val).1) :=
    measurable_from_prod_countable_right fun τ => htraj τ.val
  refine ⟨hout, ?_⟩
  change ∫⁻ ω, ENNReal.ofReal (Gm (traj cfg x0 g ω.2 ω.1.val).1) ∂(ν.prod P) ≤ _
  have hmeas : Measurable (fun ω : Fin (cfg.T + 1) × (ℕ → Ω) =>
      ENNReal.ofReal (Gm (traj cfg x0 g ω.2 ω.1.val).1)) :=
    ENNReal.measurable_ofReal.comp (hGm.comp hout)
  rw [lintegral_prod _ hmeas.aemeasurable, lintegral_fintype]
  have hsing : ∀ τ : Fin (cfg.T + 1), ν {τ} = ((cfg.T + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    intro τ
    simp only [ν]
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton τ), PMF.uniformOfFintype_apply,
      Fintype.card_fin]
  simp_rw [hsing]
  rw [← Finset.sum_mul]
  have hε := hc.ε0
  have hη := hc.η0
  have hΔ0 := hc.Δ0
  have hT : (0 : ℝ) < cfg.T + 1 := by positivity
  have hpt : ∀ ξ : ℕ → Ω, ENNReal.ofReal (∑ t ∈ Finset.range (cfg.T + 1), Gm (traj cfg x0 g ξ t).1) =
      ∑ τ : Fin (cfg.T + 1), ENNReal.ofReal (Gm (traj cfg x0 g ξ τ.val).1) := by
    intro ξ
    rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => norm_nonneg _)]
    exact (Fin.sum_univ_eq_sum_range (fun t => ENNReal.ofReal (Gm (traj cfg x0 g ξ t).1)) _).symm
  have hsum : ∑ τ : Fin (cfg.T + 1), ∫⁻ ξ, ENNReal.ofReal (Gm (traj cfg x0 g ξ τ.val).1) ∂P =
      ∫⁻ ξ, ENNReal.ofReal (∑ t ∈ Finset.range (cfg.T + 1), Gm (traj cfg x0 g ξ t).1) ∂P := by
    rw [← lintegral_finsetSum (f := fun (τ : Fin (cfg.T + 1)) ξ =>
      ENNReal.ofReal (Gm (traj cfg x0 g ξ τ.val).1)) _
      (fun (τ : Fin (cfg.T + 1)) _ => ENNReal.measurable_ofReal.comp (hGm.comp (htraj τ.val)))]
    exact lintegral_congr fun ξ => (hpt ξ).symm
  rw [hsum]
  set c := 10 / ε
  set M := σ ^ 2 / cfg.n0 + 5 * cfg.γ * σ ^ 2
  set A := Δ / cfg.η + (cfg.T + 1) * (ε / 10 + ε / 4 + ε / 4)
  have hc0 : 0 ≤ c := by positivity
  have hM0 : 0 ≤ M := by have := sq_nonneg σ; have := hc.γ0; positivity
  have hA0 : 0 ≤ A := by positivity
  have hpath : ∀ ξ, ENNReal.ofReal (∑ t ∈ Finset.range (cfg.T + 1), Gm (traj cfg x0 g ξ t).1) ≤
      ENNReal.ofReal A + ENNReal.ofReal c *
        ∑ t ∈ Finset.range (cfg.T + 1), ENNReal.ofReal (‖noise cfg x0 g grad ξ t‖ ^ 2) := by
    intro ξ
    have h := path_sum hL hg hlip hc hD hΔ ξ (g := g)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => sq_nonneg _), ← ENNReal.ofReal_mul hc0,
      ← ENNReal.ofReal_add hA0 (mul_nonneg hc0 (Finset.sum_nonneg fun t _ => sq_nonneg _))]
    refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
    simp only [A, c]
    push_cast
    ring
  have hM := noise_moment cfg x0 O hgrad hc.n0 hc.γ0 hc.γ1 (μ := μ)
  have hY : ∫⁻ ξ, ENNReal.ofReal (∑ t ∈ Finset.range (cfg.T + 1), Gm (traj cfg x0 g ξ t).1) ∂P ≤
      ENNReal.ofReal (A + c * ((cfg.T + 1) * M)) := by
    refine (lintegral_mono hpath).trans ?_
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_finsetSum (f := fun t ξ => ENNReal.ofReal (‖noise cfg x0 g grad ξ t‖ ^ 2)) _
        (fun t _ => ENNReal.measurable_ofReal.comp
          ((measurable_noise cfg x0 O hgrad t).norm.pow_const 2))]
    have hs : ∑ t ∈ Finset.range (cfg.T + 1), ∫⁻ ξ, ENNReal.ofReal (‖noise cfg x0 g grad ξ t‖ ^ 2) ∂P ≤
        ENNReal.ofReal ((cfg.T + 1) * M) := by
      calc ∑ t ∈ Finset.range (cfg.T + 1), ∫⁻ ξ, ENNReal.ofReal (‖noise cfg x0 g grad ξ t‖ ^ 2) ∂P
          ≤ ∑ t ∈ Finset.range (cfg.T + 1), ENNReal.ofReal M := Finset.sum_le_sum fun t _ => hM t
        _ = ENNReal.ofReal (∑ t ∈ Finset.range (cfg.T + 1), M) :=
            (ENNReal.ofReal_sum_of_nonneg fun _ _ => hM0).symm
        _ = ENNReal.ofReal ((cfg.T + 1) * M) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring_nf
    calc ENNReal.ofReal A + ENNReal.ofReal c * ∑ t ∈ Finset.range (cfg.T + 1),
          ∫⁻ ξ, ENNReal.ofReal (‖noise cfg x0 g grad ξ t‖ ^ 2) ∂P
        ≤ ENNReal.ofReal A + ENNReal.ofReal c * ENNReal.ofReal ((cfg.T + 1) * M) := by gcongr
      _ = ENNReal.ofReal (A + c * ((cfg.T + 1) * M)) := by
          rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add hA0 (by positivity)]
  have hinv : ((cfg.T + 1 : ℕ) : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / (cfg.T + 1)) := by
    rw [ENNReal.ofReal_div_of_pos hT, ENNReal.ofReal_one, one_div]
    congr 1
    rw [show ((cfg.T : ℝ) + 1) = ((cfg.T + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  rw [hinv]
  have hreal : (A + c * ((cfg.T + 1) * M)) * (1 / (cfg.T + 1)) ≤ ε := by
    rw [mul_one_div, div_le_iff₀ hT]
    have h1 := hc.horizon
    have h2 := mul_le_mul_of_nonneg_left hc.noise hT.le
    have e2 : A + c * ((cfg.T + 1) * M) = Δ / cfg.η + (cfg.T + 1) * (ε / 10 + ε / 4 + ε / 4) +
        (cfg.T + 1) * (10 * (σ ^ 2 / cfg.n0 + 5 * cfg.γ * σ ^ 2) / ε) := by
      simp only [A, c, M]; ring
    rw [e2]
    nlinarith
  calc (∫⁻ ξ, ENNReal.ofReal (∑ t ∈ Finset.range (cfg.T + 1), Gm (traj cfg x0 g ξ t).1) ∂P) *
        ENNReal.ofReal (1 / (cfg.T + 1))
      ≤ ENNReal.ofReal (A + c * ((cfg.T + 1) * M)) * ENNReal.ofReal (1 / (cfg.T + 1)) := by gcongr
    _ = ENNReal.ofReal ((A + c * ((cfg.T + 1) * M)) * (1 / (cfg.T + 1))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hreal

end OracleTemplate.LookaheadMomentum
