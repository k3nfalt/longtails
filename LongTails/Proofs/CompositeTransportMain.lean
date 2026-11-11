import LongTails.Proofs.CompositeTransportBound

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.CompositeTransport

open OracleTemplate.SampledComposite

variable {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω]
  {f : E → ℝ} {grad : E → E} {hess : E → E →L[ℝ] E} {ψ : E → ℝ} {Q : Set E}
  {prox : ℝ → E → E → E} {L ρ σ Δ : ℝ} {g : E → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]

structure CfgHyp (cfg : Config) (L ρ σ Δ : ℝ) : Prop where
  n0 : 1 ≤ cfg.n0
  α0 : 0 < cfg.α
  α1 : cfg.α ≤ 1
  γ0 : 0 < cfg.γ
  γL : cfg.γ * L ≤ 1
  ε0 : 0 < cfg.ε
  noise : 20 * ((ρ * (2 * cfg.γ * cfg.ε) ^ 2 / cfg.α ^ 2) ^ 2 + σ ^ 2 / cfg.n0 + cfg.α * σ ^ 2) / cfg.ε ≤
    cfg.ε / 2
  horizon : Δ / (cfg.γ * cfg.ε) ≤ (cfg.T + 1) * cfg.ε
  Δ0 : 0 ≤ Δ

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace Ω] in
lemma path_sum (H : PathHyp f grad ψ Q prox L) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hd : ∀ x, HasFDerivAt grad (hess x) x) (hl : ∀ x y, ‖hess x - hess y‖ ≤ ρ * ‖x - y‖)
    {cfg : Config} (hc : CfgHyp cfg L ρ σ Δ) {x0 : E} (hx0 : x0 ∈ Q)
    (hΔ : ∀ x ∈ Q, f x0 + ψ x0 - (f x + ψ x) ≤ Δ) (ξ : ℕ → Ω) :
    ∑ t ∈ Finset.range (cfg.T + 1), ‖L • ((traj cfg x0 g prox ξ t).1 -
        prox (1 / L) (traj cfg x0 g prox ξ t).1 (grad (traj cfg x0 g prox ξ t).1))‖ ≤
      Δ / (cfg.γ * cfg.ε) + ∑ t ∈ Finset.range (cfg.T + 1),
        (20 * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 / cfg.ε +
          (20 * (ρ * (2 * cfg.γ * cfg.ε) ^ 2 / cfg.α ^ 2) ^ 2 / cfg.ε + 11 / 8 * cfg.ε)) := by
  set B := ρ * (2 * cfg.γ * cfg.ε) ^ 2 / cfg.α ^ 2
  set X := fun t => (traj cfg x0 g prox ξ t).1
  set Fv := fun t => f (X t) + ψ (X t)
  have hstep : ∀ t, ‖L • (X t - prox (1 / L) (X t) (grad (X t)))‖ ≤
      (Fv t - Fv (t + 1)) / (cfg.γ * cfg.ε) +
        (20 * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 / cfg.ε + (20 * B ^ 2 / cfg.ε + 11 / 8 * cfg.ε)) := by
    intro t
    have hb := step_bound H hL cfg hc.γ0 hc.γL hc.ε0 (traj_mem H cfg hc.γ0 hc.ε0 hx0 g ξ t)
      (m := (traj cfg x0 g prox ξ t).2.2)
    have hX1 : X (t + 1) = capStep cfg (X t) (prox cfg.γ (X t) (traj cfg x0 g prox ξ t).2.2) :=
      traj_succ_fst cfg x0 g prox ξ t
    have hsplit := error_split cfg x0 g grad prox ξ hc.n0 t
    have hB := bias_bound (x0 := x0) (g := g) (prox := prox) hρ hd hl hc.α0 hc.α1 hc.γ0 hc.ε0 ξ t
    have he : ‖grad (X t) - (traj cfg x0 g prox ξ t).2.2‖ ^ 2 ≤
        2 * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 + 2 * B ^ 2 := by
      rw [norm_sub_rev]
      change ‖(traj cfg x0 g prox ξ t).2.2 - grad (traj cfg x0 g prox ξ t).1‖ ^ 2 ≤ _
      rw [hsplit]
      have hsq := pow_le_pow_left₀ (norm_nonneg _)
        (norm_add_le (noise cfg x0 g grad prox ξ t) (bias cfg x0 g grad prox ξ t)) 2
      have hb2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
      have h0 := norm_nonneg (noise cfg x0 g grad prox ξ t)
      have h1 := norm_nonneg (bias cfg x0 g grad prox ξ t)
      nlinarith [sq_nonneg (‖noise cfg x0 g grad prox ξ t‖ - ‖bias cfg x0 g grad prox ξ t‖)]
    simp only [Fv]
    rw [hX1]
    refine hb.trans ?_
    have : 10 * ‖grad (X t) - (traj cfg x0 g prox ξ t).2.2‖ ^ 2 / cfg.ε ≤
        20 * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 / cfg.ε + 20 * B ^ 2 / cfg.ε := by
      have e : 20 * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 / cfg.ε + 20 * B ^ 2 / cfg.ε =
          (20 * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 + 20 * B ^ 2) / cfg.ε := by ring
      rw [e]
      exact div_le_div_of_nonneg_right (by linarith) hc.ε0.le
    linarith
  have hγε : 0 < cfg.γ * cfg.ε := mul_pos hc.γ0 hc.ε0
  calc ∑ t ∈ Finset.range (cfg.T + 1), ‖L • (X t - prox (1 / L) (X t) (grad (X t)))‖
      ≤ ∑ t ∈ Finset.range (cfg.T + 1), ((Fv t - Fv (t + 1)) / (cfg.γ * cfg.ε) +
          (20 * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 / cfg.ε + (20 * B ^ 2 / cfg.ε + 11 / 8 * cfg.ε))) :=
        Finset.sum_le_sum fun t _ => hstep t
    _ = (Fv 0 - Fv (cfg.T + 1)) / (cfg.γ * cfg.ε) + ∑ t ∈ Finset.range (cfg.T + 1),
          (20 * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 / cfg.ε + (20 * B ^ 2 / cfg.ε + 11 / 8 * cfg.ε)) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_range_sub' Fv]
    _ ≤ Δ / (cfg.γ * cfg.ε) + ∑ t ∈ Finset.range (cfg.T + 1),
          (20 * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 / cfg.ε + (20 * B ^ 2 / cfg.ε + 11 / 8 * cfg.ε)) := by
        gcongr
        have := hΔ (X (cfg.T + 1)) (traj_mem H cfg hc.γ0 hc.ε0 hx0 g ξ _)
        change f x0 + ψ x0 - (f (X (cfg.T + 1)) + ψ (X (cfg.T + 1))) ≤ Δ
        exact this

omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
lemma measurable_prox_pos {a : ℝ} (ha : 0 < a)
    (hprox : Measurable (fun t : ℝ × E × E => if 0 < t.1 then prox t.1 t.2.1 t.2.2 else 0)) :
    Measurable (fun z : E × E => prox a z.1 z.2) := by
  have : (fun z : E × E => prox a z.1 z.2) =
      (fun t : ℝ × E × E => if 0 < t.1 then prox t.1 t.2.1 t.2.2 else 0) ∘ (fun z => (a, z.1, z.2)) := by
    funext z; simp [ha]
  rw [this]
  exact hprox.comp (by fun_prop)

lemma expected_bound (H : PathHyp f grad ψ Q prox L) (hL : 0 < L) (hρ : 0 ≤ ρ)
    (hd : ∀ x, HasFDerivAt grad (hess x) x) (hl : ∀ x y, ‖hess x - hess y‖ ≤ ρ * ‖x - y‖)
    {cfg : Config} (hc : CfgHyp cfg L ρ σ Δ) {x0 : E} (hx0 : x0 ∈ Q)
    (hΔ : ∀ x ∈ Q, f x0 + ψ x0 - (f x + ψ x) ≤ Δ) (O : OracleHyp g grad μ σ)
    (hprox : Measurable (fun t : ℝ × E × E => if 0 < t.1 then prox t.1 t.2.1 t.2.2 else 0)) :
    Measurable (fun ω : Fin (cfg.T + 1) × (ℕ → Ω) => (traj cfg x0 g prox ω.2 ω.1.val).1) ∧
    (∀ ω : Fin (cfg.T + 1) × (ℕ → Ω), (traj cfg x0 g prox ω.2 ω.1.val).1 ∈ Q) ∧
    ∫⁻ ω, ENNReal.ofReal ‖L • ((traj cfg x0 g prox ω.2 ω.1.val).1 -
        prox (1 / L) (traj cfg x0 g prox ω.2 ω.1.val).1 (grad (traj cfg x0 g prox ω.2 ω.1.val).1))‖
      ∂((PMF.uniformOfFintype (Fin (cfg.T + 1))).toMeasure.prod (Measure.infinitePi fun _ : ℕ => μ)) ≤
      ENNReal.ofReal (3 * cfg.ε) := by
  set P := Measure.infinitePi fun _ : ℕ => μ
  set ν := (PMF.uniformOfFintype (Fin (cfg.T + 1))).toMeasure
  set B := ρ * (2 * cfg.γ * cfg.ε) ^ 2 / cfg.α ^ 2
  have hgrad : Continuous grad := by
    have hL0 : 0 ≤ L := hL.le
    have : LipschitzWith (Real.toNNReal L) grad := LipschitzWith.of_dist_le_mul fun a b => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0]; exact H.hlip a b
    exact this.continuous
  set Gm : E → ℝ := fun x => ‖L • (x - prox (1 / L) x (grad x))‖
  have hGm : Measurable Gm := by
    have hp := measurable_prox_pos (prox := prox) (one_div_pos.mpr hL) hprox
    exact ((measurable_id.sub (hp.comp (measurable_id.prodMk hgrad.measurable))).const_smul L).norm
  have htraj : ∀ t, Measurable (fun ξ : ℕ → Ω => (traj cfg x0 g prox ξ t).1) :=
    fun t => measurable_fst.comp (measurable_traj cfg x0 g prox hc.γ0 hprox O.meas t)
  have hout : Measurable (fun ω : Fin (cfg.T + 1) × (ℕ → Ω) => (traj cfg x0 g prox ω.2 ω.1.val).1) :=
    measurable_from_prod_countable_right fun τ => htraj τ.val
  refine ⟨hout, fun ω => traj_mem H cfg hc.γ0 hc.ε0 hx0 g ω.2 _, ?_⟩
  change ∫⁻ ω, ENNReal.ofReal (Gm (traj cfg x0 g prox ω.2 ω.1.val).1) ∂(ν.prod P) ≤ _
  have hmeas : Measurable (fun ω : Fin (cfg.T + 1) × (ℕ → Ω) =>
      ENNReal.ofReal (Gm (traj cfg x0 g prox ω.2 ω.1.val).1)) :=
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
  have hγ := hc.γ0
  have hα := hc.α0
  have hΔ0 := hc.Δ0
  have hT : (0 : ℝ) < cfg.T + 1 := by positivity
  have hpt : ∀ ξ : ℕ → Ω, ENNReal.ofReal (∑ t ∈ Finset.range (cfg.T + 1), Gm (traj cfg x0 g prox ξ t).1) =
      ∑ τ : Fin (cfg.T + 1), ENNReal.ofReal (Gm (traj cfg x0 g prox ξ τ.val).1) := by
    intro ξ
    rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => norm_nonneg _)]
    exact (Fin.sum_univ_eq_sum_range (fun t => ENNReal.ofReal (Gm (traj cfg x0 g prox ξ t).1)) _).symm
  have hsum : ∑ τ : Fin (cfg.T + 1), ∫⁻ ξ, ENNReal.ofReal (Gm (traj cfg x0 g prox ξ τ.val).1) ∂P =
      ∫⁻ ξ, ENNReal.ofReal (∑ t ∈ Finset.range (cfg.T + 1), Gm (traj cfg x0 g prox ξ t).1) ∂P := by
    rw [← lintegral_finsetSum (f := fun (τ : Fin (cfg.T + 1)) ξ =>
      ENNReal.ofReal (Gm (traj cfg x0 g prox ξ τ.val).1)) _
      (fun (τ : Fin (cfg.T + 1)) _ => ENNReal.measurable_ofReal.comp (hGm.comp (htraj τ.val)))]
    exact lintegral_congr fun ξ => (hpt ξ).symm
  rw [hsum]
  set c := 20 / cfg.ε
  set M := σ ^ 2 / cfg.n0 + cfg.α * σ ^ 2
  set A := Δ / (cfg.γ * cfg.ε) + (cfg.T + 1) * (20 * B ^ 2 / cfg.ε + 11 / 8 * cfg.ε)
  have hc0 : 0 ≤ c := by positivity
  have hM0 : 0 ≤ M := by have := sq_nonneg σ; positivity
  have hA0 : 0 ≤ A := by positivity
  have hpath : ∀ ξ, ENNReal.ofReal (∑ t ∈ Finset.range (cfg.T + 1), Gm (traj cfg x0 g prox ξ t).1) ≤
      ENNReal.ofReal A + ENNReal.ofReal c *
        ∑ t ∈ Finset.range (cfg.T + 1), ENNReal.ofReal (‖noise cfg x0 g grad prox ξ t‖ ^ 2) := by
    intro ξ
    have h := path_sum H hL hρ hd hl hc hx0 hΔ ξ (g := g)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => sq_nonneg _), ← ENNReal.ofReal_mul hc0,
      ← ENNReal.ofReal_add hA0 (mul_nonneg hc0 (Finset.sum_nonneg fun t _ => sq_nonneg _))]
    refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.mul_sum]
    simp only [A, c]
    push_cast
    rw [Finset.sum_congr rfl (fun t _ => show 20 * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 / cfg.ε =
      20 / cfg.ε * ‖noise cfg x0 g grad prox ξ t‖ ^ 2 by ring)]
    ring
  have hM := noise_moment cfg x0 prox O hgrad hc.γ0 hprox hc.n0 hc.α0.le hc.α1 (μ := μ)
  have hY : ∫⁻ ξ, ENNReal.ofReal (∑ t ∈ Finset.range (cfg.T + 1), Gm (traj cfg x0 g prox ξ t).1) ∂P ≤
      ENNReal.ofReal (A + c * ((cfg.T + 1) * M)) := by
    refine (lintegral_mono hpath).trans ?_
    rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_finsetSum (f := fun t ξ => ENNReal.ofReal (‖noise cfg x0 g grad prox ξ t‖ ^ 2)) _
        (fun t _ => ENNReal.measurable_ofReal.comp
          ((measurable_noise cfg x0 prox O hgrad hc.γ0 hprox t).norm.pow_const 2))]
    have hs : ∑ t ∈ Finset.range (cfg.T + 1), ∫⁻ ξ, ENNReal.ofReal (‖noise cfg x0 g grad prox ξ t‖ ^ 2) ∂P ≤
        ENNReal.ofReal ((cfg.T + 1) * M) := by
      calc ∑ t ∈ Finset.range (cfg.T + 1), ∫⁻ ξ, ENNReal.ofReal (‖noise cfg x0 g grad prox ξ t‖ ^ 2) ∂P
          ≤ ∑ t ∈ Finset.range (cfg.T + 1), ENNReal.ofReal M := Finset.sum_le_sum fun t _ => hM t
        _ = ENNReal.ofReal (∑ t ∈ Finset.range (cfg.T + 1), M) :=
            (ENNReal.ofReal_sum_of_nonneg fun _ _ => hM0).symm
        _ = ENNReal.ofReal ((cfg.T + 1) * M) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring_nf
    calc ENNReal.ofReal A + ENNReal.ofReal c * ∑ t ∈ Finset.range (cfg.T + 1),
          ∫⁻ ξ, ENNReal.ofReal (‖noise cfg x0 g grad prox ξ t‖ ^ 2) ∂P
        ≤ ENNReal.ofReal A + ENNReal.ofReal c * ENNReal.ofReal ((cfg.T + 1) * M) := by gcongr
      _ = ENNReal.ofReal (A + c * ((cfg.T + 1) * M)) := by
          rw [← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_add hA0 (by positivity)]
  have hinv : ((cfg.T + 1 : ℕ) : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / (cfg.T + 1)) := by
    rw [ENNReal.ofReal_div_of_pos hT, ENNReal.ofReal_one, one_div]
    congr 1
    rw [show ((cfg.T : ℝ) + 1) = ((cfg.T + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  rw [hinv]
  have hreal : (A + c * ((cfg.T + 1) * M)) * (1 / (cfg.T + 1)) ≤ 3 * cfg.ε := by
    rw [mul_one_div, div_le_iff₀ hT]
    have h1 := hc.horizon
    have h2 := mul_le_mul_of_nonneg_left hc.noise hT.le
    have e2 : A + c * ((cfg.T + 1) * M) = Δ / (cfg.γ * cfg.ε) + (cfg.T + 1) * (11 / 8 * cfg.ε) +
        (cfg.T + 1) * (20 * ((ρ * (2 * cfg.γ * cfg.ε) ^ 2 / cfg.α ^ 2) ^ 2 + σ ^ 2 / cfg.n0 +
          cfg.α * σ ^ 2) / cfg.ε) := by
      simp only [A, c, M, B]; ring
    rw [e2]
    have hTε : 0 ≤ (cfg.T + 1 : ℝ) * cfg.ε := by positivity
    linarith
  calc (∫⁻ ξ, ENNReal.ofReal (∑ t ∈ Finset.range (cfg.T + 1), Gm (traj cfg x0 g prox ξ t).1) ∂P) *
        ENNReal.ofReal (1 / (cfg.T + 1))
      ≤ ENNReal.ofReal (A + c * ((cfg.T + 1) * M)) * ENNReal.ofReal (1 / (cfg.T + 1)) := by gcongr
    _ = ENNReal.ofReal ((A + c * ((cfg.T + 1) * M)) * (1 / (cfg.T + 1))) :=
        (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (3 * cfg.ε) := ENNReal.ofReal_le_ofReal hreal

end OracleTemplate.CompositeTransport
