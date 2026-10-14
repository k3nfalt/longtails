import LongTails.Proofs.HessianNcscAssembly

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.HessianNcsc

variable {E F Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]

variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}
  {ox : E × F → Ω → E} {oy : E × F → Ω → F} {p : Measure Ω} [IsProbabilityMeasure p] {σ : ℝ}

omit [CompleteSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace F] [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma outRec_eq (cfg : IgtConfig) (x0 : E) (y0 : F) (ξ : ℕ → Ω) {τ : ℕ} (hτ : τ ≤ cfg.T) :
    outRec cfg x0 y0 ox oy ξ τ cfg.T = wq cfg x0 y0 ox oy ξ τ := by
  rcases τ with _ | τ
  · simp [outRec, wq]
  · simp only [outRec, wq]
    rw [ite_eq_left ⟨by omega, hτ⟩]
    rfl

omit [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ F] in
lemma measurable_out (cfg : IgtConfig) (x0 : E) (y0 : F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) :
    Measurable (fun ω : Fin (cfg.T + 1) × (ℕ → Ω) => outRec cfg x0 y0 ox oy ω.2 ω.1.val cfg.T) := by
  refine measurable_from_prod_countable_right fun τ => ?_
  simp only
  rw [show (fun ξ => outRec cfg x0 y0 ox oy ξ τ.val cfg.T) = fun ξ => wq cfg x0 y0 ox oy ξ τ.val from
    funext fun ξ => outRec_eq cfg x0 y0 ξ (Nat.lt_succ_iff.mp τ.isLt)]
  exact measurable_wq cfg x0 y0 hox hoy τ.val

omit [FiniteDimensional ℝ F] in
lemma out_lintegral (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) (P0 : Measure (ℕ → Ω))
    [SFinite P0] :
    ∫⁻ ω, ENNReal.ofReal ‖Gs H (outRec cfg x0 y0 ox oy ω.2 ω.1.val cfg.T)‖
        ∂((PMF.uniformOfFintype (Fin (cfg.T + 1))).toMeasure.prod P0) =
      (∑ k ∈ Finset.range (cfg.T + 1), ∫⁻ ξ, ENNReal.ofReal ‖Gs H (wq cfg x0 y0 ox oy ξ k)‖ ∂P0) /
        ((cfg.T : ℝ≥0∞) + 1) := by
  have hm : Measurable (fun ω : Fin (cfg.T + 1) × (ℕ → Ω) =>
      ENNReal.ofReal ‖Gs H (outRec cfg x0 y0 ox oy ω.2 ω.1.val cfg.T)‖) :=
    ENNReal.measurable_ofReal.comp (H.Gs_continuous.measurable.comp (measurable_out cfg x0 y0 hox hoy)).norm
  rw [lintegral_prod _ hm.aemeasurable, lintegral_fintype]
  simp only [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _), Fintype.card_fin]
  have hc : ∀ τ : Fin (cfg.T + 1), (Fintype.card ({τ} : Set (Fin (cfg.T + 1))) : ℝ≥0∞) = 1 := by
    intro τ; simp
  simp only [hc, one_div]
  rw [← Finset.sum_mul, div_eq_mul_inv]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range (fun k => ∫⁻ ξ, ENNReal.ofReal ‖Gs H (wq cfg x0 y0 ox oy ξ k)‖ ∂P0)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp_rw [outRec_eq cfg x0 y0 _ (Nat.lt_succ_iff.mp τ.isLt)]
  · push_cast; rfl

lemma master_lintegral (H : Hyp f gx gy Hx Hy L μ ρ) (O : OracleHyp gx gy ox oy p σ) (cfg : IgtConfig)
    (x0 : E) (y0 : F) (hc : CfgOK cfg L μ) (hNB : 1 ≤ cfg.NB) {G Es Ps Δ ε : ℝ}
    (hG : ‖gy (x0, y0)‖ ≤ G) (hΔ : ∀ x y, ∃ y', f x0 y - f x y' ≤ Δ) (hEs : 0 < Es) (hPs : 0 < Ps)
    (hσ : 0 < σ) (hη : 0 < cfg.η)
    (hA : (1 - cfg.γ * μ) ^ cfg.NA * (G / μ) ^ 2 + cfg.γ ^ 2 * σ ^ 2 / (1 - (1 - cfg.γ * μ)) ≤ 2 * Es)
    (hC : (1 - cfg.γ * μ) ^ cfg.NC * (2 * (2 * Es) + 2 * ((L / μ) * (cfg.η / cfg.α)) ^ 2) +
      cfg.γ ^ 2 * σ ^ 2 / (1 - (1 - cfg.γ * μ)) ≤ Es)
    (hB : 2 * σ ^ 2 / cfg.NB + 2 * L ^ 2 * (2 * Es) ≤ Ps)
    (c1 : kAe L μ cfg * Es + kAh L μ cfg * Ps + kA0 L μ ρ σ cfg ≤ Es)
    (c2 : (1 - cfg.α) * Ps + 4 * cfg.α * L ^ 2 * Es + (4 * kDD L μ ρ cfg ^ 2 / cfg.α + cfg.α ^ 2 * σ ^ 2) ≤ Ps)
    (hfin : Δ / cfg.η + (cfg.T + 1) * (cfg.lam + L * (L / μ + 1 / 2) * cfg.η) +
        2 * ((cfg.T + 1) * (Real.sqrt (cfg.α * ((1 + (L / μ) ^ 2) * σ ^ 2)) +
          (kq0 L μ ρ cfg + kq1 L μ ρ cfg * Real.sqrt Es + kq2 L μ ρ cfg * Es) / (1 - (1 - cfg.α)) +
          (4 * (L / μ) ^ 2 * cfg.η / cfg.γ + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es)) +
          (Real.sqrt Ps + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es) / cfg.α) ≤ (cfg.T + 1) * ε) :
    ∫⁻ ω, ENNReal.ofReal ‖Gs H (outRec cfg x0 y0 ox oy ω.2 ω.1.val cfg.T)‖
        ∂((PMF.uniformOfFintype (Fin (cfg.T + 1))).toMeasure.prod (Measure.infinitePi fun _ : ℕ => p)) ≤
      ENNReal.ofReal ε := by
  have hm := moments_all H cfg x0 y0 O hc hNB hG hEs.le hPs.le hA hC hB c1 c2
  have hs := grad_sum H cfg x0 y0 O hc hEs hPs hσ hη hΔ hm (cfg.T + 1)
  rw [out_lintegral H cfg x0 y0 O.mx O.my]
  have hT : (0 : ℝ) < cfg.T + 1 := by positivity
  rw [ENNReal.div_le_iff (by positivity) (by simp)]
  refine (hs.trans (ENNReal.ofReal_le_ofReal (q := ((cfg.T : ℝ) + 1) * ε) ?_)).trans_eq ?_
  · exact_mod_cast hfin
  · have hε : 0 ≤ ε := by
      have h0 : 0 ≤ Δ / cfg.η + (cfg.T + 1) * (cfg.lam + L * (L / μ + 1 / 2) * cfg.η) := by
        have hg := H.phi_gap hΔ x0
        have := hc.l0; have := H.L_pos; have := H.μpos
        have : 0 ≤ Δ := by linarith
        positivity
      have h1 : 0 ≤ 2 * (((cfg.T : ℝ) + 1) * (Real.sqrt (cfg.α * ((1 + (L / μ) ^ 2) * σ ^ 2)) +
          (kq0 L μ ρ cfg + kq1 L μ ρ cfg * Real.sqrt Es + kq2 L μ ρ cfg * Es) / (1 - (1 - cfg.α)) +
          (4 * (L / μ) ^ 2 * cfg.η / cfg.γ + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es)) +
          (Real.sqrt Ps + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es) / cfg.α) := by
        have := hc.α0; have := hc.α1; have := hc.γ0; have := H.L_pos; have := H.μpos; have := H.ρnn
        have := hc.η0
        have h1a : 0 < 1 - (1 - cfg.α) := by linarith
        simp only [kq0, kq1, kq2]
        positivity
      nlinarith
    rw [ENNReal.ofReal_mul (by positivity), mul_comm]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp

end OracleTemplate.HessianNcsc
