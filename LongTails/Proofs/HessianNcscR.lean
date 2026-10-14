import LongTails.Proofs.HessianNcscNoise

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.HessianNcsc

variable {E F Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]

variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}
  {ox : E × F → Ω → E} {oy : E × F → Ω → F}

section Coeffs

variable (L μ ρ : ℝ) (cfg : IgtConfig)

noncomputable def kq0 : ℝ :=
  ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * cfg.η ^ 2 / cfg.α +
    (cfg.α / cfg.γ) * ((ρ / μ) * (1 + L / μ) * Real.sqrt (1 + (L / μ) ^ 2) * cfg.η) *
      (4 * (L / μ) * cfg.η / cfg.α)

noncomputable def kq1 : ℝ :=
  ρ * (1 + L / μ) * Real.sqrt (1 + (L / μ) ^ 2) * cfg.η +
    (cfg.α / cfg.γ) * ((ρ / μ) * (1 + L / μ) * Real.sqrt (1 + (L / μ) ^ 2) * cfg.η + cfg.α * (L / μ))

noncomputable def kq2 : ℝ := cfg.α * (ρ * (1 + L / μ))

end Coeffs

section RDefs

variable (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)
  (ox : E × F → Ω → E) (oy : E × F → Ω → F)

noncomputable def Rq (ξ : ℕ → Ω) (k : ℕ) : E :=
  chi (H := H) (α := cfg.α) (γ := cfg.γ) (w := wq cfg x0 y0 ox oy ξ) (u := uq cfg x0 y0 ox oy ξ)
    (xt := xq cfg x0 y0 ox oy ξ) (y := yq cfg x0 y0 ox oy ξ) k - nuq H cfg x0 y0 ox oy ξ k

noncomputable def rbar (ξ : ℕ → Ω) : ℕ → ℝ
  | 0 => ‖ehM H cfg x0 y0 ox oy ξ 0‖ + (cfg.α / cfg.γ) * (L / μ) * ‖eM H cfg x0 y0 ox oy ξ 0‖
  | k + 1 => (1 - cfg.α) * rbar ξ k + kq0 L μ ρ cfg + kq1 L μ ρ cfg * ‖eM H cfg x0 y0 ox oy ξ k‖ +
      kq2 L μ ρ cfg * ‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2

end RDefs

omit [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma ee_eq_eM (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F) (ξ : ℕ → Ω) (k : ℕ) :
    ee H (xq cfg x0 y0 ox oy ξ) (yq cfg x0 y0 ox oy ξ) (k + 1) = eM H cfg x0 y0 ox oy ξ k := rfl

omit [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma eh_eq_ehM (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F) (ξ : ℕ → Ω) (k : ℕ) :
    eh H (wq cfg x0 y0 ox oy ξ) (uq cfg x0 y0 ox oy ξ) k = ehM H cfg x0 y0 ox oy ξ k := rfl

omit [BorelSpace E] [SecondCountableTopology E] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma Rq_bound (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (hc : CfgOK cfg L μ) (x0 : E) (y0 : F)
    (ξ : ℕ → Ω) : ∀ k, ‖Rq H cfg x0 y0 ox oy ξ k‖ ≤ rbar H cfg x0 y0 ox oy ξ k
  | 0 => by
      have hM0 : Mm H (wq cfg x0 y0 ox oy ξ 0) 0 = 0 := by rw [← MmL_apply]; exact map_zero _
      simp only [Rq, rbar, chi, psi, nuq, Zs, sub_self, hM0, smul_zero, sub_zero]
      rw [ee_eq_eM, eh_eq_ehM]
      refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg hc.α0.le hc.γ0.le)]
      have := H.Mm_norm (wq cfg x0 y0 ox oy ξ 0) (eM H cfg x0 y0 ox oy ξ 0)
      calc cfg.α / cfg.γ * ‖Mm H (wq cfg x0 y0 ox oy ξ 0) (eM H cfg x0 y0 ox oy ξ 0)‖
          ≤ cfg.α / cfg.γ * ((L / μ) * ‖eM H cfg x0 y0 ox oy ξ 0‖) :=
            mul_le_mul_of_nonneg_left this (div_nonneg hc.α0.le hc.γ0.le)
        _ = cfg.α / cfg.γ * (L / μ) * ‖eM H cfg x0 y0 ox oy ξ 0‖ := by ring
  | k + 1 => by
      have ih := Rq_bound H cfg hc x0 y0 ξ k
      have hR := pathRel_seq H cfg x0 y0 ox oy ξ (gx := gx) (gy := gy)
      have hcs := hR.chi_succ hc.γ0.ne' k
      have hQ := hR.Qp_bound hc.α0 hc.α1 hc.γ0 hc.l0 hc.η0 k
      rw [ee_eq_eM] at hQ
      have e1 : Rq H cfg x0 y0 ox oy ξ (k + 1) = (1 - cfg.α) • Rq H cfg x0 y0 ox oy ξ k +
          Qp (H := H) (α := cfg.α) (γ := cfg.γ) (w := wq cfg x0 y0 ox oy ξ) (xt := xq cfg x0 y0 ox oy ξ)
            (y := yq cfg x0 y0 ox oy ξ) k := by
        simp only [Rq]
        rw [hcs]; simp only [nuq, smul_sub]; abel
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by linarith [hc.α1])]
      simp only [rbar, kq0, kq1, kq2]
      have h1 := mul_le_mul_of_nonneg_left ih (by linarith [hc.α1] : (0:ℝ) ≤ 1 - cfg.α)
      nlinarith

omit [BorelSpace E] [SecondCountableTopology E] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma ehM_bound (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (hc : CfgOK cfg L μ) (x0 : E) (y0 : F)
    (ξ : ℕ → Ω) (k : ℕ) :
    ‖ehM H cfg x0 y0 ox oy ξ k‖ ≤ ‖nuq H cfg x0 y0 ox oy ξ k‖ + rbar H cfg x0 y0 ox oy ξ k +
      4 * (L / μ) ^ 2 * cfg.η / cfg.γ + (cfg.α / cfg.γ) * (L / μ) * ‖eM H cfg x0 y0 ox oy ξ k‖ := by
  have hR := pathRel_seq H cfg x0 y0 ox oy ξ (gx := gx) (gy := gy)
  have hRb := Rq_bound H cfg hc x0 y0 ξ k (ox := ox) (oy := oy)
  have hZ := hR.Z_close_t hc.α0 hc.α1 hc.l0 hc.η0 k
  set M := Mm H (wq cfg x0 y0 ox oy ξ k)
  set V := ystar H (xq cfg x0 y0 ox oy ξ (k + 1)) - Zs (H := H) cfg.α (xq cfg x0 y0 ox oy ξ) k
  have e1 : ehM H cfg x0 y0 ox oy ξ k = nuq H cfg x0 y0 ox oy ξ k + Rq H cfg x0 y0 ox oy ξ k +
      (cfg.α / cfg.γ) • M V + (cfg.α / cfg.γ) • M (eM H cfg x0 y0 ox oy ξ k) := by
    simp only [Rq, chi, psi, M, V]; rw [ee_eq_eM, eh_eq_ehM]; abel
  rw [e1]
  have hag : 0 ≤ cfg.α / cfg.γ := div_nonneg hc.α0.le hc.γ0.le
  have hMV : ‖(cfg.α / cfg.γ) • M V‖ ≤ 4 * (L / μ) ^ 2 * cfg.η / cfg.γ := by
    rw [norm_smul, Real.norm_of_nonneg hag]
    have := H.Mm_norm (wq cfg x0 y0 ox oy ξ k) V
    have hk : 0 ≤ L / μ := div_nonneg H.L_pos.le H.μpos.le
    calc cfg.α / cfg.γ * ‖M V‖ ≤ cfg.α / cfg.γ * ((L / μ) * (4 * (L / μ) * cfg.η / cfg.α)) := by
          apply mul_le_mul_of_nonneg_left (this.trans (mul_le_mul_of_nonneg_left hZ hk)) hag
      _ = 4 * (L / μ) ^ 2 * cfg.η / cfg.γ := by field_simp [hc.α0.ne']
  have hMe : ‖(cfg.α / cfg.γ) • M (eM H cfg x0 y0 ox oy ξ k)‖ ≤
      (cfg.α / cfg.γ) * (L / μ) * ‖eM H cfg x0 y0 ox oy ξ k‖ := by
    rw [norm_smul, Real.norm_of_nonneg hag, mul_assoc]
    exact mul_le_mul_of_nonneg_left (H.Mm_norm _ _) hag
  have := norm_add_le (nuq H cfg x0 y0 ox oy ξ k) (Rq H cfg x0 y0 ox oy ξ k)
  calc ‖nuq H cfg x0 y0 ox oy ξ k + Rq H cfg x0 y0 ox oy ξ k + (cfg.α / cfg.γ) • M V +
        (cfg.α / cfg.γ) • M (eM H cfg x0 y0 ox oy ξ k)‖
      ≤ ‖nuq H cfg x0 y0 ox oy ξ k‖ + ‖Rq H cfg x0 y0 ox oy ξ k‖ + ‖(cfg.α / cfg.γ) • M V‖ +
          ‖(cfg.α / cfg.γ) • M (eM H cfg x0 y0 ox oy ξ k)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add this le_rfl)) le_rfl)
    _ ≤ _ := by linarith

omit [FiniteDimensional ℝ F] in
lemma measurable_rbar (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) :
    ∀ k, Measurable (fun ξ => rbar H cfg x0 y0 ox oy ξ k)
  | 0 => by
      simp only [rbar]
      exact (measurable_ehM H cfg x0 y0 hox hoy 0).norm.add
        ((measurable_eM H cfg x0 y0 hox hoy 0).norm.const_mul _)
  | k + 1 => by
      have ih := measurable_rbar H cfg x0 y0 hox hoy k
      have me := (measurable_eM H cfg x0 y0 hox hoy k).norm
      simp only [rbar]
      exact (((ih.const_mul _).add measurable_const).add (me.const_mul _)).add ((me.pow_const 2).const_mul _)

end OracleTemplate.HessianNcsc
