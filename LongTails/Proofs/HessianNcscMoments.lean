import LongTails.Proofs.HessianNcscTrack

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

section Defs

variable (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)
  (ox : E × F → Ω → E) (oy : E × F → Ω → F)

noncomputable def eM (ξ : ℕ → Ω) (k : ℕ) : F :=
  yq cfg x0 y0 ox oy ξ (k + 1) - ystar H (xq cfg x0 y0 ox oy ξ (k + 1))

noncomputable def ehM (ξ : ℕ → Ω) (k : ℕ) : E :=
  uq cfg x0 y0 ox oy ξ k - Gs H (wq cfg x0 y0 ox oy ξ k)

end Defs

omit [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma lead_succ (cfg : IgtConfig) (hα : cfg.α ≠ 0) (w u : E) :
    lead cfg (w + nphi cfg.η cfg.lam u) u = w + (1 / cfg.α) • nphi cfg.η cfg.lam u := by
  simp only [lead]
  have : (1 / cfg.α) = 1 + (1 - cfg.α) / cfg.α := by field_simp; ring
  rw [this, add_smul, one_smul]; abel

omit [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace F] in
omit [BorelSpace E] [SecondCountableTopology E] in
omit [MeasurableSpace E] in
lemma eM_succ (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (hα : cfg.α ≠ 0) (x0 : E) (y0 : F)
    (ξ : ℕ → Ω) (k : ℕ) :
    eM H cfg x0 y0 ox oy ξ (k + 1) =
      (mainS cfg x0 y0 ox oy ξ k).2.2 + cfg.γ • oy (lead cfg (mainS cfg x0 y0 ox oy ξ k).1
          (mainS cfg x0 y0 ox oy ξ k).2.1, (mainS cfg x0 y0 ox oy ξ k).2.2) (ξ (off cfg + k)) -
        ystar H ((mainS cfg x0 y0 ox oy ξ k).1 + (1 / cfg.α) • nphi cfg.η cfg.lam
          ((1 - cfg.α) • (mainS cfg x0 y0 ox oy ξ k).2.1 + cfg.α • ox (lead cfg
            (mainS cfg x0 y0 ox oy ξ k).1 (mainS cfg x0 y0 ox oy ξ k).2.1,
              (mainS cfg x0 y0 ox oy ξ k).2.2) (ξ (off cfg + k)))) := by
  simp only [eM, yq, xq, wq, uq]
  conv_lhs => rw [mainS]
  rw [lead_succ cfg hα]

noncomputable def Phie (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (ox : E × F → Ω → E)
    (oy : E × F → Ω → F) (s : (E × E × F) × Ω) : F :=
  s.1.2.2 + cfg.γ • oy (lead cfg s.1.1 s.1.2.1, s.1.2.2) s.2 -
    ystar H (s.1.1 + (1 / cfg.α) • nphi cfg.η cfg.lam
      ((1 - cfg.α) • s.1.2.1 + cfg.α • ox (lead cfg s.1.1 s.1.2.1, s.1.2.2) s.2))

omit [FiniteDimensional ℝ F] in
lemma measurable_Phie (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) :
    Measurable (Phie H cfg ox oy) := by
  have hl : Measurable (fun s : (E × E × F) × Ω => lead cfg s.1.1 s.1.2.1) :=
    (measurable_lead cfg).comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  have hy : Measurable (fun s : (E × E × F) × Ω => s.1.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_fst)
  have hu : Measurable (fun s : (E × E × F) × Ω => s.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hw : Measurable (fun s : (E × E × F) × Ω => s.1.1) := measurable_fst.comp measurable_fst
  have hz : Measurable (fun s : (E × E × F) × Ω => ((lead cfg s.1.1 s.1.2.1, s.1.2.2), s.2)) :=
    (hl.prodMk hy).prodMk measurable_snd
  have hOY : Measurable (fun s : (E × E × F) × Ω => oy (lead cfg s.1.1 s.1.2.1, s.1.2.2) s.2) :=
    hoy.comp hz
  have hOX : Measurable (fun s : (E × E × F) × Ω => ox (lead cfg s.1.1 s.1.2.1, s.1.2.2) s.2) :=
    hox.comp hz
  unfold Phie
  exact (hy.add (hOY.const_smul _)).sub (H.ystar_continuous.measurable.comp
    (hw.add (((measurable_nphi cfg.η cfg.lam).comp ((hu.const_smul _).add (hOX.const_smul _))).const_smul _)))

omit [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace F] in
omit [MeasurableSpace E] in
lemma eM_succ_Phie (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (hα : cfg.α ≠ 0) (x0 : E) (y0 : F)
    (ξ : ℕ → Ω) (k : ℕ) :
    eM H cfg x0 y0 ox oy ξ (k + 1) = Phie H cfg ox oy (mainS cfg x0 y0 ox oy ξ k, ξ (off cfg + k)) := by
  rw [eM_succ H cfg hα]; rfl

section TrackMoment

variable (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)

omit [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma eM_eq (ξ : ℕ → Ω) (k : ℕ) :
    eM H cfg x0 y0 ox oy ξ k = (mainS cfg x0 y0 ox oy ξ k).2.2 -
      ystar H (lead cfg (mainS cfg x0 y0 ox oy ξ k).1 (mainS cfg x0 y0 ox oy ξ k).2.1) := rfl

omit [BorelSpace E] [SecondCountableTopology E]
    [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [FiniteDimensional ℝ F] [MeasurableSpace F] in
lemma ehM_eq (ξ : ℕ → Ω) (k : ℕ) :
    ehM H cfg x0 y0 ox oy ξ k = (mainS cfg x0 y0 ox oy ξ k).2.1 -
      Gs H ((mainS cfg x0 y0 ox oy ξ k).1 - nphi cfg.η cfg.lam (mainS cfg x0 y0 ox oy ξ k).2.1) := by
  have h := (pathRel_seq H cfg x0 y0 ox oy ξ (gx := gx) (gy := gy)).w_succ k
  simp only [ehM]
  congr 2
  have : wq cfg x0 y0 ox oy ξ (k + 1) = (mainS cfg x0 y0 ox oy ξ k).1 := rfl
  rw [this] at h
  rw [h]; simp [uq]

omit [BorelSpace E] [SecondCountableTopology E] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [FiniteDimensional ℝ F] [MeasurableSpace F] in
lemma Gd_bound (hα0 : 0 < cfg.α) (hl : 0 < cfg.lam) (hη : 0 ≤ cfg.η) (ξ : ℕ → Ω) (k : ℕ) :
    ‖gx (lead cfg (mainS cfg x0 y0 ox oy ξ k).1 (mainS cfg x0 y0 ox oy ξ k).2.1,
        (mainS cfg x0 y0 ox oy ξ k).2.2) - (mainS cfg x0 y0 ox oy ξ k).2.1‖ ≤
      L * ‖eM H cfg x0 y0 ox oy ξ k‖ + L * Real.sqrt (1 + (L / μ) ^ 2) * (cfg.η / cfg.α) +
        ‖ehM H cfg x0 y0 ox oy ξ k‖ := by
  set s := mainS cfg x0 y0 ox oy ξ k
  set xt := lead cfg s.1 s.2.1
  set wk := s.1 - nphi cfg.η cfg.lam s.2.1
  have hxw : xt - wk = (1 / cfg.α) • nphi cfg.η cfg.lam s.2.1 := by
    simp only [xt, wk, lead]
    have : (1 / cfg.α) = 1 + (1 - cfg.α) / cfg.α := by field_simp; ring
    rw [this, add_smul, one_smul]; abel
  have hxwn : ‖xt - wk‖ ≤ cfg.η / cfg.α := by
    rw [hxw, norm_smul, Real.norm_of_nonneg (by positivity)]
    have := nphi_norm hl hη s.2.1
    calc 1 / cfg.α * ‖nphi cfg.η cfg.lam s.2.1‖ ≤ 1 / cfg.α * cfg.η :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = cfg.η / cfg.α := by ring
  have e1 : gx (xt, s.2.2) - s.2.1 = (gx (xt, s.2.2) - Gs H xt) + (Gs H xt - Gs H wk) - (s.2.1 - Gs H wk) := by
    abel
  rw [e1]
  have h1 : ‖gx (xt, s.2.2) - Gs H xt‖ ≤ L * ‖eM H cfg x0 y0 ox oy ξ k‖ := by
    rw [eM_eq]; exact H.gx_lip_y xt s.2.2 (ystar H xt)
  have h2 : ‖Gs H xt - Gs H wk‖ ≤ L * Real.sqrt (1 + (L / μ) ^ 2) * (cfg.η / cfg.α) := by
    have := H.Gs_lip xt wk
    have h3 := sqrt_zs_le (H := H) xt wk
    calc ‖Gs H xt - Gs H wk‖ ≤ L * Real.sqrt (sq (zs H xt - zs H wk)) := this
      _ ≤ L * (Real.sqrt (1 + (L / μ) ^ 2) * ‖xt - wk‖) := mul_le_mul_of_nonneg_left h3 H.L_pos.le
      _ ≤ L * (Real.sqrt (1 + (L / μ) ^ 2) * (cfg.η / cfg.α)) := by gcongr; exact H.L_pos.le
      _ = L * Real.sqrt (1 + (L / μ) ^ 2) * (cfg.η / cfg.α) := by ring
  have h4 : ‖s.2.1 - Gs H wk‖ = ‖ehM H cfg x0 y0 ox oy ξ k‖ := by rw [ehM_eq]
  calc ‖(gx (xt, s.2.2) - Gs H xt) + (Gs H xt - Gs H wk) - (s.2.1 - Gs H wk)‖
      ≤ ‖gx (xt, s.2.2) - Gs H xt‖ + ‖Gs H xt - Gs H wk‖ + ‖s.2.1 - Gs H wk‖ := by
        refine (norm_sub_le _ _).trans ?_; gcongr; exact norm_add_le _ _
    _ ≤ _ := by rw [h4]; linarith

end TrackMoment

section Cont

omit [InnerProductSpace ℝ E] [CompleteSpace E]
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace F] [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] in
omit [InnerProductSpace ℝ F] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma sq_le_two_norm (z : E × F) : ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
  have h1 : ‖z.1‖ ≤ ‖z‖ := norm_fst_le z
  have h2 : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
  have := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have := pow_le_pow_left₀ (norm_nonneg _) h2 2
  linarith

omit [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma Hyp.gx_continuous (H : Hyp f gx gy Hx Hy L μ ρ) : Continuous gx := by
  have : LipschitzWith (Real.toNNReal (L * Real.sqrt 2)) gx := by
    refine LipschitzWith.of_dist_le_mul fun z z' => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by have := H.L_pos; positivity)]
    have h := H.gx_lip z z'
    have h2 := sq_le_two_norm (z - z')
    simp only [Prod.fst_sub, Prod.snd_sub] at h2
    calc ‖gx z - gx z'‖ ≤ L * Real.sqrt (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2) := H.gx_lip z z'
      _ ≤ L * Real.sqrt (2 * ‖z - z'‖ ^ 2) := by gcongr; exact H.L_pos.le
      _ = L * Real.sqrt 2 * ‖z - z'‖ := by
          rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]; ring
  exact this.continuous

omit [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma Hyp.Gs_continuous (H : Hyp f gx gy Hx Hy L μ ρ) : Continuous (Gs H) :=
  H.gx_continuous.comp (continuous_id.prodMk H.ystar_continuous)

omit [FiniteDimensional ℝ F] in
lemma measurable_eM (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) (k : ℕ) :
    Measurable (fun ξ => eM H cfg x0 y0 ox oy ξ k) := by
  have hm := measurable_mainS cfg x0 y0 ox oy hox hoy k
  simp only [eM_eq]
  exact (measurable_snd.comp (measurable_snd.comp hm)).sub (H.ystar_continuous.measurable.comp
    ((measurable_lead cfg).comp ((measurable_fst.comp hm).prodMk (measurable_fst.comp (measurable_snd.comp hm)))))

omit [FiniteDimensional ℝ F] in
lemma measurable_ehM (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)
    (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) (k : ℕ) :
    Measurable (fun ξ => ehM H cfg x0 y0 ox oy ξ k) := by
  have hm := measurable_mainS cfg x0 y0 ox oy hox hoy k
  have hu : Measurable (fun ξ => (mainS cfg x0 y0 ox oy ξ k).2.1) := measurable_fst.comp (measurable_snd.comp hm)
  simp only [ehM_eq]
  exact hu.sub (H.Gs_continuous.measurable.comp
    ((measurable_fst.comp hm).sub ((measurable_nphi cfg.η cfg.lam).comp hu)))

end Cont

section Coeffs

variable (L μ ρ σ : ℝ) (cfg : IgtConfig)

noncomputable def kC0 : ℝ :=
  (L / μ) * cfg.η + (L / μ) * (2 * cfg.η / cfg.lam) * (L * Real.sqrt (1 + (L / μ) ^ 2) * (cfg.η / cfg.α)) +
    ((L / μ) * (6 * cfg.η * cfg.α * σ ^ 2 / cfg.lam ^ 2) +
      (ρ / μ) * (1 + (L / μ) ^ 2) * ((2 * cfg.η / cfg.lam) ^ 2 * σ ^ 2))

noncomputable def kCe : ℝ := (L / μ) * (2 * cfg.η / cfg.lam) * L

noncomputable def kCh : ℝ := (L / μ) * (2 * cfg.η / cfg.lam)

noncomputable def kAe : ℝ := 1 - cfg.γ * μ / 2 + (9 / (cfg.γ * μ)) * kCe L μ cfg ^ 2

noncomputable def kAh : ℝ := (9 / (cfg.γ * μ)) * kCh L μ cfg ^ 2

noncomputable def kA0 : ℝ :=
  2 * cfg.γ ^ 2 * σ ^ 2 + 2 * (L / μ) ^ 2 * ((2 * cfg.η / cfg.lam) ^ 2 * σ ^ 2) +
    (9 / (cfg.γ * μ)) * kC0 L μ ρ σ cfg ^ 2

end Coeffs

structure CfgOK (cfg : IgtConfig) (L μ : ℝ) : Prop where
  α0 : 0 < cfg.α
  α1 : cfg.α ≤ 1
  γ0 : 0 < cfg.γ
  γ1 : cfg.γ ≤ μ / L ^ 2
  l0 : 0 < cfg.lam
  η0 : 0 ≤ cfg.η

lemma track_moment (H : Hyp f gx gy Hx Hy L μ ρ) (O : OracleHyp gx gy ox oy p σ) (cfg : IgtConfig)
    (hc : CfgOK cfg L μ) (x0 : E) (y0 : F) (k : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ (k + 1)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (kAe L μ cfg) *
          ∫⁻ ξ, ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal (kAh L μ cfg) *
          ∫⁻ ξ, ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal (kA0 L μ ρ σ cfg) := by
  set P0 := Measure.infinitePi fun _ : ℕ => p
  have hμ := H.μpos
  have hL := H.L_pos
  have hk : 0 ≤ L / μ := div_nonneg hL.le hμ.le
  have hgm0 : 0 < cfg.γ * μ := mul_pos hc.γ0 hμ
  have hgm1 : cfg.γ * μ ≤ 1 := by
    have h1 : cfg.γ * μ ≤ μ / L ^ 2 * μ := mul_le_mul_of_nonneg_right hc.γ1 hμ.le
    have h2 : μ / L ^ 2 * μ ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]; nlinarith [H.μL]
    linarith
  have hfun : (fun ξ => ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ (k + 1)‖ ^ 2)) =
      fun ξ => (fun s => ENNReal.ofReal (‖Phie H cfg ox oy s‖ ^ 2))
        (mainS cfg x0 y0 ox oy ξ k, ξ (off cfg + k)) := by
    funext ξ; rw [eM_succ_Phie H cfg hc.α0.ne']
  rw [hfun]
  have hmeasP : Measurable (fun s : (E × E × F) × Ω => ENNReal.ofReal (‖Phie H cfg ox oy s‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((measurable_Phie H cfg O.mx O.my).norm.pow_const 2)
  rw [fresh_lintegral p (off cfg + k) (fun ξ => mainS cfg x0 y0 ox oy ξ k)
    (measurable_mainS cfg x0 y0 ox oy O.mx O.my k)
    (fun ξ ξ' h => mainS_congr cfg x0 y0 ox oy k h) _ hmeasP]
  have hpt : ∀ ξ, ∫⁻ ω, ENNReal.ofReal (‖Phie H cfg ox oy (mainS cfg x0 y0 ox oy ξ k, ω)‖ ^ 2) ∂p ≤
      ENNReal.ofReal (kAe L μ cfg * ‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2 +
        kAh L μ cfg * ‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2 + kA0 L μ ρ σ cfg) := by
    intro ξ
    set s := mainS cfg x0 y0 ox oy ξ k
    have hts := track_step H O hc.α0 hc.γ0 hc.γ1 hc.l0 hc.η0 s.1 s.2.1 s.2.2 (p := p)
    refine le_trans (le_of_eq_of_le rfl hts) (ENNReal.ofReal_le_ofReal ?_)
    have hGd := Gd_bound H cfg x0 y0 hc.α0 hc.l0 hc.η0 ξ k (ox := ox) (oy := oy)
    set e := eM H cfg x0 y0 ox oy ξ k
    set eh := ehM H cfg x0 y0 ox oy ξ k
    have he : s.2.2 - ystar H (s.1 + ((1 - cfg.α) / cfg.α) • nphi cfg.η cfg.lam s.2.1) = e := rfl
    rw [he]
    set Gd := ‖gx (s.1 + ((1 - cfg.α) / cfg.α) • nphi cfg.η cfg.lam s.2.1, s.2.2) - s.2.1‖
    have hGd' : Gd ≤ L * ‖e‖ + L * Real.sqrt (1 + (L / μ) ^ 2) * (cfg.η / cfg.α) + ‖eh‖ := by
      simpa [Gd, lead] using hGd
    set Db := (L / μ) * (cfg.η + (2 * cfg.η / cfg.lam) * Gd) +
      ((L / μ) * (6 * cfg.η * cfg.α * σ ^ 2 / cfg.lam ^ 2) +
        (ρ / μ) * (1 + (L / μ) ^ 2) * ((2 * cfg.η / cfg.lam) ^ 2 * σ ^ 2))
    have hDb0 : 0 ≤ Db := by
      have := H.ρnn; have := hc.l0; have := hc.η0; have := hc.α0; positivity
    have hDb : Db ≤ kC0 L μ ρ σ cfg + kCe L μ cfg * ‖e‖ + kCh L μ cfg * ‖eh‖ := by
      simp only [Db, kC0, kCe, kCh]
      have h2 : 0 ≤ (L / μ) * (2 * cfg.η / cfg.lam) := by have := hc.l0; have := hc.η0; positivity
      have := mul_le_mul_of_nonneg_left hGd' h2
      nlinarith
    have hDb2 : Db ^ 2 ≤ 3 * (kC0 L μ ρ σ cfg ^ 2 + kCe L μ cfg ^ 2 * ‖e‖ ^ 2 + kCh L μ cfg ^ 2 * ‖eh‖ ^ 2) := by
      have h1 := pow_le_pow_left₀ hDb0 hDb 2
      nlinarith [sq_nonneg (kC0 L μ ρ σ cfg - kCe L μ cfg * ‖e‖), sq_nonneg (kC0 L μ ρ σ cfg - kCh L μ cfg * ‖eh‖),
        sq_nonneg (kCe L μ cfg * ‖e‖ - kCh L μ cfg * ‖eh‖)]
    have hc3 : 0 ≤ 3 / (cfg.γ * μ) := by positivity
    have h33 := mul_le_mul_of_nonneg_left hDb2 hc3
    calc (1 - cfg.γ * μ / 2) * ‖e‖ ^ 2 + 2 * cfg.γ ^ 2 * σ ^ 2 +
          2 * (L / μ) ^ 2 * ((2 * cfg.η / cfg.lam) ^ 2 * σ ^ 2) + 3 / (cfg.γ * μ) * Db ^ 2
        ≤ (1 - cfg.γ * μ / 2) * ‖e‖ ^ 2 + 2 * cfg.γ ^ 2 * σ ^ 2 +
          2 * (L / μ) ^ 2 * ((2 * cfg.η / cfg.lam) ^ 2 * σ ^ 2) +
          3 / (cfg.γ * μ) * (3 * (kC0 L μ ρ σ cfg ^ 2 + kCe L μ cfg ^ 2 * ‖e‖ ^ 2 +
            kCh L μ cfg ^ 2 * ‖eh‖ ^ 2)) := by linarith
      _ = kAe L μ cfg * ‖e‖ ^ 2 + kAh L μ cfg * ‖eh‖ ^ 2 + kA0 L μ ρ σ cfg := by
          simp only [kAe, kAh, kA0]; ring
  refine (lintegral_mono hpt).trans ?_
  have hAe : 0 ≤ kAe L μ cfg := by
    simp only [kAe]; have : 0 ≤ (9 / (cfg.γ * μ)) * kCe L μ cfg ^ 2 := by positivity
    linarith
  have hAh : 0 ≤ kAh L μ cfg := by simp only [kAh]; positivity
  have hA0 : 0 ≤ kA0 L μ ρ σ cfg := by simp only [kA0]; positivity
  have me := measurable_eM H cfg x0 y0 O.mx O.my k (ox := ox) (oy := oy)
  have mh := measurable_ehM H cfg x0 y0 O.mx O.my k (ox := ox) (oy := oy)
  have hsplit : ∀ ξ, ENNReal.ofReal (kAe L μ cfg * ‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2 +
        kAh L μ cfg * ‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2 + kA0 L μ ρ σ cfg) =
      ENNReal.ofReal (kAe L μ cfg) * ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2) +
        ENNReal.ofReal (kAh L μ cfg) * ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2) +
        ENNReal.ofReal (kA0 L μ ρ σ cfg) := by
    intro ξ
    rw [ENNReal.ofReal_add (by positivity) hA0, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hAe, ENNReal.ofReal_mul hAh]
  simp_rw [hsplit]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  rw [lintegral_add_left (f := fun ξ => ENNReal.ofReal (kAe L μ cfg) *
      ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2))
    ((ENNReal.measurable_ofReal.comp (me.norm.pow_const 2)).const_mul _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

noncomputable def Phih (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (ox : E × F → Ω → E)
    (s : (E × E × F) × Ω) : E :=
  (1 - cfg.α) • s.1.2.1 + cfg.α • ox (lead cfg s.1.1 s.1.2.1, s.1.2.2) s.2 - Gs H s.1.1

omit [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma ehM_succ_Phih (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)
    (ξ : ℕ → Ω) (k : ℕ) :
    ehM H cfg x0 y0 ox oy ξ (k + 1) = Phih H cfg ox (mainS cfg x0 y0 ox oy ξ k, ξ (off cfg + k)) := by
  simp only [ehM, uq, wq, Phih]
  conv_lhs => rw [mainS]

omit [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma Dterm_state (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (hc : CfgOK cfg L μ) (w u : E) :
    ‖(1 - cfg.α) • Gs H (w - nphi cfg.η cfg.lam u) + cfg.α • Gs H (lead cfg w u) - Gs H w‖ ≤
      ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * cfg.η ^ 2 / cfg.α := by
  have hα := hc.α0
  have hconv : (1 - cfg.α) • (w - nphi cfg.η cfg.lam u) + cfg.α • lead cfg w u = w := by
    simp only [lead, smul_add, smul_smul, smul_sub]
    rw [show cfg.α * ((1 - cfg.α) / cfg.α) = 1 - cfg.α by field_simp]
    simp only [sub_smul, one_smul]; abel
  have hd := H.Gs_defect (w - nphi cfg.η cfg.lam u) (lead cfg w u) hα.le hc.α1
  rw [hconv] at hd
  have hsq := H.zs_sq (w - nphi cfg.η cfg.lam u) (lead cfg w u)
  have hsub : ‖(w - nphi cfg.η cfg.lam u) - lead cfg w u‖ ≤ cfg.η / cfg.α := by
    have e : (w - nphi cfg.η cfg.lam u) - lead cfg w u = -((1 / cfg.α) • nphi cfg.η cfg.lam u) := by
      simp only [lead]
      have : (1 / cfg.α) = 1 + (1 - cfg.α) / cfg.α := by field_simp; ring
      rw [this, add_smul, one_smul]; abel
    rw [e, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
    have := nphi_norm hc.l0 hc.η0 u
    calc 1 / cfg.α * ‖nphi cfg.η cfg.lam u‖ ≤ 1 / cfg.α * cfg.η := mul_le_mul_of_nonneg_left this (by positivity)
      _ = cfg.η / cfg.α := by ring
  have hsub2 := pow_le_pow_left₀ (norm_nonneg _) hsub 2
  have hρ := H.ρnn
  have hμ := H.μpos
  have hk : 0 ≤ 1 + L / μ := by have := H.L_pos; positivity
  have ha1 : 0 ≤ cfg.α * (1 - cfg.α) := mul_nonneg hα.le (by linarith [hc.α1])
  calc _ ≤ ρ * (1 + L / μ) * (cfg.α * (1 - cfg.α)) *
        sq (zs H (w - nphi cfg.η cfg.lam u) - zs H (lead cfg w u)) := hd
    _ ≤ ρ * (1 + L / μ) * (cfg.α * (1 - cfg.α)) * ((1 + (L / μ) ^ 2) * (cfg.η / cfg.α) ^ 2) := by
        gcongr
        exact hsq.trans (mul_le_mul_of_nonneg_left hsub2 (by positivity))
    _ ≤ ρ * (1 + L / μ) * (cfg.α * 1) * ((1 + (L / μ) ^ 2) * (cfg.η / cfg.α) ^ 2) := by
        gcongr; linarith
    _ = ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * cfg.η ^ 2 / cfg.α := by field_simp

noncomputable def kDD (L μ ρ : ℝ) (cfg : IgtConfig) : ℝ :=
  ρ * (1 + L / μ) * (1 + (L / μ) ^ 2) * cfg.η ^ 2 / cfg.α

omit [FiniteDimensional ℝ F] in
lemma eh_moment (H : Hyp f gx gy Hx Hy L μ ρ) (O : OracleHyp gx gy ox oy p σ) (cfg : IgtConfig)
    (hc : CfgOK cfg L μ) (x0 : E) (y0 : F) (k : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ (k + 1)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (1 - cfg.α) *
          ∫⁻ ξ, ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal (4 * cfg.α * L ^ 2) *
          ∫⁻ ξ, ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal (4 * kDD L μ ρ cfg ^ 2 / cfg.α + cfg.α ^ 2 * σ ^ 2) := by
  have hα0 := hc.α0
  have hα1 := hc.α1
  have hfun : (fun ξ => ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ (k + 1)‖ ^ 2)) =
      fun ξ => (fun s => ENNReal.ofReal (‖Phih H cfg ox s‖ ^ 2))
        (mainS cfg x0 y0 ox oy ξ k, ξ (off cfg + k)) := by
    funext ξ; rw [ehM_succ_Phih H cfg]
  rw [hfun]
  have hmeasP : Measurable (fun s : (E × E × F) × Ω => ENNReal.ofReal (‖Phih H cfg ox s‖ ^ 2)) := by
    have hl : Measurable (fun s : (E × E × F) × Ω => lead cfg s.1.1 s.1.2.1) :=
      (measurable_lead cfg).comp ((measurable_fst.comp measurable_fst).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_fst)))
    have hOX : Measurable (fun s : (E × E × F) × Ω => ox (lead cfg s.1.1 s.1.2.1, s.1.2.2) s.2) :=
      O.mx.comp ((hl.prodMk (measurable_snd.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd)
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.norm ?_) 2)
    unfold Phih
    exact (((measurable_fst.comp (measurable_snd.comp measurable_fst)).const_smul _).add
      (hOX.const_smul _)).sub (H.Gs_continuous.measurable.comp (measurable_fst.comp measurable_fst))
  rw [fresh_lintegral p (off cfg + k) (fun ξ => mainS cfg x0 y0 ox oy ξ k)
    (measurable_mainS cfg x0 y0 ox oy O.mx O.my k)
    (fun ξ ξ' h => mainS_congr cfg x0 y0 ox oy k h) _ hmeasP]
  have hpt : ∀ ξ, ∫⁻ ω, ENNReal.ofReal (‖Phih H cfg ox (mainS cfg x0 y0 ox oy ξ k, ω)‖ ^ 2) ∂p ≤
      ENNReal.ofReal ((1 - cfg.α) * ‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2 +
        (4 * cfg.α * L ^ 2) * ‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2 +
        (4 * kDD L μ ρ cfg ^ 2 / cfg.α + cfg.α ^ 2 * σ ^ 2)) := by
    intro ξ
    set s := mainS cfg x0 y0 ox oy ξ k
    set z : E × F := (lead cfg s.1 s.2.1, s.2.2)
    set A := (1 - cfg.α) • s.2.1 + cfg.α • gx z - Gs H s.1
    have he : ∀ ω, Phih H cfg ox (s, ω) = A + cfg.α • (ox z ω - gx z) := by
      intro ω; simp only [Phih, A, z, smul_sub]; abel
    simp_rw [he]
    refine (noise_step p A cfg.α (fun ω => ox z ω - gx z) ((O.meas_x z).sub measurable_const)
      (O.nx_int z) (O.nx_mean z) (O.ivx z) (O.vx z)).trans (ENNReal.ofReal_le_ofReal ?_)
    set eh := ehM H cfg x0 y0 ox oy ξ k
    set e := eM H cfg x0 y0 ox oy ξ k
    set wk := s.1 - nphi cfg.η cfg.lam s.2.1
    have hA : A = (1 - cfg.α) • eh + ((1 - cfg.α) • Gs H wk + cfg.α • Gs H (lead cfg s.1 s.2.1) - Gs H s.1) +
        cfg.α • (gx z - Gs H (lead cfg s.1 s.2.1)) := by
      have heh : eh = s.2.1 - Gs H wk := by simp only [eh, wk]; exact ehM_eq H cfg x0 y0 ξ k
      rw [heh]; simp only [A, smul_sub]; abel
    have hD := Dterm_state H cfg hc s.1 s.2.1
    have hb : ‖gx z - Gs H (lead cfg s.1 s.2.1)‖ ≤ L * ‖e‖ := by
      have := H.gx_lip_y (lead cfg s.1 s.2.1) s.2.2 (ystar H (lead cfg s.1 s.2.1))
      simpa [z, e, eM_eq, Gs, zs] using this
    have hrest : ‖((1 - cfg.α) • Gs H wk + cfg.α • Gs H (lead cfg s.1 s.2.1) - Gs H s.1) +
        cfg.α • (gx z - Gs H (lead cfg s.1 s.2.1))‖ ≤ kDD L μ ρ cfg + cfg.α * (L * ‖e‖) := by
      refine (norm_add_le _ _).trans (add_le_add hD ?_)
      rw [norm_smul, Real.norm_of_nonneg hα0.le]; exact mul_le_mul_of_nonneg_left hb hα0.le
    have hy := young_sq ((1 - cfg.α) • eh) (((1 - cfg.α) • Gs H wk + cfg.α • Gs H (lead cfg s.1 s.2.1) -
        Gs H s.1) + cfg.α • (gx z - Gs H (lead cfg s.1 s.2.1))) hα0
    rw [← add_assoc, ← hA] at hy
    rw [norm_smul, Real.norm_of_nonneg (by linarith), mul_pow] at hy
    have hr2 := pow_le_pow_left₀ (norm_nonneg _) hrest 2
    have hDD0 : 0 ≤ kDD L μ ρ cfg := by
      simp only [kDD]; have := H.ρnn; have := H.L_pos; have := H.μpos; positivity
    have h1 : (1 + cfg.α) * ((1 - cfg.α) ^ 2 * ‖eh‖ ^ 2) ≤ (1 - cfg.α) * ‖eh‖ ^ 2 := by
      have e1 : (1 + cfg.α) * (1 - cfg.α) ^ 2 = (1 - cfg.α) - cfg.α ^ 2 * (1 - cfg.α) := by ring
      have h0 : 0 ≤ cfg.α ^ 2 * (1 - cfg.α) := mul_nonneg (sq_nonneg _) (by linarith)
      have : (1 + cfg.α) * (1 - cfg.α) ^ 2 ≤ 1 - cfg.α := by rw [e1]; linarith
      calc (1 + cfg.α) * ((1 - cfg.α) ^ 2 * ‖eh‖ ^ 2) = ((1 + cfg.α) * (1 - cfg.α) ^ 2) * ‖eh‖ ^ 2 := by ring
        _ ≤ (1 - cfg.α) * ‖eh‖ ^ 2 := mul_le_mul_of_nonneg_right this (sq_nonneg _)
    have h2 : (1 + 1 / cfg.α) * (kDD L μ ρ cfg + cfg.α * (L * ‖e‖)) ^ 2 ≤
        4 * kDD L μ ρ cfg ^ 2 / cfg.α + 4 * cfg.α * L ^ 2 * ‖e‖ ^ 2 := by
      have hc2 : 1 + 1 / cfg.α ≤ 2 / cfg.α := by
        have e2 : 2 / cfg.α - (1 + 1 / cfg.α) = (1 - cfg.α) / cfg.α := by field_simp; ring
        have : 0 ≤ (1 - cfg.α) / cfg.α := div_nonneg (by linarith) hα0.le
        linarith
      have hsq : (kDD L μ ρ cfg + cfg.α * (L * ‖e‖)) ^ 2 ≤ 2 * kDD L μ ρ cfg ^ 2 + 2 * (cfg.α * (L * ‖e‖)) ^ 2 := by
        nlinarith [sq_nonneg (kDD L μ ρ cfg - cfg.α * (L * ‖e‖))]
      calc (1 + 1 / cfg.α) * (kDD L μ ρ cfg + cfg.α * (L * ‖e‖)) ^ 2
          ≤ (2 / cfg.α) * (2 * kDD L μ ρ cfg ^ 2 + 2 * (cfg.α * (L * ‖e‖)) ^ 2) := by
            apply mul_le_mul hc2 hsq (sq_nonneg _) (by positivity)
        _ = 4 * kDD L μ ρ cfg ^ 2 / cfg.α + 4 * cfg.α * L ^ 2 * ‖e‖ ^ 2 := by field_simp; ring
    have h3 := mul_le_mul_of_nonneg_left hr2 (by positivity : (0:ℝ) ≤ 1 + 1 / cfg.α)
    nlinarith
  refine (lintegral_mono hpt).trans ?_
  have me := measurable_eM H cfg x0 y0 O.mx O.my k (ox := ox) (oy := oy)
  have mh := measurable_ehM H cfg x0 y0 O.mx O.my k (ox := ox) (oy := oy)
  have hsplit : ∀ ξ, ENNReal.ofReal ((1 - cfg.α) * ‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2 +
        (4 * cfg.α * L ^ 2) * ‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2 +
        (4 * kDD L μ ρ cfg ^ 2 / cfg.α + cfg.α ^ 2 * σ ^ 2)) =
      ENNReal.ofReal (1 - cfg.α) * ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2) +
        ENNReal.ofReal (4 * cfg.α * L ^ 2) * ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2) +
        ENNReal.ofReal (4 * kDD L μ ρ cfg ^ 2 / cfg.α + cfg.α ^ 2 * σ ^ 2) := by
    intro ξ
    have h1 : 0 ≤ 1 - cfg.α := by linarith
    have hDD0 : 0 ≤ kDD L μ ρ cfg := by
      simp only [kDD]; have := H.ρnn; have := H.L_pos; have := H.μpos; positivity
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul h1, ENNReal.ofReal_mul (by positivity)]
  simp_rw [hsplit]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  rw [lintegral_add_left (f := fun ξ => ENNReal.ofReal (1 - cfg.α) *
      ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2))
    ((ENNReal.measurable_ofReal.comp (mh.norm.pow_const 2)).const_mul _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end OracleTemplate.HessianNcsc
