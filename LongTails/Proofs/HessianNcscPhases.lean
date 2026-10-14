import LongTails.Proofs.HessianNcscR

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

omit [FiniteDimensional ℝ F] in
lemma ystep_point (H : Hyp f gx gy Hx Hy L μ ρ) (O : OracleHyp gx gy ox oy p σ) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ : γ ≤ μ / L ^ 2) (x : E) (y : F) :
    ∫⁻ ω, ENNReal.ofReal (‖y + γ • oy (x, y) ω - ystar H x‖ ^ 2) ∂p ≤
      ENNReal.ofReal ((1 - γ * μ) * ‖y - ystar H x‖ ^ 2 + γ ^ 2 * σ ^ 2) := by
  set A := (y - ystar H x) + γ • gy (x, y)
  have he : ∀ ω, y + γ • oy (x, y) ω - ystar H x = A + γ • (oy (x, y) ω - gy (x, y)) := by
    intro ω; simp only [A, smul_sub]; abel
  simp_rw [he]
  refine (noise_step p A γ (fun ω => oy (x, y) ω - gy (x, y)) ((O.meas_y _).sub measurable_const)
    (O.ny_int _) (O.ny_mean _) (O.ivy _) (O.vy _)).trans (ENNReal.ofReal_le_ofReal ?_)
  have hy : y = ystar H x + (y - ystar H x) := by abel
  have hc := H.contraction x (y - ystar H x) hγ0.le hγ
  rw [← hy] at hc
  linarith

section PhaseA

variable (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)

omit [FiniteDimensional ℝ F] in
lemma phaseA_moment (O : OracleHyp gx gy ox oy p σ) (hc : CfgOK cfg L μ) (j : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (‖yA cfg x0 y0 oy ξ (j + 1) - ystar H x0‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (1 - cfg.γ * μ) *
          ∫⁻ ξ, ENNReal.ofReal (‖yA cfg x0 y0 oy ξ j - ystar H x0‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal (cfg.γ ^ 2 * σ ^ 2) := by
  have hgm : cfg.γ * μ ≤ 1 := by
    have h1 : cfg.γ * μ ≤ μ / L ^ 2 * μ := mul_le_mul_of_nonneg_right hc.γ1 H.μpos.le
    have h2 : μ / L ^ 2 * μ ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by have := H.L_pos; positivity)]; nlinarith [H.μL, H.μpos]
    linarith
  have hfun : (fun ξ => ENNReal.ofReal (‖yA cfg x0 y0 oy ξ (j + 1) - ystar H x0‖ ^ 2)) =
      fun ξ => (fun s : F × Ω => ENNReal.ofReal (‖s.1 + cfg.γ • oy (x0, s.1) s.2 - ystar H x0‖ ^ 2))
        (yA cfg x0 y0 oy ξ j, ξ j) := by
    funext ξ; simp only [yA]
  rw [hfun]
  have hmeas : Measurable (fun s : F × Ω => ENNReal.ofReal (‖s.1 + cfg.γ • oy (x0, s.1) s.2 - ystar H x0‖ ^ 2)) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.norm ?_) 2)
    exact (measurable_fst.add ((O.my.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)).const_smul _)).sub
      measurable_const
  rw [fresh_lintegral p j (fun ξ => yA cfg x0 y0 oy ξ j) (measurable_yA cfg x0 y0 oy O.my j)
    (fun ξ ξ' h => yA_congr cfg x0 y0 oy j h) _ hmeas]
  refine (lintegral_mono fun ξ => ystep_point H O hc.γ0 hc.γ1 x0 (yA cfg x0 y0 oy ξ j)).trans ?_
  have hsplit : ∀ ξ, ENNReal.ofReal ((1 - cfg.γ * μ) * ‖yA cfg x0 y0 oy ξ j - ystar H x0‖ ^ 2 + cfg.γ ^ 2 * σ ^ 2) =
      ENNReal.ofReal (1 - cfg.γ * μ) * ENNReal.ofReal (‖yA cfg x0 y0 oy ξ j - ystar H x0‖ ^ 2) +
        ENNReal.ofReal (cfg.γ ^ 2 * σ ^ 2) := by
    intro ξ
    rw [ENNReal.ofReal_add (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity),
      ENNReal.ofReal_mul (by linarith)]
  simp_rw [hsplit]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end PhaseA

section PhaseBC

variable (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)

noncomputable def bdev (ox : E × F → Ω → E) (oy : E × F → Ω → F) (ξ : ℕ → Ω) (j : ℕ) : E :=
  accB cfg x0 y0 ox oy ξ j - (j : ℝ) • gx (x0, yA cfg x0 y0 oy ξ cfg.NA)

include H in
omit [FiniteDimensional ℝ F] in
lemma batch_moment (O : OracleHyp gx gy ox oy p σ) (j : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (‖bdev cfg x0 y0 (gx := gx) ox oy ξ (j + 1)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ∫⁻ ξ, ENNReal.ofReal (‖bdev cfg x0 y0 (gx := gx) ox oy ξ j‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal (σ ^ 2) := by
  have hfun : (fun ξ => ENNReal.ofReal (‖bdev cfg x0 y0 (gx := gx) ox oy ξ (j + 1)‖ ^ 2)) =
      fun ξ => (fun s : (F × E) × Ω => ENNReal.ofReal (‖s.1.2 + (1 : ℝ) • (ox (x0, s.1.1) s.2 - gx (x0, s.1.1))‖ ^ 2))
        ((yA cfg x0 y0 oy ξ cfg.NA, bdev cfg x0 y0 (gx := gx) ox oy ξ j), ξ (cfg.NA + j)) := by
    funext ξ; simp only [bdev, accB, one_smul, Nat.cast_succ, add_smul]; congr 2; abel
  rw [hfun]
  have hgx := H.gx_continuous
  have hmeas : Measurable (fun s : (F × E) × Ω =>
      ENNReal.ofReal (‖s.1.2 + (1 : ℝ) • (ox (x0, s.1.1) s.2 - gx (x0, s.1.1))‖ ^ 2)) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.norm ?_) 2)
    have hz : Measurable (fun s : (F × E) × Ω => (x0, s.1.1)) := measurable_const.prodMk (measurable_fst.comp measurable_fst)
    exact (measurable_snd.comp measurable_fst).add
      (((O.mx.comp (hz.prodMk measurable_snd)).sub (hgx.measurable.comp hz)).const_smul _)
  have hbm : Measurable (fun ξ => bdev cfg x0 y0 (gx := gx) ox oy ξ j) := by
    simp only [bdev]
    exact (measurable_accB cfg x0 y0 ox oy O.mx O.my j).sub
      ((hgx.measurable.comp (measurable_const.prodMk (measurable_yA cfg x0 y0 oy O.my cfg.NA))).const_smul _)
  rw [fresh_lintegral p (cfg.NA + j) (fun ξ => (yA cfg x0 y0 oy ξ cfg.NA, bdev cfg x0 y0 (gx := gx) ox oy ξ j))
    ((measurable_yA cfg x0 y0 oy O.my cfg.NA).prodMk hbm)
    (fun ξ ξ' h => by
      simp only [Prod.mk.injEq, bdev]
      have h1 := yA_congr cfg x0 y0 oy cfg.NA (fun i hi => h i (by omega)) (ξ := ξ) (ξ' := ξ')
      have h2 := accB_congr cfg x0 y0 ox oy j h (ξ := ξ) (ξ' := ξ')
      exact ⟨h1, by rw [h1, h2]⟩) _ hmeas]
  refine (lintegral_mono fun ξ => noise_step p (bdev cfg x0 y0 (gx := gx) ox oy ξ j) (1 : ℝ)
    (fun ω => ox (x0, yA cfg x0 y0 oy ξ cfg.NA) ω - gx (x0, yA cfg x0 y0 oy ξ cfg.NA))
    ((O.meas_x _).sub measurable_const) (O.nx_int _) (O.nx_mean _) (O.ivx _) (O.vx _)).trans ?_
  have hsplit : ∀ ξ, ENNReal.ofReal (‖bdev cfg x0 y0 (gx := gx) ox oy ξ j‖ ^ 2 + (1 : ℝ) ^ 2 * σ ^ 2) =
      ENNReal.ofReal (‖bdev cfg x0 y0 (gx := gx) ox oy ξ j‖ ^ 2) + ENNReal.ofReal (σ ^ 2) := by
    intro ξ; rw [one_pow, one_mul, ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  simp_rw [hsplit]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

noncomputable def eC (ox : E × F → Ω → E) (oy : E × F → Ω → F) (ξ : ℕ → Ω) (j : ℕ) : F :=
  yC cfg x0 y0 ox oy ξ j - ystar H (xtOne cfg x0 y0 ox oy ξ)

omit [FiniteDimensional ℝ F] in
lemma phaseC_moment (O : OracleHyp gx gy ox oy p σ) (hc : CfgOK cfg L μ) (j : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (‖eC H cfg x0 y0 ox oy ξ (j + 1)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (1 - cfg.γ * μ) *
          ∫⁻ ξ, ENNReal.ofReal (‖eC H cfg x0 y0 ox oy ξ j‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal (cfg.γ ^ 2 * σ ^ 2) := by
  have hgm : cfg.γ * μ ≤ 1 := by
    have h1 : cfg.γ * μ ≤ μ / L ^ 2 * μ := mul_le_mul_of_nonneg_right hc.γ1 H.μpos.le
    have h2 : μ / L ^ 2 * μ ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by have := H.L_pos; positivity)]; nlinarith [H.μL, H.μpos]
    linarith
  have hfun : (fun ξ => ENNReal.ofReal (‖eC H cfg x0 y0 ox oy ξ (j + 1)‖ ^ 2)) =
      fun ξ => (fun s : (E × F) × Ω => ENNReal.ofReal (‖s.1.2 + cfg.γ • oy (s.1.1, s.1.2) s.2 - ystar H s.1.1‖ ^ 2))
        ((xtOne cfg x0 y0 ox oy ξ, yC cfg x0 y0 ox oy ξ j), ξ (cfg.NA + cfg.NB + j)) := by
    funext ξ; simp only [eC, yC]
  rw [hfun]
  have hmeas : Measurable (fun s : (E × F) × Ω =>
      ENNReal.ofReal (‖s.1.2 + cfg.γ • oy (s.1.1, s.1.2) s.2 - ystar H s.1.1‖ ^ 2)) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.norm ?_) 2)
    exact ((measurable_snd.comp measurable_fst).add ((O.my.comp (measurable_fst.prodMk measurable_snd)).const_smul _)).sub
      (H.ystar_continuous.measurable.comp (measurable_fst.comp measurable_fst))
  rw [fresh_lintegral p (cfg.NA + cfg.NB + j) (fun ξ => (xtOne cfg x0 y0 ox oy ξ, yC cfg x0 y0 ox oy ξ j))
    ((measurable_xtOne cfg x0 y0 ox oy O.mx O.my).prodMk (measurable_yC cfg x0 y0 ox oy O.mx O.my j))
    (fun ξ ξ' h => by
      simp only [Prod.mk.injEq]
      have hm := mInit_congr cfg x0 y0 ox oy (fun i hi => h i (by omega)) (ξ := ξ) (ξ' := ξ')
      refine ⟨by simp only [xtOne, wOne, hm], yC_congr cfg x0 y0 ox oy j h⟩) _ hmeas]
  refine (lintegral_mono fun ξ => ystep_point H O hc.γ0 hc.γ1 (xtOne cfg x0 y0 ox oy ξ)
    (yC cfg x0 y0 ox oy ξ j)).trans ?_
  have hsplit : ∀ ξ, ENNReal.ofReal ((1 - cfg.γ * μ) * ‖yC cfg x0 y0 ox oy ξ j - ystar H (xtOne cfg x0 y0 ox oy ξ)‖ ^ 2 +
        cfg.γ ^ 2 * σ ^ 2) =
      ENNReal.ofReal (1 - cfg.γ * μ) * ENNReal.ofReal (‖eC H cfg x0 y0 ox oy ξ j‖ ^ 2) +
        ENNReal.ofReal (cfg.γ ^ 2 * σ ^ 2) := by
    intro ξ
    rw [ENNReal.ofReal_add (mul_nonneg (by linarith) (sq_nonneg _)) (by positivity),
      ENNReal.ofReal_mul (by linarith)]; rfl
  simp_rw [hsplit]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end PhaseBC

end OracleTemplate.HessianNcsc
