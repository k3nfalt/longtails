import LongTails.Proofs.HessianNcscMain

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.HessianNcsc

lemma inv_pair (me mh : ℕ → ℝ≥0∞) {Ae Ah A0 Be B0 a Es Ps : ℝ} (hAe : 0 ≤ Ae) (hAh : 0 ≤ Ah)
    (hA0 : 0 ≤ A0) (hBe : 0 ≤ Be) (hB0 : 0 ≤ B0) (ha : a ≤ 1) (hEs : 0 ≤ Es) (hPs : 0 ≤ Ps)
    (hme : ∀ k, me (k + 1) ≤ ENNReal.ofReal Ae * me k + ENNReal.ofReal Ah * mh k + ENNReal.ofReal A0)
    (hmh : ∀ k, mh (k + 1) ≤ ENNReal.ofReal (1 - a) * mh k + ENNReal.ofReal Be * me k + ENNReal.ofReal B0)
    (h0e : me 0 ≤ ENNReal.ofReal Es) (h0h : mh 0 ≤ ENNReal.ofReal Ps)
    (c1 : Ae * Es + Ah * Ps + A0 ≤ Es) (c2 : (1 - a) * Ps + Be * Es + B0 ≤ Ps) :
    ∀ k, me k ≤ ENNReal.ofReal Es ∧ mh k ≤ ENNReal.ofReal Ps := by
  intro k
  induction k with
  | zero => exact ⟨h0e, h0h⟩
  | succ k ih =>
    exact ⟨(hme k).trans (enn_affine_le hAe hAh hA0 hEs hPs ih.1 ih.2 c1),
      (hmh k).trans (enn_affine_le (by linarith) hBe hB0 hPs hEs ih.2 ih.1 c2)⟩

variable {E F Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω]

variable {f : E → F → ℝ} {gx : E × F → E} {gy : E × F → F}
  {Hx : E × F → (E × F →L[ℝ] E)} {Hy : E × F → (E × F →L[ℝ] F)} {L μ ρ : ℝ}
  {ox : E × F → Ω → E} {oy : E × F → Ω → F} {p : Measure Ω} [IsProbabilityMeasure p] {σ : ℝ}

omit [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma CfgOK.gm (H : Hyp f gx gy Hx Hy L μ ρ) {cfg : IgtConfig} (hc : CfgOK cfg L μ) :
    0 < cfg.γ * μ ∧ cfg.γ * μ ≤ 1 := by
  refine ⟨mul_pos hc.γ0 H.μpos, ?_⟩
  have h1 : cfg.γ * μ ≤ μ / L ^ 2 * μ := mul_le_mul_of_nonneg_right hc.γ1 H.μpos.le
  have h2 : μ / L ^ 2 * μ ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by have := H.L_pos; positivity)]; nlinarith [H.μL, H.μpos]
  linarith

lemma sq_add_le2 {V : Type*} [NormedAddCommGroup V] (a b : V) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have := norm_add_le a b
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]

section Init

variable (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)

omit [FiniteDimensional ℝ F] in
lemma mA_bound (O : OracleHyp gx gy ox oy p σ) (hc : CfgOK cfg L μ) {G : ℝ} (hG : ‖gy (x0, y0)‖ ≤ G) :
    ∫⁻ ξ, ENNReal.ofReal (‖yA cfg x0 y0 oy ξ cfg.NA - ystar H x0‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal ((1 - cfg.γ * μ) ^ cfg.NA * (G / μ) ^ 2 + cfg.γ ^ 2 * σ ^ 2 / (1 - (1 - cfg.γ * μ))) := by
  obtain ⟨h0, h1⟩ := hc.gm H
  have hd := H.y0_dist x0 y0 hG
  refine geom_closed (by linarith) (by linarith) (by positivity) (sq_nonneg _)
    (fun j => ∫⁻ ξ, ENNReal.ofReal (‖yA cfg x0 y0 oy ξ j - ystar H x0‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p))
    ?_ (fun j => phaseA_moment H cfg x0 y0 O hc j) cfg.NA
  simp only [yA]
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hd 2)

include H in
omit [FiniteDimensional ℝ F] in
lemma batch_total (O : OracleHyp gx gy ox oy p σ) : ∀ j : ℕ,
    ∫⁻ ξ, ENNReal.ofReal (‖bdev cfg x0 y0 (gx := gx) ox oy ξ j‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (j * σ ^ 2)
  | 0 => by simp [bdev, accB]
  | j + 1 => by
      refine (batch_moment H cfg x0 y0 O j).trans ?_
      refine (add_le_add (batch_total O j) le_rfl).trans ?_
      rw [← ENNReal.ofReal_add (by positivity) (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal; push_cast; ring_nf; rfl

omit [FiniteDimensional ℝ F] in
lemma me0_bound (O : OracleHyp gx gy ox oy p σ) (hc : CfgOK cfg L μ) {MA : ℝ} (hMA0 : 0 ≤ MA)
    (hMA : ∫⁻ ξ, ENNReal.ofReal (‖yA cfg x0 y0 oy ξ cfg.NA - ystar H x0‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal MA) :
    ∫⁻ ξ, ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ 0‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal ((1 - cfg.γ * μ) ^ cfg.NC * (2 * MA + 2 * ((L / μ) * (cfg.η / cfg.α)) ^ 2) +
        cfg.γ ^ 2 * σ ^ 2 / (1 - (1 - cfg.γ * μ))) := by
  obtain ⟨h0, h1⟩ := hc.gm H
  have hm := measurable_yA cfg x0 y0 oy O.my cfg.NA
  have hz : ∫⁻ ξ, ENNReal.ofReal (‖eC H cfg x0 y0 ox oy ξ 0‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (2 * MA + 2 * ((L / μ) * (cfg.η / cfg.α)) ^ 2) := by
    have hpt : ∀ ξ, ENNReal.ofReal (‖eC H cfg x0 y0 ox oy ξ 0‖ ^ 2) ≤
        ENNReal.ofReal 2 * ENNReal.ofReal (‖yA cfg x0 y0 oy ξ cfg.NA - ystar H x0‖ ^ 2) +
          ENNReal.ofReal (2 * ((L / μ) * (cfg.η / cfg.α)) ^ 2) := by
      intro ξ
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hb := eC_zero_bound H cfg x0 y0 hc ξ (ox := ox) (oy := oy)
      have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      nlinarith [sq_nonneg (‖yA cfg x0 y0 oy ξ cfg.NA - ystar H x0‖ - (L / μ) * (cfg.η / cfg.α))]
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal 2 * ∫⁻ ξ, ENNReal.ofReal (‖yA cfg x0 y0 oy ξ cfg.NA - ystar H x0‖ ^ 2)
          ∂(Measure.infinitePi fun _ : ℕ => p) + ENNReal.ofReal (2 * ((L / μ) * (cfg.η / cfg.α)) ^ 2)
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal MA + ENNReal.ofReal (2 * ((L / μ) * (cfg.η / cfg.α)) ^ 2) := by
          gcongr
      _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have := geom_closed (by linarith) (by linarith) (by positivity) (by positivity)
    (fun j => ∫⁻ ξ, ENNReal.ofReal (‖eC H cfg x0 y0 ox oy ξ j‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p))
    hz (fun j => phaseC_moment H cfg x0 y0 O hc j) cfg.NC
  exact this

omit [FiniteDimensional ℝ F] in
lemma mh0_bound (O : OracleHyp gx gy ox oy p σ) (hNB : 1 ≤ cfg.NB) {MA : ℝ} (hMA0 : 0 ≤ MA)
    (hMA : ∫⁻ ξ, ENNReal.ofReal (‖yA cfg x0 y0 oy ξ cfg.NA - ystar H x0‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal MA) :
    ∫⁻ ξ, ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ 0‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (2 * σ ^ 2 / cfg.NB + 2 * L ^ 2 * MA) := by
  have hN1 : (1 : ℝ) ≤ cfg.NB := by exact_mod_cast hNB
  have hN0 : (0 : ℝ) < cfg.NB := by linarith
  have hL := H.L_pos
  have hpt : ∀ ξ, ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ 0‖ ^ 2) ≤
      ENNReal.ofReal (2 / (cfg.NB : ℝ) ^ 2) * ENNReal.ofReal (‖bdev cfg x0 y0 (gx := gx) ox oy ξ cfg.NB‖ ^ 2) +
        ENNReal.ofReal (2 * L ^ 2) * ENNReal.ofReal (‖yA cfg x0 y0 oy ξ cfg.NA - ystar H x0‖ ^ 2) := by
    intro ξ
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [ehM_zero_eq H cfg x0 y0 hNB ξ]
    refine (sq_add_le2 _ _).trans ?_
    have hb : ‖gx (x0, yA cfg x0 y0 oy ξ cfg.NA) - Gs H x0‖ ≤ L * ‖yA cfg x0 y0 oy ξ cfg.NA - ystar H x0‖ := by
      have := H.gx_lip_y x0 (yA cfg x0 y0 oy ξ cfg.NA) (ystar H x0)
      simpa [Gs, zs] using this
    have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    rw [norm_smul, mul_pow, Real.norm_of_nonneg (by positivity), div_pow, one_pow]
    have : 2 * (1 / (cfg.NB : ℝ) ^ 2 * ‖bdev cfg x0 y0 (gx := gx) ox oy ξ cfg.NB‖ ^ 2) =
        2 / (cfg.NB : ℝ) ^ 2 * ‖bdev cfg x0 y0 (gx := gx) ox oy ξ cfg.NB‖ ^ 2 := by ring
    nlinarith
  refine (lintegral_mono hpt).trans ?_
  have hbm : Measurable (fun ξ => ENNReal.ofReal (‖bdev cfg x0 y0 (gx := gx) ox oy ξ cfg.NB‖ ^ 2)) := by
    simp only [bdev]
    exact ENNReal.measurable_ofReal.comp (((measurable_accB cfg x0 y0 ox oy O.mx O.my cfg.NB).sub
      ((H.gx_continuous.measurable.comp (measurable_const.prodMk
        (measurable_yA cfg x0 y0 oy O.my cfg.NA))).const_smul _)).norm.pow_const 2)
  rw [lintegral_add_left (hbm.const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hB := batch_total H cfg x0 y0 O cfg.NB
  calc ENNReal.ofReal (2 / (cfg.NB : ℝ) ^ 2) * ∫⁻ ξ, ENNReal.ofReal (‖bdev cfg x0 y0 (gx := gx) ox oy ξ cfg.NB‖ ^ 2)
        ∂(Measure.infinitePi fun _ : ℕ => p) + ENNReal.ofReal (2 * L ^ 2) *
        ∫⁻ ξ, ENNReal.ofReal (‖yA cfg x0 y0 oy ξ cfg.NA - ystar H x0‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p)
      ≤ ENNReal.ofReal (2 / (cfg.NB : ℝ) ^ 2) * ENNReal.ofReal (cfg.NB * σ ^ 2) +
          ENNReal.ofReal (2 * L ^ 2) * ENNReal.ofReal MA := by gcongr
    _ = ENNReal.ofReal (2 * σ ^ 2 / cfg.NB + 2 * L ^ 2 * MA) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; field_simp

end Init

section All

variable (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)

lemma moments_all (O : OracleHyp gx gy ox oy p σ) (hc : CfgOK cfg L μ) (hNB : 1 ≤ cfg.NB)
    {G Es Ps : ℝ} (hG : ‖gy (x0, y0)‖ ≤ G) (hEs : 0 ≤ Es) (hPs : 0 ≤ Ps)
    (hA : (1 - cfg.γ * μ) ^ cfg.NA * (G / μ) ^ 2 + cfg.γ ^ 2 * σ ^ 2 / (1 - (1 - cfg.γ * μ)) ≤ 2 * Es)
    (hC : (1 - cfg.γ * μ) ^ cfg.NC * (2 * (2 * Es) + 2 * ((L / μ) * (cfg.η / cfg.α)) ^ 2) +
      cfg.γ ^ 2 * σ ^ 2 / (1 - (1 - cfg.γ * μ)) ≤ Es)
    (hB : 2 * σ ^ 2 / cfg.NB + 2 * L ^ 2 * (2 * Es) ≤ Ps)
    (c1 : kAe L μ cfg * Es + kAh L μ cfg * Ps + kA0 L μ ρ σ cfg ≤ Es)
    (c2 : (1 - cfg.α) * Ps + 4 * cfg.α * L ^ 2 * Es + (4 * kDD L μ ρ cfg ^ 2 / cfg.α + cfg.α ^ 2 * σ ^ 2) ≤ Ps) :
    ∀ k, ∫⁻ ξ, ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        ENNReal.ofReal Es ∧
      ∫⁻ ξ, ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        ENNReal.ofReal Ps := by
  obtain ⟨h0, h1⟩ := hc.gm H
  have hμ := H.μpos
  have hL := H.L_pos
  have hα := hc.α0
  have hMA := (mA_bound H cfg x0 y0 O hc hG).trans (ENNReal.ofReal_le_ofReal hA)
  have hDD0 : 0 ≤ kDD L μ ρ cfg := by
    simp only [kDD]; have := H.ρnn; have := hc.η0; positivity
  refine inv_pair _ _ ?_ ?_ ?_ (by positivity) (by positivity) hc.α1 hEs hPs
    (fun k => track_moment H O cfg hc x0 y0 k) (fun k => eh_moment H O cfg hc x0 y0 k)
    ((me0_bound H cfg x0 y0 O hc (by positivity) hMA).trans (ENNReal.ofReal_le_ofReal hC))
    ((mh0_bound H cfg x0 y0 O hNB (by positivity) hMA).trans (ENNReal.ofReal_le_ofReal hB)) c1 c2
  · simp only [kAe]; have : 0 ≤ (9 / (cfg.γ * μ)) * kCe L μ cfg ^ 2 := by positivity
    linarith
  · simp only [kAh]; positivity
  · simp only [kA0]; positivity

lemma nu_all (O : OracleHyp gx gy ox oy p σ) (hc : CfgOK cfg L μ) (k : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (‖nuq H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (cfg.α * ((1 + (L / μ) ^ 2) * σ ^ 2)) := by
  have hα := hc.α0
  have hα1 := hc.α1
  have h := geom_closed (r := (1 - cfg.α) ^ 2) (c := cfg.α ^ 2 * ((1 + (L / μ) ^ 2) * σ ^ 2)) (X0 := 0)
    (sq_nonneg _) (by nlinarith) (by positivity) le_rfl
    (fun j => ∫⁻ ξ, ENNReal.ofReal (‖nuq H cfg x0 y0 ox oy ξ j‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p))
    (by simp [nuq]) (fun j => nu_moment H O cfg x0 y0 j) k
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  have hd : 1 - (1 - cfg.α) ^ 2 = cfg.α * (2 - cfg.α) := by ring
  rw [mul_zero, zero_add, hd]
  have hc0 : 0 ≤ (1 + (L / μ) ^ 2) * σ ^ 2 := by positivity
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith [mul_nonneg (mul_nonneg hα.le hα.le) hc0]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
lemma rbar_nonneg (hc : CfgOK cfg L μ) (ξ : ℕ → Ω) : ∀ k, 0 ≤ rbar H cfg x0 y0 ox oy ξ k
  | 0 => by
      simp only [rbar]
      have := hc.α0; have := hc.γ0; have := H.L_pos; have := H.μpos; positivity
  | k + 1 => by
      have ih := rbar_nonneg hc ξ k
      have := hc.α0; have := hc.α1; have := hc.γ0; have := H.L_pos; have := H.μpos; have := H.ρnn
      have := hc.η0
      simp only [rbar, kq0, kq1, kq2]
      have : 0 ≤ (1 - cfg.α) * rbar H cfg x0 y0 ox oy ξ k := mul_nonneg (by linarith) ih
      positivity

lemma l1_add3 {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) (u v w : Ξ → ℝ)
    (hu : Measurable u) (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x)
    (h : ∀ x, w x ≤ u x + v x) :
    ∫⁻ x, ENNReal.ofReal (w x) ∂P ≤ ∫⁻ x, ENNReal.ofReal (u x) ∂P + ∫⁻ x, ENNReal.ofReal (v x) ∂P := by
  rw [← lintegral_add_left (f := fun x => ENNReal.ofReal (u x)) (ENNReal.measurable_ofReal.comp hu)]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_add (hu0 x) (hv0 x)]
  exact ENNReal.ofReal_le_ofReal (h x)

omit [FiniteDimensional ℝ F] in
lemma rbar_l1 (O : OracleHyp gx gy ox oy p σ) (hc : CfgOK cfg L μ) {Es Ps : ℝ} (hEs : 0 < Es) (hPs : 0 < Ps)
    (hm : ∀ k, ∫⁻ ξ, ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        ENNReal.ofReal Es ∧
      ∫⁻ ξ, ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        ENNReal.ofReal Ps) (k : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (rbar H cfg x0 y0 ox oy ξ k) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal ((1 - cfg.α) ^ k * (Real.sqrt Ps + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es) +
        (kq0 L μ ρ cfg + kq1 L μ ρ cfg * Real.sqrt Es + kq2 L μ ρ cfg * Es) / (1 - (1 - cfg.α))) := by
  set P0 := Measure.infinitePi fun _ : ℕ => p
  have hα := hc.α0
  have hα1 := hc.α1
  have hγ := hc.γ0
  have hk : 0 ≤ L / μ := div_nonneg H.L_pos.le H.μpos.le
  have hq0 : 0 ≤ kq0 L μ ρ cfg := by
    simp only [kq0]; have := H.ρnn; have := hc.η0; have := H.μpos; have := H.L_pos; positivity
  have hq1 : 0 ≤ kq1 L μ ρ cfg := by
    simp only [kq1]; have := H.ρnn; have := hc.η0; have := H.μpos; have := H.L_pos; positivity
  have hq2 : 0 ≤ kq2 L μ ρ cfg := by
    simp only [kq2]; have := H.ρnn; positivity
  have me1 : ∀ k, ∫⁻ ξ, ENNReal.ofReal ‖eM H cfg x0 y0 ox oy ξ k‖ ∂P0 ≤ ENNReal.ofReal (Real.sqrt Es) :=
    fun k => l1_of_l2 P0 _ hEs (hm k).1
  have mh1 : ∀ k, ∫⁻ ξ, ENNReal.ofReal ‖ehM H cfg x0 y0 ox oy ξ k‖ ∂P0 ≤ ENNReal.ofReal (Real.sqrt Ps) :=
    fun k => l1_of_l2 P0 _ hPs (hm k).2
  refine geom_closed (by linarith) (by linarith) (by positivity) (by positivity)
    (fun k => ∫⁻ ξ, ENNReal.ofReal (rbar H cfg x0 y0 ox oy ξ k) ∂P0) ?_ ?_ k
  · simp only [rbar]
    refine (l1_add3 P0 _ _ _ (measurable_ehM H cfg x0 y0 O.mx O.my 0).norm
      (fun _ => norm_nonneg _) (fun _ => by positivity) (fun _ => le_rfl)).trans ?_
    have h2 : ∫⁻ ξ, ENNReal.ofReal (cfg.α / cfg.γ * (L / μ) * ‖eM H cfg x0 y0 ox oy ξ 0‖) ∂P0 ≤
        ENNReal.ofReal (cfg.α / cfg.γ * (L / μ) * Real.sqrt Es) := by
      simp_rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ cfg.α / cfg.γ * (L / μ))]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr; exact me1 0
    calc _ ≤ ENNReal.ofReal (Real.sqrt Ps) + ENNReal.ofReal (cfg.α / cfg.γ * (L / μ) * Real.sqrt Es) :=
          add_le_add (mh1 0) h2
      _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  · intro j
    have hr := measurable_rbar H cfg x0 y0 O.mx O.my j
    have he := (measurable_eM H cfg x0 y0 O.mx O.my j).norm
    have hpt : ∀ ξ, ENNReal.ofReal (rbar H cfg x0 y0 ox oy ξ (j + 1)) =
        ENNReal.ofReal (1 - cfg.α) * ENNReal.ofReal (rbar H cfg x0 y0 ox oy ξ j) +
          (ENNReal.ofReal (kq1 L μ ρ cfg) * ENNReal.ofReal ‖eM H cfg x0 y0 ox oy ξ j‖ +
            ENNReal.ofReal (kq2 L μ ρ cfg) * ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ j‖ ^ 2)) +
          ENNReal.ofReal (kq0 L μ ρ cfg) := by
      intro ξ
      have h0 := rbar_nonneg H cfg x0 y0 hc ξ j (ox := ox) (oy := oy)
      rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul hq1, ← ENNReal.ofReal_mul hq2,
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (mul_nonneg (by linarith) h0) (by positivity),
        ← ENNReal.ofReal_add (by positivity) hq0]
      congr 1; simp only [rbar]; ring
    simp_rw [hpt]
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      lintegral_add_left (f := fun ξ => ENNReal.ofReal (1 - cfg.α) * ENNReal.ofReal (rbar H cfg x0 y0 ox oy ξ j))
        ((ENNReal.measurable_ofReal.comp hr).const_mul _),
      lintegral_add_left (f := fun ξ => ENNReal.ofReal (kq1 L μ ρ cfg) * ENNReal.ofReal ‖eM H cfg x0 y0 ox oy ξ j‖)
        ((ENNReal.measurable_ofReal.comp he).const_mul _),
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc ENNReal.ofReal (1 - cfg.α) * ∫⁻ ξ, ENNReal.ofReal (rbar H cfg x0 y0 ox oy ξ j) ∂P0 +
          (ENNReal.ofReal (kq1 L μ ρ cfg) * ∫⁻ ξ, ENNReal.ofReal ‖eM H cfg x0 y0 ox oy ξ j‖ ∂P0 +
            ENNReal.ofReal (kq2 L μ ρ cfg) * ∫⁻ ξ, ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ j‖ ^ 2) ∂P0) +
          ENNReal.ofReal (kq0 L μ ρ cfg)
        ≤ ENNReal.ofReal (1 - cfg.α) * ∫⁻ ξ, ENNReal.ofReal (rbar H cfg x0 y0 ox oy ξ j) ∂P0 +
          (ENNReal.ofReal (kq1 L μ ρ cfg) * ENNReal.ofReal (Real.sqrt Es) +
            ENNReal.ofReal (kq2 L μ ρ cfg) * ENNReal.ofReal Es) + ENNReal.ofReal (kq0 L μ ρ cfg) := by
          gcongr
          · exact me1 j
          · exact (hm j).1
      _ = _ := by
          rw [← ENNReal.ofReal_mul hq1, ← ENNReal.ofReal_mul hq2,
            ← ENNReal.ofReal_add (by positivity) (by positivity), add_assoc,
            ← ENNReal.ofReal_add (by positivity) hq0]
          congr 2; ring

lemma ehM_l1 (O : OracleHyp gx gy ox oy p σ) (hc : CfgOK cfg L μ) {Es Ps : ℝ} (hEs : 0 < Es) (hPs : 0 < Ps)
    (hσ : 0 < σ)
    (hm : ∀ k, ∫⁻ ξ, ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        ENNReal.ofReal Es ∧
      ∫⁻ ξ, ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        ENNReal.ofReal Ps) (k : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal ‖ehM H cfg x0 y0 ox oy ξ k‖ ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (Real.sqrt (cfg.α * ((1 + (L / μ) ^ 2) * σ ^ 2)) +
        ((1 - cfg.α) ^ k * (Real.sqrt Ps + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es) +
          (kq0 L μ ρ cfg + kq1 L μ ρ cfg * Real.sqrt Es + kq2 L μ ρ cfg * Es) / (1 - (1 - cfg.α))) +
        (4 * (L / μ) ^ 2 * cfg.η / cfg.γ + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es)) := by
  set P0 := Measure.infinitePi fun _ : ℕ => p
  have hα := hc.α0
  have hγ := hc.γ0
  have hk : 0 ≤ L / μ := div_nonneg H.L_pos.le H.μpos.le
  have hη := hc.η0
  have hn := measurable_nuq H cfg x0 y0 ox oy O.mx O.my k
  have hr := measurable_rbar H cfg x0 y0 O.mx O.my k (ox := ox) (oy := oy)
  have he := (measurable_eM H cfg x0 y0 O.mx O.my k).norm
  have h1 := l1_add3 P0 (fun ξ => ‖nuq H cfg x0 y0 ox oy ξ k‖ + rbar H cfg x0 y0 ox oy ξ k)
    (fun ξ => 4 * (L / μ) ^ 2 * cfg.η / cfg.γ + cfg.α / cfg.γ * (L / μ) * ‖eM H cfg x0 y0 ox oy ξ k‖)
    (fun ξ => ‖ehM H cfg x0 y0 ox oy ξ k‖) (hn.norm.add hr)
     (fun ξ => add_nonneg (norm_nonneg _) (rbar_nonneg H cfg x0 y0 hc ξ k))
    (fun _ => by positivity) (fun ξ => by have := ehM_bound H cfg hc x0 y0 ξ k (ox := ox) (oy := oy); linarith)
  have h2 := l1_add3 P0 (fun ξ => ‖nuq H cfg x0 y0 ox oy ξ k‖) (fun ξ => rbar H cfg x0 y0 ox oy ξ k)
    (fun ξ => ‖nuq H cfg x0 y0 ox oy ξ k‖ + rbar H cfg x0 y0 ox oy ξ k) hn.norm
     (fun _ => norm_nonneg _)
    (fun ξ => rbar_nonneg H cfg x0 y0 hc ξ k) (fun _ => le_rfl)
  have h3 := l1_add3 P0 (fun _ => 4 * (L / μ) ^ 2 * cfg.η / cfg.γ)
    (fun ξ => cfg.α / cfg.γ * (L / μ) * ‖eM H cfg x0 y0 ox oy ξ k‖)
    (fun ξ => 4 * (L / μ) ^ 2 * cfg.η / cfg.γ + cfg.α / cfg.γ * (L / μ) * ‖eM H cfg x0 y0 ox oy ξ k‖)
    measurable_const (fun _ => by positivity) (fun _ => by positivity)
    (fun _ => le_rfl)
  have hnu := l1_of_l2 P0 _ (by positivity) (nu_all H cfg x0 y0 O hc k)
  have hrb := rbar_l1 H cfg x0 y0 O hc hEs hPs hm k
  have he1 : ∫⁻ ξ, ENNReal.ofReal ‖eM H cfg x0 y0 ox oy ξ k‖ ∂P0 ≤ ENNReal.ofReal (Real.sqrt Es) :=
    l1_of_l2 P0 _ hEs (hm k).1
  have h4 : ∫⁻ ξ, ENNReal.ofReal (cfg.α / cfg.γ * (L / μ) * ‖eM H cfg x0 y0 ox oy ξ k‖) ∂P0 ≤
      ENNReal.ofReal (cfg.α / cfg.γ * (L / μ) * Real.sqrt Es) := by
    simp_rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ cfg.α / cfg.γ * (L / μ))]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
  rw [lintegral_const, measure_univ, mul_one] at h3
  refine h1.trans ((add_le_add (h2.trans (add_le_add hnu hrb)) (h3.trans (add_le_add le_rfl h4))).trans ?_)
  have hR : 0 ≤ (1 - cfg.α) ^ k * (Real.sqrt Ps + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es) +
      (kq0 L μ ρ cfg + kq1 L μ ρ cfg * Real.sqrt Es + kq2 L μ ρ cfg * Es) / (1 - (1 - cfg.α)) := by
    have : 0 ≤ 1 - cfg.α := by linarith [hc.α1]
    have hq0 : 0 ≤ kq0 L μ ρ cfg := by
      simp only [kq0]; have := H.ρnn; have := H.μpos; have := H.L_pos; positivity
    have hq1 : 0 ≤ kq1 L μ ρ cfg := by
      simp only [kq1]; have := H.ρnn; have := H.μpos; have := H.L_pos; positivity
    have hq2 : 0 ≤ kq2 L μ ρ cfg := by
      simp only [kq2]; have := H.ρnn; have := H.μpos; have := H.L_pos; positivity
    have : 0 < 1 - (1 - cfg.α) := by linarith
    positivity
  rw [← ENNReal.ofReal_add (by positivity) hR, ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

omit [BorelSpace E] [SecondCountableTopology E]
    [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [FiniteDimensional ℝ F] [MeasurableSpace F] in
lemma descent_path (hc : CfgOK cfg L μ) {Δ : ℝ} (hΔ : ∀ x y, ∃ y', f x0 y - f x y' ≤ Δ) (ξ : ℕ → Ω) (n : ℕ) :
    cfg.η * ∑ k ∈ Finset.range n, (‖Gs H (wq cfg x0 y0 ox oy ξ k)‖ - cfg.lam -
        2 * ‖ehM H cfg x0 y0 ox oy ξ k‖) ≤ Δ + n * (L * (L / μ + 1 / 2) * cfg.η ^ 2) := by
  have hR := pathRel_seq H cfg x0 y0 ox oy ξ (gx := gx) (gy := gy)
  have key : ∀ n, cfg.η * ∑ k ∈ Finset.range n, (‖Gs H (wq cfg x0 y0 ox oy ξ k)‖ - cfg.lam -
      2 * ‖ehM H cfg x0 y0 ox oy ξ k‖) ≤ Phi H x0 - Phi H (wq cfg x0 y0 ox oy ξ n) +
        n * (L * (L / μ + 1 / 2) * cfg.η ^ 2) := by
    intro n
    induction n with
    | zero => simp [wq]
    | succ n ih =>
      have hd := H.descent_step hc.l0 hc.η0 (wq cfg x0 y0 ox oy ξ n) (uq cfg x0 y0 ox oy ξ n)
      rw [← hR.w_succ n] at hd
      rw [Finset.sum_range_succ, mul_add]
      have : ehM H cfg x0 y0 ox oy ξ n = uq cfg x0 y0 ox oy ξ n - Gs H (wq cfg x0 y0 ox oy ξ n) := rfl
      rw [this]; push_cast
      nlinarith
  have hg := H.phi_gap hΔ (wq cfg x0 y0 ox oy ξ n)
  linarith [key n]

lemma geom_le {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (n : ℕ) : ∑ k ∈ Finset.range n, (1 - a) ^ k ≤ 1 / a := by
  have h := mul_neg_geom_sum (1 - a) n
  rw [sub_sub_cancel] at h
  have hp : 0 ≤ (1 - a) ^ n := pow_nonneg (by linarith) n
  rw [le_div_iff₀ ha, mul_comm]; linarith

omit [CompleteSpace E] [CompleteSpace F] [FiniteDimensional ℝ F] in
lemma measurable_wq (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) :
    ∀ k, Measurable (fun ξ => wq cfg x0 y0 ox oy ξ k)
  | 0 => measurable_const
  | k + 1 => measurable_fst.comp (measurable_mainS cfg x0 y0 ox oy hox hoy k)

lemma grad_sum (O : OracleHyp gx gy ox oy p σ) (hc : CfgOK cfg L μ) {Es Ps Δ : ℝ} (hEs : 0 < Es) (hPs : 0 < Ps)
    (hσ : 0 < σ) (hη : 0 < cfg.η) (hΔ : ∀ x y, ∃ y', f x0 y - f x y' ≤ Δ)
    (hm : ∀ k, ∫⁻ ξ, ENNReal.ofReal (‖eM H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        ENNReal.ofReal Es ∧
      ∫⁻ ξ, ENNReal.ofReal (‖ehM H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
        ENNReal.ofReal Ps) (n : ℕ) :
    ∑ k ∈ Finset.range n, ∫⁻ ξ, ENNReal.ofReal ‖Gs H (wq cfg x0 y0 ox oy ξ k)‖ ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal (Δ / cfg.η + n * (cfg.lam + L * (L / μ + 1 / 2) * cfg.η) +
        2 * (n * (Real.sqrt (cfg.α * ((1 + (L / μ) ^ 2) * σ ^ 2)) +
          (kq0 L μ ρ cfg + kq1 L μ ρ cfg * Real.sqrt Es + kq2 L μ ρ cfg * Es) / (1 - (1 - cfg.α)) +
          (4 * (L / μ) ^ 2 * cfg.η / cfg.γ + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es)) +
          (Real.sqrt Ps + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es) / cfg.α)) := by
  set P0 := Measure.infinitePi fun _ : ℕ => p
  have hα := hc.α0
  have hα1 := hc.α1
  have hγ := hc.γ0
  have hk : 0 ≤ L / μ := div_nonneg H.L_pos.le H.μpos.le
  have hl := hc.l0
  have hL := H.L_pos
  have hΔ0 : 0 ≤ Δ := by have hg := H.phi_gap hΔ x0; linarith
  set A := Δ / cfg.η + n * (cfg.lam + L * (L / μ + 1 / 2) * cfg.η)
  have hA0 : 0 ≤ A := by positivity
  have hgm : ∀ k, Measurable (fun ξ => ENNReal.ofReal ‖Gs H (wq cfg x0 y0 ox oy ξ k)‖) := fun k =>
    ENNReal.measurable_ofReal.comp (H.Gs_continuous.measurable.comp (measurable_wq cfg x0 y0 O.mx O.my k)).norm
  have hhm : ∀ k, Measurable (fun ξ => ENNReal.ofReal (2 * ‖ehM H cfg x0 y0 ox oy ξ k‖)) := fun k =>
    ENNReal.measurable_ofReal.comp ((measurable_ehM H cfg x0 y0 O.mx O.my k).norm.const_mul _)
  have hpath : ∀ ξ, ∑ k ∈ Finset.range n, ENNReal.ofReal ‖Gs H (wq cfg x0 y0 ox oy ξ k)‖ ≤
      ENNReal.ofReal A + ∑ k ∈ Finset.range n, ENNReal.ofReal (2 * ‖ehM H cfg x0 y0 ox oy ξ k‖) := by
    intro ξ
    have hd := descent_path H cfg x0 y0 hc hΔ ξ n (ox := ox) (oy := oy)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _),
      ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    rw [← ENNReal.ofReal_add hA0 (Finset.sum_nonneg fun _ _ => by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, ← Finset.mul_sum] at hd
    have hdiv : ∑ k ∈ Finset.range n, ‖Gs H (wq cfg x0 y0 ox oy ξ k)‖ - n * cfg.lam -
        2 * ∑ k ∈ Finset.range n, ‖ehM H cfg x0 y0 ox oy ξ k‖ ≤
        Δ / cfg.η + n * (L * (L / μ + 1 / 2) * cfg.η) := by
      rw [div_add' _ _ _ hη.ne', le_div_iff₀ hη]
      nlinarith
    rw [← Finset.mul_sum]
    simp only [A]; nlinarith
  calc ∑ k ∈ Finset.range n, ∫⁻ ξ, ENNReal.ofReal ‖Gs H (wq cfg x0 y0 ox oy ξ k)‖ ∂P0
      = ∫⁻ ξ, ∑ k ∈ Finset.range n, ENNReal.ofReal ‖Gs H (wq cfg x0 y0 ox oy ξ k)‖ ∂P0 :=
        (lintegral_finsetSum _ fun k _ => hgm k).symm
    _ ≤ ∫⁻ ξ, (ENNReal.ofReal A + ∑ k ∈ Finset.range n, ENNReal.ofReal (2 * ‖ehM H cfg x0 y0 ox oy ξ k‖)) ∂P0 :=
        lintegral_mono hpath
    _ = ENNReal.ofReal A + ∑ k ∈ Finset.range n, ∫⁻ ξ, ENNReal.ofReal (2 * ‖ehM H cfg x0 y0 ox oy ξ k‖) ∂P0 := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_finsetSum _ fun k _ => hhm k]
    _ ≤ ENNReal.ofReal A + ∑ k ∈ Finset.range n, ENNReal.ofReal (2 * (Real.sqrt (cfg.α * ((1 + (L / μ) ^ 2) * σ ^ 2)) +
        ((1 - cfg.α) ^ k * (Real.sqrt Ps + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es) +
          (kq0 L μ ρ cfg + kq1 L μ ρ cfg * Real.sqrt Es + kq2 L μ ρ cfg * Es) / (1 - (1 - cfg.α))) +
        (4 * (L / μ) ^ 2 * cfg.η / cfg.γ + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es))) := by
        gcongr with k hk'
        simp_rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
        exact ehM_l1 H cfg x0 y0 O hc hEs hPs hσ hm k
    _ ≤ _ := by
        have hq0 : 0 ≤ kq0 L μ ρ cfg := by
          simp only [kq0]; have := H.ρnn; have := H.μpos; positivity
        have hq1 : 0 ≤ kq1 L μ ρ cfg := by
          simp only [kq1]; have := H.ρnn; have := H.μpos; positivity
        have hq2 : 0 ≤ kq2 L μ ρ cfg := by
          simp only [kq2]; have := H.ρnn; have := H.μpos; positivity
        have h1a : 0 < 1 - (1 - cfg.α) := by linarith
        have hx : 0 ≤ 1 - cfg.α := by linarith
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
          ← ENNReal.ofReal_add hA0 (Finset.sum_nonneg fun _ _ => by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have hg := geom_le hα hα1 n
        set R0 := Real.sqrt Ps + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es
        have hR0 : 0 ≤ R0 := by positivity
        have hsum : ∑ k ∈ Finset.range n, (2 * (Real.sqrt (cfg.α * ((1 + (L / μ) ^ 2) * σ ^ 2)) +
            ((1 - cfg.α) ^ k * R0 +
              (kq0 L μ ρ cfg + kq1 L μ ρ cfg * Real.sqrt Es + kq2 L μ ρ cfg * Es) / (1 - (1 - cfg.α))) +
            (4 * (L / μ) ^ 2 * cfg.η / cfg.γ + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es))) =
            2 * (n * (Real.sqrt (cfg.α * ((1 + (L / μ) ^ 2) * σ ^ 2)) +
              (kq0 L μ ρ cfg + kq1 L μ ρ cfg * Real.sqrt Es + kq2 L μ ρ cfg * Es) / (1 - (1 - cfg.α)) +
              (4 * (L / μ) ^ 2 * cfg.η / cfg.γ + cfg.α / cfg.γ * (L / μ) * Real.sqrt Es)) +
              R0 * ∑ k ∈ Finset.range n, (1 - cfg.α) ^ k) := by
          rw [← Finset.mul_sum, Finset.mul_sum]
          simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
        rw [hsum]
        have : R0 * ∑ k ∈ Finset.range n, (1 - cfg.α) ^ k ≤ R0 / cfg.α := by
          calc R0 * ∑ k ∈ Finset.range n, (1 - cfg.α) ^ k ≤ R0 * (1 / cfg.α) := mul_le_mul_of_nonneg_left hg hR0
            _ = R0 / cfg.α := by ring
        linarith

end All

end OracleTemplate.HessianNcsc
