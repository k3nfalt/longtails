import LongTails.Proofs.HessianNcscPhases

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.HessianNcsc

section ENN

lemma enn_affine_le {a b c X Y Z : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    {u v : ℝ≥0∞} (hu : u ≤ ENNReal.ofReal X) (hv : v ≤ ENNReal.ofReal Y)
    (h : a * X + b * Y + c ≤ Z) :
    ENNReal.ofReal a * u + ENNReal.ofReal b * v + ENNReal.ofReal c ≤ ENNReal.ofReal Z := by
  calc ENNReal.ofReal a * u + ENNReal.ofReal b * v + ENNReal.ofReal c
      ≤ ENNReal.ofReal a * ENNReal.ofReal X + ENNReal.ofReal b * ENNReal.ofReal Y + ENNReal.ofReal c := by
        gcongr
    _ = ENNReal.ofReal (a * X + b * Y + c) := by
        rw [ENNReal.ofReal_add (by positivity) hc, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
    _ ≤ ENNReal.ofReal Z := ENNReal.ofReal_le_ofReal h

variable {Ξ : Type*} [MeasurableSpace Ξ] (P : Measure Ξ) [IsProbabilityMeasure P]

lemma l1_of_l2 (g : Ξ → ℝ) {V : ℝ} (hV : 0 < V)
    (h : ∫⁻ ξ, ENNReal.ofReal (g ξ ^ 2) ∂P ≤ ENNReal.ofReal V) :
    ∫⁻ ξ, ENNReal.ofReal (g ξ) ∂P ≤ ENNReal.ofReal (Real.sqrt V) := by
  have hs : 0 < Real.sqrt V := Real.sqrt_pos.mpr hV
  have hpt : ∀ ξ, ENNReal.ofReal (g ξ) ≤
      ENNReal.ofReal (1 / (2 * Real.sqrt V)) * ENNReal.ofReal (g ξ ^ 2) +
        ENNReal.ofReal (Real.sqrt V / 2) := by
    intro ξ
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ (g ξ - Real.sqrt V) ^ 2 / (2 * Real.sqrt V) := by positivity
    have e : 1 / (2 * Real.sqrt V) * g ξ ^ 2 + Real.sqrt V / 2 - g ξ =
        (g ξ - Real.sqrt V) ^ 2 / (2 * Real.sqrt V) := by
      field_simp; ring
    linarith
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc ENNReal.ofReal (1 / (2 * Real.sqrt V)) * ∫⁻ ξ, ENNReal.ofReal (g ξ ^ 2) ∂P + ENNReal.ofReal (Real.sqrt V / 2)
      ≤ ENNReal.ofReal (1 / (2 * Real.sqrt V)) * ENNReal.ofReal V + ENNReal.ofReal (Real.sqrt V / 2) := by gcongr
    _ = ENNReal.ofReal (Real.sqrt V) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have hv : V = Real.sqrt V * Real.sqrt V := (Real.mul_self_sqrt hV.le).symm
        set s := Real.sqrt V
        rw [hv]; field_simp; norm_num

end ENN

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
lemma Hyp.y0_dist (H : Hyp f gx gy Hx Hy L μ ρ) (x0 : E) (y0 : F) {G : ℝ} (hG : ‖gy (x0, y0)‖ ≤ G) :
    ‖y0 - ystar H x0‖ ≤ G / μ := by
  have hm := H.gy_mono x0 (ystar H x0) y0
  rw [H.gy_ystar x0, sub_zero] at hm
  have hc := real_inner_le_norm (-gy (x0, y0)) (y0 - ystar H x0)
  rw [inner_neg_left, norm_neg] at hc
  rw [le_div_iff₀ H.μpos]
  by_cases h0 : ‖y0 - ystar H x0‖ = 0
  · rw [h0, zero_mul]; exact (norm_nonneg _).trans hG
  · have hp : 0 < ‖y0 - ystar H x0‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have h1 : μ * ‖y0 - ystar H x0‖ ^ 2 ≤ ‖gy (x0, y0)‖ * ‖y0 - ystar H x0‖ := by linarith
    have h2 : ‖gy (x0, y0)‖ * ‖y0 - ystar H x0‖ ≤ G * ‖y0 - ystar H x0‖ :=
      mul_le_mul_of_nonneg_right hG (norm_nonneg _)
    have h3 : ‖y0 - ystar H x0‖ * μ * ‖y0 - ystar H x0‖ ≤ G * ‖y0 - ystar H x0‖ := by nlinarith
    exact le_of_mul_le_mul_right h3 hp

lemma geom_closed {r c X0 : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hc : 0 ≤ c) (hX0 : 0 ≤ X0)
    (m : ℕ → ℝ≥0∞) (h0 : m 0 ≤ ENNReal.ofReal X0)
    (hs : ∀ j, m (j + 1) ≤ ENNReal.ofReal r * m j + ENNReal.ofReal c) :
    ∀ j, m j ≤ ENNReal.ofReal (r ^ j * X0 + c / (1 - r)) := by
  have hd : 0 < 1 - r := by linarith
  intro j
  induction j with
  | zero =>
    refine h0.trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [pow_zero, one_mul]
    have : 0 ≤ c / (1 - r) := div_nonneg hc hd.le
    linarith
  | succ j ih =>
    refine (hs j).trans ?_
    calc ENNReal.ofReal r * m j + ENNReal.ofReal c
        ≤ ENNReal.ofReal r * ENNReal.ofReal (r ^ j * X0 + c / (1 - r)) + ENNReal.ofReal c := by gcongr
      _ = ENNReal.ofReal (r * (r ^ j * X0 + c / (1 - r)) + c) := by
          rw [ENNReal.ofReal_add (by positivity) hc, ENNReal.ofReal_mul hr0]
      _ = ENNReal.ofReal (r ^ (j + 1) * X0 + c / (1 - r)) := by
          congr 1; field_simp; ring

section Init

variable (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)

omit [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma ehM_zero_eq (hNB : 1 ≤ cfg.NB) (ξ : ℕ → Ω) :
    ehM H cfg x0 y0 ox oy ξ 0 = (1 / (cfg.NB : ℝ)) • bdev cfg x0 y0 (gx := gx) ox oy ξ cfg.NB +
      (gx (x0, yA cfg x0 y0 oy ξ cfg.NA) - Gs H x0) := by
  have h1 : (1 : ℝ) ≤ cfg.NB := by exact_mod_cast hNB
  have hN : (cfg.NB : ℝ) ≠ 0 := by linarith
  simp only [ehM, uq, wq, mainS, mInit, mzero, bdev, smul_sub, smul_smul]
  rw [one_div_mul_cancel hN, one_smul]; abel

omit [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma eM_zero_eq (ξ : ℕ → Ω) : eM H cfg x0 y0 ox oy ξ 0 = eC H cfg x0 y0 ox oy ξ cfg.NC := rfl

omit [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma eC_zero_bound (hc : CfgOK cfg L μ) (ξ : ℕ → Ω) :
    ‖eC H cfg x0 y0 ox oy ξ 0‖ ≤ ‖yA cfg x0 y0 oy ξ cfg.NA - ystar H x0‖ + (L / μ) * (cfg.η / cfg.α) := by
  have e : eC H cfg x0 y0 ox oy ξ 0 = (yA cfg x0 y0 oy ξ cfg.NA - ystar H x0) +
      (ystar H x0 - ystar H (xtOne cfg x0 y0 ox oy ξ)) := by simp only [eC, yC]; abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  refine (H.ystar_lip _ _).trans (mul_le_mul_of_nonneg_left ?_ (div_nonneg H.L_pos.le H.μpos.le))
  have hx : x0 - xtOne cfg x0 y0 ox oy ξ = -((1 / cfg.α) • nphi cfg.η cfg.lam (mInit cfg x0 y0 ox oy ξ)) := by
    simp only [xtOne, wOne, lead]
    have : (1 / cfg.α) = 1 + (1 - cfg.α) / cfg.α := by field_simp [hc.α0.ne']; ring
    rw [this, add_smul, one_smul]; abel
  rw [hx, norm_neg, norm_smul, Real.norm_of_nonneg (by have := hc.α0; positivity)]
  have := nphi_norm hc.l0 hc.η0 (mInit cfg x0 y0 ox oy ξ)
  calc 1 / cfg.α * ‖nphi cfg.η cfg.lam (mInit cfg x0 y0 ox oy ξ)‖ ≤ 1 / cfg.α * cfg.η :=
        mul_le_mul_of_nonneg_left this (by have := hc.α0; positivity)
    _ = cfg.η / cfg.α := by ring

end Init

end OracleTemplate.HessianNcsc
