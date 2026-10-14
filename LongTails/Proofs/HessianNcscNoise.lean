import LongTails.Proofs.HessianNcscMoments

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

omit [BorelSpace E] [SecondCountableTopology E] [BorelSpace F] [SecondCountableTopology F] in
omit [MeasurableSpace E] [MeasurableSpace F] in
lemma Hyp.MmL_continuous (H : Hyp f gx gy Hx Hy L μ ρ) : Continuous (MmL H) := by
  have : LipschitzWith (Real.toNNReal ((ρ / μ) * (1 + L / μ) * Real.sqrt (1 + (L / μ) ^ 2))) (MmL H) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by have := H.ρnn; have := H.L_pos; have := H.μpos; positivity)]
    refine ContinuousLinearMap.opNorm_le_bound _ (by have := H.ρnn; have := H.L_pos; have := H.μpos; positivity) ?_
    intro v
    rw [sub_apply, MmL_apply, MmL_apply]
    have h := H.Mm_diff a b v
    have h2 := sqrt_zs_le (H := H) a b
    calc ‖Mm H a v - Mm H b v‖ ≤ (ρ / μ) * (1 + L / μ) * Real.sqrt (sq (zs H a - zs H b)) * ‖v‖ := h
      _ ≤ (ρ / μ) * (1 + L / μ) * (Real.sqrt (1 + (L / μ) ^ 2) * ‖a - b‖) * ‖v‖ := by
          gcongr
          have := H.ρnn; have := H.L_pos; have := H.μpos; positivity
      _ = (ρ / μ) * (1 + L / μ) * Real.sqrt (1 + (L / μ) ^ 2) * ‖a - b‖ * ‖v‖ := by ring
  exact this.continuous

omit [SecondCountableTopology E] in
lemma Hyp.measurable_Mm (H : Hyp f gx gy Hx Hy L μ ρ) :
    Measurable (fun q : E × F => Mm H q.1 q.2) := by
  have : Continuous (fun q : E × F => MmL H q.1 q.2) :=
    (H.MmL_continuous.comp continuous_fst).clm_apply continuous_snd
  exact this.measurable

section Nu

variable (H : Hyp f gx gy Hx Hy L μ ρ) (cfg : IgtConfig) (x0 : E) (y0 : F)
  (ox : E × F → Ω → E) (oy : E × F → Ω → F)

noncomputable def nuq (ξ : ℕ → Ω) : ℕ → E
  | 0 => 0
  | k + 1 => (1 - cfg.α) • nuq ξ k + cfg.α • (nxq cfg x0 y0 ox oy gx ξ (k + 1) -
      Mm H (wq cfg x0 y0 ox oy ξ (k + 1)) (nyq cfg x0 y0 ox oy gy ξ (k + 1)))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [MeasurableSpace Ω] in
lemma nuq_congr {ξ ξ' : ℕ → Ω} : ∀ k, (∀ i, i < off cfg + k → ξ i = ξ' i) →
    nuq H cfg x0 y0 ox oy ξ k = nuq H cfg x0 y0 ox oy ξ' k
  | 0, _ => rfl
  | k + 1, h => by
      have ih := nuq_congr k (fun i hi => h i (by omega))
      have hm := mainS_congr cfg x0 y0 ox oy k (fun i hi => h i (by omega)) (ξ := ξ) (ξ' := ξ')
      simp only [nuq, nxq, nyq, xq, yq, wq, uq]
      rw [ih, hm, h (off cfg + k) (by omega)]

lemma measurable_nuq (hox : Measurable (Function.uncurry ox)) (hoy : Measurable (Function.uncurry oy)) :
    ∀ k, Measurable (fun ξ => nuq H cfg x0 y0 ox oy ξ k)
  | 0 => measurable_const
  | k + 1 => by
      have ih := measurable_nuq hox hoy k
      have hm := measurable_mainS cfg x0 y0 ox oy hox hoy k
      have hw : Measurable (fun ξ => (mainS cfg x0 y0 ox oy ξ k).1) := measurable_fst.comp hm
      have hz : Measurable (fun ξ => (lead cfg (mainS cfg x0 y0 ox oy ξ k).1 (mainS cfg x0 y0 ox oy ξ k).2.1,
          (mainS cfg x0 y0 ox oy ξ k).2.2)) :=
        ((measurable_lead cfg).comp (hw.prodMk (measurable_fst.comp (measurable_snd.comp hm)))).prodMk
          (measurable_snd.comp (measurable_snd.comp hm))
      have hnx : Measurable (fun ξ => nxq cfg x0 y0 ox oy gx ξ (k + 1)) := by
        simp only [nxq, xq, yq, wq, uq]
        exact (hox.comp (hz.prodMk (measurable_pi_apply _))).sub (H.gx_continuous.measurable.comp hz)
      have hgy : Continuous gy := by
        have : LipschitzWith (Real.toNNReal (L * Real.sqrt 2)) gy := by
          refine LipschitzWith.of_dist_le_mul fun z z' => ?_
          rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by have := H.L_pos; positivity)]
          have h2 := sq_le_two_norm (z - z')
          simp only [Prod.fst_sub, Prod.snd_sub] at h2
          calc ‖gy z - gy z'‖ ≤ L * Real.sqrt (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2) := H.gy_lip z z'
            _ ≤ L * Real.sqrt (2 * ‖z - z'‖ ^ 2) := by gcongr; exact H.L_pos.le
            _ = L * Real.sqrt 2 * ‖z - z'‖ := by
                rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]; ring
        exact this.continuous
      have hny : Measurable (fun ξ => nyq cfg x0 y0 ox oy gy ξ (k + 1)) := by
        simp only [nyq, xq, yq, wq, uq]
        exact (hoy.comp (hz.prodMk (measurable_pi_apply _))).sub (hgy.measurable.comp hz)
      simp only [nuq]
      exact (ih.const_smul _).add ((hnx.sub (H.measurable_Mm.comp
        ((show Measurable (fun ξ => wq cfg x0 y0 ox oy ξ (k + 1)) from hw).prodMk hny))).const_smul _)

end Nu

lemma nu_moment (H : Hyp f gx gy Hx Hy L μ ρ) (O : OracleHyp gx gy ox oy p σ) (cfg : IgtConfig)
     (x0 : E) (y0 : F) (k : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal (‖nuq H cfg x0 y0 ox oy ξ (k + 1)‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) ≤
      ENNReal.ofReal ((1 - cfg.α) ^ 2) *
          ∫⁻ ξ, ENNReal.ofReal (‖nuq H cfg x0 y0 ox oy ξ k‖ ^ 2) ∂(Measure.infinitePi fun _ : ℕ => p) +
        ENNReal.ofReal (cfg.α ^ 2 * ((1 + (L / μ) ^ 2) * σ ^ 2)) := by
  set Φ : ((E × E × F) × E) × Ω → E := fun s =>
    (1 - cfg.α) • s.1.2 + cfg.α • ((ox (lead cfg s.1.1.1 s.1.1.2.1, s.1.1.2.2) s.2 -
        gx (lead cfg s.1.1.1 s.1.1.2.1, s.1.1.2.2)) -
      Mm H s.1.1.1 (oy (lead cfg s.1.1.1 s.1.1.2.1, s.1.1.2.2) s.2 - gy (lead cfg s.1.1.1 s.1.1.2.1, s.1.1.2.2)))
  have hfun : (fun ξ => ENNReal.ofReal (‖nuq H cfg x0 y0 ox oy ξ (k + 1)‖ ^ 2)) =
      fun ξ => (fun s => ENNReal.ofReal (‖Φ s‖ ^ 2))
        ((mainS cfg x0 y0 ox oy ξ k, nuq H cfg x0 y0 ox oy ξ k), ξ (off cfg + k)) := by
    funext ξ; simp only [Φ, nuq, nxq, nyq, xq, yq, wq, uq]
  rw [hfun]
  have hgy : Continuous gy := by
    have : LipschitzWith (Real.toNNReal (L * Real.sqrt 2)) gy := by
      refine LipschitzWith.of_dist_le_mul fun z z' => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by have := H.L_pos; positivity)]
      have h2 := sq_le_two_norm (z - z')
      simp only [Prod.fst_sub, Prod.snd_sub] at h2
      calc ‖gy z - gy z'‖ ≤ L * Real.sqrt (‖z.1 - z'.1‖ ^ 2 + ‖z.2 - z'.2‖ ^ 2) := H.gy_lip z z'
        _ ≤ L * Real.sqrt (2 * ‖z - z'‖ ^ 2) := by gcongr; exact H.L_pos.le
        _ = L * Real.sqrt 2 * ‖z - z'‖ := by
            rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)]; ring
    exact this.continuous
  have hΦ : Measurable Φ := by
    have hs1 : Measurable (fun s : ((E × E × F) × E) × Ω => s.1.1) := measurable_fst.comp measurable_fst
    have hz : Measurable (fun s : ((E × E × F) × E) × Ω => (lead cfg s.1.1.1 s.1.1.2.1, s.1.1.2.2)) :=
      ((measurable_lead cfg).comp ((measurable_fst.comp hs1).prodMk
        (measurable_fst.comp (measurable_snd.comp hs1)))).prodMk (measurable_snd.comp (measurable_snd.comp hs1))
    have hzw : Measurable (fun s : ((E × E × F) × E) × Ω => ((lead cfg s.1.1.1 s.1.1.2.1, s.1.1.2.2), s.2)) :=
      hz.prodMk measurable_snd
    simp only [Φ]
    exact ((measurable_snd.comp measurable_fst).const_smul _).add
      ((((O.mx.comp hzw).sub (H.gx_continuous.measurable.comp hz)).sub
        (H.measurable_Mm.comp ((measurable_fst.comp hs1).prodMk
          ((O.my.comp hzw).sub (hgy.measurable.comp hz))))).const_smul _)
  have hmeasP : Measurable (fun s : ((E × E × F) × E) × Ω => ENNReal.ofReal (‖Φ s‖ ^ 2)) :=
    ENNReal.measurable_ofReal.comp (hΦ.norm.pow_const 2)
  rw [fresh_lintegral p (off cfg + k) (fun ξ => (mainS cfg x0 y0 ox oy ξ k, nuq H cfg x0 y0 ox oy ξ k))
    ((measurable_mainS cfg x0 y0 ox oy O.mx O.my k).prodMk (measurable_nuq H cfg x0 y0 ox oy O.mx O.my k))
    (fun ξ ξ' h => by
      simp only [Prod.mk.injEq]
      exact ⟨mainS_congr cfg x0 y0 ox oy k h, nuq_congr H cfg x0 y0 ox oy k h⟩) _ hmeasP]
  have hpt : ∀ ξ, ∫⁻ ω, ENNReal.ofReal (‖Φ ((mainS cfg x0 y0 ox oy ξ k, nuq H cfg x0 y0 ox oy ξ k), ω)‖ ^ 2) ∂p ≤
      ENNReal.ofReal ((1 - cfg.α) ^ 2 * ‖nuq H cfg x0 y0 ox oy ξ k‖ ^ 2 + cfg.α ^ 2 * ((1 + (L / μ) ^ 2) * σ ^ 2)) := by
    intro ξ
    have h := m_noise_step H O ((1 - cfg.α) • nuq H cfg x0 y0 ox oy ξ k) cfg.α (mainS cfg x0 y0 ox oy ξ k).1
      (lead cfg (mainS cfg x0 y0 ox oy ξ k).1 (mainS cfg x0 y0 ox oy ξ k).2.1, (mainS cfg x0 y0 ox oy ξ k).2.2)
    refine le_trans (le_of_eq ?_) (h.trans (ENNReal.ofReal_le_ofReal ?_))
    · rfl
    · rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  refine (lintegral_mono hpt).trans ?_
  have mn := measurable_nuq H cfg x0 y0 ox oy O.mx O.my k
  have hsplit : ∀ ξ, ENNReal.ofReal ((1 - cfg.α) ^ 2 * ‖nuq H cfg x0 y0 ox oy ξ k‖ ^ 2 +
        cfg.α ^ 2 * ((1 + (L / μ) ^ 2) * σ ^ 2)) =
      ENNReal.ofReal ((1 - cfg.α) ^ 2) * ENNReal.ofReal (‖nuq H cfg x0 y0 ox oy ξ k‖ ^ 2) +
        ENNReal.ofReal (cfg.α ^ 2 * ((1 + (L / μ) ^ 2) * σ ^ 2)) := by
    intro ξ
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)]
  simp_rw [hsplit]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end OracleTemplate.HessianNcsc
