import LongTails.Proofs.RiverValleyTuning
import LongTails.Proofs.RiverValleyExecution
import LongTails.Proofs.AdaptiveIID
import LongTails.Setups.RiverValleyHillNoise

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.RiverValley

open LongTails.Setups.RiverValleyHillNoise OracleTemplate.StepDecaySgd

noncomputable def etaS (q : Params) : ℝ :=
  1 / (8 * q.Lv + 64 * Nhat q.Lh q.ρh q.G q.Γ q.LJ q.ρJ q.μ q.Lv q.σu q.σv / q.ε ^ 2)

noncomputable def lRq (q : Params) : ℝ :=
  Real.log (Rf q.Lh q.ρh q.G q.Γ q.LJ q.ρJ q.μ q.Lv q.σu q.σv q.ε)

noncomputable def etaC (q : Params) : ℝ :=
  1 / (8 * q.Lv + 256 * lRq q * Mcf q.Lh q.ρh q.G q.Γ q.LJ q.μ q.Lv q.σu q.σv / (q.μ * q.ε ^ 2))

noncomputable def Tq (q : Params) : ℕ :=
  ⌈256 * q.Δ * (8 * q.Lv + 64 * Nhat q.Lh q.ρh q.G q.Γ q.LJ q.ρJ q.μ q.Lv q.σu q.σv / q.ε ^ 2) /
    q.ε ^ 2⌉₊

noncomputable def Kq (q : Params) : ℕ :=
  ⌈2 * lRq q * (8 * q.Lv + 256 * lRq q * Mcf q.Lh q.ρh q.G q.Γ q.LJ q.μ q.Lv q.σu q.σv /
    (q.μ * q.ε ^ 2)) / q.μ⌉₊

lemma measurable_sd_out {E Ω : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
    {g : E → Ω → E} (hg : Measurable (Function.uncurry g)) (ηs ηc : ℝ) (T K : ℕ) (x0 : E) :
    Measurable (fun ω : Fin (T + 1) × (ℕ → Ω) =>
      schedSeq g (schedOf ηs ηc ω.1.val) x0 ω.2 (ω.1.val + K)) :=
  measurable_from_prod_countable_right fun τ =>
    measurable_schedSeq hg (schedOf ηs ηc τ.val) x0 (τ.val + K)

theorem convergence_of_le (b : Params → ℕ)
    (hb : ∀ q, LongTails.Setups.RiverValleyHillNoise.spec.valid q → Tq q + Kq q ≤ b q) :
    Convergence LongTails.Setups.RiverValleyHillNoise.spec (fun q _ => b q) := by
  refine ⟨fun q => method (etaS q) (etaC q) (Tq q) (Kq q) q.x0, ?_, ?_⟩
  · intro q hq f O hadm
    dsimp only
    have hbq := hb q hq
    obtain ⟨hμ, hμLv, hLh, hρh, hG, hΓ0, hLJ, hρJ, hσu, hσv, hΔ, hε, hΓ, hLm, hc, hval⟩ := hq
    obtain ⟨K, h, gh, Hh, φ, Jφ, DJ, A, g, P0, P, hIID, rfl, hf, hgh, hgl, hHh, hHl, hGb, hφK,
      hJφ, hJl, hDJ, hDl, hsym, hAK, hAl, hAu, hcross, hgap, hgm, hint, hmean, hiQ, hiP, hvQ,
      hvP⟩ := hadm
    have H : Model K h gh Hh φ Jφ DJ A q.Lh q.ρh q.G (q.Γ * q.μ) q.μ q.Lv q.LJ q.ρJ :=
      ⟨hgh, hgl, hHh, hHl, hGb, hφK, hJφ, hJl, hDJ, hDl, hsym, hAK, hAl, hAu, hcross, hμ, hμLv,
        hLh, hρh, hG, mul_nonneg hΓ0 hμ.le, hLJ, hρJ⟩
    have hfe : f = fval K h φ A := hf
    have hgrad : ∀ x, gradient f x = gradF K gh φ Jφ A x := fun x => by
      rw [hfe]; exact (H.hasGradient x).gradient
    have O' : Orc K (P0 : Measure q.Ω) g (gradF K gh φ Jφ A) q.σu q.σv :=
      ⟨hgm, hint, fun x => by rw [hmean, hgrad], fun x => by simpa [hgrad] using hiQ x,
        fun x => by simpa [hgrad] using hiP x, fun x => by simpa [hgrad] using hvQ x,
        fun x => by simpa [hgrad] using hvP x⟩
    have eΓ : q.Γ * q.μ / q.μ = q.Γ := by field_simp
    have hLv : 0 < q.Lv := lt_of_lt_of_le hμ hμLv
    have hRlog : 1 ≤ lRq q := (one_le_logR hμ hLv hε
      (by simp only [Nhat, lamH]; positivity) (by simp only [Mcf]; positivity)).2
    have hLh16 : 16 * q.Lh ≤ q.μ := by
      have := mul_le_mul_of_nonneg_left hRlog (by positivity : (0:ℝ) ≤ 32 * q.Lh)
      simp only [lRq, Rf, Nhat, lamH, Mcf] at this; linarith
    have R : Regime q.Lh q.ρh q.G (q.Γ * q.μ) q.μ q.Lv q.LJ q.ρJ q.σu q.σv :=
      ⟨by nlinarith, hLh16, by rw [eΓ]; exact hLm, by rw [eΓ]; exact hc, hσu, hσv⟩
    set hstar := f q.x0 - q.Δ
    have hlow : ∀ y ∈ Kᗮ, hstar ≤ h y := by
      intro y hy
      have h1 := hgap (y + φ y)
      have hQ : Kᗮ.starProjection (y + φ y) = y := by
        rw [map_add, Q_of_orth hy, Q_of_mem (hφK y), add_zero]
      have hP : K.starProjection (y + φ y) = φ y := by
        rw [map_add, P_of_orth hy, P_of_mem (hφK y), zero_add]
      have hfy : f (y + φ y) = h y := by
        rw [hfe]; simp only [fval, wv, hQ, hP, sub_self, map_zero, inner_zero_right, mul_zero,
          add_zero]
      simp only [hstar]; linarith
    have hΔ' : fval K h φ A q.x0 - hstar ≤ q.Δ := by simp only [hstar, ← hfe]; linarith
    obtain ⟨hηs0, hηs8, hηc0, hηc8, hKc, hfin⟩ := tune hμ hμLv hLh hρh hG hΓ0 hLJ hρJ hσu hσv hΔ
      hε hΓ hLm hc hval
    obtain ⟨hint_all, hbound⟩ := H.master O' R hlow q.x0 hΔ' hηs0 hηs8 hηc0 hηc8 (Tq q) (Kq q) hKc
    have hb := hbound
    simp only [eΓ] at hb
    have hf2 := hfin
    have hmain : 1 / ((Tq q : ℝ) + 1) * ∑ τ ∈ Finset.range (Tq q + 1),
        ∫ ξ, ‖gradF K gh φ Jφ A (schedSeq g (schedOf (etaS q) (etaC q) τ) q.x0 ξ (τ + Kq q))‖
          ∂(Measure.infinitePi fun _ : ℕ => (P0 : Measure q.Ω)) ≤ q.ε := le_trans hb hf2
    set η := etaS q
    set ηc := etaC q
    set T := Tq q
    set Kc := Kq q
    set Pω := Measure.infinitePi fun _ : ℕ => (P0 : Measure q.Ω)
    have hP : (P : Measure (ℕ → q.Ω)) = Pω := by
      have := hIID.stream_law.map_eq
      exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
    set Or : Oracle q.E q.E :=
      { Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) seed => g x seed } with hOr
    have hexec : ∀ (τ : Fin (T + 1)) (ξ : ℕ → q.Ω),
        execute Or (method η ηc T Kc q.x0) (fun _ => b q) τ ξ =
        schedSeq g (schedOf η ηc τ.val) q.x0 ξ (τ.val + Kc) :=
      fun τ ξ => execute_sd g P η ηc T Kc q.x0 (b q) τ ξ hbq
    have hout : (fun seed : (method η ηc T Kc q.x0).Seed × ((k : ℕ) → q.Ω) =>
        execute Or (method η ηc T Kc q.x0) (fun _ => b q) seed.1 seed.2) =
        fun ω => schedSeq g (schedOf η ηc ω.1.val) q.x0 ω.2 (ω.1.val + Kc) := by
      funext seed; exact hexec seed.1 seed.2
    have hfun : (fun seed : (method η ηc T Kc q.x0).Seed × ((k : ℕ) → q.Ω) =>
        ‖gradient f (execute Or (method η ηc T Kc q.x0) (fun _ => b q) seed.1 seed.2)‖) =
        fun ω => ‖gradF K gh φ Jφ A (schedSeq g (schedOf η ηc ω.1.val) q.x0 ω.2 (ω.1.val + Kc))‖ := by
      funext seed; rw [hexec seed.1 seed.2, hgrad]
    have hmo := measurable_sd_out hgm η ηc T Kc q.x0
    refine ⟨by rw [hout]; exact hmo, ?_⟩
    rw [hfun]
    change Integrable (fun ω : Fin (T + 1) × (ℕ → q.Ω) =>
        ‖gradF K gh φ Jφ A (schedSeq g (schedOf η ηc ω.1.val) q.x0 ω.2 (ω.1.val + Kc))‖)
        ((PMF.uniformOfFintype (Fin (T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ∧
      ∫ ω : Fin (T + 1) × (ℕ → q.Ω),
        ‖gradF K gh φ Jφ A (schedSeq g (schedOf η ηc ω.1.val) q.x0 ω.2 (ω.1.val + Kc))‖
        ∂((PMF.uniformOfFintype (Fin (T + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
    rw [hP]
    have hm : Measurable (fun ω : Fin (T + 1) × (ℕ → q.Ω) =>
        ‖gradF K gh φ Jφ A (schedSeq g (schedOf η ηc ω.1.val) q.x0 ω.2 (ω.1.val + Kc))‖) :=
      (H.gradF_cont.measurable.comp hmo).norm
    have hL : ∫⁻ ω : Fin (T + 1) × (ℕ → q.Ω),
        ENNReal.ofReal ‖gradF K gh φ Jφ A (schedSeq g (schedOf η ηc ω.1.val) q.x0 ω.2
          (ω.1.val + Kc))‖ ∂((PMF.uniformOfFintype (Fin (T + 1))).toMeasure.prod Pω) ≤
        ENNReal.ofReal q.ε := by
      have hm' : Measurable (fun ω : Fin (T + 1) × (ℕ → q.Ω) => ENNReal.ofReal
          ‖gradF K gh φ Jφ A (schedSeq g (schedOf η ηc ω.1.val) q.x0 ω.2 (ω.1.val + Kc))‖) :=
        ENNReal.measurable_ofReal.comp hm
      rw [lintegral_prod _ hm'.aemeasurable, lintegral_fintype]
      simp only [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _),
        Fintype.card_fin]
      have hc : ∀ τ : Fin (T + 1), (Fintype.card ({τ} : Set (Fin (T + 1))) : ℝ≥0∞) = 1 := by
        intro τ; simp
      simp only [hc, one_div]
      have hj : ∀ τ : Fin (T + 1), ∫⁻ ξ, ENNReal.ofReal ‖gradF K gh φ Jφ A
          (schedSeq g (schedOf η ηc τ.val) q.x0 ξ (τ.val + Kc))‖ ∂Pω =
          ENNReal.ofReal (∫ ξ, ‖gradF K gh φ Jφ A
            (schedSeq g (schedOf η ηc τ.val) q.x0 ξ (τ.val + Kc))‖ ∂Pω) := by
        intro τ
        exact (ofReal_integral_eq_lintegral_ofReal (hint_all τ.val)
          (Filter.Eventually.of_forall fun _ => norm_nonneg _)).symm
      simp_rw [hj]
      have hnn : ∀ i : ℕ, 0 ≤ ∫ ξ, ‖gradF K gh φ Jφ A
          (schedSeq g (schedOf η ηc i) q.x0 ξ (i + Kc))‖ ∂Pω :=
        fun i => integral_nonneg fun _ => norm_nonneg _
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun τ _ => hnn _)]
      rw [Fin.sum_univ_eq_sum_range (fun k => ∫ ξ, ‖gradF K gh φ Jφ A
          (schedSeq g (schedOf η ηc k) q.x0 ξ (k + Kc))‖ ∂Pω)]
      have hT : (0 : ℝ) < (T : ℝ) + 1 := by positivity
      have hinv : (((T + 1 : ℕ) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / ((T : ℝ) + 1)) := by
        rw [ENNReal.ofReal_div_of_pos hT, ENNReal.ofReal_one, one_div]
        congr 1
        rw [ENNReal.ofReal_add (by positivity) zero_le_one]
        simp
      have hsum0 : 0 ≤ ∑ k ∈ Finset.range (T + 1), ∫ ξ, ‖gradF K gh φ Jφ A
          (schedSeq g (schedOf η ηc k) q.x0 ξ (k + Kc))‖ ∂Pω :=
        Finset.sum_nonneg fun k _ => hnn _
      rw [hinv, ← ENNReal.ofReal_mul hsum0]
      apply ENNReal.ofReal_le_ofReal
      rw [mul_comm]
      exact hmain
    have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL
    have hnn : ∀ ω : Fin (T + 1) × (ℕ → q.Ω), 0 ≤
        ‖gradF K gh φ Jφ A (schedSeq g (schedOf η ηc ω.1.val) q.x0 ω.2 (ω.1.val + Kc))‖ :=
      fun ω => norm_nonneg _
    refine ⟨?_, ?_⟩
    · have := integrable_toReal_of_lintegral_ne_top
        (ENNReal.measurable_ofReal.comp hm).aemeasurable hfinite
      simpa [ENNReal.toReal_ofReal (hnn _)] using this
    · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
        hm.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hε.le hL
  · intro q hq
    obtain ⟨hμ, hμLv, hLh, hρh, hG, hΓ0, hLJ, hρJ, hσu, hσv, hΔ, hε, hΓ, hLm, hc, hval⟩ := hq
    have hLv : 0 < q.Lv := lt_of_lt_of_le hμ hμLv
    have hN : 0 ≤ Nhat q.Lh q.ρh q.G q.Γ q.LJ q.ρJ q.μ q.Lv q.σu q.σv := by
      simp only [Nhat, lamH]; positivity
    have hM : 0 ≤ Mcf q.Lh q.ρh q.G q.Γ q.LJ q.μ q.Lv q.σu q.σv := by
      simp only [Mcf]; positivity
    have hR := (one_le_logR (ρJ := q.ρJ) hμ hLv hε hN hM).2
    have hl : 0 ≤ lRq q := le_trans zero_le_one hR
    refine ⟨etaS q, etaC q, ?_, ?_, Tq q, Kq q, rfl⟩
    · simp only [etaS]; positivity
    · simp only [etaC]; positivity

lemma ceil_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : ⌈a⌉₊ + ⌈b⌉₊ ≤ ⌈a + b + 1⌉₊ := by
  have h1 := Nat.ceil_lt_add_one ha
  have h2 := Nat.ceil_lt_add_one hb
  have h3 := Nat.le_ceil (a + b + 1)
  have h4 : ((⌈a⌉₊ + ⌈b⌉₊ : ℕ) : ℝ) < ((⌈a + b + 1⌉₊ + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact Nat.lt_add_one_iff.mp (by exact_mod_cast h4)

set_option maxHeartbeats 800000 in
lemma budget_ge (q : Params) (hq : LongTails.Setups.RiverValleyHillNoise.spec.valid q) :
    Tq q + Kq q ≤ ⌈256 * q.Δ * (8 * q.Lv + 64 * (2 * q.Lh * q.σu ^ 2 + (q.Γ * q.Lh + 2 * q.LJ * q.G) * ((1792 * (q.Γ * q.Lh + 2 * q.LJ * q.G) / q.μ + 224 * q.Γ) * (q.σu ^ 2 + q.σv ^ 2) + q.σu * q.σv) + (2 * q.G * q.ρJ + 2 * q.LJ * q.Lh + q.Γ * q.ρh + q.G * q.LJ ^ 2) * q.σu * (14 * (q.σu ^ 2 + q.σv ^ 2) / q.Lv + q.σu ^ 2 / q.μ + q.Γ * q.G * q.σu / q.Lv) + 2 * q.LJ ^ 2 * q.σu ^ 4 / q.Lv) / q.ε ^ 2) / q.ε ^ 2 + Real.log (3 + q.Lv ^ 2 / q.μ ^ 2 + 4 * q.Lv ^ 2 * (2 * q.G * q.ρh * q.σu ^ 2 + q.μ ^ 2 * q.σu ^ 2 + 4 * q.Lv ^ 2 * q.σv ^ 2 + 8 * q.Lv * q.LJ ^ 2 * q.σu ^ 4 / q.μ) / (q.μ ^ 3 * (q.Lv * q.ε ^ 2 + 8 * (2 * q.Lh * q.σu ^ 2 + (q.Γ * q.Lh + 2 * q.LJ * q.G) * ((1792 * (q.Γ * q.Lh + 2 * q.LJ * q.G) / q.μ + 224 * q.Γ) * (q.σu ^ 2 + q.σv ^ 2) + q.σu * q.σv) + (2 * q.G * q.ρJ + 2 * q.LJ * q.Lh + q.Γ * q.ρh + q.G * q.LJ ^ 2) * q.σu * (14 * (q.σu ^ 2 + q.σv ^ 2) / q.Lv + q.σu ^ 2 / q.μ + q.Γ * q.G * q.σu / q.Lv) + 2 * q.LJ ^ 2 * q.σu ^ 4 / q.Lv)))) ^ 2 * (16 * q.Lv / q.μ + 512 * (2 * q.G * q.ρh * q.σu ^ 2 + q.μ ^ 2 * q.σu ^ 2 + 4 * q.Lv ^ 2 * q.σv ^ 2 + 8 * q.Lv * q.LJ ^ 2 * q.σu ^ 4 / q.μ) / (q.μ ^ 2 * q.ε ^ 2)) + 1⌉₊ := by
  obtain ⟨hμ, hμLv, hLh, hρh, hG, hΓ0, hLJ, hρJ, hσu, hσv, hΔ, hε, hΓ, hLm, hc, hval⟩ := hq
  have hLv : 0 < q.Lv := lt_of_lt_of_le hμ hμLv
  have hN : 0 ≤ Nhat q.Lh q.ρh q.G q.Γ q.LJ q.ρJ q.μ q.Lv q.σu q.σv := by
    simp only [Nhat, lamH]; positivity
  have hM : 0 ≤ Mcf q.Lh q.ρh q.G q.Γ q.LJ q.μ q.Lv q.σu q.σv := by
    simp only [Mcf]; positivity
  have hR := one_le_logR (ρJ := q.ρJ) hμ hLv hε hN hM
  have hLh16 : 16 * q.Lh ≤ q.μ := by
    have := mul_le_mul_of_nonneg_left hR.2 (by positivity : (0:ℝ) ≤ 32 * q.Lh)
    simp only [Rf, Nhat, lamH, Mcf] at this; linarith
  clear hval hc
  have eN : (2 * q.Lh * q.σu ^ 2 + (q.Γ * q.Lh + 2 * q.LJ * q.G) * ((1792 * (q.Γ * q.Lh + 2 * q.LJ * q.G) / q.μ + 224 * q.Γ) * (q.σu ^ 2 + q.σv ^ 2) + q.σu * q.σv) + (2 * q.G * q.ρJ + 2 * q.LJ * q.Lh + q.Γ * q.ρh + q.G * q.LJ ^ 2) * q.σu * (14 * (q.σu ^ 2 + q.σv ^ 2) / q.Lv + q.σu ^ 2 / q.μ + q.Γ * q.G * q.σu / q.Lv) + 2 * q.LJ ^ 2 * q.σu ^ 4 / q.Lv) = Nhat q.Lh q.ρh q.G q.Γ q.LJ q.ρJ q.μ q.Lv q.σu q.σv := by
    unfold Nhat lamH; ring
  rw [eN]
  set Mb := (2 * q.G * q.ρh * q.σu ^ 2 + q.μ ^ 2 * q.σu ^ 2 + 4 * q.Lv ^ 2 * q.σv ^ 2 + 8 * q.Lv * q.LJ ^ 2 * q.σu ^ 4 / q.μ) with hMb
  have k1 : q.Lh ^ 2 ≤ (q.μ / 16) ^ 2 := pow_le_pow_left₀ hLh (by linarith) 2
  have k2 : q.Γ ^ 2 ≤ (1 / 16) ^ 2 := pow_le_pow_left₀ hΓ0 (by linarith) 2
  have k3 : q.LJ * q.G ≤ q.μ / 128 := by linarith [mul_nonneg hΓ0 hLh]
  have k4 : q.Γ * (q.LJ * q.G) ≤ 1 / 16 * (q.μ / 128) :=
    mul_le_mul (by linarith) k3 (mul_nonneg hLJ hG) (by norm_num)
  have k5 := mul_le_mul_of_nonneg_left k2 (sq_nonneg q.μ)
  have k6 := mul_le_mul_of_nonneg_left k4 hμ.le
  have coef : q.Lh ^ 2 + 20 * q.Γ ^ 2 * q.μ ^ 2 + q.Γ * q.μ * q.G * q.LJ / 4 ≤ q.μ ^ 2 := by
    have e1 : q.Γ * q.μ * q.G * q.LJ = q.μ * (q.Γ * (q.LJ * q.G)) := by ring
    have e2 : 20 * q.Γ ^ 2 * q.μ ^ 2 = 20 * (q.μ ^ 2 * q.Γ ^ 2) := by ring
    have e3 : (q.μ / 16) ^ 2 + 20 * (q.μ ^ 2 * (1 / 16) ^ 2) + q.μ * (1 / 16 * (q.μ / 128)) / 4 =
        q.μ ^ 2 * (1 / 256 + 20 / 256 + 1 / 8192) := by ring
    have e4 : q.Lh ^ 2 + 20 * q.Γ ^ 2 * q.μ ^ 2 + q.Γ * q.μ * q.G * q.LJ / 4 ≤
        (q.μ / 16) ^ 2 + 20 * (q.μ ^ 2 * (1 / 16) ^ 2) + q.μ * (1 / 16 * (q.μ / 128)) / 4 := by
      rw [e1, e2]; linarith
    have e5 : 0 ≤ q.μ ^ 2 := sq_nonneg _
    rw [e3] at e4; linarith
  have hMM : Mcf q.Lh q.ρh q.G q.Γ q.LJ q.μ q.Lv q.σu q.σv ≤ Mb := by
    have := mul_le_mul_of_nonneg_right coef (sq_nonneg q.σu)
    simp only [Mcf, hMb]; ring_nf; ring_nf at this; linarith
  set Nh := Nhat q.Lh q.ρh q.G q.Γ q.LJ q.ρJ q.μ q.Lv q.σu q.σv
  set Mc := Mcf q.Lh q.ρh q.G q.Γ q.LJ q.μ q.Lv q.σu q.σv
  have hD : 0 < q.μ ^ 3 * (q.Lv * q.ε ^ 2 + 8 * Nh) := by positivity
  have hRR : Rf q.Lh q.ρh q.G q.Γ q.LJ q.ρJ q.μ q.Lv q.σu q.σv q.ε ≤
      3 + q.Lv ^ 2 / q.μ ^ 2 + 4 * q.Lv ^ 2 * Mb / (q.μ ^ 3 * (q.Lv * q.ε ^ 2 + 8 * Nh)) := by
    simp only [Rf]
    have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hMM
      (by positivity : (0:ℝ) ≤ 4 * q.Lv ^ 2)) hD.le
    linarith
  set l := lRq q with hl
  set L := Real.log (3 + q.Lv ^ 2 / q.μ ^ 2 + 4 * q.Lv ^ 2 * Mb /
    (q.μ ^ 3 * (q.Lv * q.ε ^ 2 + 8 * Nh)))
  have hl1 : 1 ≤ l := hR.2
  have hlL : l ≤ L := Real.log_le_log (by linarith [hR.1]) hRR
  have hl2 : l ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by linarith) hlL 2
  have hll : l ≤ l ^ 2 := by
    calc l = l * 1 := by ring
      _ ≤ l * l := mul_le_mul_of_nonneg_left hl1 (by linarith)
      _ = l ^ 2 := by ring
  have hA : 0 ≤ 16 * q.Lv / q.μ := by positivity
  have hB : 512 * Mc / (q.μ ^ 2 * q.ε ^ 2) ≤ 512 * Mb / (q.μ ^ 2 * q.ε ^ 2) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hB0 : 0 ≤ 512 * Mc / (q.μ ^ 2 * q.ε ^ 2) := by positivity
  have ek : 2 * l * (8 * q.Lv + 256 * l * Mc / (q.μ * q.ε ^ 2)) / q.μ =
      l * (16 * q.Lv / q.μ) + l ^ 2 * (512 * Mc / (q.μ ^ 2 * q.ε ^ 2)) := by
    field_simp; ring
  have hk : 2 * l * (8 * q.Lv + 256 * l * Mc / (q.μ * q.ε ^ 2)) / q.μ ≤
      L ^ 2 * (16 * q.Lv / q.μ + 512 * Mb / (q.μ ^ 2 * q.ε ^ 2)) := by
    rw [ek]
    have := mul_le_mul_of_nonneg_right (le_trans hll hl2) hA
    have := mul_le_mul hl2 hB hB0 (by positivity)
    rw [mul_add]; linarith
  have ha : 0 ≤ 256 * q.Δ * (8 * q.Lv + 64 * Nh / q.ε ^ 2) / q.ε ^ 2 := by positivity
  have hk0 : 0 ≤ 2 * l * (8 * q.Lv + 256 * l * Mc / (q.μ * q.ε ^ 2)) / q.μ := by positivity
  calc Tq q + Kq q ≤ ⌈256 * q.Δ * (8 * q.Lv + 64 * Nh / q.ε ^ 2) / q.ε ^ 2 +
        2 * l * (8 * q.Lv + 256 * l * Mc / (q.μ * q.ε ^ 2)) / q.μ + 1⌉₊ := ceil_add_le ha hk0
    _ ≤ _ := Nat.ceil_mono (by linarith)

end OracleTemplate.RiverValley
