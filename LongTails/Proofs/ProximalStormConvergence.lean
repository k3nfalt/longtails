import LongTails.Proofs.ProximalStormExecution
import LongTails.Proofs.AdaptiveIID
import LongTails.Proofs.Execution
import LongTails.Setups.StrongGrowthMeanSquaredSmoothConvex

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace OracleTemplate.ProximalStorm

noncomputable def pB (Γh : ℝ) : ℕ := ⌈6 * Γh ^ 2⌉₊

noncomputable def pK (Lbar R ε Γh : ℝ) : ℕ := ⌈Real.sqrt (2 * Lbar * R ^ 2 / (Γh * ε))⌉₊

lemma block_calls_le {Γh : ℝ} (hΓ : 1 ≤ Γh) :
    pB Γh + (pT0 Γh + pW Γh + 1) ≤ ⌈Γh ^ 2 * (4810 + 3200 * Real.log Γh)⌉₊ := by
  have hlog : 0 ≤ Real.log Γh := Real.log_nonneg hΓ
  have h1 : (pB Γh : ℝ) ≤ 6 * Γh ^ 2 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h2 : (pT0 Γh : ℝ) ≤ 800 * Γh ^ 2 * (5 + 4 * Real.log Γh) + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have h3 : (pW Γh : ℝ) ≤ 800 * Γh ^ 2 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hsq : 1 ≤ Γh ^ 2 := one_le_pow₀ hΓ
  have hr : ((pB Γh + (pT0 Γh + pW Γh + 1) : ℕ) : ℝ) ≤ Γh ^ 2 * (4810 + 3200 * Real.log Γh) := by
    push_cast
    nlinarith
  exact (Nat.cast_le (α := ℝ)).mp (hr.trans (Nat.le_ceil _))

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {Ω : Type} [MeasurableSpace Ω]

omit [CompleteSpace E] in
lemma measurable_outerOut {g : E → Ω → E} (hg : Measurable (Function.uncurry g))
    (lam eta a : ℝ) (T0 Wm B K : ℕ) (x0 : E) :
    Measurable fun s : (Fin K → Fin (Wm + 1)) × (ℕ → Ω) =>
      (outerRun g lam eta a T0 (Wm + 1) B x0 (seedIndex s.1) s.2 K).2.1 :=
  measurable_from_prod_countable_right fun σ =>
    (measurable_outerRun hg lam eta a T0 (Wm + 1) B x0 (seedIndex σ) K).snd.fst

section Master

variable {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E}
  {Lbar Γ : ℝ} {xstar : E}

theorem Hyp.master (H : Hyp p f g Lbar Γ xstar) {R ε : ℝ} (hε : 0 < ε) (x0 : E)
    (hx0 : ‖x0 - xstar‖ ≤ R) :
    ∫⁻ s, ENNReal.ofReal (f (outerRun g (pLam Lbar (1 + Γ)) (pEta Lbar (1 + Γ)) (pA (1 + Γ))
        (pT0 (1 + Γ)) (pW (1 + Γ) + 1) (pB (1 + Γ)) x0 (seedIndex s.1) s.2
          (pK Lbar R ε (1 + Γ))).2.1 - f xstar)
      ∂((PMF.uniformOfFintype (Fin (pK Lbar R ε (1 + Γ)) → Fin (pW (1 + Γ) + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => p)) ≤ ENNReal.ofReal ε := by
  set Γh := 1 + Γ
  have hΓ : 1 ≤ Γh := by simp only [Γh]; linarith [H.Γ_nn]
  have hΓΓ : Γ ≤ Γh := by simp only [Γh]; linarith
  have hL := H.Lbar_pos
  set lam := pLam Lbar Γh
  set eta := pEta Lbar Γh
  set a := pA Γh
  set T0 := pT0 Γh
  set Wm := pW Γh
  set B := pB Γh
  set K := pK Lbar R ε Γh
  set P := Measure.infinitePi fun _ : ℕ => p
  have hlam : 0 < lam := (tune_inner hL hΓ).lam_pos
  have hB1 : 1 ≤ B := by
    simp only [B, pB]; exact Nat.one_le_iff_ne_zero.mpr (by
      intro h; rw [Nat.ceil_eq_zero] at h; nlinarith [sq_nonneg Γh])
  have hB : 6 * Γ ^ 2 ≤ (B : ℝ) := by
    simp only [B, pB]
    refine le_trans ?_ (Nat.le_ceil _)
    nlinarith [pow_le_pow_left₀ H.Γ_nn hΓΓ 2]
  have hW : 800 * Γh ^ 2 ≤ ((Wm + 1 : ℕ) : ℝ) := by
    simp only [Wm, pW]; push_cast
    linarith [Nat.le_ceil (800 * Γh ^ 2)]
  have hfgap : ∀ x, 0 ≤ f x - f xstar := fun x => by
    have := H.min (mem_univ x); simp only [mem_ofPred_eq] at this; linarith
  set y : (Fin K → Fin (Wm + 1)) × (ℕ → Ω) → E := fun s =>
    (outerRun g lam eta a T0 (Wm + 1) B x0 (seedIndex s.1) s.2 K).2.1
  have hym : Measurable y := measurable_outerOut H.meas lam eta a T0 Wm B K x0
  have hm : Measurable fun s => ENNReal.ofReal (f (y s) - f xstar) :=
    ((H.f_continuous.measurable.comp hym).sub_const _).ennreal_ofReal
  change ∫⁻ s, ENNReal.ofReal (f (y s) - f xstar) ∂_ ≤ _
  rw [lintegral_prod _ hm.aemeasurable, lintegral_fintype]
  simp only [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _)]
  have hc : ∀ σ : Fin K → Fin (Wm + 1), (Fintype.card ({σ} : Set (Fin K → Fin (Wm + 1))) :
      ℝ≥0∞) = 1 := by intro σ; simp
  simp only [hc, one_div]
  rw [← Finset.sum_mul]
  set N := (Fintype.card (Fin K → Fin (Wm + 1)) : ℝ≥0∞)
  have hN0 : N ≠ 0 := by simp [N]
  have hNt : N ≠ ⊤ := by simp [N]
  have hpb := H.process_bound hΓ hΓΓ hB1 hB hW x0 K K le_rfl
  have hpot0 : outerPot f xstar ((0 : ℝ), x0, x0) ≤ R ^ 2 / 2 := by
    simp only [outerPot, zero_mul, zero_add]
    have := pow_le_pow_left₀ (norm_nonneg _) hx0 2
    linarith
  set AK := accA lam K
  have hAK0 : 0 ≤ AK := accA_nonneg hlam K
  have hlow : ∀ σ : Fin K → Fin (Wm + 1), ENNReal.ofReal AK *
      ∫⁻ ξ, ENNReal.ofReal (f (y (σ, ξ)) - f xstar) ∂P ≤
      ∫⁻ ξ, ENNReal.ofReal (outerPot f xstar (outerRun g lam eta a T0 (Wm + 1) B x0
        (seedIndex σ) ξ K)) ∂P := by
    intro σ
    have hu : Measurable fun ξ => f (y (σ, ξ)) - f xstar :=
      (H.f_continuous.measurable.comp
        ((measurable_outerRun H.meas lam eta a T0 (Wm + 1) B x0 (seedIndex σ) K).snd.fst)).sub_const _
    rw [lint_smul hu hAK0]
    refine lintegral_mono fun ξ => ENNReal.ofReal_le_ofReal ?_
    simp only [outerPot, y, outerRun_fst]
    have := sq_nonneg ‖(outerRun g lam eta a T0 (Wm + 1) B x0 (seedIndex σ) ξ K).2.2 - xstar‖
    linarith
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · -- K = 0: then R = 0 and x0 = xstar
    have hR0 : R = 0 := by
      have h0 : Real.sqrt (2 * Lbar * R ^ 2 / (Γh * ε)) ≤ 0 := by
        have := Nat.ceil_eq_zero.mp (show ⌈Real.sqrt (2 * Lbar * R ^ 2 / (Γh * ε))⌉₊ = 0 from hK0)
        exact this
      have h1 := Real.sqrt_eq_zero'.mp (le_antisymm h0 (Real.sqrt_nonneg _))
      rw [div_le_iff₀ (by positivity), zero_mul] at h1
      have hR2 : R ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg R]) (sq_nonneg R)
      exact pow_eq_zero_iff two_ne_zero |>.mp hR2
    have hx : x0 = xstar := by
      have := hx0; rw [hR0] at this; exact sub_eq_zero.mp (norm_le_zero_iff.mp this)
    have hgen : ∀ (τ : ℕ → ℕ) (ξ : ℕ → Ω) (n : ℕ), n = 0 →
        (outerRun g lam eta a T0 (Wm + 1) B x0 τ ξ n).2.1 = x0 := by
      intro τ ξ n hn; subst hn; rfl
    have hy : ∀ s, y s = x0 := fun s => hgen _ _ K hK0
    simp_rw [hy, hx, sub_self, ENNReal.ofReal_zero, lintegral_zero, Finset.sum_const_zero,
      zero_mul]
    simp
  · have hAKpos : lam * (K : ℝ) ^ 2 / 4 ≤ AK := accA_ge hlam K
    have hKsq : 2 * R ^ 2 / (lam * ε) ≤ (K : ℝ) ^ 2 := by
      have hs := Nat.le_ceil (Real.sqrt (2 * Lbar * R ^ 2 / (Γh * ε)))
      have h0 : 0 ≤ Real.sqrt (2 * Lbar * R ^ 2 / (Γh * ε)) := Real.sqrt_nonneg _
      have h2 := pow_le_pow_left₀ h0 hs 2
      rw [Real.sq_sqrt (by positivity)] at h2
      have heq : 2 * R ^ 2 / (lam * ε) = 2 * Lbar * R ^ 2 / (Γh * ε) := by
        simp only [lam, pLam]; field_simp
      rw [heq]; exact h2
    have hKpos' : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hAK : 0 < AK := lt_of_lt_of_le (by positivity) hAKpos
    have hbound : R ^ 2 / 2 ≤ AK * ε := by
      have : 2 * R ^ 2 / (lam * ε) * (lam * ε) = 2 * R ^ 2 := by field_simp
      have h1 : 2 * R ^ 2 ≤ (K : ℝ) ^ 2 * (lam * ε) := by
        have := mul_le_mul_of_nonneg_right hKsq (by positivity : 0 ≤ lam * ε)
        linarith
      nlinarith
    have hsum : ENNReal.ofReal AK * ∑ σ : Fin K → Fin (Wm + 1),
        ∫⁻ ξ, ENNReal.ofReal (f (y (σ, ξ)) - f xstar) ∂P ≤ N * ENNReal.ofReal (R ^ 2 / 2) := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum fun σ _ => hlow σ).trans (hpb.trans ?_)
      gcongr
    have hfin : ∑ σ : Fin K → Fin (Wm + 1), ∫⁻ ξ, ENNReal.ofReal (f (y (σ, ξ)) - f xstar) ∂P ≤
        N * ENNReal.ofReal ε := by
      have h2 : N * ENNReal.ofReal (R ^ 2 / 2) ≤ ENNReal.ofReal AK * (N * ENNReal.ofReal ε) := by
        rw [mul_left_comm, ← ENNReal.ofReal_mul hAK.le]
        gcongr
      exact (ENNReal.mul_le_mul_iff_right (by simpa using hAK) ENNReal.ofReal_ne_top).mp
        (hsum.trans h2)
    calc (∑ σ, ∫⁻ ξ, ENNReal.ofReal (f (y (σ, ξ)) - f xstar) ∂P) * N⁻¹
        ≤ (N * ENNReal.ofReal ε) * N⁻¹ := by gcongr
      _ = ENNReal.ofReal ε := by
          rw [mul_comm N, mul_assoc, ENNReal.mul_inv_cancel hN0 hNt, mul_one]

end Master

open LongTails.Setups.StrongGrowthMeanSquaredSmoothConvex

theorem convergence : Convergence LongTails.Setups.StrongGrowthMeanSquaredSmoothConvex.spec
    (fun q _ => ⌈Real.sqrt (2 * q.Lbar * q.R ^ 2 / ((1 + q.Γ) * q.ε))⌉₊ *
      ⌈(1 + q.Γ) ^ 2 * (4810 + 3200 * Real.log (1 + q.Γ))⌉₊) := by
  apply convergence_of_call_budget (S := spec) (fun q => ⌈Real.sqrt (2 * q.Lbar * q.R ^ 2 /
    ((1 + q.Γ) * q.ε))⌉₊ * ⌈(1 + q.Γ) ^ 2 * (4810 + 3200 * Real.log (1 + q.Γ))⌉₊)
  refine ⟨fun q => proximalStorm (pLam q.Lbar (1 + q.Γ)) (pEta q.Lbar (1 + q.Γ)) (pA (1 + q.Γ))
    (pT0 (1 + q.Γ)) (pW (1 + q.Γ)) (pB (1 + q.Γ)) (pK q.Lbar q.R q.ε (1 + q.Γ)) q.x0, ?_,
    fun _ _ => trivial⟩
  intro q hq N hN f O hadm
  dsimp only
  obtain ⟨hL, hΓ, hR, hε⟩ := hq
  obtain ⟨g, p, P, hIID, rfl, hconv, hgrad, ⟨xstar, hmin, hx0⟩, hgm, hint, hmean, hvi, hsgc,
    hdi, hmss⟩ := hadm
  have H : Hyp (p : Measure q.Ω) f g q.Lbar q.Γ xstar :=
    ⟨hconv, hgrad, hmin, hgm, hint, hmean, hvi, hsgc, hdi, hmss, hL, hΓ⟩
  set Γh := 1 + q.Γ
  have hΓh : 1 ≤ Γh := by simp only [Γh]; linarith
  set lam := pLam q.Lbar Γh
  set eta := pEta q.Lbar Γh
  set a := pA Γh
  set T0 := pT0 Γh
  set Wm := pW Γh
  set B := pB Γh
  set K := pK q.Lbar q.R q.ε Γh
  have hlen : (B + (T0 + Wm + 1)) * K ≤ N := by
    refine le_trans ?_ hN
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ (block_calls_le hΓh)
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω) := by
    have := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
  have hτ : ∀ σ : Fin K → Fin (Wm + 1), ∀ i, seedIndex σ i ≤ Wm := fun σ i =>
    Nat.lt_succ_iff.mp (seedIndex_lt σ (by omega) i)
  have hexec : ∀ (σ : Fin K → Fin (Wm + 1)) (ξ : ℕ → q.Ω),
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (proximalStorm lam eta a T0 Wm B K q.x0) (fun _ => N)
        σ ξ = (outerRun g lam eta a T0 (Wm + 1) B q.x0 (seedIndex σ) ξ K).2.1 := by
    intro σ ξ
    unfold proximalStorm
    erw [QueryPlan.execute_sampledPlan_of_le _ P _ _ _ N _
      (fun (z : q.E × q.E) (ω : q.Ω) => (g z.1 ω, g z.2 ω)) σ ξ hlen]
    rw [QueryPlan.sampledEval_map]
    have h := eval_fullPlan g lam eta a T0 Wm B q.x0 (hτ σ) ξ K 0
    simp only [zero_mul, zero_add] at h
    exact congrArg (fun o : ℝ × q.E × q.E => o.2.1) h
  have hout : (fun s : (proximalStorm lam eta a T0 Wm B K q.x0).Seed × ((k : ℕ) → q.Ω) =>
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω => (g z.1 ω, g z.2 ω) } :
        Oracle (q.E × q.E) (q.E × q.E)) (proximalStorm lam eta a T0 Wm B K q.x0) (fun _ => N)
          s.1 s.2) = fun s => (outerRun g lam eta a T0 (Wm + 1) B q.x0 (seedIndex s.1) s.2 K).2.1 := by
    funext s; exact hexec s.1 s.2
  refine ⟨?_, xstar, hmin, ?_⟩
  · erw [hout]; exact measurable_outerOut hgm lam eta a T0 Wm B K q.x0
  have hfun : (fun s : (proximalStorm lam eta a T0 Wm B K q.x0).Seed × ((k : ℕ) → q.Ω) =>
      f (execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, z) ω =>
        (g z.1 ω, g z.2 ω) } : Oracle (q.E × q.E) (q.E × q.E))
        (proximalStorm lam eta a T0 Wm B K q.x0) (fun _ => N) s.1 s.2) - f xstar) =
      fun s => f (outerRun g lam eta a T0 (Wm + 1) B q.x0 (seedIndex s.1) s.2 K).2.1 - f xstar := by
    funext s; rw [hexec s.1 s.2]
  erw [hfun]
  change Integrable (fun s : (Fin K → Fin (Wm + 1)) × (ℕ → q.Ω) =>
      f (outerRun g lam eta a T0 (Wm + 1) B q.x0 (seedIndex s.1) s.2 K).2.1 - f xstar)
      ((PMF.uniformOfFintype (Fin K → Fin (Wm + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ∧
    ∫ s : (Fin K → Fin (Wm + 1)) × (ℕ → q.Ω),
      f (outerRun g lam eta a T0 (Wm + 1) B q.x0 (seedIndex s.1) s.2 K).2.1 - f xstar
      ∂((PMF.uniformOfFintype (Fin K → Fin (Wm + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
  rw [hP]
  have hm : Measurable fun s : (Fin K → Fin (Wm + 1)) × (ℕ → q.Ω) =>
      f (outerRun g lam eta a T0 (Wm + 1) B q.x0 (seedIndex s.1) s.2 K).2.1 - f xstar :=
    (H.f_continuous.measurable.comp (measurable_outerOut hgm lam eta a T0 Wm B K q.x0)).sub_const _
  have hnn : ∀ s : (Fin K → Fin (Wm + 1)) × (ℕ → q.Ω),
      0 ≤ f (outerRun g lam eta a T0 (Wm + 1) B q.x0 (seedIndex s.1) s.2 K).2.1 - f xstar := by
    intro s; have := hmin (mem_univ ((outerRun g lam eta a T0 (Wm + 1) B q.x0 (seedIndex s.1) s.2
      K).2.1)); simp only [mem_ofPred_eq] at this; linarith
  have hL' := H.master (R := q.R) hε q.x0 hx0
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL'
  refine ⟨?_, ?_⟩
  · have := integrable_toReal_of_lintegral_ne_top hm.ennreal_ofReal.aemeasurable hfin
    simpa [ENNReal.toReal_ofReal (hnn _)] using this
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
      hm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hL'

end OracleTemplate.ProximalStorm
