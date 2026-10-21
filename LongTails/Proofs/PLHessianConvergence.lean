import LongTails.Proofs.PLHessianRun
import LongTails.Proofs.PLHessianTuning
import LongTails.Proofs.Execution
import LongTails.Setups.PLHessianLipschitzKurtosis
import LongTails.Proofs.NormalizedStormConvergence

open Set MeasureTheory
open scoped ENNReal

namespace OracleTemplate.PLHessian

open OracleTemplate.WindowSgd

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω : Type}

lemma run_window (g : E → Ω → E) (η : ℝ) (Ta Tb : ℕ) (x0 : E) (ξ : ℕ → Ω) (T : ℕ) :
    ∀ j, j ≤ T →
      (fun sc : (ℕ × ℕ × E) × ℕ =>
          ((method η Ta Tb x0).update sc.1 (g (sc.1.2.2) (ξ sc.2)), sc.2 + 1))^[j] ((T, 0, x0), 0) =
        ((T, j, sgdSeq g η x0 ξ j), j)
  | 0, _ => rfl
  | j + 1, h => by
      rw [Function.iterate_succ_apply', run_window g η Ta Tb x0 ξ T j (by omega)]
      have hj : j < T := by omega
      simp [method, hj, sgdSeq]

lemma run_frozen (g : E → Ω → E) (η : ℝ) (Ta Tb : ℕ) (x0 : E) (ξ : ℕ → Ω) (T : ℕ) :
    ∀ m, ((fun sc : (ℕ × ℕ × E) × ℕ =>
          ((method η Ta Tb x0).update sc.1 (g (sc.1.2.2) (ξ sc.2)), sc.2 + 1))^[T + m]
          ((T, 0, x0), 0)).1 = (T, T, sgdSeq g η x0 ξ T)
  | 0 => by rw [Nat.add_zero, run_window g η Ta Tb x0 ξ T T le_rfl]
  | m + 1 => by
      rw [show T + (m + 1) = (T + m) + 1 by omega, Function.iterate_succ_apply']
      have ih := run_frozen g η Ta Tb x0 ξ T m
      set sc := (fun sc : (ℕ × ℕ × E) × ℕ =>
          ((method η Ta Tb x0).update sc.1 (g (sc.1.2.2) (ξ sc.2)), sc.2 + 1))^[T + m]
          ((T, 0, x0), 0)
      obtain ⟨s, c⟩ := sc
      simp only at ih
      subst ih
      simp [method]

noncomputable def winOracle [MeasurableSpace Ω] (g : E → Ω → E) (P : ProbabilityMeasure (ℕ → Ω)) :
    Oracle E E where
  Seed := fun _ => Ω
  law := P
  answer := fun _ (_, x) ω => g x ω

lemma execute_window [MeasurableSpace Ω] (g : E → Ω → E) (P : ProbabilityMeasure (ℕ → Ω))
    (η : ℝ) (Ta Tb : ℕ) (x0 : E) (K : ℕ) (τ : Fin (Tb + 1)) (ξ : ℕ → Ω) (hK : Ta + Tb ≤ K) :
    execute (winOracle g P) (method η Ta Tb x0) (fun _ => K) τ ξ =
      sgdSeq g η x0 ξ (Ta + τ.val) := by
  refine (execute_indexed_of_answer (winOracle g P) (method η Ta Tb x0) K τ ξ (fun k q => g q.2 (ξ k)) (fun _ _ => rfl)).trans ?_
  obtain ⟨m, hm⟩ : ∃ m, K = (Ta + τ.val) + m := ⟨K - (Ta + τ.val), by have := τ.isLt; omega⟩
  subst hm
  have h := run_frozen g η Ta Tb x0 ξ (Ta + τ.val) m
  change ((((fun sc : (ℕ × ℕ × E) × ℕ =>
          ((method η Ta Tb x0).update sc.1 (g (sc.1.2.2) (ξ sc.2)), sc.2 + 1))^[Ta + τ.val + m]
          ((Ta + τ.val, 0, x0), 0)).1).2.2) = _
  rw [h]

section Master

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω]
  {p : Measure Ω} [IsProbabilityMeasure p] {f : E → ℝ} {g : E → Ω → E} {u : E}
  {L μ ρ σ K : ℝ}

omit [BorelSpace E] [IsProbabilityMeasure p] in
lemma Hyp.pot_le_gap (H : Hyp p f g u L μ ρ σ K) {Φ0 : ℝ} (hΦ0 : 0 < Φ0) (x : E) :
    pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 x ≤
      48 * Real.sqrt (L / μ) * (f x - f u) / μ := by
  have hμ := H.μ_pos
  have hL := H.L_pos
  have hsk : 1 ≤ Real.sqrt (L / μ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by rw [le_div_iff₀ hμ]; linarith [H.μ_le])
  have hgap : 0 ≤ f x - f u := sub_nonneg.mpr (H.min (mem_univ x))
  obtain ⟨p', hp', hq⟩ := quad_growth hL hμ H.μ_le H.grad H.lip H.min H.pl x
  have hD : distSq f u x ≤ ‖x - p'‖ ^ 2 :=
    distSq_le x p' (le_antisymm (hp' (mem_univ u)) (H.min (mem_univ p')))
  have hD' : distSq f u x ≤ 16 * (f x - f u) / μ := by
    rw [le_div_iff₀ hμ]; nlinarith
  have hh := hub_le_self (a := Φ0 / 4) (by positivity) (by positivity : (0 : ℝ) < Φ0 / 4) hgap
  unfold pot
  have hm : 32 * Real.sqrt (L / μ) / μ * hub (Φ0 / 4) (Φ0 / 4) (f x - f u) ≤
      32 * Real.sqrt (L / μ) / μ * (f x - f u) :=
    mul_le_mul_of_nonneg_left hh (by positivity)
  have e : 32 * Real.sqrt (L / μ) / μ * (f x - f u) = 32 * Real.sqrt (L / μ) * (f x - f u) / μ := by
    ring
  have : 16 * (f x - f u) / μ ≤ 16 * Real.sqrt (L / μ) * (f x - f u) / μ := by
    apply div_le_div_of_nonneg_right _ hμ.le; nlinarith
  have e2 : 16 * Real.sqrt (L / μ) * (f x - f u) / μ + 32 * Real.sqrt (L / μ) * (f x - f u) / μ =
      48 * Real.sqrt (L / μ) * (f x - f u) / μ := by ring
  linarith

lemma measurable_window_out (hg : Measurable (Function.uncurry g)) (η : ℝ) (Ta Tb : ℕ) (x0 : E) :
    Measurable (fun ω : Fin (Tb + 1) × (ℕ → Ω) => sgdSeq g η x0 ω.2 (Ta + ω.1.val)) :=
  measurable_from_prod_countable_right fun τ => measurable_sgdSeq hg η x0 (Ta + τ.val)

theorem Hyp.master (H : Hyp p f g u L μ ρ σ K) {Δ ε : ℝ} (h : Tune L μ ρ σ K Δ ε) (x0 : E)
    (hgap : f x0 - f u ≤ Δ) :
    ∫⁻ ω, ENNReal.ofReal (f (sgdSeq g (1 / tH L μ ρ σ K ε) x0 ω.2
        (tTa L μ ρ σ K Δ ε + ω.1.val)) - f u)
      ∂((PMF.uniformOfFintype (Fin (tTb L μ ρ σ K ε + 1))).toMeasure.prod
        (Measure.infinitePi fun _ : ℕ => p)) ≤ ENNReal.ofReal ε := by
  set η := 1 / tH L μ ρ σ K ε with hηdef
  set Ta := tTa L μ ρ σ K Δ ε
  set Tb := tTb L μ ρ σ K ε
  set Φ0 := tΦ0 L μ ρ K ε
  set P := Measure.infinitePi fun _ : ℕ => p
  have hη : 0 < η := by have := h.H_pos; positivity
  have hΦ0 := h.Φ0_pos
  have hΦ0ρ := h.Φ0ρ
  have h1 := h.c1
  have h2 := h.c2
  have h3 := h.c3
  have hm : Measurable (fun ω : Fin (Tb + 1) × (ℕ → Ω) =>
      ENNReal.ofReal (f (sgdSeq g η x0 ω.2 (Ta + ω.1.val)) - f u)) :=
    ENNReal.measurable_ofReal.comp
      ((H.continuous.measurable.comp (measurable_window_out H.meas η Ta Tb x0)).sub_const _)
  rw [lintegral_prod _ hm.aemeasurable, lintegral_fintype]
  simp only [PMF.toMeasure_uniformOfFintype_apply _ (measurableSet_singleton _), Fintype.card_fin]
  have hc : ∀ τ : Fin (Tb + 1), (Fintype.card ({τ} : Set (Fin (Tb + 1))) : ℝ≥0∞) = 1 := by
    intro τ; simp
  simp only [hc, one_div]
  have higap : ∀ n, Integrable (fun ξ => f (sgdSeq g η x0 ξ n) - f u) P := fun n =>
    (H.run_step hη hΦ0 hΦ0ρ h1 h2 h3 x0 n (H.run_bound hη hΦ0 hΦ0ρ h1 h2 h3 x0 n).1).2.1
  have hj : ∀ τ : Fin (Tb + 1), ∫⁻ ξ, ENNReal.ofReal (f (sgdSeq g η x0 ξ (Ta + τ.val)) - f u) ∂P =
      ENNReal.ofReal (∫ ξ, (f (sgdSeq g η x0 ξ (Ta + τ.val)) - f u) ∂P) := by
    intro τ
    rw [ofReal_integral_eq_lintegral_ofReal (higap _)
      (Filter.Eventually.of_forall fun _ => sub_nonneg.mpr (H.min (mem_univ _)))]
  simp_rw [hj]
  have hnn : ∀ i, 0 ≤ ∫ ξ, (f (sgdSeq g η x0 ξ i) - f u) ∂P :=
    fun i => integral_nonneg fun _ => sub_nonneg.mpr (H.min (mem_univ _))
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun τ _ => hnn _)]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∫ ξ, (f (sgdSeq g η x0 ξ (Ta + k)) - f u) ∂P)]
  set sum := ∑ k ∈ Finset.range (Tb + 1), ∫ ξ, (f (sgdSeq g η x0 ξ (Ta + k)) - f u) ∂P
  have hT : (0 : ℝ) < (Tb : ℝ) + 1 := by positivity
  have hinv : (((Tb + 1 : ℕ) : ℝ≥0∞))⁻¹ = ENNReal.ofReal (1 / ((Tb : ℝ) + 1)) := by
    rw [ENNReal.ofReal_div_of_pos hT, ENNReal.ofReal_one, one_div]
    congr 1
    rw [ENNReal.ofReal_add (by positivity) zero_le_one]
    simp
  have hsum0 : 0 ≤ sum := Finset.sum_nonneg fun k _ => hnn _
  rw [hinv, ← ENNReal.ofReal_mul hsum0]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_one_div]
  have hw := H.window_sum hη hΦ0 hΦ0ρ h1 h2 h3 x0 Ta (Tb + 1)
  have hpotn : 0 ≤ ∫ ξ, pot f u (32 * Real.sqrt (L / μ) / μ) Φ0
      (sgdSeq g η x0 ξ (Ta + (Tb + 1))) ∂P :=
    integral_nonneg fun _ => pot_nonneg (by have := H.μ_pos; positivity) hΦ0 _
  rw [← Finset.mul_sum] at hw
  have hEa := (H.run_bound hη hΦ0 hΦ0ρ h1 h2 h3 x0 Ta).2
  have hP0 := H.pot_le_gap hΦ0 x0
  have hP0' : pot f u (32 * Real.sqrt (L / μ) / μ) Φ0 x0 ≤ 48 * Real.sqrt (L / μ) * Δ / μ := by
    refine hP0.trans (div_le_div_of_nonneg_right ?_ H.μ_pos.le)
    exact mul_le_mul_of_nonneg_left hgap (by positivity)
  refine h.accuracy hP0' (pot_nonneg (by have := H.μ_pos; positivity) hΦ0 _) hEa ?_
  push_cast at hw
  linarith

end Master

end OracleTemplate.PLHessian

namespace OracleTemplate.PLHessian

open LongTails.Setups.PLHessianLipschitzKurtosis OracleTemplate.WindowSgd

lemma Tune.calls {L μ ρ σ K Δ ε : ℝ} (h : Tune L μ ρ σ K Δ ε) :
    tTa L μ ρ σ K Δ ε + tTb L μ ρ σ K ε ≤
      ⌈32 * tH L μ ρ σ K ε / μ * (Real.log (1 + 6 * Real.sqrt (L / μ) * Δ / ε) + 1) +
        512 * σ ^ 2 / (μ * ε)⌉₊ + 1 := by
  have hH := h.H_pos
  have hμ := h.μ_pos
  have hε := h.ε_pos
  have hlog : 0 ≤ Real.log (1 + 6 * Real.sqrt (L / μ) * Δ / ε) := by
    have := h.Δ_nn; apply Real.log_nonneg; have : 0 ≤ 6 * Real.sqrt (L / μ) * Δ / ε := by positivity
    linarith
  have hx : 0 ≤ 32 * tH L μ ρ σ K ε / μ * Real.log (1 + 6 * Real.sqrt (L / μ) * Δ / ε) := by
    positivity
  have hy : 0 ≤ 512 * σ ^ 2 / (μ * ε) + 32 * tH L μ ρ σ K ε / μ := by positivity
  have hs := NormalizedStorm.ceil_add_ceil_le hx hy
  have e : 32 * tH L μ ρ σ K ε / μ * Real.log (1 + 6 * Real.sqrt (L / μ) * Δ / ε) +
      (512 * σ ^ 2 / (μ * ε) + 32 * tH L μ ρ σ K ε / μ) =
      32 * tH L μ ρ σ K ε / μ * (Real.log (1 + 6 * Real.sqrt (L / μ) * Δ / ε) + 1) +
        512 * σ ^ 2 / (μ * ε) := by ring
  rw [e] at hs
  unfold tTa tTb
  exact hs

theorem convergence : Convergence LongTails.Setups.PLHessianLipschitzKurtosis.spec
    (fun q _ => ⌈32 * tH q.L q.μ q.ρ q.σ q.K q.ε / q.μ *
      (Real.log (1 + 6 * Real.sqrt (q.L / q.μ) * q.Δ / q.ε) + 1) +
        512 * q.σ ^ 2 / (q.μ * q.ε)⌉₊ + 1) := by
  refine ⟨fun q => method (1 / tH q.L q.μ q.ρ q.σ q.K q.ε) (tTa q.L q.μ q.ρ q.σ q.K q.Δ q.ε)
    (tTb q.L q.μ q.ρ q.σ q.K q.ε) q.x0, ?_, ?_⟩
  · intro q hq f O hadm
    dsimp only
    obtain ⟨hμ, hμL, hρ, hσ, hK, hΔ, hε⟩ := hq
    obtain ⟨g, P0, P, hIID, rfl, hgrad, hlip, hdiff, hhess, ⟨u, hmin, hpl, hgap⟩, hgm, hint,
      hmean, hvi, hki, hvar, hkurt⟩ := hadm
    have H : Hyp (P0 : Measure q.Ω) f g u q.L q.μ q.ρ q.σ q.K :=
      ⟨hgrad, hlip, hdiff, hhess, hmin, hpl, hgm, hint, hmean, hvi, hki, hvar, hkurt,
        lt_of_lt_of_le hμ hμL, hμ, hμL, hρ, hσ, hK⟩
    have h : Tune q.L q.μ q.ρ q.σ q.K q.Δ q.ε := ⟨hμ, hμL, hρ, hσ, hK, hΔ, hε⟩
    set η := 1 / tH q.L q.μ q.ρ q.σ q.K q.ε
    set Ta := tTa q.L q.μ q.ρ q.σ q.K q.Δ q.ε
    set Tb := tTb q.L q.μ q.ρ q.σ q.K q.ε
    set B := ⌈32 * tH q.L q.μ q.ρ q.σ q.K q.ε / q.μ *
      (Real.log (1 + 6 * Real.sqrt (q.L / q.μ) * q.Δ / q.ε) + 1) +
        512 * q.σ ^ 2 / (q.μ * q.ε)⌉₊ + 1
    have hB : Ta + Tb ≤ B := h.calls
    have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (P0 : Measure q.Ω) := by
      have := hIID.stream_law.map_eq
      exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans this
    have hexec : ∀ (τ : Fin (Tb + 1)) (ξ : ℕ → q.Ω),
        execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) seed => g x seed } :
          Oracle q.E q.E) (method η Ta Tb q.x0) (fun _ => B) τ ξ =
        sgdSeq g η q.x0 ξ (Ta + τ.val) :=
      fun τ ξ => execute_window g P η Ta Tb q.x0 B τ ξ hB
    have hout : (fun seed : (method η Ta Tb q.x0).Seed × ((k : ℕ) → q.Ω) =>
        execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) seed => g x seed } :
          Oracle q.E q.E) (method η Ta Tb q.x0) (fun _ => B) seed.1 seed.2) =
        fun ω => sgdSeq g η q.x0 ω.2 (Ta + ω.1.val) := by
      funext seed; exact hexec seed.1 seed.2
    have hfun : (fun seed : (method η Ta Tb q.x0).Seed × ((k : ℕ) → q.Ω) =>
        f (execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) seed => g x seed } :
          Oracle q.E q.E) (method η Ta Tb q.x0) (fun _ => B) seed.1 seed.2) - f u) =
        fun ω => f (sgdSeq g η q.x0 ω.2 (Ta + ω.1.val)) - f u := by
      funext seed; rw [hexec seed.1 seed.2]
    refine ⟨?_, u, hmin, ?_⟩
    · erw [hout]; exact measurable_window_out hgm η Ta Tb q.x0
    erw [hfun]
    change Integrable (fun ω : Fin (Tb + 1) × (ℕ → q.Ω) =>
        f (sgdSeq g η q.x0 ω.2 (Ta + ω.1.val)) - f u)
        ((PMF.uniformOfFintype (Fin (Tb + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ∧
      ∫ ω : Fin (Tb + 1) × (ℕ → q.Ω), (f (sgdSeq g η q.x0 ω.2 (Ta + ω.1.val)) - f u)
        ∂((PMF.uniformOfFintype (Fin (Tb + 1))).toMeasure.prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
    rw [hP]
    have hm : Measurable (fun ω : Fin (Tb + 1) × (ℕ → q.Ω) =>
        f (sgdSeq g η q.x0 ω.2 (Ta + ω.1.val)) - f u) :=
      (H.continuous.measurable.comp (measurable_window_out hgm η Ta Tb q.x0)).sub_const _
    have hnn : ∀ ω : Fin (Tb + 1) × (ℕ → q.Ω), 0 ≤ f (sgdSeq g η q.x0 ω.2 (Ta + ω.1.val)) - f u :=
      fun ω => sub_nonneg.mpr (hmin (mem_univ _))
    have hL' := H.master h q.x0 hgap
    have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL'
    refine ⟨?_, ?_⟩
    · have := integrable_toReal_of_lintegral_ne_top
        (ENNReal.measurable_ofReal.comp hm).aemeasurable hfin
      simpa [ENNReal.toReal_ofReal (hnn _)] using this
    · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnn)
        hm.aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal hε.le hL'
  · intro q hq
    have hμ := hq.1
    have h : Tune q.L q.μ q.ρ q.σ q.K q.Δ q.ε :=
      ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1, hq.2.2.2.2.2.1, hq.2.2.2.2.2.2⟩
    exact ⟨_, by have := h.H_pos; positivity, _, _, rfl⟩

end OracleTemplate.PLHessian
