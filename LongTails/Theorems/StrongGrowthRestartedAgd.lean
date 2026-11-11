import LongTails.Setups.StrongGrowthHessianLipschitz
import LongTails.Proofs.StrongGrowthAgdBudget

namespace OracleTemplate.StrongGrowthRestartedAgd

open MeasureTheory LongTails.Setups.StrongGrowthHessianLipschitz
  LongTails.Algorithms.StrongGrowthRestartedAgd LongTails.Proofs.StrongGrowthAgdProcess
  LongTails.Proofs.StrongGrowthAgdInvariant LongTails.Proofs.StrongGrowthAgdBlocks
  LongTails.Proofs.StrongGrowthAgdEpochRun LongTails.Proofs.StrongGrowthAgdFinal
  LongTails.Proofs.StrongGrowthAgdBridge LongTails.Proofs.StrongGrowthAgdBudget
  LongTails.Proofs.StrongGrowthAgdMeasurable

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ =>
  (⌈Real.log (1 + 8 * Real.sqrt (2 * q.L * q.Δ) / q.ε)⌉₊ + 1) * (⌈268435456 * q.Δ * Real.sqrt q.ρ / (q.ε * Real.sqrt q.ε)⌉₊ + 1) * (⌈1 / Real.sqrt (Real.sqrt (q.ρ * q.ε) / q.L)⌉₊ + 1 + (8 + ⌈2 * Real.log (1 + 8 * (Real.log (1 + 8 * Real.sqrt (2 * q.L * q.Δ) / q.ε) + 2) * (268435456 * q.Δ * Real.sqrt q.ρ / (q.ε * Real.sqrt q.ε) + 2) * (Real.sqrt (8 * q.L * q.Δ + q.L * q.ε * Real.sqrt (q.ε / q.ρ) + q.ε ^ 2) + q.L * Real.sqrt (q.ε / q.ρ)) / q.ε)⌉₊)) * ⌈800 * q.κ⌉₊

theorem result : Convergence LongTails.Setups.StrongGrowthHessianLipschitz.spec budget := by
  refine ⟨fun q => method (cfgOf q.L q.ρ q.κ q.Δ q.ε) q.x0, ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  dsimp only
  obtain ⟨hL, hρ, hκ, hΔ, hε, hvalid⟩ := hq
  obtain ⟨g, P0, P, hIID, rfl, hf, hlip, hhess, hΔf, hmeas, hint, hmean, hint2, hvar⟩ := hadm
  have T : Tune q.L q.ρ q.κ q.Δ q.ε := ⟨hL, hρ, hκ, hΔ, hε, hvalid⟩
  set cfg := cfgOf q.L q.ρ q.κ q.Δ q.ε with hcfg
  have H : Hyps cfg q.x0 g f (P0 : Measure q.Ω) q.L q.ρ q.κ q.Δ (q.ε / 4) :=
    hyps_of T q.x0 f g (P0 : Measure q.Ω) hf hlip hhess hΔf hmeas hint hmean hint2 hvar
  set R := Rc q.L q.Δ q.ε with hR
  set N := R * cfg.N1 * cfg.Eb with hN
  have hbud : budget q = fun _ => N * cfg.b := by
    funext i
    rfl
  have hexec : ∀ ξ : ℕ → q.Ω,
      execute ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) seed => g x seed } : Oracle q.E q.E)
        (method cfg q.x0) (budget q) () ξ =
      (run (astep cfg q.x0 g f) (s₀ cfg q.x0) (blocks cfg ξ) N).1.out := by
    intro ξ
    rw [hbud, execute_method cfg q.x0 g ξ P H.hb N, traj_eq_run cfg q.x0 g f ξ N]
  have hmeasrun : Measurable (fun β : ℕ → (Fin cfg.b → q.Ω) =>
      ‖gradient f (run (astep cfg q.x0 g f) (s₀ cfg q.x0) β N).1.out‖) :=
    ((H.h.gradDiff.continuous.measurable).comp (measurable_out.comp (measurable_fst.comp
      (run_measurable _ _ (measurable_astep' H) N)))).norm
  have hcert := (cert_lt T).1
  have hq := fail_le_quarter T
  have hτ : 0 < Real.sqrt (2 * q.L * (q.Δ + cfg.N1 * cEpoch cfg q.ρ) + (q.ε / 4) ^ 2) :=
    Real.sqrt_pos.mpr (by
      have := cEpoch_nonneg H
      have : (0:ℝ) ≤ cfg.N1 := Nat.cast_nonneg _
      positivity)
  obtain ⟨hinteg, hbound⟩ := output_expectation H hcert hq _ hτ R
  have hg0 : ‖gradient f q.x0‖ ≤ Real.sqrt (2 * q.L * q.Δ) := by
    have h1 := grad_le_gap H.h (f q.x0 - q.Δ) (fun x => by linarith [hΔf x]) q.x0
    rw [sub_sub_cancel] at h1
    exact Real.le_sqrt_of_sq_le h1
  have hfin := final_le T ‖gradient f q.x0‖ (norm_nonneg _) hg0
  have hle : ∫ β, ‖gradient f (run (astep cfg q.x0 g f) (s₀ cfg q.x0) β N).1.out‖
      ∂(Measure.infinitePi fun _ : ℕ => (Measure.pi fun _ : Fin cfg.b => (P0 : Measure q.Ω))) ≤ q.ε := by
    rw [hN]
    exact hbound.trans hfin
  have hmout : Measurable (fun β : ℕ → (Fin cfg.b → q.Ω) =>
      (run (astep cfg q.x0 g f) (s₀ cfg q.x0) β N).1.out) :=
    measurable_out.comp (measurable_fst.comp (run_measurable _ _ (measurable_astep' H) N))
  set h : (ℕ → (Fin cfg.b → q.Ω)) → ℝ := fun β =>
    ‖gradient f (run (astep cfg q.x0 g f) (s₀ cfg q.x0) β N).1.out‖ with hh
  have hint_P : Integrable (fun ξ => h (blocks cfg ξ)) (P : Measure (ℕ → q.Ω)) :=
    integrable_blocks cfg (P0 : Measure q.Ω) (P : Measure _) hIID h hmeasrun hinteg
  have hint_P' : ∫ ξ, h (blocks cfg ξ) ∂(P : Measure (ℕ → q.Ω)) ≤ q.ε := by
    rw [integral_blocks cfg (P0 : Measure q.Ω) (P : Measure _) hIID h hmeasrun]
    exact hle
  let result := fun seed : Unit × (ℕ → q.Ω) => execute
      ({ Seed := fun _ => q.Ω, law := P, answer := fun _ (_, x) seed => g x seed } : Oracle q.E q.E)
      (method cfg q.x0) (budget q) seed.1 seed.2
  change Measurable result ∧
    Integrable (fun seed => ‖gradient f (result seed)‖) ((Measure.dirac ()).prod (P : Measure (ℕ → q.Ω))) ∧
    (∫ seed, ‖gradient f (result seed)‖ ∂(Measure.dirac ()).prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
  have hexec' : result = fun seed => (run (astep cfg q.x0 g f) (s₀ cfg q.x0) (blocks cfg seed.2) N).1.out := by
    funext seed; exact hexec seed.2
  rw [hexec']
  refine ⟨hmout.comp ((blocks_measurable cfg).comp measurable_snd), ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := (P : Measure (ℕ → q.Ω)))).integrable_comp_of_integrable
      hint_P
  · change (∫ seed : Unit × (ℕ → q.Ω), h (blocks cfg seed.2) ∂(Measure.dirac ()).prod (P : Measure (ℕ → q.Ω))) ≤ q.ε
    rw [integral_fun_snd (fun ξ : ℕ → q.Ω => h (blocks cfg ξ)), probReal_univ, one_smul]
    exact hint_P'

end OracleTemplate.StrongGrowthRestartedAgd
