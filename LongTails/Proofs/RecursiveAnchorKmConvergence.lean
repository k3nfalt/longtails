import LongTails.Proofs.Execution
import LongTails.Proofs.RecursiveAnchorKmExpectation
import LongTails.Proofs.RecursiveAnchorKmExecution
import LongTails.Proofs.RecursiveAnchorKmSchedule

open MeasureTheory

namespace OracleTemplate.RecursiveAnchorKm

open LongTails.Setups.StochasticFixedPointSmoothBanach

noncomputable def horizon (q : spec.Params) : ℕ :=
  ⌈(Real.logb 2 (1 + q.D / q.ε) + 4) * (16 + 20 * q.D / q.ε +
    2048 * q.K * q.σ ^ 2 * (Real.logb 2 (1 + q.D / q.ε) + 4) ^ 2 / q.ε ^ 2)⌉₊

theorem convergence : Convergence spec (fun p _ => horizon p) := by
  apply convergence_of_public_budget (S := spec) horizon
  refine ⟨fun q => tunedAnchorKm q.K q.σ q.D q.ε q.x0, ?_, fun _ _ => trivial⟩
  rintro q ⟨hK, hD, hσ, hε⟩ M O
    ⟨law, h_samples, hO, hsmooth, hnonexp, ⟨xstar, hstar, hdist⟩, hmeas, hunb, hvar⟩
  have hlaw : (law : Measure _) = Measure.infinitePi (fun _ : ℕ => (M.law : Measure q.Ξ)) := by
    have h := h_samples.independent.map_fun_eq_infinitePi_map h_samples.measurable
    change (law : Measure (ℕ → q.Ξ)).map id = _ at h
    simpa only [h_samples.marginal, Measure.map_id] using h
  have hlaw' : law = ⟨Measure.infinitePi (fun _ : ℕ => (M.law : Measure q.Ξ)), inferInstance⟩ :=
    Subtype.ext hlaw
  rw [hlaw'] at hO
  subst hO
  set P := Measure.infinitePi (fun _ : ℕ => (M.law : Measure q.Ξ))
  set S := lastStage q.D q.ε
  set lam := anchorWeight q.D q.ε
  set Λ := totalWeight q.D q.ε
  set α := stageStep q.K q.σ q.D q.ε
  set N := stageLength q.K q.σ q.D q.ε
  set η := stageTarget q.D q.ε
  have hN : ∀ u, u ≤ S → 0 < N u := fun u _ => stageLength_pos hD hε hK u
  have hB : start N (S + 1) ≤ horizon q := by
    have h1 := budget_le hD hε (σ := q.σ) hK
    have h2 : ((start N (S + 1) : ℕ) : ℝ) =
        ∑ u ∈ Finset.range (lastStage q.D q.ε + 1), (stageLength q.K q.σ q.D q.ε u : ℝ) := by
      simp only [start, Nat.cast_sum]; rfl
    have h3 := Nat.le_ceil ((Real.logb 2 (1 + q.D / q.ε) + 4) * (16 + 20 * q.D / q.ε +
      2048 * q.K * q.σ ^ 2 * (Real.logb 2 (1 + q.D / q.ε) + 4) ^ 2 / q.ε ^ 2))
    have h4 : ((start N (S + 1) : ℕ) : ℝ) ≤ (horizon q : ℝ) := by
      rw [h2]; exact le_trans h1 h3
    exact_mod_cast h4
  have hexec : ∀ ξ : ℕ → q.Ξ,
      execute
        { Seed := fun _ => q.Ξ
          law := ⟨P, inferInstance⟩
          answer := fun _ (_, x) ω => M.sample ω x }
        (tunedAnchorKm q.K q.σ q.D q.ε q.x0) (fun _ => horizon q) () ξ =
      (stage M.sample lam Λ α N q.x0 ξ (S + 1)).1 :=
    fun ξ => execute_recursiveAnchorKm _ M.sample S lam Λ α N q.x0 hN _ hB ξ
  have hyp : Hyp (M.law : Measure q.Ξ) M.map M.sample q.K q.σ :=
    ⟨hsmooth, hnonexp, hmeas, hunb, hvar, hK⟩
  set out : (ℕ → q.Ξ) → q.E := fun ξ => (stage M.sample lam Λ α N q.x0 ξ (S + 1)).1
  have hout : Measurable out := (measurable_stage hmeas lam Λ α N q.x0 (S + 1)).fst
  have hres_m : Measurable (fun ξ => ‖out ξ - M.map (out ξ)‖) := by
    have hT : Continuous M.map := by
      refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => ?_)
      rw [dist_eq_norm, dist_eq_norm]; simpa using hnonexp x y
    exact (hout.sub (hT.measurable.comp hout)).norm
  have hbound := hyp.residual_bound lam Λ α N q.x0 xstar hstar hdist S η
    (b := q.ε / (2 * (S + 1)))
    (anchorWeight_pos hD hε) totalWeight_zero totalWeight_succ (totalWeight_pos hD hε)
    (stageStep_mem hD hε hK) (stageTarget_pos hD hε) (stage_noise hD hε hK)
    (by
      have h1 := stage_count hD hε (σ := q.σ) hK 0
      simp only [ite_true] at h1
      exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) (initial_contraction hD hε))
    (by
      intro u hu
      have h1 := stage_count hD hε (σ := q.σ) hK (u + 1)
      simp only [Nat.add_one_ne_zero, ite_false] at h1
      exact le_trans (mul_le_mul_of_nonneg_right h1 (by positivity)) (later_contraction hD hε hu))
    (fun u hu => accuracy_step hD hε hu) (by positivity)
  have hlint : ∫⁻ ξ, ENNReal.ofReal ‖out ξ - M.map (out ξ)‖ ∂P ≤ ENNReal.ofReal q.ε :=
    le_trans hbound (ENNReal.ofReal_le_ofReal (accuracy_total hD hε))
  have hnn : 0 ≤ᵐ[P] fun ξ => ‖out ξ - M.map (out ξ)‖ :=
    Filter.Eventually.of_forall fun _ => norm_nonneg _
  have hint : Integrable (fun ξ => ‖out ξ - M.map (out ξ)‖) P :=
    ⟨hres_m.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal hnn).mpr (lt_of_le_of_lt hlint ENNReal.ofReal_lt_top)⟩
  have hval : ∫ ξ, ‖out ξ - M.map (out ξ)‖ ∂P ≤ q.ε := by
    rw [integral_eq_lintegral_of_nonneg_ae hnn hres_m.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hε.le hlint
  change spec.successful q M
      (fun seed : Unit × (ℕ → q.Ξ) =>
        execute
          { Seed := fun _ => q.Ξ
            law := ⟨P, inferInstance⟩
            answer := fun _ (_, x) ω => M.sample ω x }
          (tunedAnchorKm q.K q.σ q.D q.ε q.x0) (fun _ => horizon q) seed.1 seed.2)
      ⟨(Measure.dirac ()).prod P, inferInstance⟩
  have hfun : (fun seed : Unit × (ℕ → q.Ξ) =>
      execute
        { Seed := fun _ => q.Ξ
          law := ⟨P, inferInstance⟩
          answer := fun _ (_, x) ω => M.sample ω x }
        (tunedAnchorKm q.K q.σ q.D q.ε q.x0) (fun _ => horizon q) seed.1 seed.2) =
      fun seed => out seed.2 := by
    funext ⟨⟨⟩, ξ⟩
    exact hexec ξ
  rw [hfun]
  refine ⟨hout.comp measurable_snd, ?_, ?_⟩
  · exact (measurePreserving_snd (μ := Measure.dirac ()) (ν := P)).integrable_comp_of_integrable hint
  · have hsnd := integral_fun_snd (μ := (Measure.dirac () : Measure Unit)) (ν := P)
      (fun ξ => ‖out ξ - M.map (out ξ)‖)
    change ∫ seed : Unit × (ℕ → q.Ξ), ‖out seed.2 - M.map (out seed.2)‖
      ∂((Measure.dirac ()).prod P) ≤ q.ε
    rw [show (∫ seed : Unit × (ℕ → q.Ξ), ‖out seed.2 - M.map (out seed.2)‖
      ∂((Measure.dirac ()).prod P)) = ∫ ξ, ‖out ξ - M.map (out ξ)‖ ∂P by simpa using hsnd]
    exact hval

end OracleTemplate.RecursiveAnchorKm
