import LongTails.Proofs.PowerSmoothFixedPointProcess
import LongTails.Proofs.Execution
import LongTails.Proofs.RecursiveAnchorKmExecution

open MeasureTheory

namespace LongTails.Proofs.PowerSmoothAnchoringConvergence

open OracleTemplate OracleTemplate.RecursiveAnchorKm
open LongTails.Setups.StochasticPowerSmoothFixedPoint
open LongTails.Algorithms.PowerSmoothAnchoring PowerSmoothAnchoringTuning

lemma convergence_of_budget (budget : Params → ℕ)
    (hbudget : ∀ q, spec.valid q → (levels q + 1) * innerSteps q ≤ budget q) :
    Convergence spec (fun q _ => budget q) := by
  apply convergence_of_public_budget (S := spec) budget
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  rintro q hvalid M O
    ⟨law, h_samples, hO, hsmooth, hnonexp, ⟨xstar, hstar, hdist⟩, hmeas, hunb, hvar⟩
  rcases hvalid with ⟨hs, hs2, hK, hD, hσ, hε⟩
  have hlaw : (law : Measure _) = Measure.infinitePi (fun _ : ℕ => (M.law : Measure q.Ξ)) := by
    have h := h_samples.independent.map_fun_eq_infinitePi_map h_samples.measurable
    change (law : Measure (ℕ → q.Ξ)).map id = _ at h
    simpa only [h_samples.marginal, Measure.map_id] using h
  have hlaw' : law = ⟨Measure.infinitePi (fun _ : ℕ => (M.law : Measure q.Ξ)), inferInstance⟩ :=
    Subtype.ext hlaw
  rw [hlaw'] at hO
  subst hO
  set P := Measure.infinitePi (fun _ : ℕ => (M.law : Measure q.Ξ))
  set S := levels q
  set lam := LongTails.Algorithms.PowerSmoothAnchoring.anchorWeight q
  set Λ := strength q
  set α := LongTails.Algorithms.PowerSmoothAnchoring.stageStep q
  set N := fun _ : ℕ => innerSteps q
  have hN : ∀ u, u ≤ S → 0 < N u := fun _ _ =>
    innerSteps_pos q (by linarith) hσ hε
  have hB : start N (S + 1) ≤ budget q := by
    have hb := hbudget q ⟨hs, hs2, hK, hD, hσ, hε⟩
    simpa [start, N, S] using hb
  have hexec : ∀ ξ : ℕ → q.Ξ,
      execute
        { Seed := fun _ => q.Ξ
          law := ⟨P, inferInstance⟩
          answer := fun _ (_, x) ω => M.sample ω x }
        (algorithm q) (fun _ => budget q) () ξ =
      (stage M.sample lam Λ α N q.x0 ξ (S + 1)).1 :=
    fun ξ => execute_recursiveAnchorKm _ M.sample S lam Λ α N q.x0 hN _ hB ξ
  have hyp : PowerSmoothFixedPointIteration.Hyp (M.law : Measure q.Ξ) M.map M.sample q.exponent q.K q.σ :=
    ⟨hsmooth, hnonexp, hmeas, hunb, hvar, hs.le, le_trans (by norm_num) hK, hσ⟩
  set out : (ℕ → q.Ξ) → q.E := fun ξ => (stage M.sample lam Λ α N q.x0 ξ (S + 1)).1
  have hout : Measurable out := (measurable_stage hmeas lam Λ α N q.x0 (S + 1)).fst
  have hres_m : Measurable (fun ξ => ‖out ξ - M.map (out ξ)‖) := by
    have hT : Continuous M.map := by
      refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => ?_)
      rw [dist_eq_norm, dist_eq_norm]; simpa using hnonexp x y
    exact (hout.sub (hT.measurable.comp hout)).norm
  have hlint : ∫⁻ ξ, ENNReal.ofReal ‖out ξ - M.map (out ξ)‖ ∂P ≤ ENNReal.ofReal q.ε :=
    PowerSmoothFixedPointProcess.tuned_residual_bound q hyp hs hs2 hε xstar hstar hdist
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
          (algorithm q) (fun _ => budget q) seed.1 seed.2)
      ⟨(Measure.dirac ()).prod P, inferInstance⟩
  have hfun : (fun seed : Unit × (ℕ → q.Ξ) =>
      execute
        { Seed := fun _ => q.Ξ
          law := ⟨P, inferInstance⟩
          answer := fun _ (_, x) ω => M.sample ω x }
        (algorithm q) (fun _ => budget q) seed.1 seed.2) =
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

end LongTails.Proofs.PowerSmoothAnchoringConvergence
