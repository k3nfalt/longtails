import LongTails.Setups.MixedRelativeSmoothNonconvex
import LongTails.Proofs.MixedNoiseOracleCost
import LongTails.Proofs.Execution

open MeasureTheory

namespace OracleTemplate.MixedRelativeSmoothNonconvex

open LongTails.Setups.MixedRelativeSmoothNonconvex MixedNoise

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun q _ => if 2 * q.L * q.Δ ≤ q.ε ^ 2 then 0 else 16777216 * ⌈1 + (1 + q.r) * q.L * q.Δ / q.ε ^ 2 + q.σ ^ 2 / q.ε ^ 2 + min (q.M * q.σ * q.Δ / q.ε ^ 3) (q.L * q.Δ * q.σ ^ 2 / q.ε ^ 4)⌉₊

theorem result : Convergence LongTails.Setups.MixedRelativeSmoothNonconvex.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun q => budget q 0)
  refine ⟨fun q => multiscaleRepresentatives (tunedConfig q.L q.r q.M q.σ q.Δ q.ε) q.x0,
    ?_, fun _ _ => trivial⟩
  intro q hq f O hadm
  obtain ⟨hL, hM, hr, hσ, hΔ, hε⟩ := hq
  obtain ⟨g, p, P, hIID, rfl, hgrad, hlip, hgap, hg, hmean, hnoise, hvar, hmix⟩ := hadm
  let cfg := tunedConfig q.L q.r q.M q.σ q.Δ q.ε
  let paired := P.map (fun ξ k => ξ (k / 2))
  let O : Oracle q.E q.E :=
    { Seed := fun _ => q.Ω, law := paired, answer := fun _ (_, x) ω => g x ω }
  let Q := (PMF.uniformOfFintype (RepresentativeSeed cfg)).toMeasure
  let μ := Q.prod (paired : Measure (ℕ → q.Ω))
  let ν := Q.prod (P : Measure (ℕ → q.Ω))
  let F := fun z : RepresentativeSeed cfg × (ℕ → q.Ω) =>
    execute O (multiscaleRepresentatives cfg q.x0) (fun _ => budget q 0) z.1 z.2
  let B := fun z : RepresentativeSeed cfg × (ℕ → q.Ω) =>
    representativeOutput (batchState cfg g q.x0 z.1 z.2 cfg.tasks.length)
  let φ := fun x => ‖gradient f x‖
  change Measurable F ∧ Integrable (fun z => φ (F z)) μ ∧ (∫ z, φ (F z) ∂μ) ≤ q.ε
  have hF : Measurable F := execute_measurable cfg g hg q.x0 paired (budget q 0)
  have hB : Measurable B := batchOutput_measurable cfg g hg q.x0 cfg.tasks.length
  have hG : LipschitzWith ⟨q.L, hL.le⟩ (gradient f) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change dist (gradient f x) (gradient f y) ≤ q.L * dist x y
    simpa only [dist_eq_norm] using hlip x y
  have hφ : Measurable φ := hG.continuous.measurable.norm
  have hP : (P : Measure (ℕ → q.Ω)) = Measure.infinitePi fun _ : ℕ => (p : Measure q.Ω) := by
    have h := hIID.stream_law.map_eq
    exact (Measure.map_id' (μ := (P : Measure (ℕ → q.Ω)))).symm.trans h
  have hK : cfg.calls ≤ budget q 0 := tuned_calls_bound hL hr hM hσ hΔ hε
  have hlaw : μ.map F = ν.map B := execute_paired_output_law cfg g hg q.x0 P (budget q 0) hK
  have hout := tuned_output_expected_norm (p : Measure q.Ω) hL hr hΔ hε f hgrad hG g hg
    (oracle_integrable_of_centered_sq (p : Measure q.Ω) g (gradient f) hg hnoise)
    hmean hnoise hvar
    (centered_difference_sq_integrable (p : Measure q.Ω) g (gradient f) hg hnoise)
    hmix q.x0 hgap
  have hb : Integrable (fun z => φ (B z)) ν ∧ (∫ z, φ (B z) ∂ν) ≤ q.ε := by
    dsimp only [ν, Q, B, φ, cfg]
    rw [hP]
    exact hout
  have hi : Integrable φ (μ.map F) := by
    rw [hlaw]
    exact (integrable_map_measure hφ.aestronglyMeasurable hB.aemeasurable).mpr hb.1
  refine ⟨hF, (integrable_map_measure hφ.aestronglyMeasurable hF.aemeasurable).mp hi, ?_⟩
  calc
    _ = ∫ x, φ x ∂μ.map F := (integral_map hF.aemeasurable hφ.aestronglyMeasurable).symm
    _ = ∫ x, φ x ∂ν.map B := by rw [hlaw]
    _ = ∫ z, φ (B z) ∂ν := integral_map hB.aemeasurable hφ.aestronglyMeasurable
    _ ≤ q.ε := hb.2

end OracleTemplate.MixedRelativeSmoothNonconvex
