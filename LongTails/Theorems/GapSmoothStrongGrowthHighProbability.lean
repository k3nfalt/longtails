import LongTails.Setups.GapSmoothStrongGrowth
import LongTails.Proofs.Execution
import LongTails.Proofs.GapStrongGrowthAccuracy

open MeasureTheory

namespace OracleTemplate.GapStrongGrowth

open LongTails.Setups.GapSmoothStrongGrowth

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈134217728 * (1 + Real.log (1 / p.δ)) * ((1 + p.R * Real.sqrt p.H1) * Real.log (1 + p.Δ / p.ε) + p.R * Real.sqrt (p.H0 / p.ε))⌉₊ * ⌈p.ρ⌉₊

theorem result : Convergence LongTails.Setups.GapSmoothStrongGrowth.spec budget := by
  apply convergence_of_public_budget (S := spec) (fun p => budget p 0)
  refine ⟨algorithm, ?_, fun _ _ => trivial⟩
  intro p hp f O h
  rcases hp with ⟨h0, h1, hR, hΔ, hρ, hε, hεΔ, hδ, hδ1⟩
  rcases h with ⟨g, μ, P, h_samples, rfl, hconv, hgrad, ⟨u, hmin, hr, hgap, hmodel⟩, hg⟩
  let N : ℕ := ⌈134217728 * (1 + Real.log (1 / p.δ)) * ((1 + p.R * Real.sqrt p.H1) * Real.log (1 + p.Δ / p.ε) + p.R * Real.sqrt (p.H0 / p.ε))⌉₊
  have hN : 16 * p.R ^ 2 / p.ε ≤ weight p N :=
    explicit_iterations_suffice p hR hΔ hε hεΔ h0 hδ hδ1
  have hb : 0 < batchSize p := by
    have hc : p.ρ ≤ (batchSize p : ℝ) := Nat.le_ceil _
    have : 0 < (batchSize p : ℝ) := by linarith
    exact_mod_cast this
  have hh := iid_failure_bound p hR hΔ h0 h1 hρ hε hδ hδ1
    hconv hgrad hmin hmodel hr hgap (μ : Measure _) P h_samples hg N hN
  have he : (fun seed : Unit × (ℕ → p.Ω) =>
      (execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (algorithm p) (fun _ => (N * batchSize p)) seed.1 seed.2)) =
      fun seed => (run p g (fun k i => seed.2 (k * batchSize p + i.val)) N).1 := by
    funext ⟨⟨⟩, ξ⟩
    exact (execute_run p g P ξ hb N)
  refine ⟨?_, u, hmin, ?_⟩
  · change Measurable (fun seed : Unit × (ℕ → p.Ω) =>
      (execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
        (algorithm p) (fun _ => (N * batchSize p)) seed.1 seed.2))
    rw [he]
    exact hh.1
  · change (∫ seed : Unit × (ℕ → p.Ω),
      (if p.ε < f ((fun seed : Unit × (ℕ → p.Ω) =>
        (execute { Seed := fun _ => p.Ω, law := P, answer := fun _ (_, x) ω => g x ω }
          (algorithm p) (fun _ => (N * batchSize p)) seed.1 seed.2)) seed) - f u
      then (1 : ℝ) else 0) ∂(Measure.dirac ()).prod (P : Measure _)) ≤ p.δ
    rw [he]
    exact hh.2

end OracleTemplate.GapStrongGrowth
