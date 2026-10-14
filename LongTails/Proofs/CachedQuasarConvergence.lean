import LongTails.Proofs.CachedQuasarRate
import LongTails.Proofs.CachedQuasarExecution

namespace OracleTemplate.SimilarQuasar

open LongTails.Setups.SimilarFiniteSumQuasar

lemma execution_accuracy (p : Params) (f : Fin p.n → p.E → ℝ)
    (O : Oracle (Fin p.n × p.E) p.E) (hp : spec.valid p) (ho : spec.admissible p f O) :
    let θ := Real.sqrt (p.μ / p.L)
    let B := 2 * p.Δ / p.γ
    let ν := 48 * p.δ ^ 2 / (p.γ ^ 3 * p.μ ^ 2)
    let r := ν + p.ε / (16 * (p.ε + B))
    let m := ⌈(2 / (p.γ * θ)) * Real.log (1 + 1 / r)⌉₊
    let S := ⌈Real.log (1 + B / p.ε) / Real.log (1 / (2 * r))⌉₊
    ∃ u, IsMinOn (LongTails.Setups.FiniteSumSmoothAndConvex.objective f) Set.univ u ∧
      ∀ (seed : Unit) (ξ : (k : ℕ) → O.Seed k),
        let result := execute O (cachedQuasar p θ m S) (fun _ => ((m + 1 * p.n) * S)) seed ξ
        LongTails.Setups.FiniteSumSmoothAndConvex.objective f result - LongTails.Setups.FiniteSumSmoothAndConvex.objective f u ≤ p.ε := by
  obtain ⟨hμ, hμL, hγ, hγ1, hδ, hsmall, hΔ, hε⟩ := hp
  obtain ⟨hcomponents, hans, hlip, hsim, hcurv, u, hmin, hgap, hquasar, hqg⟩ := ho
  let F := LongTails.Setups.FiniteSumSmoothAndConvex.objective f
  let g : Fin p.n × p.E → p.E := fun ix => gradient (f ix.1) ix.2
  let G := gradient F
  let θ := Real.sqrt (p.μ / p.L)
  let B := 2 * p.Δ / p.γ
  let ν := 48 * p.δ ^ 2 / (p.γ ^ 3 * p.μ ^ 2)
  let r := ν + p.ε / (16 * (p.ε + B))
  let m := ⌈(2 / (p.γ * θ)) * Real.log (1 + 1 / r)⌉₊
  let S := ⌈Real.log (1 + B / p.ε) / Real.log (1 / (2 * r))⌉₊
  have hfull : ∀ x, FiniteSum.fullGradient g x = G x := fun x =>
    (FiniteSum.objective_gradient hcomponents x).gradient.symm
  have hg : ∀ x, HasGradientAt F (G x) x := by
    intro x
    rw [← hfull]
    exact FiniteSum.objective_gradient hcomponents x
  have hmin' : ∀ x, F u ≤ F x := fun x => hmin (Set.mem_univ x)
  have ht := tuning_bounds hμ hμL hγ hγ1 hsmall hΔ hε
  change 0 < θ ∧ p.γ * θ ≤ 1 ∧ θ ^ 2 * p.L ≤ p.μ ∧ 0 ≤ ν ∧ ν ≤ r ∧
    0 < r ∧ 2 * r < 1 ∧ (1 - p.γ * θ / 2) ^ m ≤ r ∧ (2 * r) ^ S * B ≤ p.ε at ht
  obtain ⟨hθ, hrt, hstep, hν, hνr, hrpos, hr1, hm, hS⟩ := ht
  have hepoch : ∀ s, energy F p.μ u (epoch g p.γ θ p.μ m s) ≤ 2 * r * energy F p.μ u s := by
    intro anchor
    apply epoch_energy hrt hν hνr hm anchor (energy_nonneg hμ.le hmin' anchor)
    intro s
    have hs := cached_energy_step hμ hγ hγ1 hθ hrt hstep hδ hsmall hg hlip hfull hsim
      u hmin' hcurv hquasar hqg s anchor
    have hc : 24 * θ * p.δ ^ 2 / (p.γ ^ 2 * p.μ ^ 2) = p.γ * θ / 2 * ν := by
      dsimp [ν]
      field_simp
      ring
    rw [hc] at hs
    exact hs
  have hi := initial_energy hμ hγ hγ1 p.x0 u hgap (hqg p.x0)
  have hr := run_energy (by positivity) hepoch S (p.x0, p.x0)
  have hr' := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (2 * r) ^ S)
  have hacc : F (run g p.γ θ p.μ m S (p.x0, p.x0)).1 - F u ≤ p.ε := by
    have hn : 0 ≤ p.μ / 2 * ‖(run g p.γ θ p.μ m S (p.x0, p.x0)).2 - u‖ ^ 2 := by positivity
    change _ ≤ (2 * r) ^ S * (2 * p.Δ / p.γ) at hr'
    dsimp only [energy, F] at hr hr' ⊢
    change (2 * r) ^ S * (2 * p.Δ / p.γ) ≤ p.ε at hS
    linarith
  refine ⟨u, hmin, ?_⟩
  intro seed ξ
  erw [execute_eq_of_answer_eq O g (fun k ix ξ => hans k ix.1 ix.2 ξ), execute_cachedQuasar (g := g)]
  exact hacc

lemma budget_formula (p : Params) (hγ : p.γ ≠ 0) :
    let θ := Real.sqrt (p.μ / p.L)
    let B := 2 * p.Δ / p.γ
    let ν := 48 * p.δ ^ 2 / (p.γ ^ 3 * p.μ ^ 2)
    let r := ν + p.ε / (16 * (p.ε + B))
    let m := ⌈(2 / (p.γ * θ)) * Real.log (1 + 1 / r)⌉₊
    let S := ⌈Real.log (1 + B / p.ε) / Real.log (1 / (2 * r))⌉₊
    (m + p.n) * S =
      (p.n + ⌈2 * Real.sqrt (p.L / p.μ) / p.γ * Real.log (1 + 1 / (48 * p.δ ^ 2 / (p.γ ^ 3 * p.μ ^ 2) + p.γ * p.ε / (16 * (p.γ * p.ε + 2 * p.Δ))))⌉₊) * ⌈Real.log (1 + 2 * p.Δ / (p.γ * p.ε)) / Real.log (1 / (2 * (48 * p.δ ^ 2 / (p.γ ^ 3 * p.μ ^ 2) + p.γ * p.ε / (16 * (p.γ * p.ε + 2 * p.Δ)))))⌉₊ := by
  have hθ : 2 / (p.γ * Real.sqrt (p.μ / p.L)) = 2 * Real.sqrt (p.L / p.μ) / p.γ := by
    rw [div_mul_eq_div_div, div_right_comm, div_eq_mul_one_div 2,
      one_div, ← Real.sqrt_inv, inv_div]
  have hr : p.ε / (16 * (p.ε + 2 * p.Δ / p.γ)) =
      p.γ * p.ε / (16 * (p.γ * p.ε + 2 * p.Δ)) := by
    field_simp
  dsimp only
  rw [hθ, hr, div_div, Nat.add_comm]

end OracleTemplate.SimilarQuasar
