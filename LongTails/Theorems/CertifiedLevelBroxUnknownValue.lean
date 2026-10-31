import LongTails.Setups.UnknownValueSmoothConvexLocalLinear
import LongTails.Proofs.CertifiedLevelBroxExecution

namespace OracleTemplate.CertifiedLevelBrox

open LongTails.Setups.UnknownValueSmoothConvexLocalLinear

noncomputable def budget : (let S := spec; S.Params → Fin S.numOracles → ℕ) := fun p _ => ⌈400 * Real.sqrt (p.L * p.R ^ 2 / p.ε) + 40 * Real.logb 2 (2 + (p.Δ + p.L * p.R ^ 2) / p.ε)⌉₊ + 300

theorem result : Convergence LongTails.Setups.UnknownValueSmoothConvexLocalLinear.spec budget := by
  refine ⟨fun p => algorithm p.R p.ε p.x0, ?_, fun _ _ => trivial⟩
  rintro p ⟨hL, hR, hΔ, he⟩ I O
    ⟨hC, hclosed, hx0, hgrad, hlow, hup, hfoo, hlocal, xs, hxs, hmin, hdist, hgap⟩
  let c : Ctx p.E :=
    { C := I.C, f := I.f, grad := gradient I.f, L := p.L, R := p.R, ε := p.ε, Δ := p.Δ,
      x0 := p.x0, xs := xs, convex := hC, x0_mem := hx0, xs_mem := hxs,
      xs_min := fun y hy => hmin hy, dist := hdist, gap0 := hgap, lower := hlow, upper := hup,
      L_nonneg := hL, R_nonneg := hR, ε_pos := he }
  have hO : Valid c O := ⟨hfoo, hlocal⟩
  refine ⟨xs, hxs, hmin, Filter.Eventually.of_forall ?_⟩
  rintro ⟨seed, ξ⟩
  have hB : 400 * Real.sqrt (c.L * c.R ^ 2 / c.ε) +
      40 * Real.logb 2 (2 + (c.Δ + c.L * c.R ^ 2) / c.ε) + 300 ≤
      ((⌈400 * Real.sqrt (p.L * p.R ^ 2 / p.ε) +
        40 * Real.logb 2 (2 + (p.Δ + p.L * p.R ^ 2) / p.ε)⌉₊ + 300 : ℕ) : ℝ) := by
    push_cast
    have := Nat.le_ceil (400 * Real.sqrt (p.L * p.R ^ 2 / p.ε) +
      40 * Real.logb 2 (2 + (p.Δ + p.L * p.R ^ 2) / p.ε))
    linarith
  exact execute_accuracy c hO _ hB seed ξ

end OracleTemplate.CertifiedLevelBrox
